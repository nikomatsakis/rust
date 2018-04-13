// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Timely dataflow runs on its own thread.

use borrow_check::nll::region_infer::borrows_in_scope::{AllFacts, LiveBorrowResults};
use differential_dataflow::collection::Collection;
use differential_dataflow::operators::*;
use rustc_data_structures::fx::FxHashMap;
use std::mem;
use std::sync::mpsc;
use std::sync::Arc;
use std::sync::Mutex;
use timely;
use timely::dataflow::operators::*;
use timely::dataflow::ProbeHandle;

pub(super) fn timely_dataflow(all_facts: AllFacts) -> LiveBorrowResults {
    let result = Arc::new(Mutex::new(LiveBorrowResults::new()));

    // Use a channel to send `all_facts` to one worker (and only one)
    let (tx, rx) = mpsc::channel();
    tx.send(all_facts).unwrap();
    mem::drop(tx);
    let rx = Mutex::new(rx);

    timely::execute_from_args(vec![].into_iter(), {
        let result = result.clone();
        move |worker| {
            let probe = &mut ProbeHandle::new();

            // First come, first serve: one worker gets all the facts;
            // the others get empty vectors.
            let my_facts = rx.lock()
                .unwrap()
                .recv()
                .unwrap_or_else(|_| AllFacts::default());

            worker.dataflow::<(), _, _>(|scope| {
                macro_rules! make_collections {
                    ($($facts:expr,)*) => {
                        (
                            $(Collection::<_, _, isize>::new(
                                $facts
                                    .to_stream(scope)
                                    .map(|datum| (datum, Default::default(), 1)),
                            ),)*
                        )
                    }
                }

                let tuple = {
                    make_collections! {
                        my_facts.borrow_region,
                        my_facts.next_statement,
                        my_facts.goto,
                        my_facts.region_live_on_entry,
                        my_facts.killed,
                        my_facts.outlives,
                    }
                };
                let (borrow_region, next_statement, goto, region_live_on_entry, killed, outlives) =
                    tuple;

                // cfgEdge(P, Q) :- nextStatement(P, Q).
                // cfgEdge(P, Q) :- goto(P, Q).
                let cfg_edge = next_statement.concat(&goto).distinct().probe_with(probe);

                // .decl regionLiveAt( r:region, p:point )
                let region_live_at = {
                    // regionLiveAt(R, P) :- regionLiveOnEntryToStatement(R, P).
                    let region_live_at1 = region_live_on_entry.clone();

                    // regionLiveAt(R, P) :-
                    //   goto(P, Q),
                    //   regionLiveOnEntryToStatement(R, Q).
                    let region_live_at2 = {
                        let goto_invert = goto.map(|(p, q)| (q, p));
                        let region_live_on_entry_invert = region_live_on_entry.map(|(r, q)| (q, r));
                        goto_invert.join_map(&region_live_on_entry_invert, |_q, &p, &r| (r, p))
                    };

                    region_live_at1.concat(&region_live_at2).distinct()
                };

                // .decl restricts( r:region, b:borrow, p:point )
                let restricts = borrow_region.iterate(|restricts| {
                    let borrow_region = borrow_region.enter(&restricts.scope());
                    let outlives = outlives.enter(&restricts.scope());
                    let killed = killed.enter(&restricts.scope());
                    let cfg_edge = cfg_edge.enter(&restricts.scope());
                    let region_live_at = region_live_at.enter(&restricts.scope());

                    // restricts(R, B, P) :- borrowRegion(R, B, P).
                    let restricts1 = borrow_region.clone();

                    // restricts(R1, B, Q) :-
                    //   restricts(R2, B, P)
                    //   !killed(B, P)
                    //   outlives(P, R2, R1, Q)
                    let restricts2 = restricts
                        .map(|(r2, b, p)| ((b, p), r2))
                        .antijoin(&killed)
                        .map(|((b, p), r2)| ((p, r2), b))
                        .join(&outlives.map(|(p, r2, r1, q)| ((p, r2), (r1, q))))
                        .map(|((_p, _r2), b, (r1, q))| (r1, b, q));

                    // restricts(R1, B, Q) :-
                    //   restricts(R1, B, P)
                    //   !killed(B, P)
                    //   cfgEdge(P, Q)
                    //   regionLiveAt(R1, Q)
                    let restricts3 = restricts
                        .map(|(r1, b, p)| ((b, p), r1))
                        .antijoin(&killed)
                        .map(|((b, p), r1)| (p, (b, r1)))
                        .join(&cfg_edge)
                        .map(|(_p, (b, r1), q)| ((r1, q), b))
                        .semijoin(&region_live_at)
                        .map(|((r1, q), b)| (r1, b, q));

                    restricts1
                        .concat(&restricts2)
                        .concat(&restricts3)
                        .distinct()
                        .inspect_batch({
                            let result = result.clone();
                            move |_timestamp, facts| {
                                let mut result = result.lock().unwrap();
                                for ((region, borrow, location), _timestamp, multiplicity) in facts
                                {
                                    assert_eq!(*multiplicity, 1);
                                    result
                                        .restricts
                                        .entry(*location)
                                        .or_insert(FxHashMap())
                                        .entry(*borrow)
                                        .or_insert(vec![])
                                        .push(*region);
                                }
                            }
                        })
                });

                // .decl pointsTo( r:region, b:borrow, p:point )
                let _points_to = borrow_region.iterate(|points_to| {
                    let borrow_region = borrow_region.enter(&points_to.scope());
                    let outlives = outlives.enter(&points_to.scope());
                    let cfg_edge = cfg_edge.enter(&points_to.scope());
                    let region_live_at = region_live_at.enter(&points_to.scope());

                    // pointsTo(R, B, P) :- borrowRegion(R, B, P).
                    let points_to1 = borrow_region.clone();

                    // pointsTo(R1, B, Q) :-
                    //   pointsTo(R2, B, P)
                    //   outlives(P, R2, R1, Q)
                    let points_to2 = points_to
                        .map(|(r2, b, p)| ((p, r2), b))
                        .join(&outlives.map(|(p, r2, r1, q)| ((p, r2), (r1, q))))
                        .map(|((_p, _r2), b, (r1, q))| (r1, b, q));

                    // pointsTo(R1, B, Q) :-
                    //   pointsTo(R1, B, P)
                    //   cfgEdge(P, Q)
                    //   regionLiveAt(R1, Q)
                    let points_to3 = points_to
                        .map(|(r1, b, p)| (p, (b, r1)))
                        .join(&cfg_edge)
                        .map(|(_p, (b, r1), q)| ((r1, q), b))
                        .semijoin(&region_live_at)
                        .map(|((r1, q), b)| (r1, b, q));

                    points_to1
                        .concat(&points_to2)
                        .concat(&points_to3)
                        .distinct()
                        .inspect(|_| ()) // FIXME we should save these somewhere
                });

                // borrowLiveAt(B, P) :-
                //   restricts(R, B, P)
                //   regionLiveAt(R, P)
                let _borrow_live_at = {
                    let result = result.clone();
                    restricts
                        .map(|(r, b, p)| ((r, p), b))
                        .semijoin(&region_live_at)
                        .map(|((_r, p), b)| (b, p))
                        .distinct()
                        .inspect_batch(move |_timestamp, facts| {
                            let mut result = result.lock().unwrap();
                            for ((borrow, location), _timestamp, multiplicity) in facts {
                                assert_eq!(*multiplicity, 1);
                                result
                                    .borrow_live_at
                                    .entry(*location)
                                    .or_insert(Vec::new())
                                    .push(*borrow);
                            }
                        })
                };
            });
        }
    }).unwrap();

    // Remove from the Arc and Mutex, since it is fully populated now.
    Arc::try_unwrap(result)
        .unwrap_or_else(|_| panic!("somebody still has a handle to this arc"))
        .into_inner()
        .unwrap()
}
