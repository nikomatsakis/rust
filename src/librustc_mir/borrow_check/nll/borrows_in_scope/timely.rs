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

use borrow_check::nll::borrows_in_scope::LiveBorrowResults;
use borrow_check::nll::facts::AllFacts;
use differential_dataflow::collection::Collection;
use differential_dataflow::operators::*;
use rustc_data_structures::fx::FxHashMap;
use std::mem;
use std::sync::mpsc;
use std::sync::Arc;
use std::sync::Mutex;
use timely;
use timely::dataflow::operators::*;

/*
Datalog rules:

## Inputs

use(X, P).  // variable is used during P (but before successor(P))
drop(X, P). // variable is dropped at P
definition(X, P).  // variable is reassigned during P
cfgEdge(P1, P2).

useLive(X, P) :-
  use(X, P).

useLive(X, P) :-
  useLive(X, Q),
  cfgEdge(P, Q),
  !definition(X, P).

dropLive(X, P) :-
  drop(X, P).

dropLive(X, P) :-
  dropLive(X, Q),
  cfgEdge(P, Q),
  !useLive(X, P),
  !definition(X, P).

covariantUseRegion(X, R). // input: R appears in a covariant position within type X (like T = &R U)
contravariantUseRegion(X, R). // input: R appears in a contravariant position within T

covariantDropRegion(X, R). // when drop executes, R is live, and appears in covariant pos
contravariantDropRegion(X, R).

outlives(R1, R2, P). // on entry to P, R1: R2 must hold (R1 <= R2)

## subset

```
subset((R1, P), (R2, P)) :-
  outlives(R1, R2, P).

subset((R, P), (R, Q)) :-
  useLive(X, Q),
  cfgEdge(P, Q),
  covariantVarRegion(X, R).

subset((R, Q), (R, P)) :-
  useLive(X, Q),
  cfgEdge(P, Q),
  contravariantVarRegion(X, R).

subset((R, P), (R, Q)) :-
  cfgEdge(P, Q),
  dropLive(X, Q),
  dropRegion(X, R),
  covariantVarRegion(X, R).

subset((R, Q), (R, P)) :-
  cfgEdge(P, Q),
  dropLive(X, Q),
  dropRegion(X, R),
  contravariantVarRegion(X, R).
```

## Rules

```
restricts(R, B, P) :-
  borrowRegion(R, B, P).

restricts(R1, B, P1) :-
  restricts(R2, B, P2),
  !killed(B, P2),
  subset((R2, P2), (R1, P1)),
```

## Region Live At

```
regionLiveAt(R, P) :-
  useLive(X, P),
  covariantVarRegion(X, R).

regionLiveAt(R, P) :-
  useLive(X, P),
  contravariantVarRegion(X, R).

regionLiveAt(R, P) :-
  dropLive(X, P),
  dropRegion(X, R).
```

## Borrow Live At

```
borrowLiveAt(B, P) :-
  restricts(R, B, P),
  regionLiveAt(R, P).
```

*/

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
            // First come, first serve: one worker gets all the facts;
            // the others get empty vectors.
            let my_facts = rx.lock()
                .unwrap()
                .recv()
                .unwrap_or_else(|_| AllFacts::default());

            worker.dataflow::<(), _, _>(|scope| {
                macro_rules! let_collections {
                    (let ($($facts:ident,)*) = ..$base:expr;) => {
                        let ($($facts),*) = (
                            $(Collection::<_, _, isize>::new(
                                $base.$facts
                                    .to_stream(scope)
                                    .map(|datum| (datum, Default::default(), 1)),
                            ),)*
                        );
                    }
                }

                let_collections! {
                    let (
                        borrow_region,
                        cfg_edge,
                        killed,
                        outlives,
                        use_live,
                        drop_live,
                        covariant_var_region,
                        contravariant_var_region,
                        covariant_assign_region,
                        contravariant_assign_region,
                        drop_region,
                    ) = ..my_facts;
                }

                let predecessors = cfg_edge.map(|(p, q)| (q, p));

                // .decl subset( (r1:region, p1:point), (r2:region, p2:point) )
                let subset = {
                    // subset((R1, P), (R2, P)) :- outlives(R1, R2, P).
                    let subset1 = outlives.map(|(r1, r2, p)| ((r1, p), (r2, p)));

                    // subset(R, P, R, Q) :- useLive(X, Q), cfgEdge(P, Q), covariantVarRegion(X, R).
                    let subset2 = use_live
                        .map(|(x, q)| (q, x))
                        .join(&predecessors)
                        .map(|(q, x, p)| (x, (p, q)))
                        .join(&covariant_var_region)
                        .map(|(_x, (p, q), r)| ((r, p), (r, q)));

                    // subset(R, Q, R, P) :- useLive(X, Q), cfgEdge(P, Q), contravariantVarRegion(X, R).
                    let subset3 = use_live
                        .map(|(x, q)| (q, x))
                        .join(&predecessors)
                        .map(|(q, x, p)| (x, (p, q)))
                        .join(&contravariant_var_region)
                        .map(|(_x, (p, q), r)| ((r, q), (r, p)));

                    // subset(R, P, R, Q) :- dropLive(X, Q),
                    //                       cfgEdge(P, Q),
                    //                       dropRegion(X, R),
                    //                       covariantVarRegion(X, R).
                    let subset4 = drop_live
                        .map(|(x, q)| (q, x))
                        .join(&predecessors)
                        .map(|(q, x, p)| (x, (p, q)))
                        .join(&drop_region)
                        .map(|(x, (p, q), r)| ((x, r), (p, q)))
                        .semijoin(&covariant_var_region)
                        .map(|((_x, r), (p, q))| ((r, p), (r, q)));

                    // subset(R, Q, R, P) :- dropLive(X, Q),
                    //                       cfgEdge(P, Q),
                    //                       dropRegion(X, R),
                    //                       contravariantVarRegion(X, R).
                    let subset5 = drop_live
                        .map(|(x, q)| (q, x))
                        .join(&predecessors)
                        .map(|(q, x, p)| (x, (p, q)))
                        .join(&drop_region)
                        .map(|(x, (p, q), r)| ((x, r), (p, q)))
                        .semijoin(&contravariant_var_region)
                        .map(|((_x, r), (p, q))| ((r, q), (r, p)));

                    // subset(R, P, R, Q) :- covariantAssignRegion(P, R), cfgEdge(P, Q).
                    let subset6 = covariant_assign_region
                        .join(&cfg_edge)
                        .map(|(p, r, q)| ((r, p), (r, q)));

                    // subset(R, Q, R, P) :- contravariantAssignRegion(P, R), cfgEdge(P, Q)
                    let subset7 = contravariant_assign_region
                        .join(&cfg_edge)
                        .map(|(p, r, q)| ((r, q), (r, p)));

                    subset1
                        .concat(&subset2)
                        .concat(&subset3)
                        .concat(&subset4)
                        .concat(&subset5)
                        .concat(&subset6)
                        .concat(&subset7)
                        .distinct()
                        .inspect_batch({
                            let result = result.clone();
                            move |_timestamp, facts| {
                                let mut result = result.lock().unwrap();
                                for (((r1, p1), (r2, p2)), _timestamp, multiplicity) in facts {
                                    assert_eq!(*multiplicity, 1);
                                    result
                                        .superset
                                        .entry(*p2)
                                        .or_insert(vec![])
                                        .push((*r1, *p1, *r2));
                                }
                            }
                        })
                };

                // .decl restricts( r:region, b:borrow, p:point )
                let restricts = borrow_region.iterate(|restricts| {
                    let borrow_region = borrow_region.enter(&restricts.scope());
                    let killed = killed.enter(&restricts.scope());
                    let subset = subset.enter(&restricts.scope());

                    // restricts(R, B, P) :- borrowRegion(R, B, P).
                    let restricts1 = borrow_region.clone();

                    // restricts(R1, B, P1) :-
                    //   restricts(R2, B, P2)
                    //   !killed(B, P2)
                    //   subset((R2, P2), (R1, P1)).
                    let restricts2 = restricts
                        .map(|(r2, b, p2)| ((b, p2), r2))
                        .antijoin(&killed)
                        .map(|((b, p2), r2)| ((r2, p2), b))
                        .join(&subset)
                        .map(|((_r2, _p2), b, (r1, p1))| (r1, b, p1));

                    restricts1.concat(&restricts2).distinct().inspect_batch({
                        let result = result.clone();
                        move |_timestamp, facts| {
                            let mut result = result.lock().unwrap();
                            for ((region, borrow, location), _timestamp, multiplicity) in facts {
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

                //// .decl regionLiveAt( r:region, p:point )
                //let region_live_at = {
                //    // regionLiveAt(R, P) :- useLive(X, P), covariantRegion(X, R).
                //    let region_live_at1 = use_live.join(&covariant_region).map(|(_x, p, r)| (r, p));
                //
                //    // regionLiveAt(R, P) :- useLive(X, P), contravariantRegion(X, R).
                //    let region_live_at2 =
                //        use_live.join(&contravariant_region).map(|(_x, p, r)| (r, p));
                //
                //    // regionLiveAt(R, P) :- dropLive(X, P), dropRegion(X, R).
                //    let region_live_at3 = drop_live.join(&drop_region).map(|(_x, p, r)| (r, p));
                //
                //    region_live_at1
                //        .concat(&region_live_at2)
                //        .concat(&region_live_at3)
                //        .distinct()
                //        .inspect_batch({
                //            let result = result.clone();
                //            move |_timestamp, facts| {
                //                let mut result = result.lock().unwrap();
                //                for ((region, location), _timestamp, multiplicity) in facts {
                //                    assert_eq!(*multiplicity, 1);
                //                    result
                //                        .region_live_at
                //                        .entry(*location)
                //                        .or_insert(vec![])
                //                        .push(*region);
                //                }
                //            }
                //        })
                //};

                // borrowPoint(B, P) :-
                //   borrowRegion(R, B, P).
                let borrow_point = borrow_region.map(|(_r, b, p)| (b, p));

                // borrowLiveAt(B, P) :-
                //   borrowPoint(B, P).
                // borrowLiveAt(B, Q) :-
                //   borrowLiveAt(B, P),
                //   cfgEdge(P, Q),
                //   restricts(R, B, Q).
                let borrow_live_at = borrow_point.iterate(|borrow_live_at| {
                    let borrow_point = borrow_point.enter(&borrow_live_at.scope());
                    let cfg_edge = cfg_edge.enter(&borrow_live_at.scope());
                    let restricts = restricts.enter(&borrow_live_at.scope());

                    let borrow_live_at1 = borrow_point.clone();

                    let borrow_live_at2 = borrow_live_at
                        .map(|(b, p)| (p, b))
                        .join(&cfg_edge)
                        .map(|(_p, b, q)| ((b, q), ()))
                        .semijoin(&restricts.map(|(_r, b, q)| (b, q)))
                        .map(|((b, q), ())| (b, q));

                    borrow_live_at1.concat(&borrow_live_at2).distinct()
                });

                borrow_live_at.inspect_batch({
                    let result = result.clone();
                    move |_timestamp, facts| {
                        let mut result = result.lock().unwrap();
                        for ((borrow, location), _timestamp, multiplicity) in facts {
                            assert_eq!(*multiplicity, 1);
                            result
                                .borrow_live_at
                                .entry(*location)
                                .or_insert(Vec::new())
                                .push(*borrow);
                        }
                    }
                });
            });
        }
    }).unwrap();

    // Remove from the Arc and Mutex, since it is fully populated now.
    Arc::try_unwrap(result)
        .unwrap_or_else(|_| panic!("somebody still has a handle to this arc"))
        .into_inner()
        .unwrap()
}
