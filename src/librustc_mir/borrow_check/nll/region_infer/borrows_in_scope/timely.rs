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

use borrow_check::nll::region_infer::borrows_in_scope::AllFacts;
use borrow_check::nll::region_infer::values::RegionValues;
use borrow_check::nll::region_infer::{Cause, TrackCauses};
use differential_dataflow::collection::Collection;
use differential_dataflow::operators::iterate::Variable;
use differential_dataflow::operators::*;
use rustc_data_structures::fx::FxHashMap;
use std::mem;
use std::sync::mpsc;
use std::sync::Arc;
use std::sync::Mutex;
use timely;
use timely::dataflow::operators::*;
use timely::dataflow::ProbeHandle;
use timely::dataflow::Scope;

/*

Datalog reference

// inputs

successor(P, Q).
outlives(R1, R2, P).
regionLiveAt(R, P).

// Region P contains the point P

containsPoint(R, P) :-
  regionLiveAt(R, P).

containsPoint(R1, Q) :-
  outlives(R1, R2, P),
  reachable(R2, P, Q).

// Point Q is reachable from P without leaving R2.

reachable(R2, P, P) :-
  outlives(R1, R2, P).

reachable(R2, P, R) :-
  reachable(R2, P, Q),
  successor(Q, R),
  containsPoint(R2, R).

*/

pub(super) fn timely_dataflow(all_facts: AllFacts, base_values: &RegionValues) -> RegionValues {
    let result = Arc::new(Mutex::new(base_values.duplicate(TrackCauses(false))));

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
            let my_facts = rx.lock().unwrap().recv().unwrap_or(AllFacts::default());

            worker.dataflow::<(), _, _>({
                let result = result.clone();
                move |scope| {
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

                    let (successor, outlives, region_live_at) = {
                        make_collections! {
                            my_facts.successor,
                            my_facts.outlives,
                            my_facts.region_live_at,
                        }
                    };

                    let contains_point = scope.scoped(|inner| {
                        let outlives = outlives.enter(inner);
                        let successor = successor.enter(inner);
                        let region_live_at = region_live_at.enter(inner);

                        let reachable_seed = outlives.map(|(_r1, r2, p)| (r2, p, p));
                        let reachable = Variable::from(reachable_seed.clone());

                        let contains_point_seed = region_live_at;
                        let contains_point = Variable::from(contains_point_seed.clone());

                        let reachable1 = reachable
                            .clone()
                            .map(|(r2, p, q)| (q, (r2, p)))
                            .join(&successor)
                            .map(|(_q, (r2, p), r)| ((r2, r), p))
                            .semijoin(&contains_point)
                            .map(|((r2, r), p)| (r2, p, r));
                        let reachable_new_val = reachable_seed.concat(&reachable1).distinct();

                        let contains_point1 = outlives
                            .map(|(r1, r2, p)| ((r2, p), r1))
                            .join(&reachable.clone().map(|(r2, p, q)| ((r2, p), q)))
                            .map(|((_r2, _p), r1, q)| (r1, q));
                        let contains_point_new_val =
                            contains_point_seed.concat(&contains_point1).distinct();

                        reachable.set(&reachable_new_val);
                        contains_point.set(&contains_point_new_val);

                        contains_point_new_val.leave()
                    });

                    contains_point.inspect_batch({
                        let result = result.clone();
                        move |_timestamp, facts| {
                            let mut result = result.lock().unwrap();
                            for ((r, p), _, _) in facts {
                                result.add(*r, *p, &Cause::Unknown); // TODO
                            }
                        }
                    });
                }
            });
        }
    }).unwrap();

    Arc::try_unwrap(result)
        .unwrap_or_else(|_| panic!("somebody still has a handle to this arc"))
        .into_inner()
        .unwrap()
}
