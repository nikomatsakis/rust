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
use std::collections::BTreeMap;
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
cfg_edge(P1, P2).

use_live(X, P) :-
  use(X, P).

use_live(X, P) :-
  use_live(X, Q),
  cfg_edge(P, Q),
  !definition(X, P).

drop_live(X, P) :-
  drop(X, P).

drop_live(X, P) :-
  drop_live(X, Q),
  cfg_edge(P, Q),
  !use_live(X, P),
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
  use_live(X, Q),
  cfg_edge(P, Q),
  covariant_var_region(X, R).

subset((R, Q), (R, P)) :-
  use_live(X, Q),
  cfg_edge(P, Q),
  contravariant_var_region(X, R).

subset((R, P), (R, Q)) :-
  cfg_edge(P, Q),
  drop_live(X, Q),
  drop_region(X, R),
  covariant_var_region(X, R).

subset((R, Q), (R, P)) :-
  cfg_edge(P, Q),
  drop_live(X, Q),
  drop_region(X, R),
  contravariant_var_region(X, R).
```

## Rules

```
restricts(R, B, P) :-
  borrow_region(R, B, P).

restricts(R1, B, P1) :-
  restricts(R2, B, P2),
  !killed(B, P2),
  subset((R2, P2), (R1, P1)),
```

## Region Live At

```
region_live_at(R, P) :-
  use_live(X, P),
  covariant_var_region(X, R).

region_live_at(R, P) :-
  use_live(X, P),
  contravariant_var_region(X, R).

region_live_at(R, P) :-
  drop_live(X, P),
  drop_region(X, R).
```

## Borrow Live At

```
borrow_live_at(B, P) :-
  restricts(R, B, P),
  region_live_at(R, P).
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

                let carry_forward_to = {
                    // carry_forward_to(R, Q) :- use_live(X, Q), covariant_var_region(X, R).
                    let carry_forward_to1 = use_live
                        .join(&covariant_var_region)
                        .map(|(_x, q, r)| (r, q));

                    // carry_forward_to(R, Q) :- drop_live(X, Q), drop_region(X, R), covariant_var_region(X, R).
                    let carry_forward_to2 = drop_live
                        .join(&drop_region)
                        .map(|(x, q, r)| ((x, r), q))
                        .semijoin(&covariant_var_region)
                        .map(|((_x, r), q)| (r, q));

                    // carry_forward_to(R, Q) :- covariant_assign_region(P, R), cfg_edge(P, Q).
                    let carry_forward_to3 = covariant_assign_region
                        .join(&cfg_edge)
                        .map(|(_p, r, q)| (r, q));

                    carry_forward_to1
                        .concat(&carry_forward_to2)
                        .concat(&carry_forward_to3)
                        .distinct()
                };

                let carry_backward_from = {
                    // carry_backward_from(R, Q) :- use_live(X, Q), contravariant_var_region(X, R).
                    let carry_backward_from1 = use_live
                        .join(&contravariant_var_region)
                        .map(|(_x, q, r)| (r, q));

                    // carry_backward_from(Q, R) :-
                    //   drop_live(X, Q),
                    //   drop_region(X, R),
                    //   contravariant_var_region(X, R).
                    let carry_backward_from2 = drop_live
                        .join(&drop_region)
                        .map(|(x, q, r)| ((x, r), q))
                        .semijoin(&contravariant_var_region)
                        .map(|((_x, r), q)| (r, q));

                    // carry_backward_from(R, Q) :- contravariant_assign_region(Q, R).
                    let carry_backward_from3 = contravariant_assign_region.map(|(q, r)| (r, q));

                    carry_backward_from1
                        .concat(&carry_backward_from2)
                        .concat(&carry_backward_from3)
                        .distinct()
                };

                // .decl restricts( r:region, b:borrow, p:point )
                let restricts = borrow_region.iterate(|restricts| {
                    let borrow_region = borrow_region.enter(&restricts.scope());
                    let killed = killed.enter(&restricts.scope());
                    let cfg_edge = cfg_edge.enter(&restricts.scope());
                    let carry_forward_to = carry_forward_to.enter(&restricts.scope());
                    let carry_backward_from = carry_backward_from.enter(&restricts.scope());
                    let outlives = outlives.enter(&restricts.scope());

                    // restricts(R, B, P) :- borrow_region(R, B, P).
                    let restricts1 = borrow_region.clone();

                    // restricts(R1, B, P) :-
                    //   restricts(R2, B, P),
                    //   outlives(R2, R1, P).
                    let restricts2 = restricts
                        .map(|(r2, b, p)| ((r2, p), b))
                        .join(&outlives.map(|(r2, r1, p)| ((r2, p), r1)))
                        .map(|((_r2, p), b, r1)| (r1, b, p));

                    // restricts(R, B, Q) :-
                    //   restricts(R, B, P)
                    //   !killed(B, P),
                    //   cfg_edge(P, Q),
                    //   carry_forward_to(R, Q).
                    let restricts3 = restricts
                        .map(|(r, b, p)| ((b, p), r))
                        .antijoin(&killed)
                        .map(|((b, p), r)| (p, (b, r)))
                        .join(&cfg_edge)
                        .map(|(p, (b, r), q)| ((r, q), (p, b)))
                        .semijoin(&carry_forward_to)
                        .map(|((r, q), (_p, b))| (r, b, q));

                    // restricts(R, B, P) :-
                    //   restricts(R, B, Q),
                    //   carry_backward_from(R, Q),
                    //   cfg_edge(P, Q).
                    let restricts4 = restricts
                        .map(|(r, b, q)| ((r, q), b))
                        .semijoin(&carry_backward_from)
                        .map(|((r, q), b)| (q, (r, b)))
                        .join(&cfg_edge)
                        .map(|(_q, (r, b), p)| (r, b, p));

                    restricts1
                        .concat(&restricts2)
                        .concat(&restricts3)
                        .concat(&restricts4)
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
                                        .or_insert(BTreeMap::default())
                                        .entry(*region)
                                        .or_insert(vec![])
                                        .push(*borrow);
                                }
                            }
                        })
                });

                // .decl region_live_at( p:point, r:region )
                let region_live_at = {
                    // region_live_at(P, R) :- use_live(X, P), covariant_var_region(X, R).
                    let region_live_at1 = use_live
                        .join(&covariant_var_region)
                        .map(|(_x, p, r)| (p, r));

                    // region_live_at(P, R) :- use_live(X, P), contravariant_var_region(X, R).
                    let region_live_at2 = use_live
                        .join(&contravariant_var_region)
                        .map(|(_x, p, r)| (p, r));

                    // region_live_at(P, R) :- drop_live(X, P), drop_region(X, R).
                    let region_live_at3 = drop_live.join(&drop_region).map(|(_x, p, r)| (p, r));

                    region_live_at1
                        .concat(&region_live_at2)
                        .concat(&region_live_at3)
                        .distinct()
                        .inspect_batch({
                            let result = result.clone();
                            move |_timestamp, facts| {
                                let mut result = result.lock().unwrap();
                                for ((location, region), _timestamp, multiplicity) in facts {
                                    assert_eq!(*multiplicity, 1);
                                    result
                                        .region_live_at
                                        .entry(*location)
                                        .or_insert(vec![])
                                        .push(*region);
                                }
                            }
                        })
                };

                // borrow_point(B, P) :-
                //   borrow_region(R, B, P).
                let borrow_point = borrow_region.map(|(_r, b, p)| (b, p));

                // borrow_live_at(B, Q) :-
                //   borrow_point(B, P),
                //   cfg_edge(P, Q).
                // borrow_live_at(B, Q) :-
                //   borrow_live_at(B, P),
                //   cfg_edge(P, Q),
                //   region_live_at(Q, R),
                //   restricts(R, B, Q).
                let base_borrow_live_at = borrow_point
                    .map(|(b, p)| (p, b))
                    .join(&cfg_edge)
                    .map(|(_p, b, q)| (b, q));
                let borrow_live_at = base_borrow_live_at.iterate(|borrow_live_at| {
                    let base_borrow_live_at = base_borrow_live_at.enter(&borrow_live_at.scope());
                    let cfg_edge = cfg_edge.enter(&borrow_live_at.scope());
                    let restricts = restricts.enter(&borrow_live_at.scope());
                    let region_live_at = region_live_at.enter(&borrow_live_at.scope());

                    let borrow_live_at1 = base_borrow_live_at.clone();

                    let borrow_live_at2 = borrow_live_at
                        .map(|(b, p)| (p, b))
                        .join(&cfg_edge)
                        .map(|(_p, b, q)| (q, b))
                        .join(&region_live_at)
                        .map(|(q, b, r)| ((r, b, q), ()))
                        .semijoin(&restricts)
                        .map(|((_r, b, q), ())| (b, q));

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
