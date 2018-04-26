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
                        universal_region,
                        cfg_edge,
                        killed,
                        outlives,
                        use_live,
                        drop_live,
                        use_region,
                        drop_region,
                    ) = ..my_facts;
                }

                // .decl region_live_at( r:region, p:point )
                let region_live_at = {
                    // region_live_at(R, P) :- use_live(X, P), use_region(X, R).
                    let region_live_at1 = use_live.join(&use_region).map(|(_x, p, r)| (r, p));

                    // region_live_at(R, P) :- drop_live(X, P), drop_region(X, R).
                    let region_live_at2 = drop_live.join(&drop_region).map(|(_x, p, r)| (r, p));

                    region_live_at1.concat(&region_live_at2).distinct()
                };

                // .decl subset(Ra, Rb, P) -- at the point P, R1 <= R2 holds
                let subset = outlives.iterate(|subset| {
                    let outlives = outlives.enter(&subset.scope());
                    let cfg_edge = cfg_edge.enter(&subset.scope());
                    let region_live_at = region_live_at.enter(&subset.scope());
                    let universal_region = universal_region.enter(&subset.scope());

                    // subset(R1, R2, P) :- outlives(R1, R2, P).
                    let subset1 = outlives.clone();

                    // subset(R1, R3, P) :-
                    //   subset(R1, R2, P),
                    //   subset(R2, R3, P).
                    let subset2 = subset
                        .map(|(r1, r2, q)| ((r2, q), r1))
                        .join(&subset.map(|(r2, r3, p)| ((r2, p), r3)))
                        .map(|((_r2, p), r1, r3)| (r1, r3, p));

                    // subset(R1, R2, Q) :-
                    //   subset(R1, R2, P),
                    //   cfg_edge(P, Q),
                    //   (region_live_at(R1, Q); universal_region(R1)),
                    //   (region_live_at(R2, Q); universal_region(R2)).
                    let subset3base = subset.map(|(r1, r2, p)| (p, (r1, r2))).join(&cfg_edge);
                    let subset3a = subset3base
                        .map(|(_p, (r1, r2), q)| ((r1, q), r2))
                        .semijoin(&region_live_at)
                        .map(|((r1, q), r2)| ((r2, q), r1))
                        .semijoin(&region_live_at)
                        .map(|((r2, q), r1)| (r1, r2, q));
                    let subset3b = subset3base
                        .map(|(_p, (r1, r2), q)| (r1, (q, r2)))
                        .semijoin(&universal_region)
                        .map(|(r1, (q, r2))| (r2, (q, r1)))
                        .semijoin(&universal_region)
                        .map(|(r2, (q, r1))| (r1, r2, q));
                    let subset3c = subset3base
                        .map(|(_p, (r1, r2), q)| ((r1, q), r2))
                        .semijoin(&region_live_at)
                        .map(|((r1, q), r2)| (r2, (q, r1)))
                        .semijoin(&universal_region)
                        .map(|(r2, (q, r1))| (r1, r2, q));
                    let subset3d = subset3base
                        .map(|(_p, (r1, r2), q)| (r1, (q, r2)))
                        .semijoin(&universal_region)
                        .map(|(r1, (q, r2))| ((r2, q), r1))
                        .semijoin(&region_live_at)
                        .map(|((r2, q), r1)| (r1, r2, q));

                    subset1
                        .concat(&subset2)
                        .concat(&subset3a)
                        .concat(&subset3b)
                        .concat(&subset3c)
                        .concat(&subset3d)
                        .distinct()
                });

                // .decl requires(R, B, P) -- at the point, things with region R
                // may depend on data from borrow B
                let requires = borrow_region.iterate(|requires| {
                    let borrow_region = borrow_region.enter(&requires.scope());
                    let subset = subset.enter(&requires.scope());
                    let killed = killed.enter(&requires.scope());
                    let region_live_at = region_live_at.enter(&requires.scope());
                    let cfg_edge = cfg_edge.enter(&requires.scope());
                    let universal_region = universal_region.enter(&requires.scope());

                    // requires(R, B, P) :- borrow_region(R, B, P).
                    let requires1 = borrow_region.clone();

                    // requires(R2, B, P) :-
                    //   requires(R1, B, P),
                    //   subset(R1, R2, P).
                    let requires2 = requires
                        .map(|(r1, b, p)| ((r1, p), b))
                        .join(&subset.map(|(r1, r2, p)| ((r1, p), r2)))
                        .map(|((_r1, p), b, r2)| (r2, b, p));

                    // requires(R, B, Q) :-
                    //   requires(R, B, P),
                    //   !killed(B, P),
                    //   cfg_edge(P, Q),
                    //   (region_live_at(R, Q); universal_region(R)).
                    let requires_propagate_base = requires
                        .map(|(r, b, p)| ((b, p), r))
                        .antijoin(&killed)
                        .map(|((b, p), r)| (p, (r, b)))
                        .join(&cfg_edge);
                    let requires3 = requires_propagate_base
                        .map(|(_p, (r, b), q)| ((r, q), b))
                        .semijoin(&region_live_at)
                        .map(|((r, q), b)| (r, b, q));
                    let requires4 = requires_propagate_base
                        .map(|(_p, (r, b), q)| (r, (q, b)))
                        .semijoin(&universal_region)
                        .map(|(r, (q, b))| (r, b, q));

                    requires1
                        .concat(&requires2)
                        .concat(&requires3)
                        .concat(&requires4)
                        .distinct()
                });

                // .decl borrow_live_at(B, P) -- true if the restrictions of the borrow B
                // need to be enforced at the point P
                let borrow_live_at = {
                    // borrow_live_at(B, P) :- requires(R, B, P), region_live_at(R, P)
                    let borrow_live_at1 =
                        requires
                        .map(|(r, b, p)| ((r, p), b))
                        .semijoin(&region_live_at)
                        .map(|((_r, p), b)| (b, p));

                    // borrow_live_at(B, P) :- requires(R, B, P), universal_region(R).
                    let borrow_live_at2 =
                        requires
                        .map(|(r, b, p)| (r, (p, b)))
                        .semijoin(&universal_region)
                        .map(|(_r, (p, b))| (b, p));

                    borrow_live_at1.concat(&borrow_live_at2).distinct()
                };

                region_live_at.inspect_batch({
                    let result = result.clone();
                    move |_timestamp, facts| {
                        let mut result = result.lock().unwrap();
                        for ((region, location), _timestamp, multiplicity) in facts {
                            assert_eq!(*multiplicity, 1);
                            result
                                .region_live_at
                                .entry(*location)
                                .or_insert(vec![])
                                .push(*region);
                        }
                    }
                });

                requires.inspect_batch({
                    let result = result.clone();
                    move |_timestamp, facts| {
                        let mut result = result.lock().unwrap();
                        for ((region, borrow, location), _timestamp, multiplicity) in facts {
                            assert_eq!(*multiplicity, 1);
                            result
                                .restricts
                                .entry(*location)
                                .or_insert(BTreeMap::new())
                                .entry(*region)
                                .or_insert(Vec::new())
                                .push(*borrow);
                        }
                    }
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
