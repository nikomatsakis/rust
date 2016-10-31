// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use infer::InferCtxt;
use rustc_data_structures::fx::FxHashSet;
use traits::{ObligationCause, PredicateObligation};
use ty;

/// Computes all regions that have been related to `r0` since the
/// mark `mark` was made---`r0` itself will be the first
/// entry. The `directions` parameter controls what kind of
/// relations are considered. For example, one can say that only
/// "incoming" edges to `r0` are desired, in which case one will
/// get the set of regions `{r|r <= r0}`. This is used when
/// checking whether skolemized regions are being improperly
/// related to other regions.
pub fn tainted_regions<'a, 'gcx, 'tcx>(infcx: &InferCtxt<'a, 'gcx, 'tcx>,
                                       source: &'tcx ty::Region,
                                       obligations: &[PredicateObligation<'tcx>],
                                       directions: TaintDirections)
                                       -> FxHashSet<&'tcx ty::Region> {
    debug!("tainted(source={:?}, directions={:?}, obligations={:?})",
           source, directions, obligations);

    // `result_set` acts as a worklist: we explore all outgoing
    // edges and add any new regions we find to result_set.  This
    // is not a terribly efficient implementation.
    let mut taint_set = TaintSet::new(directions, source);
    taint_set.fixed_point(&obligations);
    debug!("tainted: result={:?}", taint_set.regions);
    return taint_set.into_set();
}

/// When working with skolemized regions, we often wish to find all of
/// the regions that are either reachable from a skolemized region, or
/// which can reach a skolemized region, or both. We call such regions
/// *tained* regions.  This struct allows you to decide what set of
/// tainted regions you want.
#[derive(Debug)]
pub struct TaintDirections {
    incoming: bool,
    outgoing: bool,
}

impl TaintDirections {
    pub fn incoming() -> Self {
        TaintDirections { incoming: true, outgoing: false }
    }

    pub fn outgoing() -> Self {
        TaintDirections { incoming: false, outgoing: true }
    }

    pub fn both() -> Self {
        TaintDirections { incoming: true, outgoing: true }
    }
}

struct TaintSet<'tcx> {
    directions: TaintDirections,
    regions: FxHashSet<&'tcx ty::Region>
}

impl<'tcx> TaintSet<'tcx> {
    fn new(directions: TaintDirections,
           initial_region: &'tcx ty::Region)
           -> Self {
        let mut regions = FxHashSet();
        regions.insert(initial_region);
        TaintSet { directions: directions, regions: regions }
    }

    fn fixed_point(&mut self,
                   obligations: &[PredicateObligation<'tcx>]) {
        let mut prev_len = 0;
        while prev_len < self.len() {
            debug!("tainted: prev_len = {:?} new_len = {:?}",
                   prev_len, self.len());

            prev_len = self.len();

            for obligation in obligations {
                self.process(obligation);
            }
        }
    }

    fn process(&mut self,
               obligation: &PredicateObligation<'tcx>) {
        self.process_predicate(&obligation.cause, &obligation.predicate)
    }

    fn process_predicate(&mut self,
                         cause: &ObligationCause<'tcx>,
                         predicate: &ty::Predicate<'tcx>) {
        match *predicate {
            ty::Predicate::RegionOutlives(ref data) => {
                match *data.skip_binder() {
                    ty::OutlivesPredicate(&ty::ReLateBound(..), _) |
                    ty::OutlivesPredicate(_, &ty::ReLateBound(..)) => {
                        span_bug!(cause.span, "unexpected HR outlives: {:?}", predicate);
                    }
                    ty::OutlivesPredicate(a, b) => {
                        self.add_edge(b, a); // a: b => b -> a
                    }
                }
            }
            ty::Predicate::Trait(_) |
            ty::Predicate::Projection(_) |
            ty::Predicate::Equate(_) |
            ty::Predicate::TypeOutlives(..) |
            ty::Predicate::WellFormed(_) |
            ty::Predicate::ObjectSafe(_) |
            ty::Predicate::ClosureKind(..) => {
                // We have to figure out how we are going to handle
                // these cases at some point, but currently they do
                // not arise. If we adopt lazy norm, they will.
                span_bug!(cause.span, "unexpected predicate: {:?}", predicate);
            }
        }
    }

    fn into_set(self) -> FxHashSet<&'tcx ty::Region> {
        self.regions
    }

    fn len(&self) -> usize {
        self.regions.len()
    }

    fn add_edge(&mut self,
                source: &'tcx ty::Region,
                target: &'tcx ty::Region) {
        if self.directions.incoming {
            if self.regions.contains(&target) {
                self.regions.insert(source);
            }
        }

        if self.directions.outgoing {
            if self.regions.contains(&source) {
                self.regions.insert(target);
            }
        }
    }
}

