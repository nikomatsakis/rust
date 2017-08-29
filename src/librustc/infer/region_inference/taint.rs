// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The "Tainted" code is used for computing the LUB/GLB for
//! higher-ranked types. See the README for `infer::higher_ranked` for
//! more information.

use super::{AddCombination, AddConstraint, AddGiven, AddVar, AddVerify,
            CommitedSnapshot,
            ConstrainVarSubVar, ConstrainVarSubReg, ConstrainRegSubReg, ConstrainRegSubVar,
            OpenSnapshot,
            RegionSnapshot, RegionVarBindings,
            UndoLogEntry,
            Verify};

use ty::{self, TyCtxt, Region, ReVar};
use rustc_data_structures::fx::FxHashSet;

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
    regions: FxHashSet<ty::Region<'tcx>>
}

impl<'a, 'gcx, 'tcx> TaintSet<'tcx> {
    fn new(directions: TaintDirections,
           initial_region: ty::Region<'tcx>)
           -> Self {
        let mut regions = FxHashSet();
        regions.insert(initial_region);
        TaintSet { directions: directions, regions: regions }
    }

    fn fixed_point(&mut self,
                   tcx: TyCtxt<'a, 'gcx, 'tcx>,
                   undo_log: &[UndoLogEntry<'tcx>],
                   verifys: &[Verify<'tcx>]) {
        let mut prev_len = 0;
        while prev_len < self.len() {
            debug!("tainted: prev_len = {:?} new_len = {:?}",
                   prev_len, self.len());

            prev_len = self.len();

            for undo_entry in undo_log {
                match undo_entry {
                    &AddConstraint(ConstrainVarSubVar(a, b)) => {
                        self.add_edge(tcx.mk_region(ReVar(a)),
                                      tcx.mk_region(ReVar(b)));
                    }
                    &AddConstraint(ConstrainRegSubVar(a, b)) => {
                        self.add_edge(a, tcx.mk_region(ReVar(b)));
                    }
                    &AddConstraint(ConstrainVarSubReg(a, b)) => {
                        self.add_edge(tcx.mk_region(ReVar(a)), b);
                    }
                    &AddConstraint(ConstrainRegSubReg(a, b)) => {
                        self.add_edge(a, b);
                    }
                    &AddGiven(a, b) => {
                        self.add_edge(a, tcx.mk_region(ReVar(b)));
                    }
                    &AddVerify(i) => {
                        verifys[i].bound.for_each_region(&mut |b| {
                            self.add_edge(verifys[i].region, b);
                        });
                    }
                    &AddCombination(..) |
                    &AddVar(..) |
                    &OpenSnapshot |
                    &CommitedSnapshot => {}
                }
            }
        }
    }

    fn into_set(self) -> FxHashSet<ty::Region<'tcx>> {
        self.regions
    }

    fn len(&self) -> usize {
        self.regions.len()
    }

    fn add_edge(&mut self,
                source: ty::Region<'tcx>,
                target: ty::Region<'tcx>) {
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

impl<'a, 'gcx, 'tcx> RegionVarBindings<'a, 'gcx, 'tcx> {
    /// Computes all regions that have been related to `r0` since the
    /// mark `mark` was made---`r0` itself will be the first
    /// entry. The `directions` parameter controls what kind of
    /// relations are considered. For example, one can say that only
    /// "incoming" edges to `r0` are desired, in which case one will
    /// get the set of regions `{r|r <= r0}`. This is used when
    /// checking whether skolemized regions are being improperly
    /// related to other regions.
    pub fn tainted(&self,
                   mark: &RegionSnapshot,
                   r0: Region<'tcx>,
                   directions: TaintDirections)
                   -> FxHashSet<ty::Region<'tcx>> {
        debug!("tainted(mark={:?}, r0={:?}, directions={:?})",
               mark, r0, directions);

        // `result_set` acts as a worklist: we explore all outgoing
        // edges and add any new regions we find to result_set.  This
        // is not a terribly efficient implementation.
        let mut taint_set = TaintSet::new(directions, r0);
        taint_set.fixed_point(self.tcx,
                              &self.undo_log.borrow()[mark.length..],
                              &self.verifys.borrow());
        debug!("tainted: result={:?}", taint_set.regions);
        return taint_set.into_set();
    }
}
