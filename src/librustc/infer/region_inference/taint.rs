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
            UndoLogEntry};

use std::cell::Ref;
use ty::{self, TyCtxt, Region, ReVar};
use rustc_data_structures::fx::FxHashSet;

pub(in infer) struct TaintIterator<'a, 'gcx: 'tcx, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    undo_log: Ref<'a, [UndoLogEntry<'tcx>]>,
    regions: FxHashSet<ty::NormalizedRegion>,
    queue: Vec<ty::Region<'tcx>>,
}

impl<'a, 'gcx, 'tcx> TaintIterator<'a, 'gcx, 'tcx> {
    fn new(tcx: TyCtxt<'a, 'gcx, 'tcx>,
           undo_log: Ref<'a, [UndoLogEntry<'tcx>]>,
           param_env: ty::ParamEnv<'tcx>,
           initial_region: ty::Region<'tcx>)
           -> Self {
        let mut regions = FxHashSet();
        let norm_initial_region = param_env.normalize_region(initial_region);
        regions.insert(norm_initial_region);
        let queue = vec![initial_region];
        TaintIterator { tcx, undo_log, regions, queue }
    }

    fn add_edge(regions: &mut FxHashSet<ty::NormalizedRegion>,
                queue: &mut Vec<ty::Region<'tcx>>,
                param_env: ty::ParamEnv<'tcx>,
                source: ty::Region<'tcx>,
                target: ty::Region<'tcx>) {
        let norm_source = param_env.normalize_region(source);
        let norm_target = param_env.normalize_region(target);

        if regions.contains(&norm_target) {
            if regions.insert(norm_source) {
                queue.push(source);
            }
        }

        if regions.contains(&norm_source) {
            if regions.insert(norm_target) {
                queue.push(target);
            }
        }
    }
}

impl<'a, 'gcx, 'tcx> Iterator for TaintIterator<'a, 'gcx, 'tcx> {
    type Item = ty::Region<'tcx>;

    fn next(&mut self) -> Option<ty::Region<'tcx>> {
        let region = match self.queue.pop() {
            Some(r) => r,
            None => return None,
        };

        for undo_entry in &self.undo_log[..] {
            match undo_entry {
                &AddConstraint(ConstrainVarSubVar(param_env, a, b)) => {
                    Self::add_edge(&mut self.regions,
                                   &mut self.queue,
                                   param_env,
                                   self.tcx.mk_region(ReVar(a)),
                                   self.tcx.mk_region(ReVar(b)));
                }
                &AddConstraint(ConstrainRegSubVar(param_env, a, b)) => {
                    Self::add_edge(&mut self.regions,
                                   &mut self.queue,
                                   param_env,
                                   a,
                                   self.tcx.mk_region(ReVar(b)));
                }
                &AddConstraint(ConstrainVarSubReg(param_env, a, b)) => {
                    Self::add_edge(&mut self.regions,
                                   &mut self.queue,
                                   param_env,
                                   self.tcx.mk_region(ReVar(a)),
                                   b);
                }
                &AddConstraint(ConstrainRegSubReg(param_env, a, b)) => {
                    Self::add_edge(&mut self.regions,
                                   &mut self.queue,
                                   param_env,
                                   a,
                                   b);
                }
                &AddGiven(..) => {
                    bug!("cannot use taint when givens have been added")
                }
                &AddVerify(..) => {
                    bug!("cannot use taint when verifys have been added")
                }
                &AddCombination(..) |
                &AddVar(..) |
                &OpenSnapshot |
                &CommitedSnapshot => {}
            }
        }

        Some(region)
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
    pub(in infer) fn tainted<'this>(&'this self,
                                    mark: &RegionSnapshot,
                                    param_env: ty::ParamEnv<'tcx>,
                                    r0: Region<'tcx>)
                                    -> TaintIterator<'this, 'gcx, 'tcx> {
        debug!("tainted(mark={:?}, r0={:?})", mark, r0);

        // `result_set` acts as a worklist: we explore all outgoing
        // edges and add any new regions we find to result_set.  This
        // is not a terribly efficient implementation.
        let undo_log = Ref::map(self.undo_log.borrow(), |l| &l[mark.length..]);
        TaintIterator::new(self.tcx, undo_log, param_env, r0)
    }
}
