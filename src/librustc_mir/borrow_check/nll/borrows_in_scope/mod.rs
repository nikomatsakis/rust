// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::borrow_set::BorrowRegionVid;
use borrow_check::location::LocationIndex;
use borrow_check::nll::facts::AllFacts;
use rustc::hir::def_id::DefId;
use rustc::ty::{RegionVid, TyCtxt};
use rustc_data_structures::fx::FxHashMap;
use std::borrow::Cow;
use std::path::PathBuf;

mod timely;

#[derive(Clone, Debug, Default)]
crate struct LiveBorrowResults {
    borrow_live_at: FxHashMap<LocationIndex, Vec<BorrowRegionVid>>,

    // these are just for debugging
    restricts: FxHashMap<LocationIndex, FxHashMap<BorrowRegionVid, Vec<RegionVid>>>,
    region_live_at: FxHashMap<LocationIndex, Vec<RegionVid>>,

    // Each (R1 @ P1) <= (R2 @ P2) relation, indexed by P2.
    superset: FxHashMap<LocationIndex, Vec<(RegionVid, LocationIndex, RegionVid)>>,
}

impl LiveBorrowResults {
    crate fn compute<'tcx>(
        tcx: TyCtxt<'_, '_, '_>,
        mir_def_id: DefId,
        all_facts: AllFacts,
    ) -> Self {
        if tcx.sess.opts.debugging_opts.nll_facts {
            let def_path = tcx.hir.def_path(mir_def_id);
            let dir_path = PathBuf::from("nll-facts").join(def_path.to_filename_friendly_no_crate());
            all_facts.write_to_dir(dir_path).unwrap();
        }

        timely::timely_dataflow(all_facts)
    }

    fn new() -> Self {
        LiveBorrowResults::default()
    }

    crate fn borrows_in_scope_at(
        &self,
        location: LocationIndex,
    ) -> &[BorrowRegionVid] {
        match self.borrow_live_at.get(&location) {
            Some(p) => p,
            None => &[],
        }
    }

    crate fn restricts_at(
        &self,
        location: LocationIndex,
    ) -> Cow<'_, FxHashMap<BorrowRegionVid, Vec<RegionVid>>> {
        match self.restricts.get(&location) {
            Some(map) => Cow::Borrowed(map),
            None => Cow::Owned(FxHashMap())
        }
    }

    crate fn regions_live_at(
        &self,
        location: LocationIndex,
    ) -> &[RegionVid] {
        match self.region_live_at.get(&location) {
            Some(v) => v,
            None => &[],
        }
    }

    crate fn superset(
        &self,
        location: LocationIndex,
    ) -> &[(RegionVid, LocationIndex, RegionVid)] {
        match self.superset.get(&location) {
            Some(v) => v,
            None => &[],
        }
    }
}

