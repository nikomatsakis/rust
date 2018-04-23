// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::nll::{AllFacts, BorrowRegionVid};
use rustc::mir::Location;
use rustc::ty::RegionVid;
use rustc_data_structures::fx::FxHashMap;
use std::borrow::Cow;
use std::path::PathBuf;

mod timely;

#[derive(Clone, Debug, Default)]
crate struct LiveBorrowResults {
    borrow_live_at: FxHashMap<Location, Vec<BorrowRegionVid>>,

    // these are just for debugging
    restricts: FxHashMap<Location, FxHashMap<BorrowRegionVid, Vec<RegionVid>>>,
    region_live_at: FxHashMap<Location, Vec<RegionVid>>,

    // Each (R1 @ P1) <= (R2 @ P2) relation, indexed by P2.
    superset: FxHashMap<Location, Vec<(RegionVid, Location, RegionVid)>>,
}

impl LiveBorrowResults {
    crate fn compute<'tcx>(
        all_facts: AllFacts,
        dump_facts_dir: Option<PathBuf>,
    ) -> Self {
        if let Some(dir) = dump_facts_dir {
            all_facts.write_to_dir(dir).unwrap();
        }

        timely::timely_dataflow(all_facts)
    }

    fn new() -> Self {
        LiveBorrowResults::default()
    }

    crate fn borrows_in_scope_at(
        &self,
        location: Location,
    ) -> &[BorrowRegionVid] {
        match self.borrow_live_at.get(&location) {
            Some(p) => p,
            None => &[],
        }
    }

    crate fn restricts_at(
        &self,
        location: Location,
    ) -> Cow<'_, FxHashMap<BorrowRegionVid, Vec<RegionVid>>> {
        match self.restricts.get(&location) {
            Some(map) => Cow::Borrowed(map),
            None => Cow::Owned(FxHashMap())
        }
    }

    crate fn regions_live_at(
        &self,
        location: Location,
    ) -> &[RegionVid] {
        match self.region_live_at.get(&location) {
            Some(v) => v,
            None => &[],
        }
    }

    crate fn superset(
        &self,
        location: Location,
    ) -> &[(RegionVid, Location, RegionVid)] {
        match self.superset.get(&location) {
            Some(v) => v,
            None => &[],
        }
    }
}

