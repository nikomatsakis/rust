// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::borrow_set::BorrowSet;
use borrow_check::nll::region_infer::RegionInferenceContext;
use dataflow::move_paths::indexes::BorrowIndex;
use rustc::hir::def_id::DefId;
use rustc::mir::{Location, Mir};
use rustc::ty::RegionVid;
use rustc_data_structures::fx::FxHashMap;
use std::borrow::Cow;

mod facts;
mod timely;

#[derive(Default)]
crate struct AllFacts {
    crate borrow_region: Vec<(RegionVid, BorrowIndex, Location)>,
    crate next_statement: Vec<(Location, Location)>,
    crate goto: Vec<(Location, Location)>,
    crate region_live_on_entry: Vec<(RegionVid, Location)>,
    crate killed: Vec<(BorrowIndex, Location)>,
    crate outlives: Vec<(Location, RegionVid, RegionVid, Location)>,
}

#[derive(Clone, Debug)]
crate struct LiveBorrowResults {
    borrow_live_at: FxHashMap<Location, Vec<BorrowIndex>>,

    // this is just for debugging
    restricts: FxHashMap<Location, FxHashMap<BorrowIndex, Vec<RegionVid>>>,
}

impl LiveBorrowResults {
    crate fn compute<'tcx>(
        regioncx: &RegionInferenceContext<'tcx>,
        borrow_set: &BorrowSet<'tcx>,
        mir: &Mir<'tcx>,
        mir_def_id: DefId,
        dump_facts_dir: Option<String>,
    ) -> Self {
        let all_facts = AllFacts::produce(regioncx, borrow_set, mir, mir_def_id);

        if let Some(dir) = dump_facts_dir {
            all_facts.write_to_dir(dir).unwrap();
        }

        timely::timely_dataflow(all_facts)
    }

    fn new() -> Self {
        LiveBorrowResults {
            borrow_live_at: FxHashMap(),
            restricts: FxHashMap(),
        }
    }

    crate fn restricts_at(
        &self,
        location: Location,
    ) -> Cow<'_, FxHashMap<BorrowIndex, Vec<RegionVid>>> {
        match self.restricts.get(&location) {
            Some(map) => Cow::Borrowed(map),
            None => Cow::Owned(FxHashMap())
        }
    }

    crate fn borrows_in_scope_at(
        &self,
        location: Location,
    ) -> &[BorrowIndex] {
        match self.borrow_live_at.get(&location) {
            Some(p) => p,
            None => &[],
        }
    }
}

