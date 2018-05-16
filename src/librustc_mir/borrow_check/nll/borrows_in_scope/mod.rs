// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::location::{LocationIndex, LocationTable};
use borrow_check::nll::facts::AllFacts;
use dataflow::indexes::BorrowIndex;
use rustc::hir::def_id::DefId;
use rustc::ty::{RegionVid, TyCtxt};
use rustc::util::common;
use rustc_data_structures::fx::FxHashMap;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::PathBuf;

mod timely;

#[derive(Clone, Debug)]
crate struct LiveBorrowResults {
    borrow_live_at: FxHashMap<LocationIndex, Vec<BorrowIndex>>,

    dump_enabled: bool,

    // these are just for debugging
    restricts: FxHashMap<LocationIndex, BTreeMap<RegionVid, BTreeSet<BorrowIndex>>>,
    region_live_at: FxHashMap<LocationIndex, Vec<RegionVid>>,
    subset: FxHashMap<LocationIndex, BTreeMap<RegionVid, BTreeSet<RegionVid>>>,
}

impl LiveBorrowResults {
    crate fn compute<'tcx>(
        tcx: TyCtxt<'_, '_, '_>,
        mir_def_id: DefId,
        location_table: &LocationTable,
        all_facts: AllFacts,
        dump_enabled: bool,
    ) -> Self {
        if tcx.sess.opts.debugging_opts.nll_facts {
            let def_path = tcx.hir.def_path(mir_def_id);
            let dir_path = PathBuf::from("nll-facts").join(def_path.to_filename_friendly_no_crate());
            all_facts.write_to_dir(dir_path, location_table).unwrap();
        }

        common::time(
            tcx.sess,
            &format!("LiveBorrowResults::compute({:?})", mir_def_id),
            || timely::timely_dataflow(dump_enabled, all_facts),
        )
    }

    fn new(dump_enabled: bool) -> Self {
        LiveBorrowResults {
            borrow_live_at: FxHashMap::default(),
            restricts: FxHashMap::default(),
            region_live_at: FxHashMap::default(),
            subset: FxHashMap::default(),
            dump_enabled,
        }
    }

    crate fn borrows_in_scope_at(
        &self,
        location: LocationIndex,
    ) -> &[BorrowIndex] {
        match self.borrow_live_at.get(&location) {
            Some(p) => p,
            None => &[],
        }
    }

    crate fn restricts_at(
        &self,
        location: LocationIndex,
    ) -> Cow<'_, BTreeMap<RegionVid, BTreeSet<BorrowIndex>>> {
        assert!(self.dump_enabled);
        match self.restricts.get(&location) {
            Some(map) => Cow::Borrowed(map),
            None => Cow::Owned(BTreeMap::default())
        }
    }

    crate fn regions_live_at(
        &self,
        location: LocationIndex,
    ) -> &[RegionVid] {
        assert!(self.dump_enabled);
        match self.region_live_at.get(&location) {
            Some(v) => v,
            None => &[],
        }
    }

    crate fn subsets_at(
        &self,
        location: LocationIndex,
    ) -> Cow<'_, BTreeMap<RegionVid, BTreeSet<RegionVid>>> {
        assert!(self.dump_enabled);
        match self.subset.get(&location) {
            Some(v) => Cow::Borrowed(v),
            None => Cow::Owned(BTreeMap::default()),
        }
    }
}

