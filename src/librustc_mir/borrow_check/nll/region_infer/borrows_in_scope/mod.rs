// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(unused_imports)] // TODO

use borrow_check::borrow_set::BorrowSet;
use borrow_check::nll::region_infer::{RegionInferenceContext, RegionValues};
use borrow_check::nll::region_infer::values::RegionElementIndex;
use dataflow::move_paths::indexes::BorrowIndex;
use rustc::hir::def_id::DefId;
use rustc::mir::{Location, Mir};
use rustc::ty::RegionVid;
use rustc_data_structures::fx::FxHashMap;
use std::borrow::Cow;
use std::sync::Arc;

mod facts;
mod timely;

#[derive(Default)]
crate struct AllFacts {
    // Successor:
    // - if P -> Q in the CFG, then Q is a successor of P
    // - if P is an exit from CFG, then all universal regions are successors of P
    crate successor: Vec<(RegionElementIndex, RegionElementIndex)>,

    // an `R1: R2 @ P` constraint
    crate outlives: Vec<(RegionVid, RegionVid, RegionElementIndex)>,

    // the base `R1: {P}` constriants
    crate region_live_at: Vec<(RegionVid, RegionElementIndex)>,
}

pub(super) fn compute_region_values<'tcx>(
    regioncx: &RegionInferenceContext<'tcx>,
    mir: &Mir<'tcx>,
    mir_def_id: DefId,
    dump_facts_dir: Option<String>,
) -> RegionValues {
    let all_facts = AllFacts::produce(regioncx, mir, mir_def_id);
    if let Some(dir) = dump_facts_dir {
        all_facts.write_to_dir(dir).unwrap();
    }
    timely::timely_dataflow(all_facts, &regioncx.liveness_constraints)
}
