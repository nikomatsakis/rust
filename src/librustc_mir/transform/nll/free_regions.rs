// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Code to extract the free regions declared on a function and the
//! relationships between them. For example:
//!
//! ```
//! fn foo<'a, 'b, 'c: 'b>() { }
//! ```
//!
//! here we would be returning a map assigning each of `{'a, 'b, 'c}`
//! to an index, as well as the `FreeRegionMap` which can compute
//! relationships between them.
//!
//! The code in this file doesn't *do anything* with those results; it
//! just returns them for other code to use.

use rustc::hir::def_id::DefId;
use rustc::infer::InferCtxt;
use rustc::middle::free_region::FreeRegionMap;
use rustc::ty::{self, RegionVid};
use rustc::ty::subst::Substs;
use rustc::util::nodemap::FxHashMap;
use rustc_data_structures::indexed_vec::Idx;

#[derive(Debug)]
pub struct FreeRegions<'tcx> {
    /// Given a free region defined on this function (either early- or
    /// late-bound), this maps it to its internal region index. When
    /// the region context is created, the first N variables will be
    /// created based on these indices.
    pub indices: FxHashMap<ty::Region<'tcx>, RegionVid>,

    /// The map from the typeck tables telling us how to relate free regions.
    pub free_region_map: &'tcx FreeRegionMap<'tcx>,
}

pub fn free_regions<'a, 'gcx, 'tcx>(
    infcx: &InferCtxt<'a, 'gcx, 'tcx>,
    mir_def_id: DefId,
) -> FreeRegions<'tcx> {
    debug!("free_regions(mir_def_id={:?})", mir_def_id);

    let tcx = infcx.tcx;
    let mut indices = FxHashMap();

    // `'static` is always free.
    insert_free_region(&mut indices, tcx.types.re_static);

    // Walk up the def-ids of all enclosing closures, up to (and
    // including) the enclosing fn item. If this is a fn item, then
    // this just visits it.
    let tables = tcx.typeck_tables_of(mir_def_id);
    for def_id in tcx.closure_base_def_ids(mir_def_id) {
        // Extract the early regions.
        let substs = Substs::identity_for_item(infcx.tcx, def_id);
        for region in substs.iter().filter_map(|k| k.as_region()) {
            insert_free_region(&mut indices, region);
        }

        // Extract the late-bound regions. Use the liberated fn sigs,
        // where the late-bound regions will have been converted into free
        // regions, and add them to the map.
        let fn_hir_id =
            tcx.hir.node_to_hir_id(
                tcx.hir.as_local_node_id(def_id).unwrap());
        let fn_sig = tables.liberated_fn_sigs()[fn_hir_id];
        tcx.for_each_free_region(&fn_sig.inputs_and_output, |region| {
            if let ty::ReFree(_) = *region {
                insert_free_region(&mut indices, region);
            }
        });
    }

    debug!("free_regions: indices={:#?}", indices);

    FreeRegions { indices, free_region_map: &tables.free_region_map }
}

fn insert_free_region<'tcx>(
    free_regions: &mut FxHashMap<ty::Region<'tcx>, RegionVid>,
    region: ty::Region<'tcx>,
) {
    let next = RegionVid::new(free_regions.len());
    free_regions.entry(region).or_insert(next);
}

