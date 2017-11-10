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
use rustc::middle::free_region::FreeRegionMap;
use rustc::ty::{self, TyCtxt, TypeckTables, RegionVid};
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

impl<'tcx> FreeRegions<'tcx> {
    pub fn new(tcx: TyCtxt<'_, '_, 'tcx>, mir_def_id: DefId) -> Self {
        let tables = tcx.typeck_tables_of(mir_def_id);
        FreeRegions {
            indices: FxHashMap::default(),
            free_region_map: &tables.free_region_map,
        }.init(tcx, mir_def_id, tables)
    }

    fn init(
        mut self,
        tcx: TyCtxt<'_, '_, 'tcx>,
        mir_def_id: DefId,
        tables: &'tcx TypeckTables<'tcx>,
    ) -> Self {
        // `'static` is always free.
        self.insert_free_region(tcx.types.re_static);

        // Walk up the def-ids of all enclosing closures, up to (and
        // including) the enclosing fn item. If this is a fn item, then
        // this just visits it.
        for def_id in tcx.closure_base_def_ids(mir_def_id) {
            // Extract the early regions.
            let substs = Substs::identity_for_item(tcx, def_id);
            for region in substs.iter().filter_map(|k| k.as_region()) {
                self.insert_free_region(region);
            }

            // Extract the late-bound regions. Use the liberated fn sigs,
            // where the late-bound regions will have been converted into free
            // regions, and add them to the map.
            let fn_hir_id = tcx.hir
                .node_to_hir_id(tcx.hir.as_local_node_id(def_id).unwrap());
            let fn_sig = tables.liberated_fn_sigs()[fn_hir_id];
            tcx.for_each_free_region(&fn_sig.inputs_and_output, |region| {
                if let ty::ReFree(_) = *region {
                    self.insert_free_region(region);
                }
            });
        }

        debug!("free_regions: indices={:#?}", self.indices);

        self
    }

    /// Inserts `region` into the map, assigning it the next
    /// `RegionVid` if it is not already present.
    fn insert_free_region(&mut self, region: ty::Region<'tcx>) -> RegionVid {
        let next = RegionVid::new(self.indices.len());
        *self.indices.entry(region).or_insert(next)
    }
}
