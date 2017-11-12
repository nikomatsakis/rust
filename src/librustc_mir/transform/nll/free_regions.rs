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
use rustc::infer::region_constraints::GenericKind;
use rustc::infer::outlives::bounds::{self, OutlivesBound};
use rustc::ty::{self, RegionVid, TyCtxt};
use rustc::ty::subst::Substs;
use rustc::util::nodemap::{FxHashMap, FxHashSet};
use rustc_data_structures::indexed_vec::Idx;
use rustc_data_structures::transitive_relation::TransitiveRelation;

#[derive(Debug)]
pub struct FreeRegions<'tcx> {
    /// Given a free region defined on this function (either early- or
    /// late-bound), this maps it to its internal region index. When
    /// the region context is created, the first N variables will be
    /// created based on these indices.
    ///
    /// Note that the "keys" and "values" of `indices` are disjoint --
    /// that is, the key regions never contain `ReVar`, and the value
    /// regions always do, so we can intermingle them, safe in the
    /// knowledge of how to map from one to the other later.
    ///
    /// This is important because when we invoke the MIR type checker,
    /// it sometimes must do trait resolution and other things, and
    /// this is done in terms of the parameter environment. The
    /// environment contains the free regions that were originally
    /// declared, and not our corresponding inference variables, and
    /// hence we sometimes get back results in terms of those regions.
    pub indices: FxHashMap<ty::Region<'tcx>, RegionVid>,

    /// Those indices that are bound locally on the current function.
    /// For example, if we are type-checking the function `foo`, then
    /// it `'a` and `'b` would be in this set, but not `'static`.
    /// Within the closure in the body, `'a` and `'b`' would not be
    /// local, but `'x` would be.
    ///
    /// ```
    /// fn foo<'a, 'b>(a: &'a u32, b: &'b u32, c: &'static u32) {
    ///   let closure = for<'x> |x: &'x u32| { .. };
    ///                 ^^^^^^^ pretend this were legal syntax
    ///                         for declaring a late-bound region in
    ///                         a closure signature
    /// }
    /// ```
    pub local_indices: FxHashSet<RegionVid>,

    /// Each RBP `('a, GK)` indicates that `GK: 'a` can be assumed to
    /// be true. These encode relationships like `T: 'a` that are
    /// added via implicit bounds.
    ///
    /// Each region here is guaranteed to be a key in the `indices`
    /// map.  We use the "original" regions (i.e., the keys from the
    /// map, and not the values) because the code in
    /// `process_registered_region_obligations` has some special-cased
    /// logic expecting to see (e.g.) `ReStatic`, and if we supplied
    /// our special inference variable there, we would mess that up.
    pub region_bound_pairs: Vec<(ty::Region<'tcx>, GenericKind<'tcx>)>,

    /// Stores the outlives relations that are known to hold from the
    /// implied bounds, in-scope where clauses, and that sort of
    /// thing.
    pub outlives_relation: TransitiveRelation<RegionVid>,
}

impl<'tcx> FreeRegions<'tcx> {
    pub fn new(infcx: &InferCtxt<'_, '_, 'tcx>, mir_def_id: DefId, param_env: ty::ParamEnv<'tcx>) -> Self {
        FreeRegions {
            indices: FxHashMap::default(),
            outlives_relation: TransitiveRelation::new(),
            local_indices: FxHashSet::default(),
            region_bound_pairs: vec![],
        }.init(infcx, mir_def_id, param_env)
    }

    fn init(
        mut self,
        infcx: &InferCtxt<'_, '_, 'tcx>,
        mir_def_id: DefId,
        param_env: ty::ParamEnv<'tcx>,
    ) -> Self {
        let tcx = infcx.tcx;
        let tables = tcx.typeck_tables_of(mir_def_id);
        let mir_node_id = tcx.hir.as_local_node_id(mir_def_id).unwrap();

        // `'static` is always free.
        let fr_static = self.insert_free_region(tcx, mir_def_id, tcx.types.re_static);

        // Load and process the where-clauses in scope.
        self.add_outlives_bounds(tcx, mir_def_id, bounds::explicit_outlives_bounds(param_env));

        // Walk up the def-ids of all enclosing closures, up to (and
        // including) the enclosing fn item. If this is a fn item, then
        // this just visits it.
        for def_id in tcx.closure_base_def_ids(mir_def_id) {
            // Extract the early regions.
            let substs = Substs::identity_for_item(tcx, def_id);
            for region in substs.iter().filter_map(|k| k.as_region()) {
                self.insert_free_region(tcx, mir_def_id, region);
            }

            // Extract the late-bound regions. Use the liberated fn sigs,
            // where the late-bound regions will have been converted into free
            // regions, and add them to the map.
            let fn_hir_id = tcx.hir
                .node_to_hir_id(tcx.hir.as_local_node_id(def_id).unwrap());
            let fn_sig = tables.liberated_fn_sigs()[fn_hir_id];
            tcx.for_each_free_region(&fn_sig.inputs_and_output, |region| {
                self.insert_free_region(tcx, mir_def_id, region);
            });

            // Add in the implied bounds we get from this signature.
            let span = tcx.def_span(mir_def_id);
            for ty in fn_sig.inputs_and_output {
                self.add_outlives_bounds(
                    tcx,
                    mir_def_id,
                    infcx.implied_outlives_bounds(param_env, mir_node_id, ty, span),
                );
            }
        }

        debug!("free_regions: indices={:#?}", self.indices);

        // Finally, static outlives every other free region.
        for fr in self.indices.values() {
            self.outlives_relation.add(fr_static, *fr);
        }

        self
    }

    /// Inserts `region` into the map, assigning it the next
    /// `RegionVid` if it is not already present.
    fn insert_free_region(
        &mut self,
        tcx: TyCtxt<'_, '_, 'tcx>,
        mir_def_id: DefId,
        region: ty::Region<'tcx>,
    ) -> RegionVid {
        let next = RegionVid::new(self.indices.len());
        let local_indices = &mut self.local_indices;
        *self.indices.entry(region).or_insert_with(|| {
            let is_local = match region {
                ty::ReStatic | ty::ReEmpty | ty::ReScope(..) => {
                    // For 'static and the empty region, these are not
                    // bound on any function but rather always in
                    // scope. For `ReScope`, that would only appear free
                    // within a closure, and it always would refer to some
                    // scope from the containing function.
                    false
                }

                ty::ReEarlyBound(..) | ty::ReFree(..) => {
                    region.free_region_binding_scope(tcx) == mir_def_id
                }

                ty::ReLateBound(..) | ty::ReSkolemized(..) | ty::ReVar(..) | ty::ReErased => {
                    bug!("unexpected region {:?}", region)
                }
            };

            if is_local {
                local_indices.insert(next);
            }

            next
        })
    }

    fn add_outlives_bounds<I>(
        &mut self,
        tcx: TyCtxt<'_, '_, 'tcx>,
        mir_def_id: DefId,
        outlives_bounds: I,
    ) where
        I: IntoIterator<Item = OutlivesBound<'tcx>>,
    {
        for outlives_bound in outlives_bounds {
            match outlives_bound {
                OutlivesBound::RegionSubRegion(r1, r2) => {
                    // The bound says that `r1 <= r2`; we store `r2: r1`.
                    self.relate_free_regions(tcx, mir_def_id, r2, r1);
                }

                OutlivesBound::RegionSubParam(r_a, param_b) => {
                    self.insert_free_region(tcx, mir_def_id, r_a);
                    self.region_bound_pairs
                        .push((r_a, GenericKind::Param(param_b)));
                }

                OutlivesBound::RegionSubProjection(r_a, projection_b) => {
                    self.insert_free_region(tcx, mir_def_id, r_a);
                    self.region_bound_pairs
                        .push((r_a, GenericKind::Projection(projection_b)));
                }
            }
        }
    }

    /// Records in the `outlives_relation` that `fr_a: fr_b`.
    fn relate_free_regions(
        &mut self,
        tcx: TyCtxt<'_, '_, 'tcx>,
        mir_def_id: DefId,
        fr_a: ty::Region<'tcx>,
        fr_b: ty::Region<'tcx>,
    ) {
        let fr_a = self.insert_free_region(tcx, mir_def_id, fr_a);
        let fr_b = self.insert_free_region(tcx, mir_def_id, fr_b);
        self.outlives_relation.add(fr_a, fr_b);
    }
}
