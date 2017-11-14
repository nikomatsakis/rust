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
use rustc::mir::{Local, Mir};
use rustc::ty::{self, RegionVid};
use rustc::ty::fold::TypeFoldable;
use rustc::ty::subst::Substs;
use rustc::util::nodemap::FxHashMap;
use rustc_data_structures::indexed_vec::Idx;
use rustc_data_structures::transitive_relation::TransitiveRelation;
use syntax::ast;

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

    /// We create region variables such that they are ordered by their
    /// `RegionClassification`. The first block are globals, then
    /// externals, then locals. So things from:
    /// - `0..first_extern_index` are global;
    /// - `first_extern_index..first_local_index` are external; and
    /// - first_local_index..` are local.
    first_extern_index: usize,

    /// See `first_extern_index`.
    first_local_index: usize,

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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum RegionClassification {
    /// A **global** region is one that can be named from
    /// anywhere. There are only two, `'static` and the empty region
    /// (we have no syntax for it, but it's globally defined).
    Global,

    /// An **external** region is only relevant for closures. In that
    /// case, it refers to regions that are free in the closure type
    /// -- basically, something bound in the surrounding context.
    ///
    /// Consider this example:
    ///
    /// ```
    /// fn foo<'a, 'b>(a: &'a u32, b: &'b u32, c: &'static u32) {
    ///   let closure = for<'x> |x: &'x u32| { .. };
    ///                 ^^^^^^^ pretend this were legal syntax
    ///                         for declaring a late-bound region in
    ///                         a closure signature
    /// }
    /// ```
    ///
    /// Here, the lifetimes `'a` and `'b` would be **external** to the
    /// closure.
    ///
    /// If we are not analyzing a closure, there are no external
    /// lifetimes.
    External,

    /// A **local** lifetime is one about which we know the full set
    /// of relevant constraints (that is, relationships to other named
    /// regions).  For a closure, this includes any region bound in
    /// the closure's signature.  For a fn item, this includes all
    /// regions other than global ones.
    ///
    /// Continuing with the example from `External`, if we were
    /// analyzing the closure, then `'x` would be local (and `'a` and
    /// `'b` are external).  If we are analyzing the function item
    /// `foo`, then `'a` and `'b` are local (and `'x` is not in
    /// scope).
    Local,
}

impl<'tcx> FreeRegions<'tcx> {
    /// Creates a new and fully initialized `FreeRegions` that
    /// contains indices for all the free regions found in the given
    /// MIR -- that is, all the regions that appear in the function's
    /// signature. This will also compute the relationships that are
    /// known between those regions.
    pub fn new(
        infcx: &InferCtxt<'_, '_, 'tcx>,
        mir_def_id: DefId,
        param_env: ty::ParamEnv<'tcx>,
        raw_mir: &Mir<'tcx>,
    ) -> Self {
        FreeRegions {
            indices: FxHashMap::default(),
            outlives_relation: TransitiveRelation::new(),
            first_extern_index: 0,
            first_local_index: 0,
            region_bound_pairs: vec![],
        }.init(infcx, mir_def_id, param_env, raw_mir)
    }

    fn init(
        mut self,
        infcx: &InferCtxt<'_, '_, 'tcx>,
        mir_def_id: DefId,
        param_env: ty::ParamEnv<'tcx>,
        raw_mir: &Mir<'tcx>,
    ) -> Self {
        let tcx = infcx.tcx;
        let mir_node_id = tcx.hir.as_local_node_id(mir_def_id).unwrap();
        let mir_hir_id = tcx.hir.node_to_hir_id(mir_node_id);
        let tables = tcx.typeck_tables_of(mir_def_id);

        // Create the "global" regions that are always free in all contexts: 'static
        // and the empty region (which has no syntax).
        let fr_static = self.insert_free_region(tcx.types.re_static);
        self.insert_free_region(tcx.types.re_empty);

        // We've now added all the global regions. The next ones we
        // add will be external.
        self.first_extern_index = self.indices.len();

        // Get an iterator over the def-ids of all enclosing functions
        // (but not the one we are checking).
        let closure_base_def_id = tcx.closure_base_def_id(mir_def_id);

        if closure_base_def_id == mir_def_id {
            // This is a fn item, the "base case". In this case, there
            // are no "extern" regions, everything is considered
            // local. Moreover, we wish to consider the `'a: 'b`
            // relations declared in our where clauses.
            self.first_local_index = self.indices.len();
            self.insert_free_regions_from(infcx, &param_env);
            self.insert_free_regions_from(infcx, &Substs::identity_for_item(tcx, mir_def_id));
            self.add_outlives_bounds(bounds::explicit_outlives_bounds(param_env));
        } else {
            // This is a closure item. In this case, we will be
            // computing constraints that we propagate up to our
            // caller. We want to distinguish **external** regions,
            // which appear in the closure type (or signature) and are
            // exposed to our caller, from **local** regions, which
            // are bound in our signature.
            //
            // To do this, we first add the regions appearing in our
            // signature, parameter environment, and our closure type.
            let fn_sig = tcx.fn_sig(mir_def_id);
            let closure_ty = tables.node_id_to_type(mir_hir_id); // includes the upvar types
            self.insert_free_regions_from(infcx, &(fn_sig, closure_ty));

            // Every new thing we add from this point is local to
            // the closure -- that is, bound in the closure's
            // signature.
            self.first_local_index = self.indices.len();
        }

        // Finally, record the liberated types of our arguments
        // etc.
        self.insert_free_regions_from_arguments_and_return_tys(
            infcx,
            mir_node_id,
            param_env,
            raw_mir,
        );

        // Finally, outlives is reflexive, and static outlives every
        // other free region.
        for (region, &fr) in &self.indices {
            self.outlives_relation.add(fr, fr);
            self.outlives_relation.add(fr_static, fr);
            debug!(
                "free_regions: {:?} [{:?}] = {:?}",
                fr,
                self.region_classification(fr).unwrap(),
                region
            );
        }

        self
    }

    /// Iterates over the argument and return types found in the MIR
    /// and adds the free regions found therein. Also adds any implied
    /// bounds that we can derive from there.
    fn insert_free_regions_from_arguments_and_return_tys(
        &mut self,
        infcx: &InferCtxt<'_, '_, 'tcx>,
        mir_node_id: ast::NodeId,
        param_env: ty::ParamEnv<'tcx>,
        raw_mir: &Mir<'tcx>,
    ) {
        // The 0th argument is the return type, and the next N are the
        // arguments. In each case, their types are the **liberated**
        // types.  Note that, in general, it is a bit sketchy to be
        // looking at `raw_mir`, since we have not yet run the
        // "renumbering" that replaces its regions with fresh
        // variables. *However,* it's ok for us to look at these
        // specific types from the MIR, since the renumberer expects
        // to find mapping for their regions in the free-region map
        // (which we are building right now!).
        for local in (0..=raw_mir.arg_count).map(Local::new) {
            let local_ty = raw_mir.local_decls[local].ty;
            self.insert_free_regions_from(infcx, &local_ty);

            let b = infcx.implied_outlives_bounds(param_env, mir_node_id, local_ty, raw_mir.span);
            self.add_outlives_bounds(b);
        }
    }

    /// Creates free region indices for all the regions appearing free
    /// in `value`.
    fn insert_free_regions_from<T>(&mut self, infcx: &InferCtxt<'_, '_, 'tcx>, value: &T)
    where
        T: TypeFoldable<'tcx>,
    {
        debug!("insert_free_regions_from({:?})", value);
        infcx.tcx.for_each_free_region(value, |region| {
            self.insert_free_region(region);
        });
    }

    /// Inserts `region` into the map, assigning it the next
    /// `RegionVid` if it is not already present.
    fn insert_free_region(&mut self, region: ty::Region<'tcx>) -> RegionVid {
        assert!(match region {
            ty::ReStatic |
            ty::ReEmpty |
            ty::ReScope(..) |
            ty::ReEarlyBound(..) |
            ty::ReFree(..) => true,
            ty::ReLateBound(..) | ty::ReSkolemized(..) | ty::ReVar(..) | ty::ReErased => false,
        });
        let next = RegionVid::new(self.indices.len());
        *self.indices.entry(region).or_insert_with(|| {
            debug!(
                "free_regions: insert_free_region region {:?} => {:?}",
                region,
                next,
            );
            next
        })
    }

    /// Registers the `OutlivesBound` items from `outlives_bounds` in
    /// the outlives relation as well as the region-bound pairs
    /// listing.
    fn add_outlives_bounds<I>(&mut self, outlives_bounds: I)
    where
        I: IntoIterator<Item = OutlivesBound<'tcx>>,
    {
        for outlives_bound in outlives_bounds {
            match outlives_bound {
                OutlivesBound::RegionSubRegion(r1, r2) => {
                    // The bound says that `r1 <= r2`; we store `r2: r1`.
                    self.relate_free_regions(r2, r1);
                }

                OutlivesBound::RegionSubParam(r_a, param_b) => {
                    self.insert_free_region(r_a);
                    self.region_bound_pairs
                        .push((r_a, GenericKind::Param(param_b)));
                }

                OutlivesBound::RegionSubProjection(r_a, projection_b) => {
                    self.insert_free_region(r_a);
                    self.region_bound_pairs
                        .push((r_a, GenericKind::Projection(projection_b)));
                }
            }
        }
    }

    /// Records in the `outlives_relation` that `fr_a: fr_b`.
    fn relate_free_regions(&mut self, fr_a: ty::Region<'tcx>, fr_b: ty::Region<'tcx>) {
        let fr_a = self.insert_free_region(fr_a);
        let fr_b = self.insert_free_region(fr_b);
        self.outlives_relation.add(fr_a, fr_b);
    }

    /// True if `r` is a free region in the MIR; false if it is a
    /// region inference variable.
    pub fn is_free_region(&self, r: RegionVid) -> bool {
        r.index() < self.indices.len()
    }

    /// Classifies `r` as a free region, returning `None` if this is
    /// not a free region.
    pub fn region_classification(&self, r: RegionVid) -> Option<RegionClassification> {
        let index = r.index();
        if (0..self.first_extern_index).contains(index) {
            Some(RegionClassification::Global)
        } else if (self.first_extern_index..self.first_local_index).contains(index) {
            Some(RegionClassification::External)
        } else if (self.first_local_index..self.indices.len()).contains(index) {
            Some(RegionClassification::Local)
        } else {
            None
        }
    }

    /// True if `r` is classied as a global free region.
    pub fn is_global_free_region(&self, r: RegionVid) -> bool {
        self.region_classification(r) == Some(RegionClassification::Global)
    }

    /// True if `r` is classied as an external free region.
    pub fn is_extern_free_region(&self, r: RegionVid) -> bool {
        self.region_classification(r) == Some(RegionClassification::External)
    }

    /// True if `r` is classied as an local free region.
    pub fn is_local_free_region(&self, r: RegionVid) -> bool {
        self.region_classification(r) == Some(RegionClassification::Local)
    }
}
