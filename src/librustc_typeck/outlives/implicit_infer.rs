// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(unused)]

#[allow(dead_code)]
use rustc::ty::{self, CratePredicatesMap, TyCtxt};
use rustc::ty::{AdtKind, ToPolyTraitRef, Ty};
use rustc::ty::maps::Providers;
use std::rc::Rc;
use util::nodemap::FxHashMap;
use hir::map as hir_map;
use rustc::hir;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use rustc::hir::def_id::{self, CrateNum, DefId, LOCAL_CRATE};
use std::collections::HashSet;
use rustc::ty::{ReprOptions, ToPredicate};
use syntax_pos::{Span, DUMMY_SP};
use rustc::hir::def::{CtorKind, Def};
use syntax::{abi, ast};

pub fn infer_for_fields<'tcx>(
    tcx: TyCtxt<'_, 'tcx, 'tcx>,
    mut global_inferred_outlives: &mut FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>>,
) {
    /*
        // inferred_outlives_predicate = ['b: 'a] // after round 2
        struct Foo<'a, 'b> {
            bar: Bar<'a, 'b> // []
            // round 2: ['b: 'a] in `required_predicates`
        }

        // inferred_outlives_predicate = ['b: 'a] // updated after round 1
        struct Bar<'a, 'b> {
            field &'a &'b u32 // ['b: 'a] // added to `required_predicates`
        } // required_predicates = ['b: 'a]
    */

    let mut predicates_added = true;
    // If new predicates were added then we need to re-calculate
    // all crates since there could be new implied predicates.
    while predicates_added {
        predicates_added = false;
        let mut visitor = InferVisitor {
            tcx: tcx,
            global_inferred_outlives: &mut global_inferred_outlives,
            predicates_added: predicates_added,
        };

        // Visit all the crates and infer predicates
        tcx.hir.krate().visit_all_item_likes(&mut visitor);
    }
}

pub struct InferVisitor<'cx, 'tcx: 'cx> {
    tcx: TyCtxt<'cx, 'tcx, 'tcx>,
    global_inferred_outlives: &'cx mut FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>>,
    predicates_added: bool,
}

impl<'cx, 'tcx> ItemLikeVisitor<'tcx> for InferVisitor<'cx, 'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        let item_did = self.tcx.hir.local_def_id(item.id);

        let node_id = self.tcx
            .hir
            .as_local_node_id(item_did)
            .expect("expected local def-id");
        let item = match self.tcx.hir.get(node_id) {
            hir::map::NodeItem(item) => item,
            _ => bug!(),
        };

        let mut local_predicate_map = FxHashMap();
        match item.node {
            hir::ItemUnion(..) |
            hir::ItemEnum(..) |
            hir::ItemStruct(..) => {

                let adt_def = self.tcx.adt_def(item_did);

                // Iterate over all fields in item_did
                for field_def in adt_def.all_fields() {

                    // Calculating the predicate requirements necessary
                    // for item_did.
                    //
                    // For field of type &'a T (reference) or TyAdt
                    // (struct/enum/union) there will be outlive
                    // requirements for adt_def.
                    let field_ty = self.tcx.type_of(field_def.did);
                    let requirements_for_item_did = required_predicates_to_be_wf(
                        self.tcx,
                        field_ty,
                        self.global_inferred_outlives,
                     ).into_iter().collect();

                    // Add the requirements_for_item_did to the local map
                    local_predicate_map.insert(
                        item_did,
                        Rc::new(requirements_for_item_did),
                    );
                }
            },

            _ => {},
        };

        if local_predicate_map.len() > 0 {
            self.predicates_added = true;
            self.global_inferred_outlives
                .extend(local_predicate_map);
        }
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx hir::TraitItem) {}

    fn visit_impl_item(&mut self, impl_item: &'tcx hir::ImplItem) {}
}

fn required_predicates_to_be_wf<'tcx>(
    tcx: TyCtxt<'_, 'tcx, 'tcx>,
    field_ty: Ty<'tcx>,
    global_inferred_outlives: &FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>>,
) -> HashSet<ty::Predicate<'tcx>> {

    let mut required_predicates = HashSet::new();
    match field_ty.sty {

        // The field is of type &'a T which means that we will have
        // a prediate requirement of T: 'a (T outlives 'a).
        //
        // We also want to calculate potential predicates for the T
        ty::TyRef(reg, mt) => {
            let outlives_pred = ty::Binder(ty::OutlivesPredicate(mt.ty, reg))
                .to_predicate();
            required_predicates.insert(outlives_pred);

            let predcates_for_mt: HashSet<ty::Predicate<'tcx>> =
                required_predicates_to_be_wf(
                    tcx,
                    mt.ty,
                    global_inferred_outlives,
                ).into_iter().collect();
            required_predicates.extend(predcates_for_mt);
        },

        // For each TyAdt (struct/enum/union) type `Foo<'a, T>`, we can
        // load the current set of inferred and explicit predicates from
        // `global_inferred_outlives` and filter the ones that are TypeOutlives
        ty::TyAdt(def, substs) => {

            let predicates_for_foo = global_inferred_outlives
                .get(&def.did)
                .map(|v| &v[..])
                .unwrap_or(&[]);

            //FIXME: Filter the requirements that are TypeOutlives
            // let predicates_for_foo = predicates_for_foo
            //     .filter_map(|p| p.to_opt_type_outlives());

            required_predicates.extend(predicates_for_foo);
        },

        // For `TyDynamic` types, we can do the same, but using the `expredicates_of`
        // query (those are not inferred).
        ty::TyDynamic(data, r) => { },

        _ => {},

    }

    // At this point:
    //
    // - What we want to do *conceptually* is to compute the WF (well-formedness)
    //   requirements of `_ty` and -- in particular -- any outlives requirements
    //   that `_ty` requires.
    //   - So for example if `_ty` is `&'a T`, then this would include `T: 'a`.
    //
    // - There is some code for computing these WF requirements in `ty/wf.rs` but
    //   we can't really use it as is, and it's not clear we want to use it at all
    //   - The problem is that it is meant to run **after** this inference has been
    //     done. So, e.g., when it encounters a type like `Foo<'a, T>`, it
    //     invokes the `nominal_obligations` method, which invokes the `predicates_of`
    //     query, which would then invoke this inference, causing a cycle.
    //   - I think though we can make parameterizable in terms of what
    //     it does when encountering a nominal type. If we do this, we
    //     would also want to skip normalization (which normally
    //     occurs at the top-level anyway, e.g. in the wrapper
    //     `ty::wf::obligations` -- we would be adding a new such
    //     wrapper anyway).
    //
    // - Alternatively, we may be better off making a local copy of that logic that
    //     is specialized to our needs. This inference doesn't even have to be
    //     100% complete: anything we fail to cover will 'just' result in the user
    //     having to add manual annotation, not anything like unsoundness.
    //   - If we go that way, we would basically just walk the type `_ty` recursively:
    //     - We could even use `walk` though it might be better to make a manual
    //       match.
    //     - We want to compute the set of `T: 'a` pairs that are required for `_ty`
    //       to be well-formed:
    //       - For each type `&'a T`, we require `T: 'a`
    //       - For each struct/enum/union type `Foo<'a, T>`, we can
    //         load the current set of inferred and explicit predicates from
    //         `inferred_outlives_map` and see if those include `T:
    //         'a`
    //       - For `TyDynamic` types, we can do the same, but using the `expredicates_of`
    //         query (those are not inferred).
    //       - That's...it?
    //
    //   - Either way, we will extract from the WF reuqirements a set
    //     of `T: 'a` requirements that must hold.
    //       - We only care when `'a` here maps to an early-bound
    //         region (`ReEarlyBound`), then it corresponds to one of
    //         our lifetime parameters (it could also be something
    //         like `'static`, or a higher-ranked region, which we can
    //         safely ignore for now).
    //       - When we get to a `&'a T`, we will use the `ty/outlives`
    //         code to compute the outlives obligations from `T:
    //         'a`. This gives back a set of things that must outlive `'a`
    //         (`ty::outlives::Component<'tcx>`).
    //       - We want to iterate over those components:
    //         - For each early-bound region component or type parameter, we can
    //           add the approriate outlives requirement to our result.
    //         - For each projection or escaping projection, we can iterate over
    //           the `substs` and
    //           recursively apply outlives to break that down into components.
    //
    // Done.

    // from ty/outlives.rs
    //   Foo<'b, 'c>  ==> ['b, 'c]
    //   Vec<T>: 'a
    //   outlives_components(Vec<T>) = [T]

    required_predicates
}
