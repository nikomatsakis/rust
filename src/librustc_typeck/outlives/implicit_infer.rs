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
    mut inferred_outlives_map: &mut FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>>,
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

    let mut changed = true;
    while changed {
        changed = false;
        let mut visitor = InferVisitor {
            tcx: tcx,
            inferred_outlives_map: &mut inferred_outlives_map,
            changed: changed,
        };

        //iterate over all the crates
        tcx.hir.krate().visit_all_item_likes(&mut visitor);
    }
}

pub struct InferVisitor<'cx, 'tcx: 'cx> {
    tcx: TyCtxt<'cx, 'tcx, 'tcx>,
    inferred_outlives_map: &'cx mut FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>>,
    changed: bool,
}

impl<'cx, 'tcx> ItemLikeVisitor<'tcx> for InferVisitor<'cx, 'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        let def_id = self.tcx.hir.local_def_id(item.id);

        let node_id = self.tcx
            .hir
            .as_local_node_id(def_id)
            .expect("expected local def-id");
        let item = match self.tcx.hir.get(node_id) {
            hir::map::NodeItem(item) => item,
            _ => bug!(),
        };

        let mut local_required_predicates = FxHashMap();
        match item.node {
            hir::ItemUnion(..) |
            hir::ItemEnum(..) |
            hir::ItemStruct(..) => {
                let adt_def = self.tcx.adt_def(def_id);
                for field_def in adt_def.all_fields() {
                    let required_predicates: Vec<_> = required_predicates_to_be_wf(
                        self.tcx,
                        field_def,
                        &local_required_predicates,
                     ).into_iter().collect();
                    local_required_predicates.insert(
                        field_def.did,
                        Rc::new(required_predicates),
                    );
                }
            }
            _ => {}
        };

        if local_required_predicates.len() > 0 {
            self.changed = true;
            self.inferred_outlives_map
                .extend(local_required_predicates);
        }
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx hir::TraitItem) {}

    fn visit_impl_item(&mut self, impl_item: &'tcx hir::ImplItem) {}
}

//FIXME This is custom calculation that to figure out what predicates need to be added
fn required_predicates_to_be_wf<'tcx>(
    tcx: TyCtxt<'_, 'tcx, 'tcx>,
    field_def: &ty::FieldDef,
    infered_outlives_map: &FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>>,
) -> HashSet<ty::Predicate<'tcx>> {

    let mut predicates = HashSet::new();
    // Get the type of the field with identity substs applied.  For
    // now, let's just see if that causes horrible cycles.
    let field_ty = tcx.type_of(field_def.did);
    match field_ty.sty {
        // For each type `&'a T`, we require `T: 'a`
        //
        // If you have A = &'a T, then mt.ty here represents T and
        // ty represents A (and r represents 'a). So we want T: 'a.
        ty::TyRef(r, mt) => {
            let outlives_pred = ty::Binder(ty::OutlivesPredicate(mt.ty, r))
                .to_predicate();
            predicates.insert(outlives_pred);
        }

        // For each struct/enum/union type `Foo<'a, T>`, we can
        // load the current set of inferred and explicit predicates from
        // `inferred_outlives_map` and see if those include `T: 'a`
        ty::TyAdt(def, substs) => {

            // Get type generics of def and lifetime(region) generics of def
            let generics: &ty::Generics = tcx.generics_of(def.did);
            let gen_types: &Vec<ty::TypeParameterDef> = &generics.types;
            let gen_region: &Vec<ty::RegionParameterDef> = &generics.regions;

            // Create OutlivesPredicates for each type/lifetime.
            // We will use this to test if the same OutlivesPredicate
            // also exists in the infered_outlives_map
            // let mut outlive_predicate_pairs = Vec::new();
            // for typ in gen_types {
            //     for reg in gen_region {
            //         outlive_predicate_pairs.push(
            //             ty::OutlivesPredicate(typ, reg)
            //         );
            //     };
            // };


            // iterate over all predicates in the infered_outlives_map.
            // See if there are any OutlivesPredicate kind. If there
            // exists a type and region that is also in this field
            // then that should be returned.
            for (_, p_list) in infered_outlives_map.iter() {
                for p in p_list.as_ref() {
                    match p {
                        // ty::Predicate::Trait(..) |
                        // ty::Predicate::Equate(..) |
                        // ty::Predicate::Subtype(..) |
                        // ty::Predicate::Projection(..) |
                        // ty::Predicate::ClosureKind(..) |
                        // ty::Predicate::ObjectSafe(..) |
                        // ty::Predicate::ConstEvaluatable(..) |
                        // ty::Predicate::WellFormed(subty) => |
                        // ty::Predicate::RegionOutlives(ref data) => 5,

                        ty::Predicate::TypeOutlives(ref data) => match data {
                            // ty::OutlivesPredicate(a, b) => {
                                // if gen_types.contains(typ) && gen_region.contains(reg) {
                                //     let outlives_pred =
                                //        ty::Binder(ty::OutlivesPredicate(typ, reg))
                                //        .to_predicate();
                                //     predicates.insert(outlives_pred);
                                // }

                            // },

                            _ => (),
                        },

                        _ => (),
                    };
                }
            };

            // // For each type generic check if it exists in the
            // // previously calculated predicates
            // let ty_exists_in_calculated_map = gen_types.into_iter()
            //     .filter( |typ| infered_outlives_map.contains_key(&typ.def_id));

            // // Check if the predicates for type_generic intersects
            // // with the outlive_pred_pairs. If so then we should return
            // // the same OutlivesPredicate for this field
            // for ty in ty_exists_in_calculated_map {
            //     let to_add: &Vec<_> = infered_outlives_map
            //         .get(&ty.def_id)
            //         .expect("we know the key exists")
            //         .as_ref();
            //     to_add.intersects(outlive_predicate_pairs);
            //     // predicates.chain(to_add);
            // }

        }

        // For `TyDynamic` types, we can do the same, but using the `expredicates_of`
        // query (those are not inferred).
        ty::TyDynamic(data, r) => { }

        _ => {}

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

    predicates
}
