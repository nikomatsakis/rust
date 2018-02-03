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
                    let required_predicates = required_predicates_to_be_wf(self.tcx, field_def);
                    local_required_predicates.extend(required_predicates);
                }
            }
            _ => {}
        };

        if local_required_predicates.len() > 0 {
            self.changed = true;
            self.inferred_outlives_map.extend(local_required_predicates);
        }
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx hir::TraitItem) {}

    fn visit_impl_item(&mut self, impl_item: &'tcx hir::ImplItem) {}
}

//FIXME This is custom calculation that to figure out what predicates need to be added
fn required_predicates_to_be_wf<'tcx>(
    tcx: TyCtxt<'_, 'tcx, 'tcx>,
    field_def: &ty::FieldDef,
) -> FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>> {

    let mut predicates = FxHashMap();
    // Get the type of the field with identity substs applied.  For
    // now, let's just see if that causes horrible cycles.
    let ty = tcx.type_of(field_def.did);
    match ty.sty {
        // For each type `&'a T`, we require `T: 'a`
        ty::TyRef(r, mt) => {
            let outlives_pred = ty::Binder(ty::OutlivesPredicate(mt.ty, r))
                .to_predicate();
            predicates.insert(
                field_def.did,
                Rc::new(vec![outlives_pred]),
            );
        }

        // For each struct/enum/union type `Foo<'a, T>`, we can
        // load the current set of inferred and explicit predicates from
        // `inferred_outlives_map` and see if those include `T:
        // 'a`
        ty::TyAdt(def, substs) => {}

        // For `TyDynamic` types, we can do the same, but using the `expredicates_of`
        // query (those are not inferred).
        ty::TyDynamic(data, r) => {}

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
