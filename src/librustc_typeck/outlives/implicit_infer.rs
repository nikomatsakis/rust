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
            hir::ItemUnion(ref def, _) => {
                //FIXME
            }
            hir::ItemEnum(ref def, _) => {
                //FIXME
            }
            hir::ItemStruct(ref def, _) => {
                for field in def.all_fields() {
                    local_required_predicates
                        .extend(required_predicates_to_be_wf(self.tcx, field, def_id));
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
    field: &hir::StructField,
    def_id: DefId,
) -> FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>> {

    let ty = tcx.type_of(def_id);
    tcx.outlives_components(ty);

    // from ty/outlives.rs
    //   Foo<'b, 'c>  ==> ['b, 'c]
    //   Vec<T>: 'a
    //   outlives_components(Vec<T>) = [T]
    FxHashMap()
}

