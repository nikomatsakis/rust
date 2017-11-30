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
use rustc::ty::maps::Providers;
use std::rc::Rc;
use util::nodemap::FxHashMap;
use hir::map as hir_map;
use rustc::hir;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use rustc::hir::def_id::{self, CrateNum, DefId, LOCAL_CRATE};
use std::collections::HashSet;

// Create the sets of inferred predicates for each type.




//let mut inferred_outlives_predicates = map();
pub fn infer<'tcx>(tcx: TyCtxt<'_, 'tcx, 'tcx>, crate_num: CrateNum) -> CratePredicatesMap<'tcx> {
    assert_eq!(crate_num, LOCAL_CRATE);
    let empty_predicate = Rc::new(Vec::new());
    let mut predicates = FxHashMap();

    // Now comes the inference part. We iterate over each type and figure out,
    // for each of its fields, what outlives predicates are needed to make that field's
    // type well-formed. Those get added to the `inferred_outlives_predicates` set
    // for that type.

    let mut changed = true;
    let mut eval_crate_num = crate_num;
    {
        while changed {
            let mut local_changed = false;
            {
                let mut visitor = ImplicitVisitor {
                    tcx: tcx,
                    predicates: &mut predicates,
                    crate_num: &mut eval_crate_num,
                    changed: &mut local_changed,
                };

                // iterate over all crates
                tcx.hir.krate().visit_all_item_likes(&mut visitor);
            }
            changed = local_changed;
        }
    }

    ty::CratePredicatesMap {
        predicates,
        empty_predicate,
    }
}

pub struct ImplicitVisitor<'a, 'p: 'a, 'cx, 'tcx: 'cx> {
    tcx: TyCtxt<'cx, 'tcx, 'tcx>,
    predicates: &'a mut FxHashMap<DefId, Rc<Vec<ty::Predicate<'p>>>>,
    crate_num: &'a mut CrateNum,
    changed: &'a mut bool,
}

impl<'a, 'p, 'cx, 'v, 'tcx> ItemLikeVisitor<'v> for ImplicitVisitor<'a, 'p, 'cx, 'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        *self.changed = false;

        let def_id = DefId {
            krate: *self.crate_num,
            index: item.hir_id.owner,
        };
        let adt_def = self.tcx.adt_def(def_id);
        let mut required_predicates: HashSet<i32> = HashSet::new();

        //        for variant in adt_def OB{
        //            for field in variant {
        //                // from ty/outlives.rs
        //                //   Foo<'b, 'c>  ==> ['b, 'c]
        //                //   Vec<T>: 'a
        //                //   outlives_components(Vec<T>) = [T]
        //                let outlives = tcx.outlives_components(field_ty);
        //                required_predicates.extend(required_predicates_for_type_to_be_wf(field_ty));
        //            }
        //        }
        //        inferred_outlives_predicates.extend(required_predicates);
        //        if new predicates were added { changed = true; }
        //    }

    }

    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {}

    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {}
}
