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
use rustc::hir::def_id::{CrateNum, DefId, LocalDefId, LOCAL_CRATE};

pub fn explicit_map<'tcx>(
    tcx: TyCtxt<'_, 'tcx, 'tcx>,
    crate_num: CrateNum,
) -> FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>> {
    assert_eq!(crate_num, LOCAL_CRATE);
    let mut predicates: FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>> = FxHashMap();

    {
        let mut visitor = ExplicitVisitor {
            tcx: tcx,
            explicit_predicates: &mut predicates,
            crate_num: crate_num,
        };

        //iterate over all the crates
        tcx.hir.krate().visit_all_item_likes(&mut visitor);
    }

    predicates
}


pub struct ExplicitVisitor<'cx, 'tcx: 'cx> {
    tcx: TyCtxt<'cx, 'tcx, 'tcx>,
    explicit_predicates: &'cx mut FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>>,
    crate_num: CrateNum,
}

impl<'cx, 'tcx> ItemLikeVisitor<'tcx> for ExplicitVisitor<'cx, 'tcx> {
    fn visit_item(&mut self, item: &'tcx hir::Item) {
        let def_id = DefId {
            krate: self.crate_num,
            index: item.hir_id.owner,
        };
//        let def_id = self.crate_num.as_def_id();

        let local_explicit_predicate = self.tcx.explicit_predicates_of(def_id);

        let filtered_predicates = local_explicit_predicate
            .predicates
            .into_iter()
            .filter(|pred| match pred {
                ty::Predicate::TypeOutlives(..)
                | ty::Predicate::RegionOutlives(..) => true,
                _ => false,
            })
            .collect();

        // try to fetch the adt-def
        match item.node {
            hir::ItemStruct(..) |
            hir::ItemEnum(..) => {
                self.tcx.adt_def(def_id);
            }
            _ => { }
        }

        self.explicit_predicates
            .insert(def_id, Rc::new(filtered_predicates));
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx hir::TraitItem) {}

    fn visit_impl_item(&mut self, impl_item: &'tcx hir::ImplItem) {}
}
