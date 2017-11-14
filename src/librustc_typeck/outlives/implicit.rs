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
use rustc::hir::def_id::{CrateNum, DefId, LOCAL_CRATE};

// Create the sets of inferred predicates for each type. These sets
// are initially empty but will grow during the inference step.

//let mut inferred_outlives_predicates = map();
pub fn empty<'a, 'tcx: 'a>(tcx: TyCtxt<'a, 'tcx, 'tcx>, crate_num: CrateNum) -> CratePredicatesMap<'a> {
    assert_eq!(crate_num, LOCAL_CRATE);
    let predicates = FxHashMap();
    let empty_predicate = Rc::new(Vec::new());

    let visitor = EmptyImplicitVisitor {
        predicates
    };
    //iterate over all the crates
    tcx.hir.krate().visit_all_item_likes(&mut visitor);

    ty::CratePredicatesMap {
        predicates,
        empty_predicate,
    }
}

pub struct EmptyImplicitVisitor {
    predicates: FxHashMap<DefId, Vec<String>>,
}

impl<'a, 'tcx, 'v> ItemLikeVisitor<'v> for EmptyImplicitVisitor {
    fn visit_item(&mut self, item: &hir::Item) {
        //for def_id in all_types() {
        //    inferred_outlives_predicates.insert(def_id, empty_set());
        //}

        let def_id = DefId.local(item.hir_id.owner);
        self.predicates.insert(def_id, Vec::new());
    }

    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {
    }

    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {
    }
}
