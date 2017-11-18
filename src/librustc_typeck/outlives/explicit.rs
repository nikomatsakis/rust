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

pub fn explicit_map<'a, 'tcx: 'a>(tcx: TyCtxt<'a, 'tcx, 'tcx>, crate_num: CrateNum)
        -> FxHashMap<DefId, Predicate> {
    assert_eq!(crate_num, LOCAL_CRATE);

    //let mut explicit_outlives_predicates = map();
    let explicit_predicates = FxHashMap();

    let mut visitor = ExplicitVisitor {
        tcx,
        explicit_predicates
    };
    //iterate over all the crates
    tcx.hir.krate().visit_all_item_likes(&mut visitor);

    explicit_predicates
}


pub struct ExplicitVisitor {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    explicit_predicates: FxHashMap<DefId, Vec<String>>,
}

impl<'a, 'tcx, 'v> ItemLikeVisitor<'v> for ExplicitVisitor {
    fn visit_item(&mut self, item: &hir::Item) {

        // Compute a map from each struct/enum/union S to the **explicit**
        // outlives predicates (`T: 'a`, `'a: 'b`) that the user wrote.
        // Typically there won't be many of these, except in older code where
        // they were mandatory. Nonetheless, we have to ensure that every such
        // predicate is satisfied, so they form a kind of base set of requirements
        // for the type.
        //for def_id in all_types() {
        //    let explicit_predicates = tcx.explicit_predicates(def_id);
        let def_id = DefId.local(item.hir_id.owner);
        let local_explicit_predicate = self.tcx.explicit_predicates_of(def_id);

        //    let filtered_predicates = explicit_predicates.iter()
        //    .filter_map(is_outlives_predicate).collect();
        let filtered_predicate = local_explicit_predicate.iter()
            .filter(is_outlives_predicate)
            .collect();

        self.explicit_predicates.insert(def_id, Rc::new(Vec::new()));
    }

    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {
    }

    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {
    }
}

fn is_outlives_predicate(pred: Predicate) -> Boolean {
    match *pred {
        &ty::Predicate::TypeOutlives(..) | &ty::Predicate::RegionOutlives(..) => true,
        _ => false,
    }
}
