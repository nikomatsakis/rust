// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::hir::def_id::DefId;
use rustc::ty::{self, CratePredicatesMap, TyCtxt};
use rustc::ty::maps::Providers;
use std::rc::Rc;
use util::nodemap::FxHashMap;
use hir::map as hir_map;
use rustc::hir;

/// Code to write unit test for outlives.
pub mod test;

pub fn provide(providers: &mut Providers) {
    *providers = Providers {
        inferred_outlives_of,
        ..*providers
    };
}

//todo
fn inferred_outlives_of<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                                  -> Vec<ty::Predicate<'tcx>> {
    // Assert that this is a local node-id
    let node_id = tcx.hir.as_local_node_id(def_id).unwrap();

    match tcx.hir.get(node_id) {
        hir_map::NodeItem(item) => match item.node {
            hir::ItemStruct(..) => Vec::new(),
            hir::ItemEnum(..) => Vec::new(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

#[allow(dead_code)]
fn inferred_outlives_crate <'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId)
                                      -> Rc<CratePredicatesMap<'tcx>> {


    let predicates = FxHashMap();
    let empty_predicate = Rc::new(Vec::new());

    let visitor = infer::OutlivesCrateVisitor {
        tcx,
        predicates,
        empty_predicate,
    }
    //iterate over all the crates
    tcx.hir.krate().visit_all_item_likes(&mut visitor);

    Rc::new(
        ty::CratePredicatesMap {
            predicates,
            empty_predicate,
        }
    );

}
