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

use rustc::hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc::ty::{self, CratePredicatesMap, TyCtxt};
use rustc::ty::maps::Providers;
use std::rc::Rc;
use util::nodemap::FxHashMap;
use hir::map as hir_map;
use rustc::hir;

/// Code to write unit test for outlives.
pub mod test;
mod implicit;
mod explicit;

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

fn inferred_outlives_crate <'tcx>(tcx: TyCtxt<'tcx, 'tcx, 'tcx>, crate_num: CrateNum)
                                      -> Rc<CratePredicatesMap<'tcx>> {




    // Compute a map from each struct/enum/union S to the **explicit**
    // outlives predicates (`T: 'a`, `'a: 'b`) that the user wrote.
    // Typically there won't be many of these, except in older code where
    // they were mandatory. Nonetheless, we have to ensure that every such
    // predicate is satisfied, so they form a kind of base set of requirements
    // for the type.

    let mut explicit_outlives_predicates = explicit::explicit_map(tcx, crate_num);
    //let mut explicit_outlives_predicates = map();
    //for def_id in all_types() {
    //    let explicit_predicates = tcx.explicit_predicates(def_id);
    //    let filtered_predicates = explicit_predicates
    //    .iter()
    //    .filter_map(is_outlives_predicate)
    //    .collect();
    //    explicit_outlives_predicates.insert(
    //        def_id,
    //        filtered_predicates);
    //}

    // Create the sets of inferred predicates for each type. These sets
    // are initially empty but will grow during the inference step.
    let empty = implicit::empty(tcx, crate_num);
    //let mut inferred_outlives_predicates = map();
    //for def_id in all_types() {
    //    inferred_outlives_predicates.insert(def_id, empty_set());
    //}
    Rc::new(empty)

    // Now comes the inference part. We iterate over each type and figure out,
    // for each of its fields, what outlives predicates are needed to make that field's
    // type well-formed. Those get added to the `inferred_outlives_predicates` set
    // for that type.
    //let mut changed = true;
    //while changed {
    //    changed = false;
    //    for def_id in all_types() {
    //        for field_ty in the HIR type definition {
    //            let required_predicates = required_predicates_for_type_to_be_wf(field_ty);
    //            inferred_outlives_predicates.extend(required_predicates);
    //            if new predicates were added { changed = true; }
    //        }
    //    }
    //}

    //inferred_outlives_predicates


}
