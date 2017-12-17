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
use rustc::hir::Ty_::*;
use rustc::ty::{self, CratePredicatesMap, TyCtxt};
use rustc::ty::maps::Providers;
use std::rc::Rc;
use util::nodemap::FxHashMap;
use hir::map as hir_map;
use rustc::hir;

/// Code to write unit test for outlives.
pub mod test;
mod explicit;
mod implicit_empty;
mod implicit_infer;

pub fn provide(providers: &mut Providers) {
    *providers = Providers {
        inferred_outlives_of,
        inferred_outlives_crate,
        ..*providers
    };
}

//todo
fn inferred_outlives_of<'a, 'tcx>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    def_id: DefId,
) -> Vec<ty::Predicate<'tcx>> {
    // Assert that this is a local node-id
    let node_id = tcx.hir.as_local_node_id(def_id).unwrap();

    match tcx.hir.get(node_id) {
        hir_map::NodeItem(item) => match item.node {
            hir::ItemStruct(..) |
            hir::ItemEnum(..) => {
                tcx.inferred_outlives_crate(LOCAL_CRATE);
                Vec::new()
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

fn inferred_outlives_crate<'tcx>(
    tcx: TyCtxt<'_, 'tcx, 'tcx>,
    crate_num: CrateNum,
) -> Rc<CratePredicatesMap<'tcx>> {
    // Compute a map from each struct/enum/union S to the **explicit**
    // outlives predicates (`T: 'a`, `'a: 'b`) that the user wrote.
    // Typically there won't be many of these, except in older code where
    // they were mandatory. Nonetheless, we have to ensure that every such
    // predicate is satisfied, so they form a kind of base set of requirements
    // for the type.

    // outlives that the user has annotated.
    // TypeOutlives and RegionOutlives (maybe also ProjectionPredicate??)
    let explicitly_annotated_outlives_map = explicit::explicit_map(tcx, crate_num);

    // empty inferred predicates.
    let mut inferred_outlives_map = implicit_empty::empty(tcx, crate_num);

    {
        // Add the inferred predicates to the previous empty map
        implicit_infer::infer_for_fields(tcx, crate_num, &inferred_outlives_map);
    }

    inferred_outlives_map.extend(explicitly_annotated_outlives_map);

    Rc::new(ty::CratePredicatesMap {
        predicates: inferred_outlives_map,
        empty_predicate: Rc::new(Vec::new()),
    })
}

