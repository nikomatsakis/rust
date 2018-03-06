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

use hir::map as hir_map;
use rustc::dep_graph::DepKind;
use rustc::ty::{self, CratePredicatesMap, TyCtxt};
use rustc::ty::maps::Providers;
use rustc::hir;
use rustc::hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc::hir::Ty_::*;
use std::rc::Rc;
use util::nodemap::FxHashMap;

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

fn inferred_outlives_of<'a, 'tcx>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    item_def_id: DefId,
) -> Rc<Vec<ty::Predicate<'tcx>>> {
    let id = tcx.hir.as_local_node_id(item_def_id).expect("expected local def-id");

    match tcx.hir.get(id) {
        hir_map::NodeItem(item) => match item.node {
            hir::ItemStruct(..) |
            hir::ItemEnum(..) |
            hir::ItemUnion(..) => {
                let crate_map = tcx.inferred_outlives_crate(LOCAL_CRATE);
                let dep_node = item_def_id
                    .to_dep_node(tcx, DepKind::InferredOutlivesOf);
                tcx.dep_graph.read(dep_node);

                crate_map.predicates
                    .get(&item_def_id)
                    .unwrap_or(&crate_map.empty_predicate)
                    .clone()
            },

            _ => Rc::new(Vec::new()),
        },

        _ => Rc::new(Vec::new()),
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
    let explicitly_annotated_outlives_map = explicit::explicit_predicates(tcx, crate_num);

    // empty inferred predicates.
    let mut global_inferred_outlives = implicit_empty::empty_predicate_map(tcx);

    {
        // Add the inferred predicates to the previous empty map
        implicit_infer::infer_predicates(tcx, &mut global_inferred_outlives);
    }

    global_inferred_outlives.extend(explicitly_annotated_outlives_map);

    Rc::new(ty::CratePredicatesMap {
        predicates: global_inferred_outlives,
        empty_predicate: Rc::new(Vec::new()),
    })
}

