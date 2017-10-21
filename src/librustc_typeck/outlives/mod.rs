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

    if let ty::TyAdt(_def, _) = tcx.type_of(def_id).sty {
        //todo call crate wide outlives and infer outlives
        //        let all_outlives = tcx.inferred_outlives_crate();
        Vec::new()
    } else {
        Vec::new()
    }
}

#[allow(dead_code)]
fn inferred_outlives_crate <'a, 'tcx>(_tcx: TyCtxt<'a, 'tcx, 'tcx>, _def_id: DefId)
                                      -> Rc<CratePredicatesMap<'tcx>> {
    let predicates = FxHashMap();
    let empty_predicate = Rc::new(Vec::new());

    Rc::new(
        ty::CratePredicatesMap{
            predicates,
            empty_predicate,
        }
        )
//    match explicit_predicates_of(tcx, def_id) {
//        //todo RFC definition
//        ty::GenericPredicates::TypeOutlives | ty::GenericPredicates::RegionOutlives =>
//        _ => Vec::new()
//    }
}
