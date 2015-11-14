// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use front::map::Map;
use middle::def_id::DefId;
use rustc_front::hir;
use rustc_front::intravisit;

/// The most basic visitor. It's very flexible. Basically it walks all
/// the items for you and you can decide what to do. You ought to
/// check if there IS work to do, first, and then load whatever AST
/// you need etc to do it.
///
/// Note that all the def-ids supplied to callbacks in this function
/// are always local to the current crate.
#[allow(unused_variables)]
pub trait DefsVisitor<'tcx> {
    fn should_visit_item(&mut self, def_id: DefId) -> bool {
        true
    }

    fn visit_item(&mut self, i: &'tcx hir::Item) {
    }
}

pub fn execute<'tcx, D>(map: &Map<'tcx>, delegate: &mut D)
    where D: DefsVisitor<'tcx>
{
    let mut visitor = HirVisitor {
        map: map,
        delegate: delegate,
    };
    let krate = map.krate();
    intravisit::walk_crate(&mut visitor, krate);
}

///////////////////////////////////////////////////////////////////////////
// Impl.

struct HirVisitor<'a, 'tcx:'a, D: DefsVisitor<'tcx> + 'a> {
    map: &'a Map<'tcx>,
    delegate: &'a mut D,
}

impl<'a, 'tcx, D> intravisit::Visitor<'tcx> for HirVisitor<'a, 'tcx, D>
    where D: DefsVisitor<'tcx> + 'a
{
    fn visit_item_def(&mut self, id: &'tcx hir::ItemDef) {
        let def_id = self.map.local_def_id(id.id);
        let hir = self.map.expect_item(id.id);
        if self.delegate.should_visit_item(def_id) {
            self.delegate.visit_item(hir);
        }
        intravisit::walk_item(self, hir);
    }
}
