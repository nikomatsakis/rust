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
use syntax::ast;
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
    fn should_visit_def_id(&mut self, def_id: DefId) -> bool {
        true
    }

    fn visit_item(&mut self, i: &'tcx hir::Item) {
    }

    fn visit_foreign_item(&mut self, i: &'tcx hir::ForeignItem) {
    }

    fn visit_trait_item(&mut self, ti: &'tcx hir::TraitItem) {
    }

    fn visit_impl_item(&mut self, ii: &'tcx hir::ImplItem) {
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
    fn visit_item_def(&mut self, id: ast::NodeId) {
        let def_id = self.map.local_def_id(id);
        let hir = self.map.expect_item(id);
        if self.delegate.should_visit_def_id(def_id) {
            self.delegate.visit_item(hir);
        }
        intravisit::walk_item(self, hir);
    }

    fn visit_foreign_item_def(&mut self, id: ast::NodeId) {
        let def_id = self.map.local_def_id(id);
        let hir = self.map.expect_foreign_item(id);
        if self.delegate.should_visit_def_id(def_id) {
            self.delegate.visit_foreign_item(hir);
        }
        intravisit::walk_foreign_item(self, hir);
    }

    fn visit_trait_item_def(&mut self, id: ast::NodeId) {
        let trait_item_def_id = self.map.local_def_id(id);
        let hir = self.map.expect_trait_item(id);
        if self.delegate.should_visit_def_id(trait_item_def_id) {
            self.delegate.visit_trait_item(hir);
        }
        intravisit::walk_trait_item(self, hir);
    }

    fn visit_impl_item_def(&mut self, id: ast::NodeId) {
        let impl_item_def_id = self.map.local_def_id(id);
        let hir = self.map.expect_impl_item(id);
        if self.delegate.should_visit_def_id(impl_item_def_id) {
            self.delegate.visit_impl_item(hir);
        }
        intravisit::walk_impl_item(self, hir);
    }
}
