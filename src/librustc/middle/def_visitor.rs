// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::def_id::DefId;
use middle::ty;
use rustc_front::hir;
use rustc_front::visit;

#[allow(unused_variables)]
pub trait DefVisitor<'tcx> {
    fn visit_item(&mut self, def_id: DefId, item: &'tcx hir::Item) {
    }

    fn visit_foreign_item(&mut self, def_id: DefId, foreign_item: &'tcx hir::ForeignItem) {
    }

    fn visit_trait_item(&mut self, def_id: DefId, trait_item: &'tcx hir::TraitItem) {
    }

    fn visit_impl_item(&mut self, def_id: DefId, impl_item: &'tcx hir::ImplItem) {
    }

    fn visit_closure(&mut self,
                     def_id: DefId,
                     expr: &'tcx hir::Expr,
                     decl: &'tcx hir::FnDecl,
                     body: &'tcx hir::Block) {
    }
}

pub fn visit_defs<'tcx, D>(tcx: &ty::ctxt<'tcx>, delegate: &mut D)
    where D: DefVisitor<'tcx>
{
    let mut visitor = HirVisitor {
        tcx: tcx,
        delegate: delegate,
    };
    let krate = tcx.map.krate();
    visit::walk_crate(&mut visitor, krate);
}

///////////////////////////////////////////////////////////////////////////

struct HirVisitor<'a, 'tcx:'a, D: DefVisitor<'tcx> + 'a> {
    tcx: &'a ty::ctxt<'tcx>,
    delegate: &'a mut D,
}

impl<'a, 'tcx, D> visit::Visitor<'tcx> for HirVisitor<'a, 'tcx, D>
    where D: DefVisitor<'tcx> + 'a
{
    fn visit_item(&mut self, item: &'tcx hir::Item) {
        let def_id = self.tcx.map.local_def_id(item.id);
        self.delegate.visit_item(def_id, item);
        visit::walk_item(self, item);
    }

    fn visit_foreign_item(&mut self, item: &'tcx hir::ForeignItem) {
        let def_id = self.tcx.map.local_def_id(item.id);
        self.delegate.visit_foreign_item(def_id, item);
        visit::walk_foreign_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &'tcx hir::TraitItem) {
        let def_id = self.tcx.map.local_def_id(item.id);
        self.delegate.visit_trait_item(def_id, item);
        visit::walk_trait_item(self, item);
    }

    fn visit_impl_item(&mut self, item: &'tcx hir::ImplItem) {
        let def_id = self.tcx.map.local_def_id(item.id);
        self.delegate.visit_impl_item(def_id, item);
        visit::walk_impl_item(self, item);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr) {
        match expr.node {
            hir::ExprClosure(_, ref decl, ref body) => {
                let def_id = self.tcx.map.local_def_id(expr.id);
                self.delegate.visit_closure(def_id, expr, decl, body);
            }
            _ => { }
        }
        visit::walk_expr(self, expr);
    }
}
