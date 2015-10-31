// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use front::map::{NodeForeignItem, NodeImplItem, NodeTraitItem};
use middle::def_id::DefId;
use middle::ty;
use syntax::ast;
use rustc_front::hir;
use rustc_front::intravisit;

#[allow(unused_variables)]
pub trait DefVisitor<'tcx> {
    fn visit_item(&mut self, def_id: DefId);

    fn visit_foreign_item(&mut self, def_id: DefId);

    fn visit_trait_item(&mut self, trait_def_id: DefId, trait_item_def_id: DefId);

    fn visit_impl_item(&mut self, impl_def_id: DefId, impl_item_def_id: DefId);
}

pub fn visit_defs<'tcx, D>(tcx: &ty::ctxt<'tcx>, delegate: &mut D)
    where D: DefVisitor<'tcx>
{
    let mut visitor = HirVisitor {
        tcx: tcx,
        delegate: delegate,
    };
    let krate = tcx.map.krate();
    intravisit::walk_crate(&mut visitor, krate);
}

pub fn visit_all<'tcx, D>(tcx: &ty::ctxt<'tcx>, delegate: &mut D)
    where D: intravisit::Visitor<'tcx>
{
    unimplemented!()
}

///////////////////////////////////////////////////////////////////////////
// Impl.

struct HirVisitor<'a, 'tcx:'a, D: DefVisitor<'tcx> + 'a> {
    tcx: &'a ty::ctxt<'tcx>,
    delegate: &'a mut D,
}

impl<'a, 'tcx, D> intravisit::Visitor<'tcx> for HirVisitor<'a, 'tcx, D>
    where D: DefVisitor<'tcx> + 'a
{
    fn visit_item_def(&mut self, id: ast::NodeId) {
        let item = self.tcx.map.expect_item(id);
        let def_id = self.tcx.map.local_def_id(item.id);
        self.delegate.visit_item(def_id, item);

        match item.node {
            hir::ItemTrait(_, _, _, ref trait_items) => {
                for trait_item in trait_items {
                    let trait_item_def_id = self.tcx.map.local_def_id(trait_item.id);
                    self.delegate.visit_trait_item(def_id, item, trait_item_def_id, trait_item);
                }
            }

            hir::ItemImpl(_, _, _, _, _, ref impl_items) => {
                for impl_item in impl_items {
                    let impl_item_def_id = self.tcx.map.local_def_id(impl_item.id);
                    self.delegate.visit_impl_item(def_id, item, impl_item_def_id, impl_item);
                }
            }

            _ => { }
        }

        intravisit::walk_item(self, item);
    }

    fn visit_foreign_item_def(&mut self, id: ast::NodeId) {
        let item = match self.tcx.map.find(id) {
            Some(NodeForeignItem(i)) => i,
            r => panic!("looking up foreign item {:?} got {:?}", id, r)
        };
        let def_id = self.tcx.map.local_def_id(item.id);
        self.delegate.visit_foreign_item(def_id, item);
        intravisit::walk_foreign_item(self, item);
    }

    fn visit_trait_item_def(&mut self, id: ast::NodeId) {
        // NB: We visit trait-items in the `visit_item` fn above, so
        // that we have access to the trait item
        let item = match self.tcx.map.find(id) {
            Some(NodeTraitItem(i)) => i,
            r => panic!("looking up foreign item {:?} got {:?}", id, r)
        };
        intravisit::walk_trait_item(self, item);
    }

    fn visit_impl_item_def(&mut self, id: ast::NodeId) {
        // NB: We visit impl-items in the `visit_item` fn above, so
        // that we have access to the impl item
        let item = match self.tcx.map.find(id) {
            Some(NodeImplItem(i)) => i,
            r => panic!("looking up foreign item {:?} got {:?}", id, r)
        };
        intravisit::walk_impl_item(self, item);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr) {
        match expr.node {
            hir::ExprClosure(_, ref decl, ref body) => {
                let def_id = self.tcx.map.local_def_id(expr.id);
                self.delegate.visit_closure(def_id, expr, decl, body);
            }
            _ => { }
        }
        intravisit::walk_expr(self, expr);
    }
}
