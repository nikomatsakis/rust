// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::pass::contents::{ContentsVisitor};
use rustc_front::intravisit::{self, FnKind, Visitor};
use rustc_front::hir;
use rustc_front::hir::*;
use rustc_front::util::stmt_id;
use syntax::ast::{Name, NodeId};
use syntax::ast_util;
use syntax::codemap::Span;

pub struct IdVisitor<'a, O: 'a> {
    pub operation: &'a mut O,
}

impl<'a, O: ast_util::IdVisitingOperation> IdVisitor<'a, O> {
    fn visit_generics_helper(&mut self, generics: &Generics) {
        for type_parameter in generics.ty_params.iter() {
            self.operation.visit_id(type_parameter.id)
        }
        for lifetime in &generics.lifetimes {
            self.operation.visit_id(lifetime.lifetime.id)
        }
    }
}

impl<'a, 'v, O: ast_util::IdVisitingOperation> ContentsVisitor<'v> for IdVisitor<'a, O> {
    fn visit_trait_item(&mut self, ti: &hir::TraitItem) {
        self.operation.visit_id(ti.id);
        intravisit::walk_trait_item(self, ti);
    }

    fn visit_impl_item(&mut self, ii: &hir::ImplItem) {
        self.operation.visit_id(ii.id);
        intravisit::walk_impl_item(self, ii);
    }

    fn visit_foreign_item(&mut self, foreign_item: &ForeignItem) {
        self.operation.visit_id(foreign_item.id);
        intravisit::walk_foreign_item(self, foreign_item)
    }

    fn visit_item(&mut self, item: &Item) {
        self.operation.visit_id(item.id);
        match item.node {
            ItemUse(ref view_path) => {
                match view_path.node {
                    ViewPathSimple(_, _) |
                    ViewPathGlob(_) => {}
                    ViewPathList(_, ref paths) => {
                        for path in paths {
                            self.operation.visit_id(path.node.id())
                        }
                    }
                }
            }
            _ => {}
        }

        intravisit::walk_item(self, item);
    }
}

impl<'a, 'v, O: ast_util::IdVisitingOperation> Visitor<'v> for IdVisitor<'a, O> {
    fn visit_mod(&mut self, module: &Mod, _: Span, node_id: NodeId) {
        self.operation.visit_id(node_id);
        intravisit::walk_mod(self, module)
    }

    fn visit_local(&mut self, local: &Local) {
        self.operation.visit_id(local.id);
        intravisit::walk_local(self, local)
    }

    fn visit_block(&mut self, block: &Block) {
        self.operation.visit_id(block.id);
        intravisit::walk_block(self, block)
    }

    fn visit_stmt(&mut self, statement: &Stmt) {
        self.operation.visit_id(stmt_id(statement));
        intravisit::walk_stmt(self, statement)
    }

    fn visit_pat(&mut self, pattern: &Pat) {
        self.operation.visit_id(pattern.id);
        intravisit::walk_pat(self, pattern)
    }

    fn visit_expr(&mut self, expression: &Expr) {
        self.operation.visit_id(expression.id);
        intravisit::walk_expr(self, expression)
    }

    fn visit_ty(&mut self, typ: &Ty) {
        self.operation.visit_id(typ.id);
        intravisit::walk_ty(self, typ)
    }

    fn visit_generics(&mut self, generics: &Generics) {
        self.visit_generics_helper(generics);
        intravisit::walk_generics(self, generics)
    }

    fn visit_fn(&mut self,
                function_kind: FnKind<'v>,
                function_declaration: &'v FnDecl,
                block: &'v Block,
                span: Span,
                node_id: NodeId) {
        self.operation.visit_id(node_id);

        match function_kind {
            FnKind::ItemFn(_, generics, _, _, _, _) => {
                self.visit_generics_helper(generics)
            }
            FnKind::Method(_, sig, _) => {
                self.visit_generics_helper(&sig.generics)
            }
            FnKind::Closure => {}
        }

        for argument in &function_declaration.inputs {
            self.operation.visit_id(argument.id)
        }

        intravisit::walk_fn(self, function_kind, function_declaration, block, span);
    }

    fn visit_struct_field(&mut self, struct_field: &StructField) {
        self.operation.visit_id(struct_field.node.id);
        intravisit::walk_struct_field(self, struct_field)
    }

    fn visit_variant_data(&mut self,
                        struct_def: &VariantData,
                        _: Name,
                        _: &hir::Generics,
                        _: NodeId,
                        _: Span) {
        self.operation.visit_id(struct_def.id());
        intravisit::walk_struct_def(self, struct_def);
    }

    fn visit_lifetime(&mut self, lifetime: &Lifetime) {
        self.operation.visit_id(lifetime.id);
    }

    fn visit_lifetime_def(&mut self, def: &LifetimeDef) {
        self.visit_lifetime(&def.lifetime);
    }

    fn visit_trait_ref(&mut self, trait_ref: &TraitRef) {
        self.operation.visit_id(trait_ref.ref_id);
        intravisit::walk_trait_ref(self, trait_ref);
    }
}

/// Computes the id range for a single fn body, ignoring nested items.
pub fn compute_id_range_for_fn_body(fk: FnKind,
                                    decl: &FnDecl,
                                    body: &Block,
                                    sp: Span,
                                    id: NodeId)
                                    -> ast_util::IdRange {
    let mut visitor = ast_util::IdRangeComputingVisitor { result: ast_util::IdRange::max() };
    let mut id_visitor = IdVisitor {
        operation: &mut visitor,
    };
    id_visitor.visit_fn(fk, decl, body, sp, id);
    id_visitor.operation.result
}

