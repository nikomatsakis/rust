// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Type resolution: the phase that finds all the types in the AST with
// unresolved type variables and replaces "ty_var" types with their
// substitutions.

use check::FnCtxt;
use rustc::hir;
use rustc::hir::intravisit::{self, Visitor, NestedVisitorMap};
use rustc::infer::{InferCtxt};
use rustc::ty::{self, Ty, TyCtxt};
use rustc::ty::fold::{TypeFolder,TypeFoldable};
use rustc::util::nodemap::DefIdSet;
use syntax::ast;
use syntax_pos::Span;
use std::mem;

///////////////////////////////////////////////////////////////////////////
// Entry point

impl<'a, 'gcx, 'tcx> FnCtxt<'a, 'gcx, 'tcx> {
    pub fn resolve_type_vars_in_body(&self, body: &'gcx hir::Body)
                                     -> &'gcx ty::TypeckTables<'gcx> {
        let item_id = self.tcx.hir.body_owner(body.id());
        let item_def_id = self.tcx.hir.local_def_id(item_id);

        let mut wbcx = WritebackCx::new(self, body);
        for arg in &body.arguments {
            wbcx.visit_node_id(arg.pat.span, arg.id);
        }
        if let Some(ref impl_arg) = body.impl_arg {
            wbcx.visit_node_id(impl_arg.span, impl_arg.id);
        }
        wbcx.visit_body(body);
        wbcx.visit_upvar_borrow_map();
        wbcx.visit_closures();
        wbcx.visit_liberated_fn_sigs();
        wbcx.visit_fru_field_types();
        wbcx.visit_anon_types();
        wbcx.visit_cast_types();
        wbcx.visit_lints();
        wbcx.visit_free_region_map();
        wbcx.visit_generator_sigs();
        wbcx.visit_generator_interiors();

        let used_trait_imports = mem::replace(&mut self.tables.borrow_mut().used_trait_imports,
                                              DefIdSet());
        debug!("used_trait_imports({:?}) = {:?}", item_def_id, used_trait_imports);
        wbcx.tables.used_trait_imports = used_trait_imports;

        wbcx.tables.tainted_by_errors = self.is_tainted_by_errors();

        self.tcx.alloc_tables(wbcx.tables)
    }
}

///////////////////////////////////////////////////////////////////////////
// The Writerback context. This visitor walks the AST, checking the
// fn-specific tables to find references to types or regions. It
// resolves those regions to remove inference variables and writes the
// final result back into the master tables in the tcx. Here and
// there, it applies a few ad-hoc checks that were not convenient to
// do elsewhere.

struct WritebackCx<'cx, 'gcx: 'cx+'tcx, 'tcx: 'cx> {
    fcx: &'cx FnCtxt<'cx, 'gcx, 'tcx>,

    tables: ty::TypeckTables<'gcx>,

    body: &'gcx hir::Body,
}

impl<'cx, 'gcx, 'tcx> WritebackCx<'cx, 'gcx, 'tcx> {
    fn new(fcx: &'cx FnCtxt<'cx, 'gcx, 'tcx>, body: &'gcx hir::Body)
        -> WritebackCx<'cx, 'gcx, 'tcx> {
        WritebackCx {
            fcx: fcx,
            tables: ty::TypeckTables::empty(),
            body: body
        }
    }

    fn tcx(&self) -> TyCtxt<'cx, 'gcx, 'tcx> {
        self.fcx.tcx
    }

    fn write_ty_to_tables(&mut self, node_id: ast::NodeId, ty: Ty<'gcx>) {
        debug!("write_ty_to_tables({}, {:?})", node_id,  ty);
        assert!(!ty.needs_infer());
        self.tables.node_types.insert(node_id, ty);
    }

    // Hacky hack: During type-checking, we treat *all* operators
    // as potentially overloaded. But then, during writeback, if
    // we observe that something like `a+b` is (known to be)
    // operating on scalars, we clear the overload.
    fn fix_scalar_builtin_expr(&mut self, e: &hir::Expr) {
        match e.node {
            hir::ExprUnary(hir::UnNeg, ref inner) |
            hir::ExprUnary(hir::UnNot, ref inner)  => {
                let inner_ty = self.fcx.node_ty(inner.id);
                let inner_ty = self.fcx.resolve_type_vars_if_possible(&inner_ty);

                if inner_ty.is_scalar() {
                    let mut tables = self.fcx.tables.borrow_mut();
                    tables.type_dependent_defs.remove(&e.id);
                    tables.node_substs.remove(&e.id);
                }
            }
            hir::ExprBinary(ref op, ref lhs, ref rhs) |
            hir::ExprAssignOp(ref op, ref lhs, ref rhs) => {
                let lhs_ty = self.fcx.node_ty(lhs.id);
                let lhs_ty = self.fcx.resolve_type_vars_if_possible(&lhs_ty);

                let rhs_ty = self.fcx.node_ty(rhs.id);
                let rhs_ty = self.fcx.resolve_type_vars_if_possible(&rhs_ty);

                if lhs_ty.is_scalar() && rhs_ty.is_scalar() {
                    let mut tables = self.fcx.tables.borrow_mut();
                    tables.type_dependent_defs.remove(&e.id);
                    tables.node_substs.remove(&e.id);

                    match e.node {
                        hir::ExprBinary(..) => {
                            if !op.node.is_by_value() {
                                tables.adjustments.get_mut(&lhs.id).map(|a| a.pop());
                                tables.adjustments.get_mut(&rhs.id).map(|a| a.pop());
                            }
                        },
                        hir::ExprAssignOp(..) => {
                            tables.adjustments.get_mut(&lhs.id).map(|a| a.pop());
                        },
                        _ => {},
                    }
                }
            }
            _ => {},
        }
    }
}

///////////////////////////////////////////////////////////////////////////
// Impl of Visitor for Resolver
//
// This is the master code which walks the AST. It delegates most of
// the heavy lifting to the generic visit and resolve functions
// below. In general, a function is made into a `visitor` if it must
// traffic in node-ids or update tables in the type context etc.

impl<'cx, 'gcx, 'tcx> Visitor<'gcx> for WritebackCx<'cx, 'gcx, 'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'gcx> {
        NestedVisitorMap::None
    }

    fn visit_expr(&mut self, e: &'gcx hir::Expr) {
        self.fix_scalar_builtin_expr(e);

        self.visit_node_id(e.span, e.id);

        if let hir::ExprClosure(_, _, body, _, _) = e.node {
            let body = self.fcx.tcx.hir.body(body);
            // FIXME: Why visit the args here?
            for arg in &body.arguments {
                self.visit_node_id(e.span, arg.id);
            }

            self.visit_body(body);
        }

        intravisit::walk_expr(self, e);
    }

    fn visit_block(&mut self, b: &'gcx hir::Block) {
        self.visit_node_id(b.span, b.id);
        intravisit::walk_block(self, b);
    }

    fn visit_pat(&mut self, p: &'gcx hir::Pat) {
        self.visit_node_id(p.span, p.id);
        intravisit::walk_pat(self, p);
    }

    fn visit_local(&mut self, l: &'gcx hir::Local) {
        intravisit::walk_local(self, l);
        let var_ty = self.fcx.local_ty(l.span, l.id);
        let var_ty = self.resolve(&var_ty, &l.span);
        self.write_ty_to_tables(l.id, var_ty);
    }
}

impl<'cx, 'gcx, 'tcx> WritebackCx<'cx, 'gcx, 'tcx> {
    fn visit_upvar_borrow_map(&mut self) {
        for (upvar_id, upvar_capture) in self.fcx.tables.borrow().upvar_capture_map.iter() {
            let new_upvar_capture = match *upvar_capture {
                ty::UpvarCapture::ByValue => ty::UpvarCapture::ByValue,
                ty::UpvarCapture::ByRef(ref upvar_borrow) => {
                    let r = upvar_borrow.region;
                    let r = self.resolve(&r, &upvar_id.var_id);
                    ty::UpvarCapture::ByRef(
                        ty::UpvarBorrow { kind: upvar_borrow.kind, region: r })
                }
            };
            debug!("Upvar capture for {:?} resolved to {:?}",
                   upvar_id,
                   new_upvar_capture);
            self.tables.upvar_capture_map.insert(*upvar_id, new_upvar_capture);
        }
    }

    fn visit_closures(&mut self) {
        for (&id, closure_ty) in self.fcx.tables.borrow().closure_tys.iter() {
            let closure_ty = self.resolve(closure_ty, &id);
            self.tables.closure_tys.insert(id, closure_ty);
        }

        for (&id, &closure_kind) in self.fcx.tables.borrow().closure_kinds.iter() {
            self.tables.closure_kinds.insert(id, closure_kind);
        }
    }

    fn visit_cast_types(&mut self) {
        self.tables.cast_kinds.extend(
            self.fcx.tables.borrow().cast_kinds.iter().map(|(&key, &value)| (key, value)));
    }

    fn visit_lints(&mut self) {
        self.fcx.tables.borrow_mut().lints.transfer(&mut self.tables.lints);
    }

    fn visit_free_region_map(&mut self) {
        let free_region_map = self.tcx().lift_to_global(&self.fcx.tables.borrow().free_region_map);
        let free_region_map = free_region_map.expect("all regions in free-region-map are global");
        self.tables.free_region_map = free_region_map;
    }

    fn visit_anon_types(&mut self) {
        let gcx = self.tcx().global_tcx();
        for (&node_id, &concrete_ty) in self.fcx.anon_types.borrow().iter() {
            let inside_ty = self.resolve(&concrete_ty, &node_id);

            // Convert the type from the function into a type valid outside
            // the function, by replacing invalid regions with 'static,
            // after producing an error for each of them.
            let outside_ty = gcx.fold_regions(&inside_ty, &mut false, |r, _| {
                match *r {
                    // 'static and early-bound regions are valid.
                    ty::ReStatic |
                    ty::ReEarlyBound(_) |
                    ty::ReEmpty => r,

                    ty::ReFree(_) |
                    ty::ReLateBound(..) |
                    ty::ReScope(_) |
                    ty::ReSkolemized(..) => {
                        let span = node_id.to_span(&self.fcx.tcx);
                        span_err!(self.tcx().sess, span, E0564,
                                  "only named lifetimes are allowed in `impl Trait`, \
                                   but `{}` was found in the type `{}`", r, inside_ty);
                        gcx.types.re_static
                    }

                    ty::ReVar(_) |
                    ty::ReErased => {
                        let span = node_id.to_span(&self.fcx.tcx);
                        span_bug!(span, "invalid region in impl Trait: {:?}", r);
                    }
                }
            });

            self.tables.node_types.insert(node_id, outside_ty);
        }
    }

    fn visit_node_id(&mut self, span: Span, node_id: ast::NodeId) {
        // Export associated path extensions and method resultions.
        if let Some(def) = self.fcx.tables.borrow_mut().type_dependent_defs.remove(&node_id) {
            self.tables.type_dependent_defs.insert(node_id, def);
        }

        // Resolve any borrowings for the node with id `node_id`
        self.visit_adjustments(span, node_id);

        // Resolve the type of the node with id `node_id`
        let n_ty = self.fcx.node_ty(node_id);
        let n_ty = self.resolve(&n_ty, &span);
        self.write_ty_to_tables(node_id, n_ty);
        debug!("Node {} has type {:?}", node_id, n_ty);

        // Resolve any substitutions
        if let Some(&substs) = self.fcx.tables.borrow().node_substs.get(&node_id) {
            let substs = self.resolve(&substs, &span);
            debug!("write_substs_to_tcx({}, {:?})", node_id, substs);
            assert!(!substs.needs_infer());
            self.tables.node_substs.insert(node_id, substs);
        }
    }

    fn visit_adjustments(&mut self, span: Span, node_id: ast::NodeId) {
        let adjustment = self.fcx.tables.borrow_mut().adjustments.remove(&node_id);
        match adjustment {
            None => {
                debug!("No adjustments for node {}", node_id);
            }

            Some(adjustment) => {
                let resolved_adjustment = self.resolve(&adjustment, &span);
                debug!("Adjustments for node {}: {:?}", node_id, resolved_adjustment);
                self.tables.adjustments.insert(node_id, resolved_adjustment);
            }
        }
    }

    fn visit_generator_interiors(&mut self) {
        for (&node_id, interior) in self.fcx.tables.borrow().generator_interiors.iter() {
            let interior = self.resolve(interior, &node_id);
            self.tables.generator_interiors.insert(node_id, interior);
        }
    }

    fn visit_generator_sigs(&mut self) {
        for (&node_id, gen_sig) in self.fcx.tables.borrow().generator_sigs.iter() {
            let gen_sig = gen_sig.map(|s| ty::GenSig {
                impl_arg_ty: self.resolve(&s.impl_arg_ty, &node_id),
                yield_ty: self.resolve(&s.yield_ty, &node_id),
                return_ty: self.resolve(&s.return_ty, &node_id),
            });
            self.tables.generator_sigs.insert(node_id, gen_sig);
        }
    }

    fn visit_liberated_fn_sigs(&mut self) {
        for (&node_id, fn_sig) in self.fcx.tables.borrow().liberated_fn_sigs.iter() {
            let fn_sig = self.resolve(fn_sig, &node_id);
            self.tables.liberated_fn_sigs.insert(node_id, fn_sig.clone());
        }
    }

    fn visit_fru_field_types(&mut self) {
        for (&node_id, ftys) in self.fcx.tables.borrow().fru_field_types.iter() {
            let ftys = self.resolve(ftys, &node_id);
            self.tables.fru_field_types.insert(node_id, ftys);
        }
    }

    fn resolve<T>(&self, x: &T, span: &Locatable) -> T::Lifted
        where T: TypeFoldable<'tcx> + ty::Lift<'gcx>
    {
        let x = x.fold_with(&mut Resolver::new(self.fcx, span, self.body));
        if let Some(lifted) = self.tcx().lift_to_global(&x) {
            lifted
        } else {
            span_bug!(span.to_span(&self.fcx.tcx),
                      "writeback: `{:?}` missing from the global type context",
                      x);
        }
    }
}

trait Locatable {
    fn to_span(&self, tcx: &TyCtxt) -> Span;
}

impl Locatable for Span {
    fn to_span(&self, _: &TyCtxt) -> Span { *self }
}

impl Locatable for ast::NodeId {
    fn to_span(&self, tcx: &TyCtxt) -> Span { tcx.hir.span(*self) }
}

///////////////////////////////////////////////////////////////////////////
// The Resolver. This is the type folding engine that detects
// unresolved types and so forth.

struct Resolver<'cx, 'gcx: 'cx+'tcx, 'tcx: 'cx> {
    tcx: TyCtxt<'cx, 'gcx, 'tcx>,
    infcx: &'cx InferCtxt<'cx, 'gcx, 'tcx>,
    span: &'cx Locatable,
    body: &'gcx hir::Body,
}

impl<'cx, 'gcx, 'tcx> Resolver<'cx, 'gcx, 'tcx> {
    fn new(fcx: &'cx FnCtxt<'cx, 'gcx, 'tcx>, span: &'cx Locatable, body: &'gcx hir::Body)
        -> Resolver<'cx, 'gcx, 'tcx>
    {
        Resolver {
            tcx: fcx.tcx,
            infcx: fcx,
            span: span,
            body: body,
        }
    }

    fn report_error(&self, t: Ty<'tcx>) {
        if !self.tcx.sess.has_errors() {
            self.infcx.need_type_info(Some(self.body.id()), self.span.to_span(&self.tcx), t);
        }
    }
}

impl<'cx, 'gcx, 'tcx> TypeFolder<'gcx, 'tcx> for Resolver<'cx, 'gcx, 'tcx> {
    fn tcx<'a>(&'a self) -> TyCtxt<'a, 'gcx, 'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        match self.infcx.fully_resolve(&t) {
            Ok(t) => t,
            Err(_) => {
                debug!("Resolver::fold_ty: input type `{:?}` not fully resolvable",
                       t);
                self.report_error(t);
                self.tcx().types.err
            }
        }
    }

    // FIXME This should be carefully checked
    // We could use `self.report_error` but it doesn't accept a ty::Region, right now.
    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match self.infcx.fully_resolve(&r) {
            Ok(r) => r,
            Err(_) => {
                self.tcx.types.re_static
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////
// During type check, we store promises with the result of trait
// lookup rather than the actual results (because the results are not
// necessarily available immediately). These routines unwind the
// promises. It is expected that we will have already reported any
// errors that may be encountered, so if the promises store an error,
// a dummy result is returned.
