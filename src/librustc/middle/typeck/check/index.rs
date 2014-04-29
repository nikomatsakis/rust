// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Index lookup */

use middle::subst::{TypeSpace};
use middle::ty;
use middle::typeck::{MethodCall, MethodCallee};
use std::gc::Gc;
use syntax::ast;
use syntax::parse::token;
use util::common::ErrorReported;

use super::check_expr;
use super::check_expr_has_type;
use super::check_expr_with_lvalue_pref;
use super::deref;
use super::FnCtxt;
use super::LvaluePreference;
use super::method;

// Check index expressions
pub fn check_index(fcx: &FnCtxt,
                   outer_expr: &ast::Expr,    // a[b]
                   base_expr: Gc<ast::Expr>,  // a
                   index_expr: Gc<ast::Expr>, // b
                   lvalue_pref: LvaluePreference)
                   -> ty::t
{
    check_expr_with_lvalue_pref(fcx, &*base_expr, lvalue_pref);
    check_expr(fcx, &*index_expr);

    let base_ty = fcx.expr_ty(&*base_expr);
    let index_ty = fcx.expr_ty(&*index_expr);

    if ty::type_is_error(base_ty) || ty::type_is_bot(base_ty) {
        return base_ty;
    }
    if ty::type_is_error(index_ty) || ty::type_is_bot(index_ty) {
        return index_ty;
    }

    // Check for built-in indexing.
    let mut can_index = CanIndexTest { fcx: fcx,
                                       outer_expr: outer_expr,
                                       base_expr: base_expr };
    match deref::autoderef_loop(fcx, outer_expr.span, base_ty, &mut can_index) {
        deref::FoundMatch(base_xform_ty, Builtin(index_ty, element_ty)) => {
            deref::record_autoderefs(fcx, base_expr, base_xform_ty, None);
            check_expr_has_type(fcx, index_expr, index_ty);
            return element_ty;
        }
        deref::FoundMatch(base_xform_ty, Overridden(callee)) => {
            deref::record_autoderefs(fcx, base_expr, base_xform_ty, None);

            // The index trait has two output type parameters, the
            // index and element type:
            let index_ty = *callee.substs.types.get(TypeSpace, 0);
            let element_ty = *callee.substs.types.get(TypeSpace, 1);

            let method_call = MethodCall::expr(outer_expr.id);
            fcx.inh.method_map.borrow_mut().insert(method_call, callee);

            check_expr_has_type(fcx, index_expr, index_ty);
            return element_ty;
        }
        deref::FoundReportedError => {
            return ty::mk_err();
        }
        deref::FoundNoMatch(_) => {
            fcx.type_error_message(
                outer_expr.span,
                |actual| format!("cannot index a value of type `{}`", actual),
                base_ty,
                None);
            return ty::mk_err();
        }
    }
}

struct CanIndexTest<'a> {
    fcx: &'a FnCtxt<'a>,
    outer_expr: &'a ast::Expr,
    base_expr: &'a ast::Expr,
}

enum IndexResult {
    Builtin(/*index_ty*/ ty::t, /*element_ty*/ ty::t),
    Overridden(MethodCallee)
}

impl<'a> deref::Test<IndexResult> for CanIndexTest<'a> {
    fn test(&mut self, ty: ty::t) -> Result<Option<IndexResult>,ErrorReported> {
        // Check for builtin indexing
        match ty::index(ty).map(|mt| mt.ty) {
            Some(t) => {
                return Ok(Some(Builtin(ty::mk_uint(), t)));
            }
            None => { }
        }

        // Check for overloaded indexing
        match method::lookup_in_traits(
            self.fcx,
            self.outer_expr.span,
            self.base_expr,
            ty,
            token::intern("index"),
            self.fcx.tcx().lang_items.index_trait().as_slice())
        {
            Err(ErrorReported) => Err(ErrorReported),
            Ok(None) => Ok(None),
            Ok(Some(callee)) => {
                Ok(Some(Overridden(callee)))
            }
        }
    }
}

/*
fn try_overloaded_index(fcx: &FnCtxt,
                        method_call: Option<MethodCall>,
                        expr: &ast::Expr,
                        base_expr: Gc<ast::Expr>,
                        base_ty: ty::t,
                        index_expr: Gc<ast::Expr>,
                        lvalue_pref: LvaluePreference)
                        -> Option<ty::mt> {
    // Try `IndexMut` first, if preferred.
    let method = match (lvalue_pref, fcx.tcx().lang_items.index_mut_trait()) {
        (PreferMutLvalue, Some(trait_did)) => {
            method::lookup_in_trait(fcx,
                                    expr.span,
                                    Some(&*base_expr),
                                    token::intern("index_mut"),
                                    trait_did,
                                    base_ty,
                                    [],
                                    DontAutoderefReceiver,
                                    IgnoreStaticMethods)
        }
        _ => None,
    };

    // Otherwise, fall back to `Index`.
    let method = match (method, fcx.tcx().lang_items.index_trait()) {
        (None, Some(trait_did)) => {
            method::lookup_in_trait(fcx,
                                    expr.span,
                                    Some(&*base_expr),
                                    token::intern("index"),
                                    trait_did,
                                    base_ty,
                                    [],
                                    DontAutoderefReceiver,
                                    IgnoreStaticMethods)
        }
        (method, _) => method,
    };

    // Regardless of whether the lookup succeeds, check the method arguments
    // so that we have *some* type for each argument.
    let method_type = match method {
        Some(ref method) => method.ty,
        None => ty::mk_err()
    };
    check_method_argument_types(fcx,
                                expr.span,
                                method_type,
                                expr,
                                [base_expr, index_expr],
                                DoDerefArgs,
                                DontTupleArguments);

    match method {
        Some(method) => {
            let ref_ty = ty::ty_fn_ret(method.ty);
            match method_call {
                Some(method_call) => {
                    fcx.inh.method_map.borrow_mut().insert(method_call,
                                                           method);
                }
                None => {}
            }
            ty::deref(ref_ty, true)
        }
        None => None,
    }
}
*/
