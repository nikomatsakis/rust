// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Method lookup: See doc.rs for high-level documentation */

use middle::traits::{Obligation, Selection, Vtable};
use middle::ty::*;
use middle::ty;
use middle::typeck::check::FnCtxt;
use middle::typeck::check::deref;
use middle::typeck::MethodCallee;
use syntax::ast::{DefId};
use syntax::ast;
use syntax::codemap::Span;
use util::common::ErrorReported;
use util::ppaux::Repr;

use self::inherent_methods::search_inherent_methods;
use self::trait_methods::search_trait_methods;
use self::trait_methods::test_methods_from_traits;
use self::reconcile::reconcile_receiver;

mod inherent_methods;
mod trait_methods;
mod reconcile;

struct MethodInfo {
    xform_ty: deref::TransformedSelfType,
    selection: Vtable<Obligation>,
}

pub fn lookup<'a>(
    fcx: &FnCtxt,
    call_expr: &ast::Expr,              // The expression `a.b(...)`.
    self_expr: &'a ast::Expr,           // The expression `a`.
    method_name: ast::Name,             // The name `b`.
    self_ty: ty::t,                     // The type of `a`.
    supplied_tps: &'a [ty::t])          // The list of types X, Y, ... .
    -> Result<Option<MethodCallee>, ErrorReported>
{
    debug!("lookup(call_expr={}, \
           method_name={}, \
           self_ty={}, \
           supplied_tps={})",
           call_expr.repr(fcx.tcx()),
           method_name.repr(fcx.tcx()),
           self_ty.repr(fcx.tcx()),
           supplied_tps.repr(fcx.tcx()));

    let info = {
        match try!(search_inherent_methods(fcx, call_expr, self_expr,
                                           self_ty, method_name)) {
            Some(i) => i,
            None => {
                match try!(search_trait_methods(fcx, call_expr, self_expr,
                                                self_ty, method_name)) {
                    Some(i) => i,
                    None => {
                        return Ok(None);
                    }
                }
            }
        }
    };

    Ok(Some(try!(reconcile_receiver(fcx, call_expr.span, self_expr,
                                    info.xform_ty, info.selection,
                                    method_name, supplied_tps))))
}

pub fn lookup_in_traits(
    fcx: &FnCtxt,
    call_span: Span,
    self_expr: &ast::Expr,
    self_ty: ty::t,
    method_name: ast::Name,
    trait_def_ids: &[ast::DefId])
    -> Result<Option<MethodCallee>, ErrorReported>
{
    match test_methods_from_traits(fcx, call_span, self_expr, self_ty,
                                   method_name, trait_def_ids) {
        Err(ErrorReported) => Err(ErrorReported),
        Ok(Some(info)) => {
            Ok(Some(try!(reconcile_receiver(fcx, call_span, self_expr,
                                            info.xform_ty, info.selection,
                                            method_name, []))))
        }
        Ok(None) => {
            Ok(None)
        }
    }
}

pub fn method_callee(fcx: &FnCtxt,
                     call_span: Span,
                     selection: Selection,
                     method_name: ast::Name,
                     supplied_method_type_params: &[ty::t])
                     -> MethodCallee
{
    reconcile::method_callee(fcx, call_span, selection, method_name,
                             supplied_method_type_params)
}
