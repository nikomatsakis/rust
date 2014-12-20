// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


use check::FnCtxt;
use middle::ty::{mod, Ty};
use middle::infer;

use std::result::Result::{Err, Ok};
use syntax::ast;
use syntax::codemap::Span;
use util::ppaux::Repr;

/// Requires that `actual <: expected` and prints an error if this is not true.
pub fn suptype<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>, sp: Span,
                         expected: Ty<'tcx>, actual: Ty<'tcx>) {
    suptype_with_fn(fcx, sp, false, expected, actual,
        |sp, e, a, s| { fcx.report_mismatched_types(sp, e, a, s) })
}

/// Requires that `expected <: actual` and prints an error if this is
/// not true. This is the same as `suptype` with the order of parameters
/// reversed, except for the fact that the type which is considered
/// the "expected" type is switched.
pub fn subtype<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>, sp: Span,
                         expected: Ty<'tcx>, actual: Ty<'tcx>) {
    match infer::mk_subty(fcx.infcx(), true, infer::Misc(sp), expected, actual) {
        Ok(()) => { }
        Err(ref err) => {
            fcx.report_mismatched_types(sp, expected, actual, err);
        }
    }
}

pub fn suptype_with_fn<'a, 'tcx, F>(fcx: &FnCtxt<'a, 'tcx>,
                                    sp: Span,
                                    b_is_expected: bool,
                                    ty_a: Ty<'tcx>,
                                    ty_b: Ty<'tcx>,
                                    handle_err: F) where
    F: FnOnce(Span, Ty<'tcx>, Ty<'tcx>, &ty::type_err<'tcx>),
{
    // n.b.: order of actual, expected is reversed
    match infer::mk_subty(fcx.infcx(), b_is_expected, infer::Misc(sp),
                          ty_b, ty_a) {
      Ok(()) => { /* ok */ }
      Err(ref err) => {
          handle_err(sp, ty_a, ty_b, err);
      }
    }
}

pub fn eqtype<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>, sp: Span,
                        expected: Ty<'tcx>, actual: Ty<'tcx>) {
    match infer::mk_eqty(fcx.infcx(), false, infer::Misc(sp), actual, expected) {
        Ok(()) => { /* ok */ }
        Err(ref err) => {
            fcx.report_mismatched_types(sp, expected, actual, err);
        }
    }
}

// Checks that the type `actual` can be coerced to `expected`.
pub fn coerce<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>, sp: Span,
                        expected: Ty<'tcx>, expr: &ast::Expr) {
    let expr_ty = fcx.expr_ty(expr);
    debug!("demand::coerce(expected = {}, expr_ty = {})",
           expected.repr(fcx.ccx.tcx),
           expr_ty.repr(fcx.ccx.tcx));
    let expected = fcx.infcx().resolve_type_vars_if_possible(&expected);
    match fcx.mk_assignty(expr, expr_ty, expected) {
      Ok(()) => { /* ok */ }
      Err(ref err) => {
        fcx.report_mismatched_types(sp, expected, expr_ty, err);
      }
    }
}
