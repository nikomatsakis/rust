// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Field lookup */

use middle::ty::*;
use middle::ty;
use middle::typeck::astconv::AstConv;
use middle::typeck::check::FnCtxt;
use middle::typeck::check::deref;
use syntax::ast;
use syntax::parse::token;
use util::common::ErrorReported;
use util::ppaux;
use util::ppaux::Repr;

use super::LvaluePreference;
use super::check_expr_with_lvalue_pref;
use super::lookup_field_ty;
use super::method;

// Check field access expressions
pub fn check_field(fcx: &FnCtxt,
                   expr: &ast::Expr,
                   lvalue_pref: LvaluePreference,
                   base: &ast::Expr,
                   field: ast::Name,
                   tys: &Vec<ast::P<ast::Ty>>)
                   -> ty::t
{
    let tcx = fcx.ccx.tcx;
    check_expr_with_lvalue_pref(fcx, base, lvalue_pref);
    let expr_ty = fcx.expr_ty(base);
    let mut has_field = HasFieldTest { fcx: fcx, field: field };
    match deref::autoderef_loop(fcx, expr.span, expr_ty, &mut has_field) {
        // Found a field, horray!
        deref::FoundMatch(xform_ty, field_ty) => {
            deref::record_autoderefs(fcx, expr, xform_ty, None);
            return field_ty;
        }

        // Some kind of error.
        deref::FoundReportedError => {
            return ty::mk_err();
        }

        // No match. Look for a method with that name and offer a
        // helpful suggestion:
        deref::FoundNoMatch(_) => {
            let tps: Vec<ty::t> = tys.iter().map(|&ty| fcx.to_ty(ty)).collect();
            match method::lookup(fcx,
                                 expr,
                                 base,
                                 field,
                                 expr_ty,
                                 tps.as_slice()) {
                Ok(Some(_)) => {
                    fcx.type_error_message(
                        expr.span,
                        |actual| {
                            format!("attempted to take value of method `{}` on type \
                                 `{}`", token::get_name(field), actual)
                        },
                        expr_ty,
                        None);

                    tcx.sess.span_note(expr.span,
                                       "maybe a missing `()` to call it? \
                                        If not, try an anonymous function.");
                }

                Ok(None) => {
                    fcx.type_error_message(
                        expr.span,
                        |actual| {
                            format!("attempted access of field `{}` on \
                                        type `{}`, but no field with that \
                                        name was found",
                                    token::get_name(field),
                                    actual)
                        },
                        expr_ty,
                        None);
                }

                Err(ErrorReported) => { }
            }

            return ty::mk_err();
        }
    }
}

struct HasFieldTest<'a> {
    fcx: &'a FnCtxt<'a>,
    field: ast::Name,
}

impl<'a> deref::Test<ty::t> for HasFieldTest<'a> {
    fn test(&mut self, ty: ty::t) -> Result<Option<ty::t>,ErrorReported> {
        // FIXME(eddyb) #12808 Integrate privacy into this auto-deref loop.
        let tcx = self.fcx.tcx();
        Ok(match ty::get(ty).sty {
            ty::ty_struct(struct_def_id, ref substs) => {
                debug!("struct named {}", ty.repr(tcx));
                let fields = ty::lookup_struct_fields(tcx, struct_def_id);
                lookup_field_ty(tcx,
                                struct_def_id,
                                fields.as_slice(),
                                self.field,
                                &*substs)
            }

            _ => {
                None
            }
        })
    }
}
