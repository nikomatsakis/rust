// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Deref and autoderef */

use middle::subst::Substs;
use middle::traits;
use middle::traits::{Obligation, Vtable};
use middle::ty;
use middle::typeck::MethodCall;
use middle::typeck::infer;
use std::rc::Rc;
use syntax::ast;
use syntax::codemap::Span;
use syntax::parse::token;
use util::common::ErrorReported;
use util::ppaux::{Repr,UserString};

use super::FnCtxt;
use super::structurally_resolved_type;
use super::vtable;
use super::method;
use super::{LvaluePreference, PreferMutLvalue, NoPreference};

pub enum SearchResult<R> {
    FoundMatch(TransformedSelfType, R),
    FoundNoMatch(TransformedSelfType),
    FoundReportedError
}

pub struct TransformedSelfType {
    pub ty: ty::t,
    pub xform: Transformation
}

pub enum Transformation {
    RootType,
    OverloadedDeref(/* base type */ Box<TransformedSelfType>,
                    /* deref trait def-id */ ast::DefId,
                    /* impl for deref trait */ Vtable<Obligation>),
    BuiltinDeref(Box<TransformedSelfType>),
    ObjectDeref(Box<TransformedSelfType>),
    Slice(ty::Region, /* base type */ Box<TransformedSelfType>),
}

pub trait Test<R> {
    fn test(&mut self, ty: ty::t) -> Result<Option<R>,ErrorReported>;
}

pub fn check_deref(fcx: &FnCtxt,
                   deref_expr: &ast::Expr,
                   operand_expr: &ast::Expr,
                   operand_ty: ty::t,
                   lvalue_pref: LvaluePreference)
                   -> ty::t
{
    // Explicity derefable
    let operand_ty = structurally_resolved_type(fcx,
                                                operand_expr.span,
                                                operand_ty);
    match ty::deref(operand_ty, true) {
        Some(mt) => { return mt.ty; }
        None => { }
    }

    // Check for override.
    let referent_ty = fcx.infcx().next_ty_var();
    let opt_trait_def_id = deref_trait_for_lvalue_pref(fcx, lvalue_pref);
    match resolve_overloaded_deref(fcx,
                                   operand_expr.span,
                                   opt_trait_def_id,
                                   operand_ty,
                                   referent_ty)
    {
        Ok(Some((vtable_origin, trait_def_id))) => {
            let method_call = MethodCall::expr(deref_expr.id);
            record_overloaded_deref(fcx, operand_expr.span, method_call,
                                    trait_def_id, vtable_origin);
            return referent_ty;
        }

        Err(ErrorReported) => {
            return ty::mk_err();
        }

        Ok(None) => { }
    }

    // Cannot deref. Try to give a friendly error.
    let is_newtype = match ty::get(operand_ty).sty {
        ty::ty_struct(did, ref substs) => {
            let fields = ty::struct_fields(fcx.tcx(), did, substs);
            fields.len() == 1 &&
                fields.get(0).ident == token::special_idents::unnamed_field
        }
        _ => false
    };
    if is_newtype {
        // This is an obsolete struct deref
        fcx.tcx().sess.span_err(
            operand_expr.span,
            "single-field tuple-structs can no longer be dereferenced");
    } else {
        fcx.type_error_message(
            operand_expr.span,
            |actual| format!("type `{}` cannot be dereferenced", actual),
            operand_ty,
            None);
    }
    return ty::mk_err();
}

pub fn autoderef_loop<R,T:Test<R>>(fcx: &FnCtxt,
                                   span: Span,
                                   initial_xform_ty: ty::t,
                                   test: &mut T)
                                   -> SearchResult<R>
{
    /*!
     * Repeatedly dereferences `initial_xform_ty`. For each type `t`
     * along the way, invokes `test.test(t)`.
     *
     * Stops if either:
     * - `test.test()` reports an error.
     * - `test.test()` returns `Ok(Some(_))`.
     * - it is not possible to dereference `t`.
     *
     * Returns a `TransformedSelfType` with all the information about
     * what dereferences happened along the way. If you decide to employ
     * the autodereferencing, you must call `record_autoderefs()` to
     * write the appropriate adjustments and method info into the tables.
     *
     * Autodereferencing always checks only for the `Deref` trait when
     * resolving overloaded derefs. If you want a mutable lvalue as a
     * result, you can transform the `TransformedSelfType` into
     * mutable derefs using `make_mutable()`.
     */

    let mut xform_ty = TransformedSelfType { ty: initial_xform_ty,
                                             xform: RootType };
    for _ in range(0, fcx.tcx().sess.recursion_limit.get()) {
        debug!("autoderef_loop: {}", xform_ty.repr(fcx.tcx()));

        let ty = structurally_resolved_type(fcx, span, xform_ty.ty);
        if ty::type_is_error(ty) {
            return FoundReportedError;
        }

        // Check whether to stop iterating at this type.
        match test.test(ty) {
            Ok(Some(data)) => {
                return FoundMatch(xform_ty, data);
            }

            Ok(None) => {
            }

            Err(ErrorReported) => {
                return FoundReportedError;
            }
        }

        // Check for built-in deref rules.
        match ty::deref(ty, false) {
            Some(mt) => {
                let xform = BuiltinDeref(box xform_ty);
                xform_ty = TransformedSelfType(mt.ty, xform);
                continue;
            }

            None => { }
        }

        // Assuming the `Deref` trait is defined in the stdlib,
        // create an obligation like `Deref<referent_ty> for xform_ty.ty`
        let referent_ty = fcx.infcx().next_ty_var();
        let opt_trait_def_id = fcx.tcx().lang_items.deref_trait();
        match deref_transformed_ty(fcx, span, opt_trait_def_id,
                                   xform_ty, referent_ty) {
            FoundMatch(referent_xform_ty, ()) => {
                xform_ty = referent_xform_ty;
                continue;
            }

            // Not successful! Stop the autoderef loop.

            FoundNoMatch(xform_ty) => {
                return FoundNoMatch(xform_ty);
            }

            FoundReportedError => {
                return FoundReportedError;
            }
        }
    }

    // We've reached the recursion limit, error gracefully.
    fcx.tcx().sess.span_err(
        span,
        format!("reached the recursion limit while auto-dereferencing `{}`",
                initial_xform_ty.user_string(fcx.tcx())).as_slice());
    return FoundReportedError;
}

pub fn method_autoderef_loop<R,T:Test<R>>(fcx: &FnCtxt,
                                          span: Span,
                                          initial_xform_ty: ty::t,
                                          test: &mut T)
                                          -> SearchResult<R>
{
    let xform_ty = match autoderef_loop(fcx, span, initial_xform_ty, test) {
        FoundNoMatch(xform_ty) => xform_ty,
        FoundMatch(xform_ty, r) => {
            return FoundMatch(xform_ty, r);
        }
        FoundReportedError => {
            return FoundReportedError;
        }
    };

    debug!("found no match: {}", xform_ty.repr(fcx.tcx()));

    // Special hacky behavior for trait objects, kind of simulating DST.
    match ty::get(xform_ty.ty).sty {
        ty::ty_uniq(referent_ty) |
        ty::ty_rptr(_, ty::mt { ty: referent_ty, .. }) => {
            match ty::get(referent_ty).sty {
                ty::ty_trait(..) => {
                    let new_xform = ObjectDeref(box xform_ty);
                    let new_xform_ty =
                        TransformedSelfType { ty: referent_ty,
                                              xform: new_xform };
                    debug!("method_autoderef_loop: {}",
                           new_xform_ty.repr(fcx.tcx()));
                    return match test.test(referent_ty) {
                        Ok(Some(data)) => FoundMatch(new_xform_ty, data),
                        Ok(None) => FoundNoMatch(new_xform_ty),
                        Err(ErrorReported) => FoundReportedError,
                    };
                }
                _ => {}
            }
        }
        _ => {}
    }

    // Special "autoslice" behavior for vectors (to *some extent*, this
    // will go away with DST):
    // - `&'a mut [referent_ty]` -> `&'b [referent_ty]`
    match ty::get(xform_ty.ty).sty {
        ty::ty_rptr(r_b, ty::mt { ty: referent_ty, mutbl: ast::MutMutable }) => {
            match ty::get(referent_ty).sty {
                ty::ty_vec(ty::mt { ty: element_ty, .. }, _) => {
                    let r_a = fcx.infcx().next_region_var(infer::Autoref(span));
                    fcx.mk_subr(true, infer::Reborrow(span), r_a, r_b);
                    let new_xform = Slice(r_a, box xform_ty);
                    let slice_ty =
                        ty::mk_vec(fcx.tcx(),
                                   ty::mt { ty: element_ty,
                                            mutbl: ast::MutImmutable },
                                   None);
                    let new_ty =
                        ty::mk_rptr(fcx.tcx(),
                                    r_a,
                                    ty::mt { ty: slice_ty,
                                             mutbl: ast::MutImmutable });
                    let new_xform_ty =
                        TransformedSelfType { ty: new_ty,
                                              xform: new_xform };
                    debug!("method_autoderef_loop: {}",
                           new_xform_ty.repr(fcx.tcx()));
                    return match test.test(new_ty) {
                        Ok(Some(data)) => FoundMatch(new_xform_ty, data),
                        Ok(None) => FoundNoMatch(new_xform_ty),
                        Err(ErrorReported) => FoundReportedError,
                    };
                }

                _ => {
                }
            }
        }

        _ => {
        }
    }

    FoundNoMatch(xform_ty)
}

pub fn root_type(t: ty::t) -> TransformedSelfType {
    TransformedSelfType {
        ty: t,
        xform: RootType
    }
}

fn deref_trait_for_lvalue_pref(fcx: &FnCtxt,
                               lvalue_pref: LvaluePreference)
                               -> Option<ast::DefId>
{
    match lvalue_pref {
        NoPreference => fcx.tcx().lang_items.deref_trait(),
        PreferMutLvalue => fcx.tcx().lang_items.deref_mut_trait(),
    }
}

fn deref_transformed_ty(fcx: &FnCtxt,
                        span: Span,
                        opt_trait_def_id: Option<ast::DefId>,
                        xform_ty: TransformedSelfType,
                        referent_ty: ty::t)
                        -> SearchResult<()>
{
    /*!
     *
     */

    match resolve_overloaded_deref(fcx,
                                   span,
                                   opt_trait_def_id,
                                   xform_ty.ty,
                                   referent_ty) {
        Ok(None) => {
            FoundNoMatch(xform_ty)
        }
        Ok(Some((deref_origin, trait_def_id))) => {
            FoundMatch(
                TransformedSelfType(referent_ty,
                                    OverloadedDeref(box xform_ty,
                                                    trait_def_id,
                                                    deref_origin)),
                ())
        }
        Err(ErrorReported) => {
            FoundReportedError
        }
    }
}

fn resolve_overloaded_deref(fcx: &FnCtxt,
                            span: Span,
                            deref_trait: Option<ast::DefId>,
                            self_ty: ty::t,
                            referent_ty: ty::t)
                            -> Result<Option<(Vtable<Obligation>, ast::DefId)>,
                                      ErrorReported>
{
    /*!
     * Resolves an overloaded deref using the trait `deref_trait`,
     * which must be either `Deref` or `DerefMut`
     */

    // Find the lang item for the deref trait (if any).
    let trait_def_id = match deref_trait {
        Some(d) => d,
        None => {
            // Deref trait is not defined, hence cannot be implemented.
            return Ok(None);
        }
    };

    // Create an obligation for `Deref<referent_ty> for self_ty`
    let substs = Substs::new_trait(vec!(referent_ty),
                                   vec!(),
                                   self_ty);
    let trait_ref = Rc::new(ty::TraitRef { def_id: trait_def_id,
                                           substs: substs });
    let deref_obligation = Obligation::new(span, trait_ref);

    let deref_resolution = traits::try_select_obligation(fcx.infcx(),
                                                         &fcx.inh.param_env,
                                                         &deref_obligation);
    match deref_resolution {
        Ok(Some(deref_origin)) => {
            Ok(Some((deref_origin, trait_def_id)))
        }

        Err(traits::Unimplemented) => {
            Ok(None)
        }

        Ok(None) => {
            vtable::maybe_report_ambiguity(fcx, &deref_obligation);
            Err(ErrorReported)
        }

        Err(e) => {
            vtable::report_selection_error(fcx, &deref_obligation, &e);
            Err(ErrorReported)
        }
    }
}

#[allow(non_snake_case_functions)]
fn TransformedSelfType(ty: ty::t, xform: Transformation) -> TransformedSelfType {
    TransformedSelfType { ty: ty, xform: xform }
}

pub fn record_autoderefs(fcx: &FnCtxt,
                         expr: &ast::Expr,
                         xform_ty: TransformedSelfType,
                         autoptr: Option<(ty::Region, ast::Mutability)>)
{
    /*!
     * Records the deref information from various autoderefs.
     */

    let (autoderefs, opt_autoref) = do_autoptr(fcx, expr, xform_ty, autoptr);
    let adjustment =
        ty::AutoDerefRef(ty::AutoDerefRef {
            autoderefs: autoderefs as uint,
            autoref: opt_autoref
        });
    fcx.write_adjustment(expr.id, adjustment);

    fn do_autoptr(fcx: &FnCtxt,
                  expr: &ast::Expr,
                  xform_ty: TransformedSelfType,
                  autoptr: Option<(ty::Region, ast::Mutability)>)
                  -> (uint, Option<ty::AutoRef>)
    {
        let opt_autoref = match xform_ty.xform {
            Slice(r1, _) => {
                match autoptr {
                    Some((r2, m)) => Some(ty::AutoBorrowVecRef(r1, r2, m)),
                    None => Some(ty::AutoBorrowVec(r1, ast::MutImmutable)),
                }
            }

            ObjectDeref(..) => {
                // Until DST lands in its full glory, the only real
                // combination that can arise here is an autoref
                // paired with an ObjectDeref. We take the combination
                // of that and call it an AutoObject. Post DST, this
                // whole "ObjectDeref" category won't be needed at
                // all.
                match autoptr {
                    Some((r, m)) => Some(ty::AutoBorrowObj(r, m)),
                    None => None,
                }
            }

            _ => {
                match autoptr {
                    Some((r, m)) => Some(ty::AutoPtr(r, m)),
                    None => None,
                }
            }
        };

        let autoderef_cnt = do_autoderef(fcx, expr, xform_ty);

        (autoderef_cnt, opt_autoref)
    }

    fn do_autoderef(fcx: &FnCtxt,
                    expr: &ast::Expr,
                    xform_ty: TransformedSelfType)
                    -> uint
    {
        match xform_ty.xform {
            RootType => {
                0
            }

            BuiltinDeref(box pointer_xform_ty) => {
                do_autoderef(fcx, expr, pointer_xform_ty) + 1
            }

            OverloadedDeref(box pointer_xform_ty,
                            trait_def_id,
                            origin) => {
                let n = do_autoderef(fcx, expr, pointer_xform_ty);
                let method_call = MethodCall::autoderef(expr.id, n);
                record_overloaded_deref(fcx, expr.span, method_call,
                                        trait_def_id, origin);

                n + 1
            }

            ObjectDeref(box pointer_xform_ty) => {
                // ObjectDerefs are always paired with an AutoRef into
                // an AutoBorrowObj, and they do not therefore count
                // as part of the "autoderef count".
                do_autoderef(fcx, expr, pointer_xform_ty)
            }

            Slice(_, box slice_xform_ty) => {
                // Similar to ObjectDerefs, a slice always comes at the end
                // and is integrated into the autoref portion, just ignore
                // for purpose of counting derefs.
                do_autoderef(fcx, expr, slice_xform_ty)
            }
        }
    }
}

fn record_overloaded_deref(fcx: &FnCtxt,
                           deref_span: Span,
                           method_call: MethodCall,
                           deref_trait_def_id: ast::DefId,
                           origin: Vtable<Obligation>)
{
    // Find the name of the deref method, which will be either `deref`
    // or `deref_mut`, depending on whether this is Deref<T> or
    // DerefMut<T>. Here we rely on fact that deref traits should have
    // just one method.
    let deref_trait_methods = ty::trait_methods(fcx.tcx(), deref_trait_def_id);
    assert_eq!(deref_trait_methods.len(), 1);
    let deref_method_name = deref_trait_methods.get(0).ident.name;

    // Create the method callee and store it into the map.
    let method_callee = method::method_callee(fcx,
                                              deref_span,
                                              origin,
                                              deref_method_name,
                                              []);
    fcx.inh.method_map.borrow_mut().insert(method_call, method_callee);
}

pub fn make_mutable(fcx: &FnCtxt,
                    span: Span,
                    xform_ty: TransformedSelfType)
                    -> Result<Option<TransformedSelfType>,ErrorReported>
{
    /*!
     * Convert dereferences to a shared reference into dereferences of
     * a mutable pointer. Yields `Ok(None)` if this is not possible
     * (i.e., because the receiver does not implement `DerefMut`).
     */

    Ok(match xform_ty {
        TransformedSelfType {
            ty: _,
            xform: RootType } =>
        {
            Some(xform_ty)
        }
        TransformedSelfType {
            ty: referent_ty,
            xform: BuiltinDeref(box base_xform_ty) } =>
        {
            match try!(make_mutable(fcx, span, base_xform_ty)) {
                Some(mut_base_xform_ty) => {
                    Some(TransformedSelfType {
                        ty: referent_ty,
                        xform: BuiltinDeref(box mut_base_xform_ty) })
                }

                None => {
                    None
                }
            }
        }
        TransformedSelfType {
            ty: referent_ty,
            xform: OverloadedDeref(box base_xform_ty, _, _) } =>
        {
            match try!(make_mutable(fcx, span, base_xform_ty)) {
                None => { None }
                Some(mut_base_xform_ty) => {
                    let opt_trait_def_id =
                        fcx.tcx().lang_items.deref_mut_trait();
                    match deref_transformed_ty(fcx,
                                               span,
                                               opt_trait_def_id,
                                               mut_base_xform_ty,
                                               referent_ty) {
                        FoundReportedError => return Err(ErrorReported),
                        FoundMatch(t, ()) => Some(t),
                        FoundNoMatch(_) => None
                    }
                }
            }
        }
        TransformedSelfType {
            ty: referent_ty,
            xform: ObjectDeref(box base_xform_ty) } =>
        {
            match try!(make_mutable(fcx, span, base_xform_ty)) {
                Some(mut_base_xform_ty) => {
                    Some(TransformedSelfType {
                        ty: referent_ty,
                        xform: ObjectDeref(box mut_base_xform_ty) })
                }

                None => {
                    None
                }
            }
        }
        TransformedSelfType {
            ty: referent_ty,
            xform: Slice(r, box base_xform_ty) } =>
        {
            match try!(make_mutable(fcx, span, base_xform_ty)) {
                Some(mut_base_xform_ty) => {
                    Some(TransformedSelfType {
                        ty: referent_ty,
                        xform: Slice(r, box mut_base_xform_ty) })
                }

                None => {
                    None
                }
            }
        }
    })
}

impl Repr for TransformedSelfType {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("TransformedSelfType({},{})",
                self.ty.repr(tcx), self.xform.repr(tcx))
    }
}

impl Repr for Transformation {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            RootType => {
                format!("RootType")
            }
            OverloadedDeref(ref a, ref b, ref c) => {
                format!("OverloadedDeref({},{},{})",
                        a.repr(tcx), b.repr(tcx), c.repr(tcx))
            }
            BuiltinDeref(ref a) => {
                format!("BuiltinDeref({})", a.repr(tcx))
            }
            ObjectDeref(ref a) => {
                format!("ObjectDeref({})", a.repr(tcx))
            }
            Slice(ref a, ref b) => {
                format!("Slice({},{})", a.repr(tcx), b.repr(tcx))
            }
        }
    }
}
