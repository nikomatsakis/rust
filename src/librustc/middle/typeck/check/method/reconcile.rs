// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Receiver reconciliation: see doc.rs for documentation */

use middle::subst;
use middle::subst::{Subst, Substs};
use middle::traits::{Vtable, VtableOrigin, VtableParam, Builtin};
use middle::ty;
use middle::typeck::{MethodCallee, MethodOrigin, MethodStatic,
                     MethodParam};
use middle::typeck::check::{deref, FnCtxt};
use middle::typeck::check::regionmanip::replace_late_bound_regions_in_fn_sig;
use middle::typeck::check::deref::{TransformedSelfType, RootType,
                                   BuiltinDeref, OverloadedDeref};
use middle::typeck::infer;
use std::rc::Rc;
use syntax::ast;
use syntax::codemap::Span;
use util::common::ErrorReported;

use util::ppaux::{Repr, UserString};

pub fn reconcile_receiver(fcx: &FnCtxt,
                          call_span: Span,
                          self_expr: &ast::Expr,
                          xform_ty: deref::TransformedSelfType,
                          origin: VtableOrigin,
                          method_name: ast::Name,
                          supplied_method_type_params: &[ty::t])
                          -> Result<MethodCallee, ErrorReported>
{
    let method_callee =
        method_callee(fcx, call_span, origin, method_name,
                      supplied_method_type_params);

    let method_self_ty =
        try!(extract_method_self_ty(fcx, call_span, method_name,
                                    method_callee.ty));

    let mut xform_ty = xform_ty;

    loop {
        let current_ty = xform_ty.ty;

        // Check if the method accepts T:
        if test_receiver(fcx, current_ty, method_self_ty) {
            confirm_receiver(fcx, self_expr, xform_ty, method_self_ty);
            return Ok(method_callee);
        }

        // Check if the method accepts &T:
        if test_autoref_receiver(fcx, call_span, ast::MutImmutable,
                                 current_ty, method_self_ty) {
            let (ref_region, ref_ty) =
                make_autoref_type(fcx, call_span, current_ty,
                                  ast::MutImmutable);
            confirm_autoref_receiver(fcx,
                                     self_expr,
                                     xform_ty,
                                     ref_ty,
                                     method_self_ty,
                                     ref_region,
                                     ast::MutImmutable);
            return Ok(method_callee);
        }

        // Check if the method accepts &mut T:
        if test_autoref_receiver(fcx, call_span, ast::MutMutable,
                                 current_ty, method_self_ty) {
            let (ref_region, ref_ty) =
                make_autoref_type(fcx, call_span, current_ty,
                                  ast::MutMutable);
            match deref::make_mutable(fcx, call_span, xform_ty) {
                Ok(Some(mut_xform_ty)) => {
                    confirm_autoref_receiver(fcx,
                                             self_expr,
                                             mut_xform_ty,
                                             ref_ty,
                                             method_self_ty,
                                             ref_region,
                                             ast::MutMutable);
                    return Ok(method_callee);
                }

                Ok(None) => {
                    // &mut self but does not implement DerefMut
                    report_mut_self_error(fcx, call_span,
                                          method_name, current_ty);
                    return Err(ErrorReported);
                }

                Err(ErrorReported) => {
                    return Err(ErrorReported);
                }
            }
        }

        // If no match, peel back a layer of transform and try again.
        // If there are no more layers, report an error -- probably indicates
        // that we have a receiver like `&Foo` but the request type is
        // more specific, like `Box<Foo>`.
        match xform_ty.xform {
            RootType => {
                report_reconciliation_error(fcx, call_span, current_ty,
                                            method_self_ty, method_name);
                return Err(ErrorReported);
            }

            BuiltinDeref(box t) | OverloadedDeref(box t, _, _) => {
                xform_ty = t;
            }
        }
    }
}

pub fn method_callee(fcx: &FnCtxt,
                     call_span: Span,
                     origin: VtableOrigin,
                     method_name: ast::Name,
                     supplied_method_type_params: &[ty::t])
                     -> MethodCallee
{
    let (method_substs, method, method_origin) =
        instantiate_method_params(fcx, call_span, origin, method_name,
                                  supplied_method_type_params);

    let method_fnty =
        compute_method_type(fcx, call_span, &method_substs, &method);

    MethodCallee {
        origin: method_origin,
        ty: method_fnty,
        substs: method_substs
    }
}

fn instantiate_method_params(fcx: &FnCtxt,
                             call_span: Span,
                             origin: VtableOrigin,
                             method_name: ast::Name,
                             supplied_method_type_params: &[ty::t])
                             -> (Substs, Rc<ty::Method>, MethodOrigin)
{
    let (substs, method, method_origin) =
        decompose_vtable_origin(fcx, call_span, origin, method_name);

    // Determine the values for the generic parameters of the method.
    // If they were not explicitly supplied, just construct fresh
    // variables.
    let num_supplied_tps = supplied_method_type_params.len();
    let num_method_tps = method.generics.types.get_vec(subst::FnSpace).len();
    let m_types = if num_supplied_tps == 0u {
        fcx.infcx().next_ty_vars(num_method_tps)
    } else if num_method_tps == 0u {
        fcx.tcx().sess.span_err(
            call_span,
            "this method does not take type parameters");
        Vec::new()
    } else if num_supplied_tps != num_method_tps {
        fcx.tcx().sess.span_err(
            call_span,
            "incorrect number of type parameters given for this method");
        Vec::from_elem(num_method_tps, ty::mk_err())
    } else {
        Vec::from_slice(supplied_method_type_params)
    };

    // Determine values for the early-bound lifetime parameters.
    // FIXME -- permit users to manually specify lifetimes
    let m_regions =
        fcx.infcx().region_vars_for_defs(
            call_span,
            method.generics.regions.get_vec(subst::FnSpace));

    // Combine the method's parameters with those from the trait/impl.
    (substs.with_method(m_types, m_regions), method, method_origin)
}

fn compute_method_type(fcx: &FnCtxt,
                       call_span: Span,
                       substs: &Substs,
                       method: &Rc<ty::Method>)
                       -> ty::t
{
    let tcx = fcx.tcx();

    // Compute the method type with type parameters substituted
    let fn_sig = &method.fty.sig;
    let inputs = /*match candidate.origin {
        MethodObject(..) => {
            // For annoying reasons, we've already handled the
            // substitution of self for object calls.
            let args = fn_sig.inputs.slice_from(1).iter().map(|t| {
                t.subst(tcx, &substs)
            });
            Some(*fn_sig.inputs.get(0)).move_iter().chain(args).collect()
        }
        _ => */ fn_sig.inputs.subst(tcx, substs)
    /* } */ ;
    let fn_sig = ty::FnSig {
        binder_id: fn_sig.binder_id,
        inputs: inputs,
        output: fn_sig.output.subst(tcx, substs),
        variadic: fn_sig.variadic
    };
    debug!("after subst, fty={}", fn_sig.repr(tcx));

    // Replace any bound regions that appear in the function
    // signature with region variables
    let (_, fn_sig) =
        replace_late_bound_regions_in_fn_sig(
            tcx,
            &fn_sig,
            |br| fcx.infcx().next_region_var(
                     infer::LateBoundRegion(call_span, br)));
    let fty = ty::mk_bare_fn(tcx, ty::BareFnTy {
        sig: fn_sig,
        fn_style: method.fty.fn_style,
        abi: method.fty.abi.clone(),
    });
    debug!("after replacing bound regions, fty={}", fty.repr(fcx.tcx()));

    fty
}

fn extract_method_self_ty(fcx: &FnCtxt,
                          call_span: Span,
                          method_name: ast::Name,
                          method_fnty: ty::t)
                          -> Result<ty::t,ErrorReported>
{
    let args = ty::ty_fn_args(method_fnty);
    if args.len() > 0 {
        Ok(*args.get(0))
    } else {
        fcx.tcx().sess.span_err(
            call_span,
            format!("method `{}` does not take any arguments; \
                     perhaps missing a `self` declaration?",
                    method_name.user_string(fcx.tcx())).as_slice());
        return Err(ErrorReported);
    }
}

fn test_autoref_receiver(fcx: &FnCtxt,
                         span: Span,
                         mutbl: ast::Mutability,
                         self_ty: ty::t,
                         method_self_ty: ty::t)
                         -> bool
{
    fcx.infcx().probe(|| {
        let (_, t) = make_autoref_type(fcx, span, self_ty, mutbl);
        infer::can_mk_subty(fcx.infcx(), t, method_self_ty)
    }).is_ok()
}

fn test_receiver(fcx: &FnCtxt,
                 self_ty: ty::t,
                 method_self_ty: ty::t)
                 -> bool
{
    fcx.infcx().probe(
        || infer::can_mk_subty(fcx.infcx(), self_ty, method_self_ty)).is_ok()
}

fn make_autoref_type(fcx: &FnCtxt,
                     span: Span,
                     self_ty: ty::t,
                     mutbl: ast::Mutability)
                     -> (ty::Region, ty::t)
{
    let r = fcx.infcx().next_region_var(infer::Autoref(span));
    (r, ty::mk_rptr(fcx.tcx(), r, ty::mt { mutbl: mutbl, ty: self_ty }))
}

fn report_mut_self_error(fcx: &FnCtxt,
                         call_span: Span,
                         method_name: ast::Name,
                         self_ty: ty::t)
{
    fcx.tcx().sess.span_err(
        call_span,
        format!("method `{}` requires an `&mut` receiver, \
                 but type `{}` does not implement `DerefMut`",
                method_name.user_string(fcx.tcx()),
                self_ty.user_string(fcx.tcx())).as_slice());
}

fn confirm_autoref_receiver(fcx: &FnCtxt,
                            self_expr: &ast::Expr,
                            unrefd_xform_ty: deref::TransformedSelfType,
                            refd_self_ty: ty::t,
                            method_self_ty: ty::t,
                            region: ty::Region,
                            mutbl: ast::Mutability)
{
    confirm_self_ty(fcx, self_expr.span, refd_self_ty, method_self_ty);
    deref::record_autoderefs(fcx, self_expr, unrefd_xform_ty,
                             Some(ty::AutoPtr(region, mutbl)));
}

fn confirm_receiver(fcx: &FnCtxt,
                    self_expr: &ast::Expr,
                    xform_ty: deref::TransformedSelfType,
                    method_self_ty: ty::t)
{
    confirm_self_ty(fcx, self_expr.span, xform_ty.ty, method_self_ty);
    deref::record_autoderefs(fcx, self_expr, xform_ty, None);
}

fn confirm_self_ty(fcx: &FnCtxt,
                   self_span: Span,
                   self_ty: ty::t,
                   method_self_ty: ty::t)
{
    match infer::mk_subty(fcx.infcx(), false, infer::RelateSelfType(self_span),
                          self_ty, method_self_ty) {
        Ok(()) => { }
        Err(_) => {
            fcx.tcx().sess.span_bug(
                self_span,
                format!(
                    "{} was a subtype of {} but now is not?",
                    self_ty.repr(fcx.tcx()),
                    method_self_ty.repr(fcx.tcx())).as_slice());
        }
    }
}

fn report_reconciliation_error(fcx: &FnCtxt,
                               call_span: Span,
                               self_ty: ty::t,
                               method_self_ty: ty::t,
                               method_name: ast::Name)
{
    fcx.tcx().sess.span_err(
        call_span,
        format!("in call to `{}`, cannot reconcile method receiver of type `{}` \
                 with declared receiver type `{}`",
                method_name.user_string(fcx.tcx()),
                fcx.infcx().ty_to_str(self_ty),
                fcx.infcx().ty_to_str(method_self_ty)).as_slice());
}

fn decompose_vtable_origin(fcx: &FnCtxt,
                           call_span: Span,
                           vtable_origin: VtableOrigin,
                           method_name: ast::Name)
                           -> (Substs, Rc<ty::Method>, MethodOrigin)
{
    match vtable_origin {
        Vtable(vtable, None) => {
            decompose_vtable(fcx, vtable, method_name)
        }

        VtableParam(param, None) => {
            decompose_vtable_param(fcx, call_span, param, method_name)
        }

        Vtable(_, Some(_)) |
        VtableParam(_, Some(_)) => {
            // I believe it is impossible to have deferred type errors
            // in method resolution. These errors occur when matching
            // the output type parameters of a trait against the
            // values that were specified; in the case of a method
            // call, we always use fresh type variables for output
            // type parameters, and hence I do not believe any type
            // errors should ever occur here. - nmatsakis
            fcx.tcx().sess.span_bug(
                call_span,
                "Vtable resolution yielded deferred type errors");
        }

        Builtin => {
            fcx.tcx().sess.bug("Builtin traits have no named methods");
        }
    }
}

fn decompose_vtable(fcx: &FnCtxt,
                    vtable: Vtable,
                    method_name: ast::Name)
                    -> (Substs, Rc<ty::Method>, MethodOrigin)
{
    let impl_methods_table = fcx.tcx().impl_methods.borrow();
    let impl_method_ids = match impl_methods_table.find(&vtable.impl_def_id) {
        Some(m) => m,
        None => {
            fcx.tcx().sess.bug(
                format!("no methods for impl {}",
                        vtable.impl_def_id.repr(fcx.tcx())).as_slice());
        }
    };

    let opt_impl_method =
        impl_method_ids.iter()
                       .map(|&def_id| ty::method(fcx.tcx(), def_id))
                       .find(|m| m.ident.name == method_name);
    let impl_method = match opt_impl_method {
        Some(impl_method) => impl_method,

        None => {
            fcx.tcx().sess.bug(
                format!("impl {} has no method named `{}`",
                        vtable.impl_def_id.repr(fcx.tcx()),
                        method_name.repr(fcx.tcx())).as_slice());
        }
    };

    let method_origin = MethodStatic(impl_method.def_id);

    (vtable.substs, impl_method, method_origin)
}

fn decompose_vtable_param(fcx: &FnCtxt,
                          call_span: Span,
                          vtable_param: VtableParam,
                          method_name: ast::Name)
                          -> (Substs, Rc<ty::Method>, MethodOrigin)
{
    let trait_def_id = vtable_param.bound.def_id;
    let trait_methods = ty::trait_methods(fcx.tcx(), trait_def_id);
    let opt_method_index =
        trait_methods.iter()
                     .position(|m| m.ident.name == method_name);
    let method_index = match opt_method_index {
        Some(method_index) => method_index,
        None => {
            fcx.tcx().sess.span_bug(
                call_span,
                format!("trait {} has no method named `{}`",
                        trait_def_id.repr(fcx.tcx()),
                        method_name.repr(fcx.tcx())).as_slice());
        }
    };

    let method = (*trait_methods.get(method_index)).clone();
    let substs = vtable_param.bound.substs.clone();
    let method_origin =
        MethodParam(
            MethodParam { trait_id: trait_def_id,
                          method_num: method_index,
                          path: vtable_param.path });

    (substs, method, method_origin)
}

