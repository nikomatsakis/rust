// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/* Type-checking calls of various kinds */

use middle::ty;
use middle::typeck::MethodCall;
use middle::typeck::infer;
use std::gc::Gc;
use syntax::ast;
use syntax::codemap::Span;
use syntax::parse::token;
use util::common::ErrorReported;
use util::ppaux::Repr;

use super::{check_expr,
            check_expr_coercable_to_type,
            check_expr_with_hint};
use super::DerefArgs;
use super::DoDerefArgs;
use super::DontDerefArgs;
use super::DontTupleArguments;
use super::FnCtxt;
use super::method;
use super::regionmanip::replace_late_bound_regions_in_fn_sig;
use super::structurally_resolved_type;
use super::TupleArguments;
use super::TupleArgumentsFlag;

pub fn check_call_expr(fcx: &FnCtxt,
                       call_expr: &ast::Expr,
                       callee_expr: &ast::Expr,
                       arg_exprs: &[Gc<ast::Expr>])
{
    debug!("check_call_expr: call_expr={} span={}",
           call_expr.repr(fcx.tcx()),
           call_expr.span.repr(fcx.tcx()));

    // First check the callee and extract its type.
    check_expr(fcx, callee_expr);
    let callee_ty = fcx.expr_ty(callee_expr);

    // Check for built-in callable things.
    let callee_ty = structurally_resolved_type(fcx, callee_expr.span, callee_ty);
    match ty::get(callee_ty).sty {
        ty::ty_bare_fn(ty::BareFnTy {sig: ref sig, ..}) |
        ty::ty_closure(box ty::ClosureTy {sig: ref sig, ..}) => {
            return check_builtin_call(fcx, call_expr, callee_expr,
                                      arg_exprs, sig);
        }

        _ => { }
    }

    // Check for overloaded calls.
    if try_overloaded_call(fcx, call_expr, callee_expr, callee_ty, arg_exprs) {
        return;
    }

    // Error: callee is not callable.
    if !ty::type_is_error(callee_ty) {
        fcx.tcx().sess.span_err(
            call_expr.span,
            format!("type `{}` is not known to be callable",
                    fcx.infcx().ty_to_str(callee_ty)).as_slice());
    }

    check_error_arguments(fcx, arg_exprs);
}

/// Attempts to resolve a call expression as an overloaded call.
fn try_overloaded_call(fcx: &FnCtxt,
                       call_expression: &ast::Expr,
                       callee: &ast::Expr,
                       callee_ty: ty::t,
                       arg_exprs: &[Gc<ast::Expr>])
                       -> bool {
    // Try `FnOnce`, then `FnMut`, then `Fn`.
    for &(maybe_function_trait, method_name) in [
        (fcx.tcx().lang_items.fn_once_trait(), token::intern("call_once")),
        (fcx.tcx().lang_items.fn_mut_trait(), token::intern("call_mut")),
        (fcx.tcx().lang_items.fn_trait(), token::intern("call"))
    ].iter() {
        let function_trait = match maybe_function_trait {
            None => continue,
            Some(function_trait) => function_trait,
        };
        let method_callee = match method::lookup_in_traits(fcx,
                                                           call_expression.span,
                                                           callee,
                                                           callee_ty,
                                                           method_name,
                                                           [function_trait]) {
            Ok(None) => continue,
            Ok(Some(method_callee)) => method_callee,
            Err(ErrorReported) => {
                fcx.write_ty(call_expression.id, ty::mk_err());
                return true;
            }
        };
        let method_call = MethodCall::expr(call_expression.id);
        let output_type = check_method_argument_types(fcx,
                                                      call_expression.span,
                                                      method_callee.ty,
                                                      call_expression,
                                                      arg_exprs,
                                                      DontDerefArgs,
                                                      TupleArguments);
        fcx.inh.method_map.borrow_mut().insert(method_call, method_callee);
        fcx.write_ty(call_expression.id, output_type);

        if !fcx.tcx().sess.features.overloaded_calls.get() {
            fcx.tcx().sess.span_err(call_expression.span,
                                    "overloaded calls are experimental");
            fcx.tcx().sess.span_note(call_expression.span,
                                     "add `#[feature(overloaded_calls)]` to \
                                      the crate attributes to enable");
        }

        return true
    }

    false
}

// Checks a method call.
pub fn check_method_call(fcx: &FnCtxt,
                         expr: &ast::Expr,
                         method_name: ast::SpannedIdent,
                         args: &[Gc<ast::Expr>],
                         tps: &[ast::P<ast::Ty>]) {
    debug!("check_method_call: expr={} span={}",
           expr.repr(fcx.tcx()),
           expr.span.repr(fcx.tcx()));

    let rcvr = &*args[0];
    let other_args = args.slice_from(1);

    check_expr(fcx, &*rcvr);

    // no need to check for bot/err -- callee does that
    let expr_t = structurally_resolved_type(fcx,
                                            expr.span,
                                            fcx.expr_ty(rcvr));

    let tps = tps.iter().map(|ast_ty| fcx.to_ty(&**ast_ty)).collect::<Vec<_>>();
    let fn_ty = match method::lookup(fcx, expr, rcvr,
                                     method_name.node.name,
                                     expr_t, tps.as_slice()) {
        Ok(Some(method)) => {
            let method_ty = method.ty;
            let method_call = MethodCall::expr(expr.id);
            fcx.inh.method_map.borrow_mut().insert(method_call, method);
            method_ty
        }
        Err(ErrorReported) => {
            ty::mk_err()
        }
        Ok(None) => {
            debug!("(checking method call) failing expr is {}", expr.id);

            fcx.type_error_message(method_name.span,
                                   |actual| {
                                       format!("type `{}` does not implement any \
                                                method in scope named `{}`",
                              actual,
                              token::get_ident(method_name.node))
                  },
                  expr_t,
                  None);

                // Add error type for the result
            fcx.write_error(expr.id);

            ty::mk_err()
        }
    };

    // Call the generic checker.
    let ret_ty = check_method_argument_types(fcx,
                                             method_name.span,
                                             fn_ty,
                                             expr,
                                             other_args,
                                             DontDerefArgs,
                                             DontTupleArguments);

    fcx.write_ty(expr.id, ret_ty);
}

// A generic function for doing all of the checking for call expressions
fn check_builtin_call(fcx: &FnCtxt,
                      call_expr: &ast::Expr,
                      _callee_expr: &ast::Expr,
                      arg_exprs: &[Gc<ast::Expr>],
                      fn_sig: &ty::FnSig)
{
    // Replace any bound regions that appear in the function
    // signature with region variables
    let (_, fn_sig) =
        replace_late_bound_regions_in_fn_sig(
            fcx.tcx(),
            fn_sig,
            |br| fcx.infcx().next_region_var(
                     infer::LateBoundRegion(call_expr.span, br)));

    check_argument_types(fcx,
                         call_expr.span,
                         fn_sig.inputs.as_slice(),
                         arg_exprs,
                         DontDerefArgs,
                         fn_sig.variadic,
                         DontTupleArguments);

    let arg_is_err = arg_exprs.iter().any(
        |arg_expr| ty::type_is_error(fcx.expr_ty(&**arg_expr)));
    if arg_is_err {
        return fcx.write_error(call_expr.id);
    }

    let arg_is_bot = arg_exprs.iter().any(
        |arg_expr| ty::type_is_bot(fcx.expr_ty(&**arg_expr)));
    if arg_is_bot {
        fcx.write_bot(call_expr.id);
    }

    fcx.write_ty(call_expr.id, fn_sig.output);
}

pub fn lookup_op_method(fcx: &FnCtxt,
                        op_ex: &ast::Expr,
                        self_t: ty::t,
                        opname: ast::Name,
                        trait_did: Option<ast::DefId>,
                        args: &[Gc<ast::Expr>],
                        unbound_method: ||)
                        -> ty::t
{
    let rcvr = &*args[0];
    let other_args = args.slice_from(1);

    let method = match trait_did {
        Some(trait_did) => {
            method::lookup_in_traits(fcx, op_ex.span, rcvr, self_t, opname,
                                     [trait_did])
        }
        None => Ok(None)
    };
    match method {
        Ok(Some(method)) => {
            let method_ty = method.ty;
            // HACK(eddyb) Fully qualified path to work around a resolve bug.
            let method_call = ::middle::typeck::MethodCall::expr(op_ex.id);
            fcx.inh.method_map.borrow_mut().insert(method_call, method);
            return check_method_argument_types(fcx,
                                               op_ex.span,
                                               method_ty,
                                               op_ex,
                                               other_args,
                                               DoDerefArgs,
                                               DontTupleArguments);
        }
        Ok(None) => {
            unbound_method();
        }
        Err(ErrorReported) => { }
    }

    // An error occurred. Check the args anyway so we get all the
    // error messages.
    check_error_arguments(fcx, other_args);
    ty::mk_err()
}

fn check_method_argument_types(fcx: &FnCtxt,
                               sp: Span,
                               method_fn_ty: ty::t,
                               callee_expr: &ast::Expr,
                               arg_exprs: &[Gc<ast::Expr>],
                               deref_args: DerefArgs,
                               tuple_arguments: TupleArgumentsFlag)
                               -> ty::t
{
    if ty::type_is_error(method_fn_ty) {
        check_error_arguments(fcx, arg_exprs);
        return ty::mk_err();
    }

    match ty::get(method_fn_ty).sty {
        ty::ty_bare_fn(ref fty) => {
            // Skip over the type for the self argument (which has
            // been checked separately as part of method lookup
            // anyhow).
            let input_types = fty.sig.inputs.slice_from(1);

            check_argument_types(fcx,
                                 sp,
                                 input_types,
                                 arg_exprs,
                                 deref_args,
                                 fty.sig.variadic,
                                 tuple_arguments);
            fty.sig.output
        }

        _ => {
            fcx.tcx().sess.span_bug(callee_expr.span,
                                    "method without bare fn type");
        }
    }
}

fn check_argument_types(fcx: &FnCtxt,
                        sp: Span,
                        fn_inputs: &[ty::t],
                        arg_exprs: &[Gc<ast::Expr>],
                        deref_args: DerefArgs,
                        variadic: bool,
                        tuple_arguments: TupleArgumentsFlag)
{
    /*!
     * Generic function that factors out common logic from
     * function calls, method calls and overloaded operators.
     */

    let tcx = fcx.ccx.tcx;

    // Grab the argument types, supplying fresh type variables
    // if the wrong number of arguments were supplied
    let supplied_arg_count = if tuple_arguments == DontTupleArguments {
        arg_exprs.len()
    } else {
        1
    };

    let expected_arg_count = fn_inputs.len();
    let formal_tys = if tuple_arguments == TupleArguments {
        let tuple_type = structurally_resolved_type(fcx, sp, fn_inputs[0]);
        match ty::get(tuple_type).sty {
            ty::ty_tup(ref arg_types) => {
                if arg_types.len() != arg_exprs.len() {
                    let msg = format!(
                        "this function takes {} parameter{} \
                         but {} parameter{} supplied",
                         arg_types.len(),
                         if arg_types.len() == 1 {""} else {"s"},
                         arg_exprs.len(),
                         if arg_exprs.len() == 1 {" was"} else {"s were"});
                    tcx.sess.span_err(sp, msg.as_slice());
                    return check_error_arguments(fcx, arg_exprs);
                } else {
                    (*arg_types).clone()
                }
            }
            ty::ty_nil => {
                if arg_exprs.len() != 0 {
                    let msg = format!(
                        "this function takes 0 parameters \
                         but {} parameter{} supplied",
                         arg_exprs.len(),
                         if arg_exprs.len() == 1 {" was"} else {"s were"});
                    tcx.sess.span_err(sp, msg.as_slice());
                    return check_error_arguments(fcx, arg_exprs);
                }
                Vec::new()
            }
            _ => {
                tcx.sess
                   .span_err(sp,
                             "cannot use call notation; the first type \
                              parameter for the function trait is neither a \
                              tuple nor unit");
                return check_error_arguments(fcx, arg_exprs);
            }
        }
    } else if expected_arg_count == supplied_arg_count {
        fn_inputs.iter().map(|a| *a).collect()
    } else if variadic {
        if supplied_arg_count >= expected_arg_count {
            fn_inputs.iter().map(|a| *a).collect()
        } else {
            let msg = format!(
                "this function takes at least {} parameter{} \
                 but {} parameter{} supplied",
                 expected_arg_count,
                 if expected_arg_count == 1 {""} else {"s"},
                 supplied_arg_count,
                 if supplied_arg_count == 1 {" was"} else {"s were"});

            tcx.sess.span_err(sp, msg.as_slice());
            return check_error_arguments(fcx, arg_exprs);
        }
    } else {
        let msg = format!(
            "this function takes {} parameter{} \
             but {} parameter{} supplied",
             expected_arg_count,
             if expected_arg_count == 1 {""} else {"s"},
             supplied_arg_count,
             if supplied_arg_count == 1 {" was"} else {"s were"});

        tcx.sess.span_err(sp, msg.as_slice());
        return check_error_arguments(fcx, arg_exprs);
    };

    debug!("check_argument_types: formal_tys={} sp={}",
           fcx.infcx().tys_to_str(formal_tys.as_slice()),
           sp.repr(fcx.tcx()));

    // Check the arguments.
    // We do this in a pretty awful way: first we typecheck any arguments
    // that are not anonymous functions, then we typecheck the anonymous
    // functions. This is so that we have more information about the types
    // of arguments when we typecheck the functions. This isn't really the
    // right way to do this.
    let xs = [false, true];
    for check_blocks in xs.iter() {
        let check_blocks = *check_blocks;
        debug!("check_blocks={}", check_blocks);

        // For variadic functions, we don't have a declared type for all of
        // the arguments hence we only do our usual type checking with
        // the arguments who's types we do know.
        let t = if variadic {
            expected_arg_count
        } else if tuple_arguments == TupleArguments {
            arg_exprs.len()
        } else {
            supplied_arg_count
        };
        for (i, arg) in arg_exprs.iter().take(t).enumerate() {
            let is_block = match arg.node {
                ast::ExprFnBlock(..) |
                ast::ExprProc(..) => true,
                _ => false
            };

            if is_block == check_blocks {
                debug!("checking the argument");
                let mut formal_ty = *formal_tys.get(i);

                match deref_args {
                    DoDerefArgs => {
                        match ty::get(formal_ty).sty {
                            ty::ty_rptr(_, mt) => formal_ty = mt.ty,
                            ty::ty_err => (),
                            _ => {
                                // So we hit this case when one implements the
                                // operator traits but leaves an argument as
                                // just T instead of &T. We'll catch it in the
                                // mismatch impl/trait method phase no need to
                                // ICE here.
                                // See: #11450
                                formal_ty = ty::mk_err();
                            }
                        }
                    }
                    DontDerefArgs => {}
                }

                check_expr_coercable_to_type(fcx, &**arg, formal_ty);

            }
        }
    }

    // We also need to make sure we at least write the ty of the other
    // arguments which we skipped above.
    if variadic {
        for arg in arg_exprs.iter().skip(expected_arg_count) {
            check_expr(fcx, &**arg);

            // There are a few types which get autopromoted when
            // passed via varargs in C but we just error out instead
            // and require explicit casts.
            let arg_ty = structurally_resolved_type(fcx, arg.span,
                                                    fcx.expr_ty(&**arg));
            match ty::get(arg_ty).sty {
                ty::ty_float(ast::TyF32) => {
                    fcx.type_error_message(arg.span,
                                           |t| {
                        format!("can't pass an {} to variadic \
                                 function, cast to c_double", t)
                    }, arg_ty, None);
                }
                ty::ty_int(ast::TyI8) | ty::ty_int(ast::TyI16) | ty::ty_bool => {
                    fcx.type_error_message(arg.span, |t| {
                        format!("can't pass {} to variadic \
                                 function, cast to c_int",
                                       t)
                    }, arg_ty, None);
                }
                ty::ty_uint(ast::TyU8) | ty::ty_uint(ast::TyU16) => {
                    fcx.type_error_message(arg.span, |t| {
                        format!("can't pass {} to variadic \
                                 function, cast to c_uint",
                                       t)
                    }, arg_ty, None);
                }
                _ => {}
            }
        }
    }
}

fn check_error_arguments(fcx: &FnCtxt,
                         arg_exprs: &[Gc<ast::Expr>])
{
    for arg_expr in arg_exprs.iter() {
        check_expr_with_hint(fcx, &**arg_expr, ty::mk_err());
    }
}
