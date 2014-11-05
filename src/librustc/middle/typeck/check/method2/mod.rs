// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Method lookup: the secret sauce of Rust. See `doc.rs`. */

use middle::ty;
use middle::typeck::check::{FnCtxt};
use middle::typeck::MethodCallee;
use syntax::ast;
use syntax::codemap::Span;
use std::rc::Rc;
use util::ppaux::Repr;

mod probe;
mod confirm;

pub type MethodResult = Result<MethodCallee, MethodError>;

pub enum MethodError {
    // Did not find an applicable method, but we did find various
    // static methods that may apply.
    NoMatch(Vec<CandidateSource>),

    // Multiple methods might apply.
    Ambiguity(Vec<CandidateSource>),
}

// A pared down enum describing just the places from which a method
// candidate can arise. Used for error reporting only.
#[deriving(PartialOrd, Ord, PartialEq, Eq)]
pub enum CandidateSource {
    ImplSource(ast::DefId),
    TraitSource(/* trait id */ ast::DefId),
}

type MethodIndex = uint; // just for doc purposes

enum Candidate {
    InherentImpl(ast::DefId),
    ExtensionImpl(ast::DefId, MethodIndex),
    UnboxedClosureImpl(ast::DefId),
    WhereClause(Rc<ty::TraitRef>, MethodIndex),
}

struct CacheKey {
    skol_self_ty: ty::t,
    method_name: ast::Name,
}

pub fn lookup(
    fcx: &FnCtxt,
    span: Span,
    method_name: ast::Name,
    self_ty: ty::t,
    supplied_method_types: Vec<ty::t>,
    call_expr_id: ast::NodeId,
    self_expr: &ast::Expr)
    -> Result<MethodCallee, MethodError>
{
    /*!
     * Performs method lookup. If lookup is successful, it will return the callee
     * and store an appropriate adjustment for the self-expr. In some cases it may
     * report an error (e.g., invoking the `drop` method).
     *
     * # Arguments
     *
     * Given a method call like `foo.bar::<T1,...Tn>(...)`:
     *
     * - `fcx`:                   the surrounding `FnCtxt` (!)
     * - `span`:                  the span for the method call
     * - `method_name`:           the name of the method being called (`bar`)
     * - `self_ty`:               the (unadjusted) type of the self expression (`foo`)
     * - `supplied_method_types`: the explicit method type parameters, if any (`T1..Tn`)
     * - `self_expr`:             the self expression (`foo`)
     */

    debug!("lookup(method_name={}, self_ty={}, call_expr_id={}, self_expr={})",
           method_name.repr(fcx.tcx()),
           self_ty.repr(fcx.tcx()),
           call_expr_id,
           self_expr.repr(fcx.tcx()));

    let mut probe_cx = probe::ProbeContext::new(fcx,
                                                span,
                                                method_name,
                                                self_ty);
    probe_cx.assemble_inherent_probes(None);
    probe_cx.assemble_extension_probes_for_traits_in_scope(call_expr_id);
    let pick = try!(probe_cx.pick());
    let mut confirm_cx = confirm::ConfirmContext::new(fcx,
                                                      span,
                                                      self_expr);
    Ok(confirm_cx.confirm(self_ty, pick, supplied_method_types))
}
