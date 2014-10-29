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
use syntax::ast;
use syntax::codemap::Span;
use std::rc::Rc;

mod probe;

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

struct LookupContext<'a, 'tcx:'a> {
    fcx: &'a FnCtxt<'a, 'tcx>,
    span: Span,
    method_name: ast::Name,
    types_supplied: &'a [ty::t],
}

pub fn lookup() {
}
