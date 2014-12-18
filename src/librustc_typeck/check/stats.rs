// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::FnCtxt;

use middle::ty::{mod, Ty};
use syntax::ast;
use util::nodemap::FnvHashSet;

pub fn gather<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>,
                       _decl: &ast::FnDecl,
                       _body: &ast::Block,
                       id: ast::NodeId,
                       _fn_ty: &ty::BareFnTy<'tcx>) {
    let fulfillment_cx =
        fcx.inh.fulfillment_cx.borrow();

    let types_that_must_be_sized: FnvHashSet<ast::DefId> =
        fulfillment_cx.types_that_must_be_sized()
        .iter()
        .map(|&ty| fcx.infcx().resolve_type_vars_if_possible(ty))
        .flat_map(|ty| parameter_def_id(ty).into_iter())
        .collect();

    let types_declared_as_sized: FnvHashSet<ast::DefId> =
        fcx.inh.param_env.caller_bounds.predicates
        .iter()
        .flat_map(|predicate| {
            match *predicate {
                ty::Predicate::Trait(ref data) => Some(data.self_ty()).into_iter(),
                _ => None.into_iter(),
            }
        })
        .map(|self_ty| fcx.infcx().resolve_type_vars_if_possible(self_ty))
        .flat_map(|ty| parameter_def_id(ty).into_iter())
        .collect();

    let extra_declarations =
        types_declared_as_sized.difference(&types_that_must_be_sized).count();

    debug!("id={} types_that_must_be_sized={} types_declared_as_sized={} extra_declarations={}",
           id,
           types_that_must_be_sized.len(),
           types_declared_as_sized.len(),
           extra_declarations);
}

fn parameter_def_id<'tcx>(ty: Ty<'tcx>) -> Option<ast::DefId> {
    match ty.sty {
        ty::ty_param(ref param_ty) => Some(param_ty.def_id),
        _ => None,
    }
}
