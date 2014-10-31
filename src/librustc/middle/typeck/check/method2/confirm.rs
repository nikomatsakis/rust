// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::Ambiguity;
use super::CandidateSource;
use super::ImplSource;
use super::MethodError;
use super::MethodIndex;
use super::NoMatch;
use super::TraitSource;
use super::probe::Pick;
use super::probe::PickAdjustment;
use super::probe::{AutoDeref, AutoRef, AutoUnsizeLength};

use middle::subst;
use middle::subst::Subst;
use middle::traits;
use middle::ty;
use middle::ty_fold::TypeFoldable;
use middle::typeck::check;
use middle::typeck::check::{FnCtxt, NoPreference};
use middle::typeck::check::regionmanip::replace_late_bound_regions;
use middle::typeck::{MethodObject};
use middle::typeck::infer;
use middle::typeck::infer::InferCtxt;
use syntax::ast;
use syntax::codemap::Span;
use std::collections::HashSet;
use std::rc::Rc;
use std::mem;
use util::ppaux::Repr;

struct ConfirmContext<'a, 'tcx:'a> {
    fcx: &'a FnCtxt<'a, 'tcx>,
    span: Span,
    call_expr_id: ast::NodeId,
    self_expr_id: ast::NodeId,
}

impl<'a,'tcx> ConfirmContext<'a,'tcx> {
    fn confirm(&mut self,
               self_ty: ty::t,
               pick: Pick,
               adjustment: PickAdjustment) {
        // Create the final adjustment and then apply it to the self
        // expr type and the self expr itself.
        let adjustment = ty::AdjustDerefRef(self.apply_adjustment(&adjustment));
        let adjusted_ty =
            ty::adjust_ty(
                self.tcx(), self.span, self.self_expr_id, self_ty, Some(&adjustment),
                |method_call| self.fcx.inh.method_map.borrow()
                                                     .find(&method_call)
                                                     .map(|method| method.ty));
        self.fcx.write_adjustment(self.self_expr_id, self.span, adjustment);

        // 
    }

    fn apply_adjustment(&mut self,
                        adjustment: &PickAdjustment)
                        -> ty::AutoDerefRef
    {
        match *adjustment {
            AutoDeref(num) => {
                ty::AutoDerefRef {
                    autoderefs: num,
                    autoref: None
                }
            }
            AutoRef(mutability, ref sub_adjustment) => {
                let deref = self.apply_adjustment(&**sub_adjustment);
                let region = self.infcx().next_region_var(infer::Autoref(self.span));
                wrap_autoref(deref, |base| ty::AutoPtr(region, mutability, base))
            }
            AutoUnsizeLength(n, ref sub_adjustment) => {
                let deref = self.apply_adjustment(&**sub_adjustment);
                wrap_autoref(deref, |base| ty::AutoUnsize(ty::UnsizeLength(n)))
            }
        }
    }

    fn tcx(&self) -> &'a ty::ctxt<'tcx> {
        self.fcx.tcx()
    }

    fn infcx(&self) -> &'a InferCtxt<'a, 'tcx> {
        self.fcx.infcx()
    }
}

fn wrap_autoref(mut deref: ty::AutoDerefRef,
                base_fn: |Option<Box<ty::AutoRef>>| -> ty::AutoRef)
                -> ty::AutoDerefRef {
    let autoref = mem::replace(&mut deref.autoref, None);
    let autoref = autoref.map(|r| box r);
    deref.autoref = Some(base_fn(autoref));
    deref
}
