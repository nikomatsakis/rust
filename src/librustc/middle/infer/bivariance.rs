// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::ty::{BuiltinBounds};
use middle::ty::{mod, Ty};
use middle::ty::TyVar;
use middle::infer::combine::*;
use middle::infer::{cres};
use middle::infer::type_variable::{BiTo};
use util::ppaux::{Repr};

use syntax::ast::{Onceness, FnStyle};

pub struct Bivariance<'f, 'tcx: 'f> {
    fields: CombineFields<'f, 'tcx>
}

#[allow(non_snake_case)]
pub fn Bivariance<'f, 'tcx>(cf: CombineFields<'f, 'tcx>) -> Bivariance<'f, 'tcx> {
    Bivariance { fields: cf }
}

impl<'f, 'tcx> Combine<'tcx> for Bivariance<'f, 'tcx> {
    fn tag(&self) -> String { "Bivariance".to_string() }
    fn fields<'a>(&'a self) -> &'a CombineFields<'a, 'tcx> { &self.fields }

    fn contratys(&self, a: Ty<'tcx>, b: Ty<'tcx>) -> cres<'tcx, Ty<'tcx>> {
        self.tys(a, b)
    }

    fn contraregions(&self, a: ty::Region, b: ty::Region) -> cres<'tcx, ty::Region> {
        self.regions(a, b)
    }

    fn regions(&self, a: ty::Region, _: ty::Region) -> cres<'tcx, ty::Region> {
        // Subtyping in our system is tied to regions. Bivariance
        // basically just ignores region relationships for this
        // reason.
        Ok(a)
    }

    fn mts(&self, a: &ty::mt<'tcx>, b: &ty::mt<'tcx>) -> cres<'tcx, ty::mt<'tcx>> {
        debug!("mts({} <: {})",
               a.repr(self.fields.infcx.tcx),
               b.repr(self.fields.infcx.tcx));

        if a.mutbl != b.mutbl { return Err(ty::terr_mutability); }
        let t = try!(self.tys(a.ty, b.ty));
        Ok(ty::mt { mutbl: a.mutbl, ty: t })
    }

    fn fn_styles(&self, a: FnStyle, _: FnStyle) -> cres<'tcx, FnStyle> {
        // unsafe fn <: fn normally, so ignore mismatches for bivariance
        Ok(a)
    }

    fn oncenesses(&self, a: Onceness, _: Onceness) -> cres<'tcx, Onceness> {
        // once fn <: many fn, ignore mismatches
        Ok(a)
    }

    fn builtin_bounds(&self,
                      a: BuiltinBounds,
                      _: BuiltinBounds)
                      -> cres<'tcx, BuiltinBounds>
    {
        // More bounds is a subtype of fewer bounds. Ignore for bivariance.
        Ok(a)
    }

    fn tys(&self, a: Ty<'tcx>, b: Ty<'tcx>) -> cres<'tcx, Ty<'tcx>> {
        debug!("{}.tys({}, {})", self.tag(),
               a.repr(self.fields.infcx.tcx), b.repr(self.fields.infcx.tcx));
        if a == b { return Ok(a); }

        let infcx = self.fields.infcx;
        let a = infcx.type_variables.borrow().replace_if_possible(a);
        let b = infcx.type_variables.borrow().replace_if_possible(b);
        match (&a.sty, &b.sty) {
            (&ty::ty_infer(TyVar(a_id)), &ty::ty_infer(TyVar(b_id))) => {
                infcx.type_variables.borrow_mut().relate_vars(a_id, BiTo, b_id);
                Ok(a)
            }

            (&ty::ty_infer(TyVar(a_id)), _) => {
                try!(self.fields.instantiate(b, BiTo, a_id));
                Ok(a)
            }

            (_, &ty::ty_infer(TyVar(b_id))) => {
                try!(self.fields.instantiate(a, BiTo, b_id));
                Ok(a)
            }

            _ => {
                super_tys(self, a, b)
            }
        }
    }

    fn fn_sigs(&self, a: &ty::FnSig<'tcx>, b: &ty::FnSig<'tcx>)
               -> cres<'tcx, ty::FnSig<'tcx>> {
        try!(self.sub().fn_sigs(a, b));
        self.sub().fn_sigs(b, a)
    }

    fn trait_refs(&self, a: &ty::TraitRef<'tcx>, b: &ty::TraitRef<'tcx>)
                  -> cres<'tcx, ty::TraitRef<'tcx>> {
        try!(self.sub().trait_refs(a, b));
        self.sub().trait_refs(b, a)
    }
}
