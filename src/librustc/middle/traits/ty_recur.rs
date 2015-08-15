// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::ty::{self, Ty};
use middle::ty::error::TypeError;
use middle::ty::relate::{self, Relate, TypeRelation, RelateResult};

/// A type "B" is a "recurrence" of "A" if the fresh types in B could
/// be substituted with values so as to make it equal to A. Recurrence
/// checking is intended to be used only on freshened types, and it
/// basically indicates if the non-freshened versions of A and B could
/// have been unified. We use it as part of trait match evaluation to
/// detect and sidestep infinite recursion.
///
/// It is only an approximation. If it yields false, unification would
/// definitely fail, but a true result doesn't mean unification would
/// succeed. This is because we don't track the "side-constraints" on
/// type variables, nor do we track if the same freshened type appears
/// more than once. To some extent these approximations could be
/// fixed, given effort.
///
/// Like subtyping, recurrence is really a binary relation, so the
/// only important thing about the result is Ok/Err. Also, recurrence
/// never affects any type variables or unification state.
pub fn is_recurrence<'a,'tcx,T>(tcx: &'a ty::ctxt<'tcx>, a: &T, b: &T) -> bool
    where T: Relate<'a, 'tcx>
{
    let mut recur = Recurrence::new(tcx);
    T::relate(&mut recur, a, b).is_ok()
}

struct Recurrence<'a, 'tcx: 'a> {
    tcx: &'a ty::ctxt<'tcx>
}

impl<'a, 'tcx> Recurrence<'a, 'tcx> {
    pub fn new(tcx: &'a ty::ctxt<'tcx>) -> Recurrence<'a, 'tcx> {
        Recurrence { tcx: tcx }
    }
}

impl<'a, 'tcx> TypeRelation<'a, 'tcx> for Recurrence<'a, 'tcx> {
    fn tag(&self) -> &'static str { "Recurrence" }
    fn tcx(&self) -> &'a ty::ctxt<'tcx> { self.tcx }
    fn a_is_expected(&self) -> bool { true } // irrelevant

    fn relate_with_variance<T:Relate<'a,'tcx>>(&mut self,
                                               _: ty::Variance,
                                               a: &T,
                                               b: &T)
                                               -> RelateResult<'tcx, T>
    {
        self.relate(a, b)
    }

    fn regions(&mut self, a: ty::Region, b: ty::Region) -> RelateResult<'tcx, ty::Region> {
        debug!("{}.regions({:?}, {:?})",
               self.tag(),
               a,
               b);
        Ok(a)
    }

    fn tys(&mut self, a: Ty<'tcx>, b: Ty<'tcx>) -> RelateResult<'tcx, Ty<'tcx>> {
        debug!("{}.tys({:?}, {:?})", self.tag(),
               a, b);
        if a == b { return Ok(a); }

        match (&a.sty, &b.sty) {
            (_, &ty::TyInfer(ty::FreshTy(_))) |
            (_, &ty::TyInfer(ty::FreshIntTy(_))) |
            (_, &ty::TyInfer(ty::FreshFloatTy(_))) => {
                Ok(a)
            }

            (&ty::TyInfer(_), _) |
            (_, &ty::TyInfer(_)) => {
                Err(TypeError::Sorts(relate::expected_found(self, &a, &b)))
            }

            (&ty::TyError, _) | (_, &ty::TyError) => {
                Ok(self.tcx().types.err)
            }

            _ => {
                relate::super_relate_tys(self, a, b)
            }
        }
    }

    fn binders<T>(&mut self, a: &ty::Binder<T>, b: &ty::Binder<T>)
                  -> RelateResult<'tcx, ty::Binder<T>>
        where T: Relate<'a,'tcx>
    {
        Ok(ty::Binder(try!(self.relate(a.skip_binder(), b.skip_binder()))))
    }
}
