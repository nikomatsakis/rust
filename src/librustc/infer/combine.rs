// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

///////////////////////////////////////////////////////////////////////////
// # Type combining
//
// There are four type combiners: equate, sub, lub, and glb.  Each
// implements the trait `Combine` and contains methods for combining
// two instances of various things and yielding a new instance.  These
// combiner methods always yield a `Result<T>`.  There is a lot of
// common code for these operations, implemented as default methods on
// the `Combine` trait.
//
// Each operation may have side-effects on the inference context,
// though these can be unrolled using snapshots. On success, the
// LUB/GLB operations return the appropriate bound. The Eq and Sub
// operations generally return the first operand.
//
// ## Contravariance
//
// When you are relating two things which have a contravariant
// relationship, you should use `contratys()` or `contraregions()`,
// rather than inversing the order of arguments!  This is necessary
// because the order of arguments is not relevant for LUB and GLB.  It
// is also useful to track which value is the "expected" value in
// terms of error reporting.

use super::equate::Equate;
use super::glb::Glb;
use super::{InferCtxt, MiscVariable, TypeTrace};
use super::lub::Lub;
use super::sub::Sub;
use super::type_variable::TypeVariableValue;

use ty::{IntType, UintType};
use ty::{self, Ty, TyCtxt};
use ty::error::TypeError;
use ty::context_fold::{ContextualFoldResult, ContextualTypeFolder, TypeContext};
use ty::relate::{RelateResult, TypeRelation};
use traits::{Obligation, PredicateObligations};

use syntax::ast;
use syntax_pos::Span;

#[derive(Clone)]
pub struct CombineFields<'infcx, 'gcx: 'infcx+'tcx, 'tcx: 'infcx> {
    pub infcx: &'infcx InferCtxt<'infcx, 'gcx, 'tcx>,
    pub trace: TypeTrace<'tcx>,
    pub cause: Option<ty::relate::Cause>,
    pub param_env: ty::ParamEnv<'tcx>,
    pub obligations: PredicateObligations<'tcx>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum RelationDir {
    SubtypeOf, SupertypeOf, EqTo
}

impl<'infcx, 'gcx, 'tcx> InferCtxt<'infcx, 'gcx, 'tcx> {
    pub fn super_combine_tys<R>(&self,
                                relation: &mut R,
                                a: Ty<'tcx>,
                                b: Ty<'tcx>)
                                -> RelateResult<'tcx, Ty<'tcx>>
        where R: TypeRelation<'infcx, 'gcx, 'tcx>
    {
        let a_is_expected = relation.a_is_expected();

        match (&a.sty, &b.sty) {
            // Relate integral variables to other types
            (&ty::TyInfer(ty::IntVar(a_id)), &ty::TyInfer(ty::IntVar(b_id))) => {
                self.int_unification_table
                    .borrow_mut()
                    .unify_var_var(a_id, b_id)
                    .map_err(|e| int_unification_error(a_is_expected, e))?;
                Ok(a)
            }
            (&ty::TyInfer(ty::IntVar(v_id)), &ty::TyInt(v)) => {
                self.unify_integral_variable(a_is_expected, v_id, IntType(v))
            }
            (&ty::TyInt(v), &ty::TyInfer(ty::IntVar(v_id))) => {
                self.unify_integral_variable(!a_is_expected, v_id, IntType(v))
            }
            (&ty::TyInfer(ty::IntVar(v_id)), &ty::TyUint(v)) => {
                self.unify_integral_variable(a_is_expected, v_id, UintType(v))
            }
            (&ty::TyUint(v), &ty::TyInfer(ty::IntVar(v_id))) => {
                self.unify_integral_variable(!a_is_expected, v_id, UintType(v))
            }

            // Relate floating-point variables to other types
            (&ty::TyInfer(ty::FloatVar(a_id)), &ty::TyInfer(ty::FloatVar(b_id))) => {
                self.float_unification_table
                    .borrow_mut()
                    .unify_var_var(a_id, b_id)
                    .map_err(|e| float_unification_error(relation.a_is_expected(), e))?;
                Ok(a)
            }
            (&ty::TyInfer(ty::FloatVar(v_id)), &ty::TyFloat(v)) => {
                self.unify_float_variable(a_is_expected, v_id, v)
            }
            (&ty::TyFloat(v), &ty::TyInfer(ty::FloatVar(v_id))) => {
                self.unify_float_variable(!a_is_expected, v_id, v)
            }

            // All other cases of inference are errors
            (&ty::TyInfer(_), _) |
            (_, &ty::TyInfer(_)) => {
                Err(TypeError::Sorts(ty::relate::expected_found(relation, &a, &b)))
            }


            _ => {
                ty::relate::super_relate_tys(relation, a, b)
            }
        }
    }

    fn unify_integral_variable(&self,
                               vid_is_expected: bool,
                               vid: ty::IntVid,
                               val: ty::IntVarValue)
                               -> RelateResult<'tcx, Ty<'tcx>>
    {
        self.int_unification_table
            .borrow_mut()
            .unify_var_value(vid, Some(val))
            .map_err(|e| int_unification_error(vid_is_expected, e))?;
        match val {
            IntType(v) => Ok(self.tcx.mk_mach_int(v)),
            UintType(v) => Ok(self.tcx.mk_mach_uint(v)),
        }
    }

    fn unify_float_variable(&self,
                            vid_is_expected: bool,
                            vid: ty::FloatVid,
                            val: ast::FloatTy)
                            -> RelateResult<'tcx, Ty<'tcx>>
    {
        self.float_unification_table
            .borrow_mut()
            .unify_var_value(vid, Some(ty::FloatVarValue(val)))
            .map_err(|e| float_unification_error(vid_is_expected, e))?;
        Ok(self.tcx.mk_mach_float(val))
    }
}

impl<'infcx, 'gcx, 'tcx> CombineFields<'infcx, 'gcx, 'tcx> {
    pub fn tcx(&self) -> TyCtxt<'infcx, 'gcx, 'tcx> {
        self.infcx.tcx
    }

    pub fn equate<'a>(&'a mut self, a_is_expected: bool) -> Equate<'a, 'infcx, 'gcx, 'tcx> {
        Equate::new(self, a_is_expected)
    }

    pub fn sub<'a>(&'a mut self, a_is_expected: bool) -> Sub<'a, 'infcx, 'gcx, 'tcx> {
        Sub::new(self, a_is_expected)
    }

    pub fn lub<'a>(&'a mut self, a_is_expected: bool) -> Lub<'a, 'infcx, 'gcx, 'tcx> {
        Lub::new(self, a_is_expected)
    }

    pub fn glb<'a>(&'a mut self, a_is_expected: bool) -> Glb<'a, 'infcx, 'gcx, 'tcx> {
        Glb::new(self, a_is_expected)
    }

    /// Here dir is either EqTo, SubtypeOf, or SupertypeOf. The
    /// idea is that we should ensure that the type `a_ty` is equal
    /// to, a subtype of, or a supertype of (respectively) the type
    /// to which `b_vid` is bound.
    ///
    /// Since `b_vid` has not yet been instantiated with a type, we
    /// will first instantiate `b_vid` with a *generalized* version
    /// of `a_ty`. Generalization introduces other inference
    /// variables wherever subtyping could occur.
    pub fn instantiate(&mut self,
                       a_ty: Ty<'tcx>,
                       dir: RelationDir,
                       b_vid: ty::TyVid,
                       a_is_expected: bool)
                       -> RelateResult<'tcx, ()>
    {
        use self::RelationDir::*;

        // Get the actual variable that b_vid has been inferred to
        debug_assert!(self.infcx.type_variables.borrow_mut().probe(b_vid).is_unknown());

        debug!("instantiate(a_ty={:?} dir={:?} b_vid={:?})", a_ty, dir, b_vid);

        // Generalize type of `a_ty` appropriately depending on the
        // direction.  As an example, assume:
        //
        // - `a_ty == &'x ?1`, where `'x` is some free region and `?1` is an
        //   inference variable,
        // - and `dir` == `SubtypeOf`.
        //
        // Then the generalized form `b_ty` would be `&'?2 ?3`, where
        // `'?2` and `?3` are fresh region/type inference
        // variables. (Down below, we will relate `a_ty <: b_ty`,
        // adding constraints like `'x: '?2` and `?1 <: ?3`.)
        let Generalization { ty: b_ty, needs_wf } = self.generalize(a_ty, b_vid, dir)?;
        debug!("instantiate(a_ty={:?}, dir={:?}, b_vid={:?}, generalized b_ty={:?})",
               a_ty, dir, b_vid, b_ty);
        self.infcx.type_variables.borrow_mut().instantiate(b_vid, b_ty);

        if needs_wf {
            self.obligations.push(Obligation::new(self.trace.cause.clone(),
                                                  self.param_env,
                                                  ty::Predicate::WellFormed(b_ty)));
        }

        // Finally, relate `b_ty` to `a_ty`, as described in previous comment.
        //
        // FIXME(#16847): This code is non-ideal because all these subtype
        // relations wind up attributed to the same spans. We need
        // to associate causes/spans with each of the relations in
        // the stack to get this right.
        match dir {
            EqTo => self.equate(a_is_expected).relate(&a_ty, &b_ty),
            SubtypeOf => self.sub(a_is_expected).relate(&a_ty, &b_ty),
            SupertypeOf => self.sub(a_is_expected).relate_with_variance(
                ty::Contravariant, &a_ty, &b_ty),
        }?;

        Ok(())
    }

    /// Attempts to generalize `ty` for the type variable `for_vid`.
    /// This checks for cycle -- that is, whether the type `ty`
    /// references `for_vid`. The `dir` is the "direction" for which we
    /// a performing the generalization (i.e., are we producing a type
    /// that can be used as a supertype etc).
    ///
    /// Preconditions:
    ///
    /// - `for_vid` is a "root vid"
    fn generalize(&self,
                  ty: Ty<'tcx>,
                  for_vid: ty::TyVid,
                  dir: RelationDir)
                  -> RelateResult<'tcx, Generalization<'tcx>>
    {
        // Determine the ambient variance within which `ty` appears.
        // The surrounding equation is:
        //
        //     ty [op] ty2
        //
        // where `op` is either `==`, `<:`, or `:>`. This maps quite
        // naturally.
        let ambient_variance = match dir {
            RelationDir::EqTo => ty::Invariant,
            RelationDir::SubtypeOf => ty::Covariant,
            RelationDir::SupertypeOf => ty::Contravariant,
        };

        let mut generalize = Generalizer {
            infcx: self.infcx,
            span: self.trace.cause.span,
            for_vid_sub_root: self.infcx.type_variables.borrow_mut().sub_root_var(for_vid),
            needs_wf: false,
            root_ty: ty,
        };

        let context = TypeContext { ambient_variance, num_binders: 0 };

        let ty = generalize.fold(context, &ty)?;
        let needs_wf = generalize.needs_wf;
        Ok(Generalization { ty, needs_wf })
    }
}

struct Generalizer<'cx, 'gcx: 'cx+'tcx, 'tcx: 'cx> {
    infcx: &'cx InferCtxt<'cx, 'gcx, 'tcx>,

    /// Span, used when creating new type variables and things.
    span: Span,

    /// The vid of the type variable that is in the process of being
    /// instantiated; if we find this within the type we are folding,
    /// that means we would have created a cyclic type.
    for_vid_sub_root: ty::TyVid,

    /// See the field `needs_wf` in `Generalization`.
    needs_wf: bool,

    /// The root type that we are generalizing. Used when reporting cycles.
    root_ty: Ty<'tcx>,
}

/// Result from a generalization operation. This includes
/// not only the generalized type, but also a bool flag
/// indicating whether further WF checks are needed.q
struct Generalization<'tcx> {
    ty: Ty<'tcx>,

    /// If true, then the generalized type may not be well-formed,
    /// even if the source type is well-formed, so we should add an
    /// additional check to enforce that it is. This arises in
    /// particular around 'bivariant' type parameters that are only
    /// constrained by a where-clause. As an example, imagine a type:
    ///
    ///     struct Foo<A, B> where A: Iterator<Item=B> {
    ///         data: A
    ///     }
    ///
    /// here, `A` will be covariant, but `B` is
    /// unconstrained. However, whatever it is, for `Foo` to be WF, it
    /// must be equal to `A::Item`. If we have an input `Foo<?A, ?B>`,
    /// then after generalization we will wind up with a type like
    /// `Foo<?C, ?D>`. When we enforce that `Foo<?A, ?B> <: Foo<?C,
    /// ?D>` (or `>:`), we will wind up with the requirement that `?A
    /// <: ?C`, but no particular relationship between `?B` and `?D`
    /// (after all, we do not know the variance of the normalized form
    /// of `A::Item` with respect to `A`). If we do nothing else, this
    /// may mean that `?D` goes unconstrained (as in #41677).  So, in
    /// this scenario where we create a new type variable in a
    /// bivariant context, we set the `needs_wf` flag to true. This
    /// will force the calling code to check that `WF(Foo<?C, ?D>)`
    /// holds, which in turn implies that `?C::Item == ?D`. So once
    /// `?C` is constrained, that should suffice to restrict `?D`.
    needs_wf: bool,
}

impl<'cx, 'gcx, 'tcx> ContextualTypeFolder<'cx, 'gcx, 'tcx> for Generalizer<'cx, 'gcx, 'tcx> {
    fn tcx(&self) -> TyCtxt<'cx, 'gcx, 'tcx> {
        self.infcx.tcx
    }

    fn fold_ty(&mut self, context: TypeContext, t: Ty<'tcx>) -> RelateResult<'tcx, Ty<'tcx>> {
        // Check to see whether the type we are genealizing references
        // any other type variable related to `vid` via
        // subtyping. This is basically our "occurs check", preventing
        // us from creating infinitely sized types.
        match t.sty {
            ty::TyInfer(ty::TyVar(vid)) => {
                let mut variables = self.infcx.type_variables.borrow_mut();
                let vid = variables.root_var(vid);
                let sub_vid = variables.sub_root_var(vid);
                if sub_vid == self.for_vid_sub_root {
                    // If sub-roots are equal, then `for_vid` and
                    // `vid` are related via subtyping.
                    return Err(TypeError::CyclicTy(self.root_ty));
                } else {
                    match variables.probe(vid) {
                        TypeVariableValue::Known { value: u } => {
                            drop(variables);
                            self.fold(context, &u)
                        }
                        TypeVariableValue::Unknown { .. } => {
                            match context.ambient_variance {
                                // Invariant: no need to make a fresh type variable.
                                ty::Invariant => return Ok(t),

                                // Bivariant: make a fresh var, but we
                                // may need a WF predicate. See
                                // comment on `needs_wf` field for
                                // more info.
                                ty::Bivariant => self.needs_wf = true,

                                // Co/contravariant: this will be
                                // sufficiently constrained later on.
                                ty::Covariant | ty::Contravariant => (),
                            }

                            let origin = *variables.var_origin(vid);
                            let new_var_id = variables.new_var(false, origin);
                            let u = self.tcx().mk_var(new_var_id);
                            debug!("generalize: replacing original vid={:?} with new={:?}",
                                   vid, u);
                            return Ok(u);
                        }
                    }
                }
            }
            ty::TyInfer(ty::IntVar(_)) |
            ty::TyInfer(ty::FloatVar(_)) => {
                // No matter what mode we are in,
                // integer/floating-point types must be equal to be
                // relatable.
                Ok(t)
            }
            _ => {
                self.super_fold_ty(context, t)
            }
        }
    }

    fn fold_region(
        &mut self,
        context: TypeContext,
        r: ty::Region<'tcx>,
    ) -> ContextualFoldResult<'tcx, ty::Region<'tcx>> {
        match r {
            // Never make variables for regions bound within the type itself,
            // nor for erased regions.
            ty::ReLateBound(..) |
            ty::ReErased => {
                return Ok(r);
            }

            // Always make a fresh region variable for skolemized regions;
            // the higher-ranked decision procedures rely on this.
            ty::ReSkolemized(..) => { }

            // For anything else, we make a region variable, unless we
            // are *equating*, in which case it's just wasteful.
            ty::ReEmpty |
            ty::ReStatic |
            ty::ReScope(..) |
            ty::ReVar(..) |
            ty::ReEarlyBound(..) |
            ty::ReFree(..) => {
                match context.ambient_variance {
                    ty::Invariant => return Ok(r),
                    ty::Bivariant | ty::Covariant | ty::Contravariant => (),
                }
            }

            ty::ReCanonical(..) |
            ty::ReClosureBound(..) => {
                span_bug!(
                    self.span,
                    "encountered unexpected ReClosureBound: {:?}",
                    r,
                );
            }
        }

        // FIXME: This is non-ideal because we don't give a
        // very descriptive origin for this region variable.
        Ok(self.infcx.next_region_var(MiscVariable(self.span)))
    }
}

pub trait RelateResultCompare<'tcx, T> {
    fn compare<F>(&self, t: T, f: F) -> RelateResult<'tcx, T> where
        F: FnOnce() -> TypeError<'tcx>;
}

impl<'tcx, T:Clone + PartialEq> RelateResultCompare<'tcx, T> for RelateResult<'tcx, T> {
    fn compare<F>(&self, t: T, f: F) -> RelateResult<'tcx, T> where
        F: FnOnce() -> TypeError<'tcx>,
    {
        self.clone().and_then(|s| {
            if s == t {
                self.clone()
            } else {
                Err(f())
            }
        })
    }
}

fn int_unification_error<'tcx>(a_is_expected: bool, v: (ty::IntVarValue, ty::IntVarValue))
                               -> TypeError<'tcx>
{
    let (a, b) = v;
    TypeError::IntMismatch(ty::relate::expected_found_bool(a_is_expected, &a, &b))
}

fn float_unification_error<'tcx>(a_is_expected: bool,
                                 v: (ty::FloatVarValue, ty::FloatVarValue))
                                 -> TypeError<'tcx>
{
    let (ty::FloatVarValue(a), ty::FloatVarValue(b)) = v;
    TypeError::FloatMismatch(ty::relate::expected_found_bool(a_is_expected, &a, &b))
}
