// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Code for projecting associated types out of trait references.

use super::elaborate_predicates;
use super::Obligation;
use super::SelectionContext;
use super::PredicateObligation;
use super::ProjectionMismatch;
use super::SelectionContext;
use super::SelectionError;
use super::SelectionResult;
use super::Unimplemented;
use super::VtableImplData;

use middle::infer;
use middle::subst::Subst;
use middle::ty::{mod, PolyProjectionPredicateExt, Ty};
use std::rc::Rc;
use util::ppaux::Repr;

pub type ProjectionObligation<'tcx> =
    Obligation<'tcx, ty::ProjectionPredicate<'tcx>>;

enum ProjectionCandidate<'tcx> {
    ParamEnv(ty::PolyProjectionPredicate<'tcx>),
    Impl(VtableImplData<'tcx, PredicateObligation<'tcx>>),
}

struct ProjectionCandidateSet<'tcx> {
    vec: Vec<ProjectionCandidate<'tcx>>,
    ambiguous: bool
}

pub fn project<'cx,'tcx>(
    selcx: &mut SelectionContext<'cx,'tcx>,
    obligation: &ProjectionObligation<'tcx>)
    -> SelectionResult<'tcx, ()>
{
    debug!("project(obligation={})",
           obligation.repr(selcx.tcx()));

    let mut candidates = ProjectionCandidateSet {
        vec: Vec::new(),
        ambiguous: false,
    };

    let () = assemble_candidates_from_param_env(selcx,
                                                obligation,
                                                &mut candidates);

    let () = try!(assemble_candidates_from_impls(selcx,
                                                 obligation,
                                                 &mut candidates));

    debug!("{} candidates, ambiguous={}",
           candidates.vec.len(),
           candidates.ambiguous);

    // We probably need some winnowing logic similar to select here.

    if candidates.ambiguous || candidates.vec.len() > 1 {
        return Ok(None);
    }

    match candidates.vec.pop() {
        None => Err(Unimplemented),
        Some(candidate) => Ok(Some(try!(confirm_candidate(selcx, obligation, candidate)))),
    }
}

/// The first thing we have to do is scan through the parameter
/// environment to see whether there are any projection predicates
/// there that can answer this question.
fn assemble_candidates_from_param_env<'cx,'tcx>(
    selcx: &mut SelectionContext<'cx,'tcx>,
    obligation:  &ProjectionObligation<'tcx>,
    candidate_set: &mut ProjectionCandidateSet)
{
    let infcx = selcx.infcx();
    let env_predicates = selcx.param_env().caller_bounds.predicates.clone();
    let env_predicates = env_predicates.iter().cloned().collect();
    for predicate in elaborate_predicates(selcx.tcx(), env_predicates) {
        match predicate {
            ty::Predicate::Projection(ref data) => {
                let is_match = infcx.probe(|_| {
                    let origin = infer::Misc(obligation.cause.span);
                    let obligation_poly_trait_ref =
                        obligation.trait_ref.trait_ref.to_poly_trait_ref();
                    let data_poly_trait_ref =
                        data.poly_trait_ref();
                    infcx.sub_poly_trait_refs(false,
                                              origin,
                                              obligation_poly_trait_ref,
                                              data_poly_trait_ref).is_ok()
                });

                if is_match {
                    candidate_set.vec.push(
                        ProjectionCandidate::ParamEnv(data.clone()));
                }
            }
            _ => { }
        }
    }
}

fn assemble_candidates_from_impls<'cx,'tcx>(
    selcx: &mut SelectionContext<'cx,'tcx>,
    obligation:  &ProjectionObligation<'tcx>,
    candidate_set: &mut ProjectionCandidateSet<'tcx>)
    -> Result<(),SelectionError<'tcx>>
{
    // If we are resolving `<T as TraitRef<...>>::Item == Type`,
    // start out by selecting the predicate `T as TraitRef<...>`:
    let trait_ref =
        obligation.trait_ref.trait_ref.to_poly_trait_ref();
    let trait_obligation =
        obligation.with(trait_ref);
    let vtable = match try!(selcx.select(&trait_obligation)) {
        Some(vtable) => vtable,
        None => {
            candidate_set.ambiguous = true;
            return Ok(());
        }
    };

    match vtable {
        super::VtableImpl(data) => {
            candidate_set.vec.push(
                ProjectionCandidate::Impl(data));
        }
        super::VtableParam(..) => {
            // This case tell us nothing about the value of an
            // associated type. Consider:
            //
            // ```
            // trait SomeTrait { type Foo; }
            // fn foo<T:SomeTrait>(...) { }
            // ```
            //
            // If the user writes `<T as SomeTrait>::Foo`, then the `T
            // : SomeTrait` binding does not help us decide what the
            // type `Foo` is (at least, not more specifically than
            // what we already knew).
            //
            // But wait, you say! What about an example like this:
            //
            // ```
            // fn bar<T:SomeTrait<Foo=uint>>(...) { ... }
            // ```
            //
            // Doesn't the `T : Sometrait<Foo=uint>` predicate help
            // resolve `T::Foo`? And of course it does, but in fact
            // that single predicate is desugared into two predicates
            // in the compiler: a trait predicate (`T : SomeTrait`) and a
            // projection. And the projection where clause is handled
            // in `assemble_candidates_from_param_env`.
        }
        super::VtableBuiltin(..) |
        super::VtableUnboxedClosure(..) |
        super::VtableFnPointer(..) => {
            // These traits have no associated types.
            selcx.tcx().sess.span_bug(
                obligation.cause.span,
                format!("Cannot project an associated type from `{}`",
                        vtable.repr(selcx.tcx())).as_slice());
        }
    }

    Ok(())
}

fn confirm_candidate<'cx,'tcx:'cx>(
    selcx: &mut SelectionContext<'cx,'tcx>,
    obligation:  &ProjectionObligation<'tcx>,
    candidate: ProjectionCandidate<'tcx>)
    -> Result<(), SelectionError<'tcx>>
{
    let infcx = selcx.infcx();

    let projected_ty = match candidate {
        ProjectionCandidate::ParamEnv(poly_projection) => {
            assert_eq!(poly_projection.0.item_name,
                       obligation.trait_ref.item_name);
            let projection =
                infcx.replace_late_bound_regions_with_fresh_var(
                    obligation.cause.span,
                    infer::LateBoundRegionConversionTime::HigherRankedType,
                    &poly_projection).0;

            let origin = infer::RelateOutputImplTypes(obligation.cause.span);
            match infcx.sub_trait_refs(false,
                                       origin,
                                       obligation.trait_ref.trait_ref.clone(),
                                       projection.trait_ref.clone()) {
                Ok(()) => { }
                Err(e) => {
                    selcx.tcx().sess.span_bug(
                        obligation.cause.span,
                        format!("Failed to unify `{}` and `{}` in projection: {}",
                                obligation.repr(selcx.tcx()),
                                projection.repr(selcx.tcx()),
                                ty::type_err_to_str(selcx.tcx(), &e)).as_slice());
                }
            }

            projection.ty
        }

        ProjectionCandidate::Impl(impl_vtable) => {
            // there don't seem to be nicer accessors to these:
            let impl_items_map = selcx.tcx().impl_items.borrow();
            let impl_or_trait_items_map = selcx.tcx().impl_or_trait_items.borrow();

            let impl_items = impl_items_map[impl_vtable.impl_def_id];
            let mut impl_ty = None;
            for impl_item in impl_items.iter() {
                let assoc_type = match impl_or_trait_items_map[impl_item.def_id()] {
                    ty::TypeTraitItem(ref assoc_type) => assoc_type.clone(),
                    ty::MethodTraitItem(..) => { continue; }
                };

                if assoc_type.name != obligation.trait_ref.item_name {
                    continue;
                }

                let impl_poly_ty = ty::lookup_item_type(selcx.tcx(), assoc_type.def_id);
                impl_ty = Some(impl_poly_ty.ty.subst(selcx.tcx(), &impl_vtable.substs));
                break;
            }

            match impl_ty {
                Some(ty) => ty,
                None => {
                    selcx.tcx().sess.span_bug(
                        obligation.cause.span,
                        format!("impl `{}` did not contain projection for `{}`",
                                impl_vtable.repr(selcx.tcx()),
                                obligation.repr(selcx.tcx())).as_slice());
                }
            }
        }
    };

    let origin = infer::RelateOutputImplTypes(obligation.cause.span);
    match infer::mk_eqty(infcx, true, origin, projected_ty, obligation.trait_ref.ty) {
        Ok(()) => Ok(()),
        Err(e) => Err(ProjectionMismatch(projected_ty, obligation.trait_ref.clone(), e)),
    }
}
