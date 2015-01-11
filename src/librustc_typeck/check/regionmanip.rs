// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// #![warn(deprecated_mode)]

use middle::infer::GenericKind;
use middle::subst::{ParamSpace, Subst, Substs};
use middle::traits;
use middle::ty::{self, Ty};
use middle::ty_fold::{TypeFolder};

use syntax::ast;
use syntax::codemap::Span;

use util::ppaux::Repr;

// Helper functions related to manipulating region types.

struct Wf<'a, 'tcx: 'a> {
    tcx: &'a ty::ctxt<'tcx>,
    span: Span,
    body_id: ast::NodeId,
    stack: Vec<(ty::Region, traits::ObligationCauseCode)>,
    out: Vec<traits::PredicateObligation<'tcx>>,
}

/// This routine computes the well-formedness constraints that must hold for the type `ty` to
/// appear in a context with lifetime `outer_region`
pub fn wf_obligations<'tcx>(
    tcx: &ty::ctxt<'tcx>,
    span: Span,
    body_id: ast::NodeId,
    ty: Ty<'tcx>,
    outer_region: ty::Region)
    -> Vec<traits::PredicateObligation<'tcx>>
{
    let mut stack = Vec::new();
    stack.push((outer_region, None, traits::MiscObligation));
    let mut wf = Wf { tcx: tcx, span: span, body_id: body_id, stack: stack, out: Vec::new() };
    wf.accumulate_from_ty(ty);
    wf.out
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    fn accumulate_from_ty(&mut self, ty: Ty<'tcx>) {
        debug!("Wf::accumulate_from_ty(ty={})",
               ty.repr(self.tcx));

        match ty.sty {
            ty::ty_bool |
            ty::ty_char |
            ty::ty_int(..) |
            ty::ty_uint(..) |
            ty::ty_float(..) |
            ty::ty_bare_fn(..) |
            ty::ty_err |
            ty::ty_str => {
                // No borrowed content reachable here.
            }

            ty::ty_unboxed_closure(_, region, _) => {
                // An "unboxed closure type" is basically
                // modeled here as equivalent to a struct like
                //
                //     struct TheClosure<'b> {
                //         ...
                //     }
                //
                // where the `'b` is the lifetime bound of the
                // contents (i.e., all contents must outlive 'b).
                //
                // Even though unboxed closures are glorified structs
                // of upvars, we do not need to consider them as they
                // can't generate any new constraints.  The
                // substitutions on the closure are equal to the free
                // substitutions of the enclosing parameter
                // environment.  An upvar captured by value has the
                // same type as the original local variable which is
                // already checked for consistency.  If the upvar is
                // captured by reference it must also outlive the
                // region bound on the closure, but this is explicitly
                // handled by logic in regionck.
                self.push_region_outlives_top(*region);
            }

            ty::ty_trait(ref t) => {
                let required_region_bounds =
                    ty::object_region_bounds(self.tcx, Some(&t.principal), t.bounds.builtin_bounds);
                self.accumulate_from_object_ty(ty, t.bounds.region_bound, required_region_bounds)
            }

            ty::ty_enum(def_id, substs) |
            ty::ty_struct(def_id, substs) => {
                let item_scheme = ty::lookup_item_type(self.tcx, def_id);
                self.accumulate_from_adt(ty, def_id, &item_scheme.generics, substs)
            }

            ty::ty_vec(t, _) |
            ty::ty_ptr(ty::mt { ty: t, .. }) |
            ty::ty_uniq(t) => {
                self.accumulate_from_ty(t)
            }

            ty::ty_rptr(r_b, mt) => {
                self.accumulate_from_rptr(ty, *r_b, mt.ty);
            }

            ty::ty_param(..) => {
                self.push_ty_outlives_top(ty);
            }

            ty::ty_projection(ref data) => {
                // `<T as TraitRef<..>>::Name`

                self.push_ty_outlives_top(ty);

                // this seems like a minimal requirement:
                let trait_def = ty::lookup_trait_def(self.tcx, data.trait_ref.def_id);
                self.accumulate_from_adt(ty, data.trait_ref.def_id,
                                         &trait_def.generics, data.trait_ref.substs)
            }

            ty::ty_tup(ref tuptys) => {
                for &tupty in tuptys.iter() {
                    self.accumulate_from_ty(tupty);
                }
            }

            ty::ty_infer(_) => {
                // This should not happen, BUT:
                //
                //   Currently we uncover region relationships on
                //   entering the fn check. We should do this after
                //   the fn check, then we can call this case a bug().
            }

            ty::ty_open(_) => {
                self.tcx.sess.bug(
                    &format!("Unexpected type encountered while doing wf check: {}",
                            ty.repr(self.tcx))[]);
            }
        }
    }

    fn accumulate_from_rptr(&mut self,
                            ty: Ty<'tcx>,
                            r_b: ty::Region,
                            ty_b: Ty<'tcx>) {
        // We are walking down a type like this, and current
        // position is indicated by caret:
        //
        //     &'a &'b ty_b
        //         ^
        //
        // At this point, top of stack will be `'a`. We must require
        // that `'a <= 'b` (`'b : 'a`).

        self.push_region_outlives_top(r_b);

        // Now we push `'b` onto the stack, because it must
        // constrain any borrowed content we find within `T`.

        self.stack.push((r_b, traits::MiscObligation)); // TODO cause
        self.accumulate_from_ty(ty_b);
        self.stack.pop().unwrap();
    }

    /// Pushes a constraint that `r_b` must outlive the top region on the stack.
    fn push_region_outlives_top(&mut self,
                                r_b: ty::Region) {
        // Indicates that we have found borrowed content with a lifetime
        // of at least `r_b`. This adds a constraint that `r_b` must
        // outlive the region `r_a` on top of the stack.
        //
        // As an example, imagine walking a type like:
        //
        //     &'a &'b T
        //         ^
        //
        // when we hit the inner pointer (indicated by caret), `'a`
        // will be on top of stack and `'b` will be the lifetime of
        // the content we just found. So we add the obligation that
        // `'b : 'a`.

        let &(r_a, ref code) = self.stack.last().unwrap();
        self.out.push(
            traits::Obligation::new(
                traits::ObligationCause::new(self.span, self.body_id, code),
                ty::OutlivesPredicate(r_b, r_a).as_predicate()));
    }

    /// Pushes a constraint that `param_ty` must outlive the top region on the stack.
    fn push_ty_outlives_top(&mut self, ty: Ty<'tcx>) {
        let &(r_a, ref code) = self.stack.last().unwrap();
        self.out.push(
            traits::Obligation::new(
                traits::ObligationCause::new(self.span, self.body_id, code),
                ty::OutlivesPredicate(ty, r_a).as_predicate()));
    }

    fn accumulate_from_adt(&mut self,
                           _ty: Ty<'tcx>,
                           def_id: ast::DefId,
                           substs: &Substs<'tcx>)
    {
        let bounds =
            ty::lookup_item_type(self.tcx, def_id)
            .generics
            .to_bounds(self.tcx, substs);
        self.out.extend(bounds.predicates.iter().cloned());

        // Variance of each type/region parameter.
        let variances = ty::item_variances(self.tcx, def_id);

        for (space, index, &region) in substs.regions().iter_enumerated() {
            let &variance = variances.regions.get(space, index);

            match variance {
                ty::Covariant | ty::Bivariant => {
                    // Ignore covariant or bivariant region
                    // parameters.  To understand why, consider a
                    // struct `Foo<'a>`. If `Foo` contains any
                    // references with lifetime `'a`, then `'a` must
                    // be at least contravariant (and possibly
                    // invariant). The only way to have a covariant
                    // result is if `Foo` contains only a field with a
                    // type like `fn() -> &'a T`; i.e., a bare
                    // function that can produce a reference of
                    // lifetime `'a`. In this case, there is no
                    // *actual data* with lifetime `'a` that is
                    // reachable. (Presumably this bare function is
                    // really returning static data.)
                }

                ty::Contravariant | ty::Invariant => {
                    // If the parameter is contravariant or
                    // invariant, there may indeed be reachable
                    // data with this lifetime. See other case for
                    // more details.
                    self.push_region_outlives_top(region);
                }
            }
        }

        for (space, index, &ty) in substs.types.iter_enumerated() {
            let &variance = variances.types.get(space, index);

            match variance {
                ty::Contravariant | ty::Bivariant => {
                    // As above, except that in this it is a
                    // *contravariant* reference that indices that no
                    // actual data of type T is reachable.
                }

                ty::Covariant | ty::Invariant => {
                    self.accumulate_from_ty(ty);
                }
            }
        }
    }

    fn accumulate_from_object_ty(&mut self,
                                 ty: Ty<'tcx>,
                                 region_bound: ty::Region,
                                 required_region_bounds: Vec<ty::Region>)
    {
        // Imagine a type like this:
        //
        //     trait Foo { }
        //     trait Bar<'c> : 'c { }
        //
        //     &'b (Foo+'c+Bar<'d>)
        //         ^
        //
        // In this case, the following relationships must hold:
        //
        //     'c : 'b
        //     'c : 'd
        //
        // The first conditions is due to the normal region pointer
        // rules, which say that a reference cannot outlive its
        // referent.
        //
        // The final condition may be a bit surprising. In particular,
        // you may expect that it would have been `'d : 'c`, since
        // usually lifetimes of outer things are conservative
        // approximations for inner things. However, it works somewhat
        // differently with trait objects: here the idea is that if the
        // user specifies a region bound (`'c`, in this case) it is the
        // "master bound" that *implies* that bounds from other traits are
        // all met. (Remember that *all bounds* in a type like
        // `Foo+Bar+Zed` must be met, not just one, hence if we write
        // `Foo<'x>+Bar<'y>`, we know that the type outlives *both* 'x and
        // 'y.)
        //
        // Note: in fact we only permit builtin traits, not `Bar<'d>`, I
        // am looking forward to the future here.

        // The content of this object type must outlive
        // `bounds.region_bound`:
        let r_c = region_bound;
        self.push_region_constraint_from_top(r_c);

        // And then, in turn, to be well-formed, the
        // `region_bound` that user specified must imply the
        // region bounds required from all of the trait types:
        for &r_d in required_region_bounds.iter() {
            // Each of these is an instance of the `'c : 'd`
            // constraint above
            let code = traits::MiscObligation; // TODO use a better code
            self.out.push(
                traits::Obligation::new(
                    traits::ObligationCause::new(self.span, self.body_id, code),
                    ty::OutlivesPredicate(r_c, r_d).as_predicate()));
        }
    }
}
