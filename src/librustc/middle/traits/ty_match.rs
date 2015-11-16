// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::infer;
use middle::subst::{Substs, VecPerParamSpace};
use middle::ty::{self, Ty};
use middle::ty::error::TypeError;
use middle::ty::relate::{self, Relate, TypeRelation, RelateResult};
use std::fmt::Debug;
use syntax::codemap::Span;
use util::nodemap::FnvHashMap;

pub fn perform_match<'a,'tcx,T>(infcx: &infer::InferCtxt<'a, 'tcx>,
                                generics: &ty::Generics<'tcx>,
                                span: Span,
                                template: &T,
                                value: &T)
                                -> RelateResult<'tcx, Substs<'tcx>>
    where T: Relate<'a, 'tcx> + Debug
{
    debug!("perform_match(template={:?}, value={:?}, generics={:?}, span={:?}",
           template, value, generics, span);

    let mut matcher = Match::new(infcx, generics, span);
    try!(matcher.relate(template, value));
    Ok(matcher.into_substs())
}

struct Match<'mtch, 'a:'mtch, 'tcx: 'a> {
    infcx: &'mtch infer::InferCtxt<'a, 'tcx>,
    generics: &'mtch ty::Generics<'tcx>,
    types: VecPerParamSpace<Option<Ty<'tcx>>>,
    regions: VecPerParamSpace<Option<ty::Region>>,
    span: Span,
}

impl<'mtch, 'a, 'tcx> Match<'mtch, 'a, 'tcx> {
    fn new(infcx: &'mtch infer::InferCtxt<'a, 'tcx>,
           generics: &'mtch ty::Generics<'tcx>,
           span: Span)
           -> Match<'mtch, 'a, 'tcx> {
        let types = generics.types.map(|_| None);
        let regions = generics.regions.map(|_| None);
        Match { infcx: infcx, generics: generics, types: types, regions: regions, span: span }
    }

    /// When we are matching a higher-ranked type, we replace the bound regions within
    /// with skolemized variants.
    fn search_for_skolemized_region(&self, skol_map: &infer::SkolemizationMap)
                                    -> RelateResult<'tcx, ()>
    {
        debug!("search_for_skolemized_region(skol_map={:?})", skol_map);

        let inverse_skol_map: FnvHashMap<_,_> =
            skol_map.iter()
                    .map(|(br, r)| (r, br))
                    .collect();

        let regions_from_regions = self.regions.iter()
                                               .flat_map(|opt_r| opt_r.iter())
                                               .cloned();
        let regions_from_types = self.types.iter()
                                           .flat_map(|opt_t| opt_t.iter())
                                           .flat_map(|t| t.walk()) // (*)
                                           .flat_map(|t| t.regions());
        let regions = regions_from_regions.chain(regions_from_types);

        // (*) skips over binders, but that's ok, because the regions we are searching for
        // would appear free in the subst

        for r in regions {
            debug!("search_for_skolemized_region: r={:?}", r);
            if let Some(&&br) = inverse_skol_map.get(&r) {
                return Err(TypeError::RegionsInsufficientlyPolymorphic(br, r));
            }
        }

        Ok(())
    }

    fn into_substs(self) -> Substs<'tcx> {
        debug!("into_substs(self.types={:?}, self.regions={:?})",
               self.types, self.regions);

        // There are sometimes types that are unconstrained due
        // in cases like:
        //
        //     impl<O,I> Foo for Bar<I> where I: Trait<Output=O> { ... }
        //
        // In those cases, just make a fresh type variable.
        let types =
            self.types
                .map_enumerated(|(space, index, opt_ty)| {
                    opt_ty.unwrap_or_else(|| {
                        let def = self.generics.types.get(space, index);

                        // TODO -- deal with defaults. Hmm.
                        assert!(def.default.is_none());

                        self.infcx.next_ty_var_with_default(None)
                    })
                });

        // For regions, we allow impls where there are region parameters
        // that are not used in the trait reference somewhere, which is
        // really kind of sad. Anyway, if we didn't find a value, then
        // just create a new region variable.
        let regions =
            self.regions
                .map_enumerated(|(space, index, opt_region)| {
                    opt_region.unwrap_or_else(|| {
                        let def = self.generics.regions.get(space, index);
                        self.infcx.next_region_var(infer::EarlyBoundRegion(self.span, def.name))
                    })
                });

        Substs::new(types, regions)
    }
}

impl<'mtch, 'a, 'tcx> TypeRelation<'a, 'tcx> for Match<'mtch, 'a, 'tcx> {
    fn tag(&self) -> &'static str { "Match" }
    fn tcx(&self) -> &'a ty::ctxt<'tcx> { self.infcx.tcx }
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
        debug!("regions(a={:?}, b={:?})", a, b);

        // if LHS is a type, assign substitution
        let a_prime = match a {
            ty::ReEarlyBound(data) => {
                let slot = self.regions.get_mut(data.space, data.index as usize);
                *slot = Some(b); // see (*) below
                return Ok(b);
            }

            ty::ReVar(_) => {
                self.infcx.tcx.sess.span_bug(
                    self.span,
                    &format!("encountered inference region {:?} in LHS of match", a));
            }

            _ => a,
        };
        debug!("regions: a_prime={:?}", a_prime);

        let origin = infer::SubregionOrigin::TraitMatch(self.span);
        self.infcx.equate_regions(origin, a_prime, b);
        Ok(b)
    }

    fn tys(&mut self, a: Ty<'tcx>, b: Ty<'tcx>) -> RelateResult<'tcx, Ty<'tcx>> {
        debug!("tys(a={:?}, b={:?})", a, b);

        // remove any type variables in RHS that we can
        let b = self.infcx.shallow_resolve(b);
        debug!("tys: b={:?}", b);

        // if LHS was a type variable, either use RHS as its value or, if it
        // already has a value, unify old value with RHS; else just unify
        let a_prime = match a.sty {
            ty::TyParam(param_ty) => {
                let slot = self.types.get_mut(param_ty.space, param_ty.idx as usize);
                *slot = Some(b); // see (*) below
                return Ok(b);
            }

            ty::TyProjection(_) => {
                // If LHS is a projection, then unifying the result
                // doesn't tell us anything about the inputs per se.
                // Moreover, any parameters in the inputs must appear
                // elsewhere in the impl or else the impl is
                // underconstrained, so we can just skip this
                // case. Note that we do have to come back once subst
                // is known to doublecheck that the result of the
                // projection; for notes on this, see (*) below.
                return Ok(b);
            }

            ty::TyInfer(_) => {
                self.infcx.tcx.sess.span_bug(
                    self.span,
                    &format!("encountered inference variable {:?} in LHS of match", a));
            }

            _ => a,
        };
        debug!("tys: a_prime={:?}", a_prime);

        match b.sty {
            ty::TyInfer(_) => {
                // If RHS is an inference variable, we can't learn
                // much from unifying it, and in fact we have to be
                // careful because `a` may contain early bound regions
                // and parameters, so we can't unify with `b` unless
                // we apply SOME sort of substitution. For more
                // details, see (*) below.
            }
            _ => {
                try!(relate::super_relate_tys(self, a_prime, b));
            }
        }

        Ok(b)
    }

    fn binders<T>(&mut self, a: &ty::Binder<T>, b: &ty::Binder<T>)
                  -> RelateResult<'tcx, ty::Binder<T>>
        where T: Relate<'a,'tcx>
    {
        debug!("binders(a={:?}, b={:?})", a, b);

        // TODO This is kind of hacky. But we want to check that the
        // `a` and `b` are *equally* polymorphic, and the primitives
        // we currently have implemented are targeted at subtyping. We
        // should integrate a new equality check, but for now we'll
        // just do the check in both directions, as equate.rs does.

        try!(self.infcx.commit_if_ok(|snapshot| {
            let (a_prime, _) =
                self.infcx.replace_late_bound_regions_with_fresh_var(
                    self.span, infer::HigherRankedType, a);

            let (b_prime, skol_map) =
                self.infcx.skolemize_late_bound_regions(b, snapshot);

            try!(self.relate(&a_prime, &b_prime));

            // check whether any of the skolemization regions appear
            // in the substitution we've been building up; if so,
            // that's a leak
            try!(self.search_for_skolemized_region(&skol_map));

            // also search the inference graph
            self.infcx.leak_check(&skol_map, snapshot)
        }));

        try!(self.infcx.commit_if_ok(|snapshot| {
            let (a_prime, skol_map) =
                self.infcx.skolemize_late_bound_regions(a, snapshot);

            let (b_prime, _) =
                self.infcx.replace_late_bound_regions_with_fresh_var(
                    self.span, infer::HigherRankedType, b);

            try!(self.relate(&a_prime, &b_prime));

            // no need to re-search the substitution we're building
            // up, because reversing role of A and B should not cause
            // any new entries to appear since the last time we
            // checked
            debug_assert!(self.search_for_skolemized_region(&skol_map).is_ok());

            self.infcx.leak_check(&skol_map, snapshot)
        }));

        Ok(b.clone())
    }
}

// (*) In general in this code, we are just trying to find the best
// values we can for regions and types. Even if this operation
// succeeds, there is no guarantee that the types we found are
// sufficient to permit unification; therefore this operation should
// be followed up by doing the substitution with the returned types
// and then doing the unification. Forcing this second step is
// inefficient but simplifies the logic here, since when we encounter
// multiple constraints relating to the same thing, we don't have to
// record them all, we can just keep track of one of them.
