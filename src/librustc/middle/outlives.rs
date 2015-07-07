// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// The outlines relation `T: 'a` or `'a: 'b`.

use middle::subst::Substs;
use middle::infer::InferCtxt;
use middle::ty::{self, RegionEscape, Ty};
use syntax::ast;

#[derive(Debug)]
pub enum Component<'tcx> {
    Region(ty::Region),
    Param(ty::ParamTy),
    Closure(ast::DefId, &'tcx Substs<'tcx>),
    UnresolvedInferenceVariable(ty::InferTy),

    // Projections like `T::Foo` are tricky because a constraint like
    // `T::Foo: 'a` can be satisfied in so many ways. There may be a
    // where-clause that says `T::Foo: 'a`, or the defining trait may
    // include a bound like `type Foo: 'static`, or -- in the most
    // conservative way -- we can prove that `T: 'a` (more generally,
    // that all components in the projection outlive `'a`). This code
    // is not in a position to judge which is the best technique, so
    // we just product the projection as a component and leave it to
    // the consumer to decide (but see `EscapingProjection` below).
    Projection(ty::ProjectionTy<'tcx>),

    // In the case where a projection has escaping regions -- meaning
    // regions bound within the type itself -- we always use
    // the most conservative rule, which requires that all components
    // outlive the bound. So for example if we had a type like this:
    //
    //     for<'a> Trait1<  <T as Trait2<'a,'b>>::Foo  >
    //                      ~~~~~~~~~~~~~~~~~~~~~~~~~
    //
    // then the inner projection (underlined) has an escaping region
    // `'a`. We consider that outer trait `'c` to meet a bound if `'b`
    // outlives `'b: 'c`, and we don't consider whether the trait
    // declares that `Foo: 'static` etc. Therefore, we just return the
    // free components of such a projection (in this case, `'b`).
    //
    // However, in the future, we may want to get smarter, and
    // actually return a "higher-ranked projection" here. Therefore,
    // we mark that these components are part of an escaping
    // projection, so that implied bounds code can avoid relying on
    // them. This gives us room to improve the regionck reasoning in
    // the future without breaking backwards compat.
    EscapingProjection(Vec<Component<'tcx>>),
}

/// Returns all the things that must outlive `'a` for the condition
/// `ty0: 'a` to hold.
pub fn components<'a,'tcx>(infcx: &InferCtxt<'a,'tcx>,
                        ty0: Ty<'tcx>)
                        -> Vec<Component<'tcx>> {
    let mut components = vec![];
    compute_components(infcx, ty0, &mut components);
    debug!("outlives({:?}) = {:?}", ty0, components);
    components
}

fn compute_components<'a,'tcx>(infcx: &InferCtxt<'a,'tcx>,
                               ty0: Ty<'tcx>,
                               out: &mut Vec<Component<'tcx>>) {
    // Descend through the types, looking for the various "base"
    // components and collecting them into `out`. This is not written
    // with `collect()` because of the need to sometimes skip subtrees
    // in the `subtys` iterator (e.g., when encountering a
    // projection).
    let mut subtys = ty0.walk();
    while let Some(ty) = subtys.next() {
        match ty.sty {
            ty::TyClosure(def_id, substs) => {
                out.push(Component::Closure(def_id, substs));
                subtys.skip_current_subtree();
            }
            ty::TyParam(p) => {
                out.push(Component::Param(p));
                subtys.skip_current_subtree();
            }
            ty::TyProjection(ref data) => {
                // For projections, we prefer to generate an
                // obligation like `<P0 as Trait<P1...Pn>>::Foo: 'a`,
                // because this gives the regionck more ways to prove
                // that it holds. However, regionck is not (at least
                // currently) prepared to deal with higher-ranked
                // regions that may appear in the
                // trait-ref. Therefore, if we see any higher-ranke
                // regions, we simply fallback to the most restrictive
                // rule, which requires that `Pi: 'a` for all `i`.

                if !data.has_escaping_regions() {
                    // best case: no escaping reions, so push the
                    // projection and skip the subtree (thus
                    // generating no constraints for Pi).
                    out.push(Component::Projection(*data));
                } else {
                    // fallback case: continue walking through and
                    // constrain Pi.
                    let mut temp = vec![];
                    push_region_constraints(&mut temp, ty.regions());
                    for subty in ty.walk_shallow() {
                        compute_components(infcx, subty, &mut temp);
                    }
                    out.push(Component::EscapingProjection(temp));
                }
                subtys.skip_current_subtree();
            }
            ty::TyInfer(_) => {
                let ty = infcx.resolve_type_vars_if_possible(&ty);
                if let ty::TyInfer(infer_ty) = ty.sty {
                    out.push(Component::UnresolvedInferenceVariable(infer_ty));
                } else {
                    compute_components(infcx, ty, out);
                }
            }
            _ => {
                // for all other types, just constrain the regions and
                // keep walking to find any other types.
                push_region_constraints(out, ty.regions());
            }
        }
    }
}

fn push_region_constraints<'tcx>(out: &mut Vec<Component<'tcx>>, regions: Vec<ty::Region>) {
    for r in regions {
        if !r.is_bound() {
            out.push(Component::Region(r));
        }
    }
}

