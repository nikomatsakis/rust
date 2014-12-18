// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::super::CrateCtxt;
use super::FnCtxt;

use middle::subst::{ParamSpace, Substs};
use middle::traits::elaborate_predicates;
use middle::ty::{mod, Predicate, Ty};
use std::collections::hash_map::Entry;
use std::os;
use syntax::ast;
use syntax::ast_util::local_def;
use syntax::codemap::{DUMMY_SP, Span};
use util::nodemap::FnvHashSet;
use util::ppaux::Repr;

pub struct ParameterStats {
    requires_sized: bool,
    declared_sized: bool,
    inferred_sized: bool,
    not_inferred_sized: bool,
    not_inferred_sized_span: Span,
    not_inferred_nor_by_value: bool,
    not_inferred_nor_by_value_span: Span,
}

fn stat<F>(ccx: &CrateCtxt,
           def_id: ast::DefId,
           f: F)
    where F : FnOnce(&mut ParameterStats)
{
    let mut stats_map = ccx.parameter_stats_map.borrow_mut();
    match stats_map.entry(def_id) {
        Entry::Occupied(mut entry) => {
            f(entry.get_mut())
        }
        Entry::Vacant(entry) => {
            let stats = ParameterStats {
                requires_sized: false,
                declared_sized: false,
                inferred_sized: false,
                not_inferred_sized: false,
                not_inferred_sized_span: DUMMY_SP,
                not_inferred_nor_by_value: false,
                not_inferred_nor_by_value_span: DUMMY_SP,
            };
            f(entry.set(stats))
        }
    }
}

pub fn global(ccx: &CrateCtxt) {
    for &space in ParamSpace::all().iter() {
        summarize(ccx, Some(space));
    }

    summarize(ccx, None);
}

fn summarize(ccx: &CrateCtxt, just_space: Option<ParamSpace>) {
    let stats_map = ccx.parameter_stats_map.borrow();
    let defs_map = ccx.tcx.ty_param_defs.borrow();

    let mut requires_sized: uint = 0;
    let mut declared_sized: uint = 0;
    let mut inferred_sized: uint = 0;
    let mut not_inferred_sized: uint = 0;
    let mut not_inferred_nor_by_value: uint = 0;
    let mut total: uint = 0;

    for (&def_id, stats) in stats_map.iter() {
        if let Some(space) = just_space {
            assert_eq!(def_id.krate, ast::LOCAL_CRATE);
            let def = &defs_map[def_id.node];
            if def.space != space { continue; }
        }

        total += 1;
        if stats.declared_sized { declared_sized += 1; }
        if stats.requires_sized { requires_sized += 1; }
        if stats.inferred_sized { inferred_sized += 1; }
        if stats.not_inferred_sized {
            not_inferred_sized += 1;

            if os::getenv("NOTE_NOT_INFERRED_SIZE").is_some() {
                let def = &defs_map[def_id.node];
                ccx.tcx.sess.span_note(
                    stats.not_inferred_sized_span,
                    format!("type parameter `{}` would not be inferred to be `Sized`",
                            def.name).as_slice());
            }
        }
        if stats.not_inferred_nor_by_value {
            not_inferred_nor_by_value += 1;

            if os::getenv("NOTE_NOT_INFERRED_NOR_BY_VALUE").is_some() {
                let def = &defs_map[def_id.node];
                ccx.tcx.sess.span_note(
                    stats.not_inferred_sized_span,
                    format!("type parameter `{}` would not be inferred to be `Sized` \
                             nor is it taken by value",
                            def.name).as_slice());
            }
        }
    }

    let total = total as f64;

    debug!("{} requires_sized = {} ({}%)",
           just_space,
           requires_sized,
           (requires_sized as f64) / total * 100.0);

    debug!("{} declared_sized = {} ({}%)",
           just_space,
           declared_sized,
           (declared_sized as f64) / total * 100.0);

    debug!("{} inferred_sized = {} ({}%)",
           just_space,
           inferred_sized,
           (inferred_sized as f64) / total * 100.0);

    debug!("{} not_inferred_sized = {} ({}%)",
           just_space,
           not_inferred_sized,
           (not_inferred_sized as f64) / total * 100.0);

    debug!("{} not_inferred_nor_by_value = {} ({}%)",
           just_space,
           not_inferred_nor_by_value,
           (not_inferred_nor_by_value as f64) / total * 100.0);
}

pub fn gather<'a,'tcx>(fcx: &FnCtxt<'a,'tcx>,
                       _decl: &ast::FnDecl,
                       body: &ast::Block,
                       id: ast::NodeId,
                       fn_ty: &ty::BareFnTy<'tcx>) {
    let fulfillment_cx =
        fcx.inh.fulfillment_cx.borrow();

    let types_that_must_be_sized: FnvHashSet<ast::DefId> =
        fulfillment_cx.types_that_must_be_sized()
        .iter()
        .map(|&ty| fcx.infcx().resolve_type_vars_if_possible(ty))
        .flat_map(|ty| parameter_def_id(ty).into_iter())
        .collect();
    for &def_id in types_that_must_be_sized.iter() {
        stat(fcx.ccx, def_id, |s| s.requires_sized = true)
    }

    let polytype = ty::lookup_item_type(fcx.tcx(), local_def(id));
    for tp_def in polytype.generics.types.iter() {
        stat(fcx.ccx, tp_def.def_id, |s| {
            if tp_def.bounds.builtin_bounds.contains(&ty::BoundSized) {
                s.declared_sized = true;
            }
        })
    }

    // type parameters that would be inferred *in this context* to be Sized
    let mut inferred_sized = FnvHashSet::new();
    for predicate in
        elaborate_predicates(fcx.tcx(), wf_constraints(fcx.tcx(), fn_ty, ty::ReStatic))
    {
        match predicate {
            Predicate::Trait(trait_ref) => {
                match fcx.tcx().lang_items.to_builtin_kind(trait_ref.def_id) {
                    Some(ty::BoundSized) => {
                        let ty = fcx.infcx().resolve_type_vars_if_possible(trait_ref.self_ty());
                        if let Some(def_id) = parameter_def_id(ty) {
                            inferred_sized.insert(def_id);
                            stat(fcx.ccx, def_id, |s| s.inferred_sized = true);
                        }
                    }
                    _ => { }
                }
            }
            _ => { }
        }
    }
    match fn_ty.sig.output { // also consider that returned values must be Sized
        ty::FnConverging(ty) => {
            if let Some(def_id) = parameter_def_id(ty) {
                inferred_sized.insert(def_id);
            }
        }
        ty::FnDiverging => { }
    }

    // type parameters that must be sized *in this context* but are not inferred to be
    for &def_id in types_that_must_be_sized.difference(&inferred_sized) {
        stat(fcx.ccx, def_id, |s| {
            s.not_inferred_sized = true;
            s.not_inferred_sized_span = body.span;
        });
    }

    // now also include those that are passed (or returned) by value, just for fun
    for &ty in fn_ty.sig.inputs.iter() {
        if let Some(def_id) = parameter_def_id(ty) {
            inferred_sized.insert(def_id);
        }
    }
    for &def_id in types_that_must_be_sized.difference(&inferred_sized) {
        stat(fcx.ccx, def_id, |s| {
            s.not_inferred_nor_by_value = true;
            s.not_inferred_nor_by_value_span = body.span;
        });
    }
}

fn parameter_def_id<'tcx>(ty: Ty<'tcx>) -> Option<ast::DefId> {
    match ty.sty {
        ty::ty_param(ref param_ty) => Some(param_ty.def_id),
        _ => None,
    }
}

struct Wf<'a, 'tcx: 'a> {
    tcx: &'a ty::ctxt<'tcx>,
    stack: Vec<(ty::Region, Option<Ty<'tcx>>)>,
    out: Vec<Predicate<'tcx>>,
}

pub fn wf_constraints<'tcx>(
    tcx: &ty::ctxt<'tcx>,
    bare_fn_ty: &ty::BareFnTy<'tcx>,
    outer_region: ty::Region)
    -> Vec<Predicate<'tcx>>
{
    let mut stack = Vec::new();
    stack.push((outer_region, None));
    let mut wf = Wf { tcx: tcx,
                      stack: stack,
                      out: Vec::new() };
    for &ty in bare_fn_ty.sig.inputs.iter() {
        wf.accumulate_from_ty(ty);
    }
    match bare_fn_ty.sig.output {
        ty::FnConverging(ty) => {
            wf.accumulate_from_ty(ty);
        }
        ty::FnDiverging => { }
    }
    wf.out
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    fn accumulate_from_ty(&mut self, ty: Ty<'tcx>) {
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

            ty::ty_closure(box ref c) => {
                self.accumulate_from_closure_ty(ty, c);
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
                self.push_region_constraint_from_top(region);
            }

            ty::ty_trait(ref t) => {
                let required_region_bounds =
                    ty::object_region_bounds(self.tcx, Some(&t.principal), t.bounds.builtin_bounds);
                self.accumulate_from_object_ty(ty, t.bounds.region_bound, required_region_bounds)
            }

            ty::ty_enum(def_id, ref substs) |
            ty::ty_struct(def_id, ref substs) => {
                self.accumulate_from_adt(ty, def_id, substs)
            }

            ty::ty_vec(t, _) |
            ty::ty_ptr(ty::mt { ty: t, .. }) |
            ty::ty_uniq(t) => {
                self.accumulate_from_ty(t)
            }

            ty::ty_rptr(r_b, mt) => {
                self.accumulate_from_rptr(ty, r_b, mt.ty);
            }

            ty::ty_param(p) => {
                self.push_param_constraint_from_top(ty, p);
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
                    format!("Unexpected type encountered while doing wf check: {}",
                            ty.repr(self.tcx)).as_slice());
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
        // At this point, top of stack will be `'a`. We must
        // require that `'a <= 'b`.

        self.push_region_constraint_from_top(r_b);

        // Now we push `'b` onto the stack, because it must
        // constrain any borrowed content we find within `T`.

        self.stack.push((r_b, Some(ty)));
        self.accumulate_from_ty(ty_b);
        self.stack.pop().unwrap();
    }

    /// Pushes a constraint that `r_b` must outlive the top region on the stack.
    fn push_region_constraint_from_top(&mut self,
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
        // when we hit the inner pointer (indicated by caret), `'a` will
        // be on top of stack and `'b` will be the lifetime of the content
        // we just found. So we add constraint that `'a <= 'b`.

        let &(r_a, opt_ty) = self.stack.last().unwrap();
        self.push_sub_region_constraint(opt_ty, r_a, r_b);
    }

    /// Pushes a constraint that `r_a <= r_b`, due to `opt_ty`
    fn push_sub_region_constraint(&mut self,
                                  _opt_ty: Option<Ty<'tcx>>,
                                  r_a: ty::Region,
                                  r_b: ty::Region) {
        self.out.push(Predicate::RegionOutlives(r_a, r_b));
    }

    /// Pushes a constraint that `param_ty` must outlive the top region on the stack.
    fn push_param_constraint_from_top(&mut self,
                                      ty: Ty<'tcx>,
                                      param_ty: ty::ParamTy) {
        let &(region, opt_ty) = self.stack.last().unwrap();
        self.push_param_constraint(region, opt_ty, ty, param_ty);
    }

    /// Pushes a constraint that `region <= param_ty`, due to `opt_ty`
    fn push_param_constraint(&mut self,
                             region: ty::Region,
                             _opt_ty: Option<Ty<'tcx>>,
                             ty: Ty<'tcx>,
                             _param_ty: ty::ParamTy) {
        self.out.push(Predicate::TypeOutlives(ty, region));
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
                    self.push_region_constraint_from_top(region);
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

    fn accumulate_from_closure_ty(&mut self,
                                  ty: Ty<'tcx>,
                                  c: &ty::ClosureTy<'tcx>)
    {
        match c.store {
            ty::RegionTraitStore(r_b, _) => {
                self.push_region_constraint_from_top(r_b);
            }
            ty::UniqTraitStore => { }
        }

        let required_region_bounds =
            ty::object_region_bounds(self.tcx, None, c.bounds.builtin_bounds);
        self.accumulate_from_object_ty(ty, c.bounds.region_bound, required_region_bounds);
    }

    fn accumulate_from_object_ty(&mut self,
                                 _ty: Ty<'tcx>,
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
        //     'b <= 'c
        //     'd <= 'c
        //
        // The first conditions is due to the normal region pointer
        // rules, which say that a reference cannot outlive its
        // referent.
        //
        // The final condition may be a bit surprising. In particular,
        // you may expect that it would have been `'c <= 'd`, since
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
            // Each of these is an instance of the `'c <= 'b`
            // constraint above
            self.out.push(Predicate::RegionOutlives(r_d, r_c));
        }
    }
}
