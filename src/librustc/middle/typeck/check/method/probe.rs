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

use middle::subst;
use middle::subst::Subst;
use middle::traits;
use middle::ty;
use middle::typeck::check;
use middle::typeck::check::{FnCtxt, NoPreference};
use middle::typeck::{MethodObject};
use middle::typeck::infer;
use middle::typeck::infer::InferCtxt;
use syntax::ast;
use syntax::codemap::{Span, DUMMY_SP};
use std::collections::HashSet;
use std::rc::Rc;
use util::ppaux::Repr;

pub struct ProbeContext<'a,'tcx:'a> {
    fcx: &'a FnCtxt<'a, 'tcx>,
    span: Span,
    method_name: ast::Name,
    steps: Rc<Vec<ProbeStep>>,
    inherent_probes: Vec<Probe>,
    extension_probes: Vec<Probe>,
    impl_dups: HashSet<ast::DefId>,
    static_candidates: Vec<CandidateSource>,
}

struct ProbeStep {
    self_ty: ty::t,
    adjustment: PickAdjustment
}

struct Probe {
    xform_self_ty: ty::t,
    method_ty: Rc<ty::Method>,
    kind: ProbeKind,
}

enum ProbeKind {
    InherentImplProbe(/* Impl */ ast::DefId, subst::Substs),
    ObjectProbe(MethodObject),
    ExtensionImplProbe(/* Impl */ ast::DefId, Rc<ty::TraitRef>, subst::Substs, MethodIndex),
    WhereClauseProbe(Rc<ty::TraitRef>, MethodIndex),
}

pub struct Pick {
    pub method_ty: Rc<ty::Method>,
    pub adjustment: PickAdjustment,
    pub kind: PickKind,
}

#[deriving(Clone,Show)]
pub enum PickKind {
    InherentImplPick(/* Impl */ ast::DefId),
    ObjectPick(/* Trait */ ast::DefId, /* method_num */ uint, /* real_index */ uint),
    ExtensionImplPick(/* Impl */ ast::DefId, MethodIndex),
    TraitPick(/* Trait */ ast::DefId, MethodIndex),
    WhereClausePick(/* Trait */ Rc<ty::TraitRef>, MethodIndex),
}

pub type PickResult = Result<Pick, MethodError>;

// This is a kind of "abstracted" version of ty::AutoAdjustment.  The
// difference is that it doesn't embed any regions or other
// specifics. The "confirmation" step recreates those details as
// needed.
#[deriving(Clone,Show)]
pub enum PickAdjustment {
    AutoDeref(/* number of autoderefs */ uint),     // A = expr, *expr, **expr
    AutoRef(ast::Mutability, Box<PickAdjustment>),  // A = &A | &mut A
    AutoUnsizeLength(uint, Box<PickAdjustment>),    // [T, ..n] => [T]
}

impl<'a,'tcx> ProbeContext<'a,'tcx> {
    pub fn new(fcx: &'a FnCtxt<'a,'tcx>,
               span: Span,
               method_name: ast::Name,
               self_ty: ty::t,
               call_expr_id: ast::NodeId)
               -> ProbeContext<'a,'tcx>
    {
        let mut steps = Vec::new();

        let (fully_dereferenced_ty, dereferences, _) =
            check::autoderef(
                fcx, span, self_ty, None, NoPreference,
                |t, d| {
                    let adjustment = consider_reborrow(t, d);
                    steps.push(ProbeStep { self_ty: t, adjustment: adjustment });
                    None::<()> // keep iterating until we can't anymore
                });

        match ty::get(fully_dereferenced_ty).sty {
            ty::ty_vec(elem_ty, Some(len)) => {
                steps.push(ProbeStep {
                    self_ty: ty::mk_vec(fcx.tcx(), elem_ty, None),
                    adjustment: AutoUnsizeLength(len, box AutoDeref(dereferences))
                });
            }
            _ => {
            }
        }

        debug!("ProbeContext: steps for self_ty={} are {}",
               self_ty.repr(fcx.tcx()),
               steps.repr(fcx.tcx()));

         let mut probe_cx = ProbeContext {
            fcx: fcx,
            span: span,
            method_name: method_name,
            inherent_probes: Vec::new(),
            extension_probes: Vec::new(),
            impl_dups: HashSet::new(),
            steps: Rc::new(steps),
            static_candidates: Vec::new(),
        };

        probe_cx.assemble_inherent_probes();
        probe_cx.assemble_extension_probes_for_traits_in_scope(call_expr_id);
        return probe_cx;

        fn consider_reborrow(t: ty::t, d: uint) -> PickAdjustment {
            // Insert a `&*` or `&mut *` if this is a reference type:
            match ty::get(t).sty {
                ty::ty_rptr(_, ref mt) => AutoRef(mt.mutbl, box AutoDeref(d+1)),
                _ => AutoDeref(d),
            }
        }
    }

    pub fn tcx(&self) -> &'a ty::ctxt<'tcx> {
        self.fcx.tcx()
    }

    pub fn infcx(&self) -> &'a InferCtxt<'a, 'tcx> {
        self.fcx.infcx()
    }

    ///////////////////////////////////////////////////////////////////////////
    // PROBE ASSEMBLY

    fn assemble_inherent_probes(&mut self) {
        let steps = self.steps.clone();
        for step in steps.iter() {
            self.assemble_probe(step.self_ty);
        }
    }

    fn assemble_probe(&mut self, self_ty: ty::t) {
        debug!("assemble_probe: self_ty={}",
               self_ty.repr(self.tcx()));

        match ty::get(self_ty).sty {
            ty::ty_trait(box ty::TyTrait { def_id, ref substs, bounds, .. }) => {
                self.assemble_inherent_probes_from_object(self_ty, def_id, substs, bounds);
                self.assemble_inherent_impl_probes_for_type(def_id);
            }
            ty::ty_enum(did, _) |
            ty::ty_struct(did, _) |
            ty::ty_unboxed_closure(did, _, _) => {
                self.assemble_inherent_impl_probes_for_type(did);
            }
            ty::ty_param(p) => {
                self.assemble_inherent_probes_from_param(self_ty, p);
            }
            _ => {
            }
        }
    }

    fn assemble_inherent_impl_probes_for_type(&mut self, def_id: ast::DefId) {
        // Read the inherent implementation candidates for this type from the
        // metadata if necessary.
        ty::populate_implementations_for_type_if_necessary(self.tcx(), def_id);

        for impl_infos in self.tcx().inherent_impls.borrow().find(&def_id).iter() {
            for &impl_did in impl_infos.iter() {
                self.assemble_inherent_impl_probe(impl_did);
            }
        }
    }

    fn assemble_inherent_impl_probe(&mut self, impl_did: ast::DefId) {
        if !self.impl_dups.insert(impl_did) {
            return; // already visited
        }

        let method = match impl_method(self.tcx(), impl_did, self.method_name) {
            Some(m) => m,
            None => { return; } // No method with correct name on this impl
        };

        if !self.has_applicable_self(&*method) {
            // No receiver declared. Not a candidate.
            return self.record_static_candidate(ImplSource(impl_did));
        }

        let impl_pty = check::impl_self_ty(self.fcx, self.span, impl_did);
        let impl_substs = impl_pty.substs;

        // Determine the receiver type that the method itself expects.
        let xform_self_ty =
            self.xform_self_ty(&method, &impl_substs);

        self.inherent_probes.push(Probe {
            xform_self_ty: xform_self_ty,
            method_ty: method,
            kind: InherentImplProbe(impl_did, impl_substs)
        });
    }

    fn assemble_inherent_probes_from_object(&mut self,
                                            self_ty: ty::t,
                                            did: ast::DefId,
                                            substs: &subst::Substs,
                                            _bounds: ty::ExistentialBounds) {
        debug!("assemble_inherent_probes_from_object(self_ty={})",
               self_ty.repr(self.tcx()));

        let tcx = self.tcx();

        // It is illegal to invoke a method on a trait instance that
        // refers to the `Self` type. An error will be reported by
        // `enforce_object_limitations()` if the method refers to the
        // `Self` type anywhere other than the receiver. Here, we use
        // a substitution that replaces `Self` with the object type
        // itself. Hence, a `&self` method will wind up with an
        // argument type like `&Trait`.
        let rcvr_substs = substs.with_self_ty(self_ty);
        let trait_ref = Rc::new(ty::TraitRef {
            def_id: did,
            substs: rcvr_substs.clone()
        });

        self.elaborate_bounds(&[trait_ref.clone()], |this, new_trait_ref, m, method_num| {
            let vtable_index =
                get_method_index(tcx, &*new_trait_ref,
                                 trait_ref.clone(), method_num);

            // FIXME Hacky. By-value `self` methods in objects ought to be
            // just a special case of passing ownership of a DST value
            // as a parameter. *But* we currently hack them in and tie them to
            // the particulars of the `Box` type. So basically for a `fn foo(self,...)`
            // method invoked on an object, we don't want the receiver type to be
            // `TheTrait`, but rather `Box<TheTrait>`. Yuck.
            let mut m = m;
            match m.explicit_self {
                ty::ByValueExplicitSelfCategory => {
                    let mut n = (*m).clone();
                    let self_ty = n.fty.sig.inputs[0];
                    n.fty.sig.inputs[0] = ty::mk_uniq(tcx, self_ty);
                    m = Rc::new(n);
                }
                _ => { }
            }

            let xform_self_ty =
                this.xform_self_ty(&m, &new_trait_ref.substs);

            this.inherent_probes.push(Probe {
                xform_self_ty: xform_self_ty,
                method_ty: m,
                kind: ObjectProbe(MethodObject {
                    trait_ref: new_trait_ref,
                    object_trait_id: did,
                    method_num: method_num,
                    real_index: vtable_index
                })
            });
        });
    }

    fn assemble_inherent_probes_from_param(&mut self,
                                           _rcvr_ty: ty::t,
                                           param_ty: ty::ParamTy) {
        let ty::ParamTy { space, idx: index, .. } = param_ty;
        let bounds =
            self.fcx.inh.param_env.bounds.get(space, index).trait_bounds
            .as_slice();
        self.elaborate_bounds(bounds, |this, trait_ref, m, method_num| {
            let xform_self_ty =
                this.xform_self_ty(&m, &trait_ref.substs);

            debug!("found match: trait_ref={} substs={} m={}",
                   trait_ref.repr(this.tcx()),
                   trait_ref.substs.repr(this.tcx()),
                   m.repr(this.tcx()));
            assert_eq!(m.generics.types.get_slice(subst::TypeSpace).len(),
                       trait_ref.substs.types.get_slice(subst::TypeSpace).len());
            assert_eq!(m.generics.regions.get_slice(subst::TypeSpace).len(),
                       trait_ref.substs.regions().get_slice(subst::TypeSpace).len());
            assert_eq!(m.generics.types.get_slice(subst::SelfSpace).len(),
                       trait_ref.substs.types.get_slice(subst::SelfSpace).len());
            assert_eq!(m.generics.regions.get_slice(subst::SelfSpace).len(),
                       trait_ref.substs.regions().get_slice(subst::SelfSpace).len());

            this.inherent_probes.push(Probe {
                xform_self_ty: xform_self_ty,
                method_ty: m,
                kind: WhereClauseProbe(trait_ref, method_num)
            });
        });
    }

    // Do a search through a list of bounds, using a callback to actually
    // create the candidates.
    fn elaborate_bounds(
        &mut self,
        bounds: &[Rc<ty::TraitRef>],
        mk_cand: |this: &mut ProbeContext,
                  tr: Rc<ty::TraitRef>,
                  m: Rc<ty::Method>,
                  method_num: uint|)
    {
        let tcx = self.tcx();
        let mut cache = HashSet::new();
        for bound_trait_ref in traits::transitive_bounds(tcx, bounds) {
            // Already visited this trait, skip it.
            if !cache.insert(bound_trait_ref.def_id) {
                continue;
            }

            let (pos, method) = match trait_method(tcx, bound_trait_ref.def_id, self.method_name) {
                Some(v) => v,
                None => { continue; }
            };

            if !self.has_applicable_self(&*method) {
                self.record_static_candidate(TraitSource(bound_trait_ref.def_id));
            } else {
                mk_cand(self, bound_trait_ref, method, pos);
            }
        }
    }

    pub fn assemble_extension_probes_for_traits_in_scope(&mut self,
                                                         expr_id: ast::NodeId)
    {
        let mut duplicates = HashSet::new();
        let opt_applicable_traits = self.fcx.ccx.trait_map.find(&expr_id);
        for applicable_traits in opt_applicable_traits.into_iter() {
            for &trait_did in applicable_traits.iter() {
                if duplicates.insert(trait_did) {
                    self.assemble_extension_probes_for_trait(trait_did);
                }
            }
        }
    }

    pub fn assemble_extension_probes_for_trait(&mut self,
                                               trait_def_id: ast::DefId) {
        debug!("assemble_extension_probes_for_trait: trait_def_id={}",
               trait_def_id.repr(self.tcx()));

        // Check whether `trait_def_id` defines a method with suitable name:
        let trait_items =
            ty::trait_items(self.tcx(), trait_def_id);
        let matching_index =
            trait_items.iter()
                       .position(|item| item.name() == self.method_name);
        let matching_index = match matching_index {
            Some(i) => i,
            None => { return; }
        };
        let method = match (&*trait_items)[matching_index].as_opt_method() {
            Some(m) => m,
            None => { return; }
        };

        // Check whether `trait_def_id` defines a method with suitable name:
        if !self.has_applicable_self(&*method) {
            debug!("method has inapplicable self");
            return self.record_static_candidate(TraitSource(trait_def_id));
        }

        self.assemble_extension_probes_for_trait_impls(trait_def_id,
                                                       method.clone(),
                                                       matching_index);

        self.assemble_unboxed_closure_probes(trait_def_id,
                                             method,
                                             matching_index);
    }

    fn assemble_extension_probes_for_trait_impls(&mut self,
                                                 trait_def_id: ast::DefId,
                                                 method: Rc<ty::Method>,
                                                 method_index: uint)
    {
        ty::populate_implementations_for_trait_if_necessary(self.tcx(),
                                                            trait_def_id);

        let trait_impls = self.tcx().trait_impls.borrow();
        let impl_def_ids = match trait_impls.find(&trait_def_id) {
            None => { return; }
            Some(impls) => impls,
        };

        for &impl_def_id in impl_def_ids.borrow().iter() {
            debug!("assemble_extension_probes_for_trait_impl: trait_def_id={} impl_def_id={}",
                   trait_def_id.repr(self.tcx()),
                   impl_def_id.repr(self.tcx()));

            let impl_pty = check::impl_self_ty(self.fcx, self.span, impl_def_id);
            let impl_substs = impl_pty.substs;

            debug!("impl_substs={}", impl_substs.repr(self.tcx()));

            let impl_trait_ref =
                ty::impl_trait_ref(self.tcx(), impl_def_id)
                .unwrap() // we know this is a trait impl
                .subst(self.tcx(), &impl_substs);

            debug!("impl_trait_ref={}", impl_trait_ref.repr(self.tcx()));

            // Determine the receiver type that the method itself expects.
            let xform_self_ty =
                self.xform_self_ty(&method, &impl_trait_ref.substs);

            debug!("xform_self_ty={}", xform_self_ty.repr(self.tcx()));

            self.extension_probes.push(Probe {
                xform_self_ty: xform_self_ty,
                method_ty: method.clone(),
                kind: ExtensionImplProbe(impl_def_id, impl_trait_ref, impl_substs, method_index)
            });
        }
    }

    fn assemble_unboxed_closure_probes(&mut self,
                                       trait_def_id: ast::DefId,
                                       method_ty: Rc<ty::Method>,
                                       method_index: uint)
    {
        // Check if this is one of the Fn,FnMut,FnOnce traits.
        let tcx = self.tcx();
        let kind = if Some(trait_def_id) == tcx.lang_items.fn_trait() {
            ty::FnUnboxedClosureKind
        } else if Some(trait_def_id) == tcx.lang_items.fn_mut_trait() {
            ty::FnMutUnboxedClosureKind
        } else if Some(trait_def_id) == tcx.lang_items.fn_once_trait() {
            ty::FnOnceUnboxedClosureKind
        } else {
            return;
        };

        // Check if there is an unboxed-closure self-type in the list of receivers.
        // If so, add "synthetic impls".
        let steps = self.steps.clone();
        for step in steps.iter() {
            let (closure_def_id, _, _) = match ty::get(step.self_ty).sty {
                ty::ty_unboxed_closure(a, b, ref c) => (a, b, c),
                _ => continue,
            };

            let unboxed_closures = self.fcx.inh.unboxed_closures.borrow();
            let closure_data = match unboxed_closures.find(&closure_def_id) {
                Some(data) => data,
                None => {
                    self.tcx().sess.span_bug(
                        self.span,
                        format!("No entry for unboxed closure: {}",
                                closure_def_id.repr(self.tcx())).as_slice());
                }
            };

            // this closure doesn't implement the right kind of `Fn` trait
            if closure_data.kind != kind {
                continue;
            }

            // create some substitutions for the argument/return type;
            // for the purposes of our method lookup, we only take
            // receiver type into account, so we can just substitute
            // fresh types here. Trait matching will wind up unifying
            // these appropriately later.
            let trait_def = ty::lookup_trait_def(self.tcx(), trait_def_id);
            let substs = self.infcx().fresh_substs_for_trait(self.span,
                                                             &trait_def.generics,
                                                             step.self_ty);

            // add a where-clause probe, meaning that we just look to
            // try and match the self-type and that's enough.
            let trait_ref = Rc::new(ty::TraitRef::new(trait_def_id, substs));
            let xform_self_ty = self.xform_self_ty(&method_ty, &trait_ref.substs);
            self.inherent_probes.push(Probe {
                xform_self_ty: xform_self_ty,
                method_ty: method_ty.clone(),
                kind: WhereClauseProbe(trait_ref, method_index)
            });
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // THE ACTUAL SEARCH

    pub fn pick(mut self) -> PickResult {
        let steps = self.steps.clone();

        for step in steps.iter() {
            match self.pick_step(step) {
                Some(r) => {
                    return r;
                }
                None => { }
            }
        }

        Err(NoMatch(self.static_candidates))
    }

    fn pick_step(&mut self, step: &ProbeStep) -> Option<PickResult> {
        debug!("pick_step: step={}", step.repr(self.tcx()));

        if ty::type_is_error(step.self_ty) {
            return None;
        }

        match self.pick_adjusted_method(step) {
            Some(result) => return Some(result),
            None => {}
        }

        match self.pick_autorefd_method(step) {
            Some(result) => return Some(result),
            None => {}
        }

        // FIXME -- Super hack. For DST types, we will convert to
        // &&[T] or &&str, as part of a kind of legacy lookup scheme.
        match ty::get(step.self_ty).sty {
            ty::ty_str | ty::ty_vec(_, None) => self.pick_autorefrefd_method(step),
            _ => None
        }
    }

    fn pick_adjusted_method(&mut self,
                            step: &ProbeStep)
                            -> Option<PickResult>
    {
        self.pick_method(step.self_ty).map(|r| self.adjust(r, step.adjustment.clone()))
    }

    fn pick_autorefd_method(&mut self,
                            step: &ProbeStep)
                            -> Option<PickResult>
    {
        let tcx = self.tcx();
        self.search_mutabilities(
            |m| AutoRef(m, box step.adjustment.clone()),
            |m,r| ty::mk_rptr(tcx, r, ty::mt {ty:step.self_ty, mutbl:m}))
    }

    fn pick_autorefrefd_method(&mut self,
                            step: &ProbeStep)
                            -> Option<PickResult>
    {
        let tcx = self.tcx();
        self.search_mutabilities(
            |m| AutoRef(m, box AutoRef(m, box step.adjustment.clone())),
            |m,r| ty::mk_rptr(tcx, r, ty::mt { ty: ty::mk_rptr(tcx, r, ty::mt { ty:step.self_ty,
                                                                                mutbl:m}),
                                               mutbl: m }))
    }

    fn search_mutabilities(&mut self,
                           mk_adjustment: |ast::Mutability| -> PickAdjustment,
                           mk_autoref_ty: |ast::Mutability, ty::Region| -> ty::t)
                           -> Option<PickResult>
    {
        let region = self.infcx().next_region_var(infer::Autoref(self.span));

        // Search through mutabilities in order to find one where pick works:
        [ast::MutImmutable, ast::MutMutable]
            .iter()
            .flat_map(|&m| {
                let autoref_ty = mk_autoref_ty(m, region);
                self.pick_method(autoref_ty)
                    .map(|r| self.adjust(r, mk_adjustment(m)))
                    .into_iter()
            })
            .nth(0)
    }

    fn adjust(&mut self, result: PickResult, adjustment: PickAdjustment) -> PickResult {
        match result {
            Err(e) => Err(e),
            Ok(mut pick) => {
                pick.adjustment = adjustment;
                Ok(pick)
            }
        }
    }

    fn pick_method(&mut self, self_ty: ty::t) -> Option<PickResult> {
        debug!("pick_method(self_ty={})", self.infcx().ty_to_string(self_ty));

        debug!("searching inherent candidates");
        match self.consider_probes(self_ty, self.inherent_probes[]) {
            None => {}
            Some(pick) => {
                return Some(pick);
            }
        }

        debug!("searching extension candidates");
        self.consider_probes(self_ty, self.extension_probes[])
    }

    fn consider_probes(&self, self_ty: ty::t, probes: &[Probe]) -> Option<PickResult> {
        let mut applicable_probes: Vec<_> =
            probes.iter()
                  .filter(|&probe| self.consider_probe(self_ty, probe))
                  .collect();

        debug!("applicable_probes: {}", applicable_probes.repr(self.tcx()));

        if applicable_probes.len() > 1 {
            match self.collapse_probes_to_trait(applicable_probes[]) {
                Some(pick) => { return Some(Ok(pick)); }
                None => { }
            }
        }

        if applicable_probes.len() > 1 {
            let sources = probes.iter().map(|p| p.to_source()).collect();
            return Some(Err(Ambiguity(sources)));
        }

        applicable_probes.pop().map(|probe| {
            let pick = probe.to_unadjusted_pick();
            Ok(pick)
        })
    }

    fn consider_probe(&self, self_ty: ty::t, probe: &Probe) -> bool {
        debug!("consider_probe: self_ty={} probe={}",
               self_ty.repr(self.tcx()),
               probe.repr(self.tcx()));

        self.infcx().probe(|| {
            match self.make_sub_ty(self_ty, probe.xform_self_ty) {
                Ok(()) => { }
                Err(_) => {
                    debug!("--> cannot relate self-types");
                    return false;
                }
            }

            match probe.kind {
                InherentImplProbe(impl_def_id, ref substs) |
                ExtensionImplProbe(impl_def_id, _, ref substs, _) => {
                    // Check whether the impl imposes obligations we have to worry about.
                    let obligations =
                        traits::impl_obligations(
                            self.tcx(),
                            traits::ObligationCause::misc(self.span),
                            impl_def_id,
                            substs);

                    debug!("impl_obligations={}", obligations.repr(self.tcx()));

                    let mut selcx = traits::SelectionContext::new(self.infcx(),
                                                                  &self.fcx.inh.param_env,
                                                                  self.fcx);

                    obligations.all(|o| selcx.evaluate_obligation_intracrate(o))
                }

                ObjectProbe(_) |
                WhereClauseProbe(_, _) => {
                    // These cannot be "winnowed" any further.
                    true
                }
            }
        })
    }

    fn collapse_probes_to_trait(&self, probes: &[&Probe]) -> Option<Pick> {
        /*!
         * Sometimes we get in a situation where we have multiple
         * probes that are all impls of the same trait, but we don't
         * know which impl to use. In this case, since in all cases
         * the external interface of the method can be determined from
         * the trait, it's ok not to decide.  We can basically just
         * collapse all of the probes for various impls into one
         * where-clause probe. This will result in a pending
         * obligation so when more type-info is available we can make
         * the final decision.
         *
         * Example (`src/test/run-pass/method-two-trait-defer-resolution-1.rs`):
         *
         * ```
         * trait Foo { ... }
         * impl Foo for Vec<int> { ... }
         * impl Foo for Vec<uint> { ... }
         * ```
         *
         * Now imagine the receiver is `Vec<_>`. It doesn't really
         * matter at this time which impl we use, so it's ok to just
         * commit to "using the method from the trait Foo".
         */

        // Do all probes correspond to the same trait?
        let trait_data = match probes[0].to_trait_data() {
            Some(data) => data,
            None => return None,
        };
        if probes[1..].iter().any(|p| p.to_trait_data() != Some(trait_data)) {
            return None;
        }

        // If so, just use this trait and call it a day.
        let (trait_def_id, method_num) = trait_data;
        let method_ty = probes[0].method_ty.clone();
        Some(Pick {
            method_ty: method_ty,
            adjustment: AutoDeref(0),
            kind: TraitPick(trait_def_id, method_num)
        })
    }

    ///////////////////////////////////////////////////////////////////////////
    // MISCELLANY

    fn make_sub_ty(&self, sub: ty::t, sup: ty::t) -> infer::ures {
        self.infcx().sub_types(false, infer::Misc(DUMMY_SP), sub, sup)
    }

    fn has_applicable_self(&self, method: &ty::Method) -> bool {
        // "fast track" -- check for usage of sugar
        match method.explicit_self {
            ty::StaticExplicitSelfCategory => {
                // fallthrough
            }
            ty::ByValueExplicitSelfCategory |
            ty::ByReferenceExplicitSelfCategory(..) |
            ty::ByBoxExplicitSelfCategory => {
                return true;
            }
        }

        // FIXME -- check for types that deref to `Self`,
        // like `Rc<Self>` and so on.
        //
        // Note also that the current code will break if this type
        // includes any of the type parameters defined on the method
        // -- but this could be overcome.
        return false;
    }

    fn record_static_candidate(&mut self, source: CandidateSource) {
        self.static_candidates.push(source);
    }

    fn xform_self_ty(&self, method: &Rc<ty::Method>, substs: &subst::Substs) -> ty::t {
        debug!("xform_self_ty(self_ty={}, substs={})",
               method.fty.sig.inputs[0].repr(self.tcx()),
               substs.repr(self.tcx()));

        let xform_self_ty = method.fty.sig.inputs[0].subst(self.tcx(), substs);
        self.infcx().replace_late_bound_regions_with_fresh_var(method.fty.sig.binder_id,
                                                               self.span,
                                                               &xform_self_ty)
    }
}

fn impl_method(tcx: &ty::ctxt,
               impl_def_id: ast::DefId,
               method_name: ast::Name)
               -> Option<Rc<ty::Method>>
{
    let impl_items = tcx.impl_items.borrow();
    let impl_items = impl_items.find(&impl_def_id).unwrap();
    impl_items
        .iter()
        .map(|&did| ty::impl_or_trait_item(tcx, did.def_id()))
        .find(|m| m.name() == method_name)
        .and_then(|item| item.as_opt_method())
}

fn trait_method(tcx: &ty::ctxt,
                trait_def_id: ast::DefId,
                method_name: ast::Name)
                -> Option<(uint, Rc<ty::Method>)>
{
    /*!
     * Find method with name `method_name` defined in `trait_def_id` and return it,
     * along with its index (or `None`, if no such method).
     */

    let trait_items = ty::trait_items(tcx, trait_def_id);
    trait_items
        .iter()
        .enumerate()
        .find(|&(_, ref item)| item.name() == method_name)
        .and_then(|(idx, item)| item.as_opt_method().map(|m| (idx, m)))
}

// Determine the index of a method in the list of all methods belonging
// to a trait and its supertraits.
fn get_method_index(tcx: &ty::ctxt,
                    trait_ref: &ty::TraitRef,
                    subtrait: Rc<ty::TraitRef>,
                    n_method: uint) -> uint {
    // We need to figure the "real index" of the method in a
    // listing of all the methods of an object. We do this by
    // iterating down the supertraits of the object's trait until
    // we find the trait the method came from, counting up the
    // methods from them.
    let mut method_count = 0;
    ty::each_bound_trait_and_supertraits(tcx, &[subtrait], |bound_ref| {
        if bound_ref.def_id == trait_ref.def_id {
            false
        } else {
            let trait_items = ty::trait_items(tcx, bound_ref.def_id);
            for trait_item in trait_items.iter() {
                match *trait_item {
                    ty::MethodTraitItem(_) => method_count += 1,
                    ty::TypeTraitItem(_) => {}
                }
            }
            true
        }
    });
    method_count + n_method
}

impl Probe {
    fn to_unadjusted_pick(&self) -> Pick {
        Pick {
            method_ty: self.method_ty.clone(),
            adjustment: AutoDeref(0),
            kind: match self.kind {
                InherentImplProbe(def_id, _) => {
                    InherentImplPick(def_id)
                }
                ObjectProbe(ref data) => {
                    ObjectPick(data.trait_ref.def_id, data.method_num, data.real_index)
                }
                ExtensionImplProbe(def_id, _, _, index) => {
                    ExtensionImplPick(def_id, index)
                }
                WhereClauseProbe(ref trait_ref, index) => {
                    WhereClausePick((*trait_ref).clone(), index)
                }
            }
        }
    }

    fn to_source(&self) -> CandidateSource {
        match self.kind {
            InherentImplProbe(def_id, _) => ImplSource(def_id),
            ObjectProbe(ref obj) => TraitSource(obj.trait_ref.def_id),
            ExtensionImplProbe(def_id, _, _, _) => ImplSource(def_id),
            WhereClauseProbe(ref trait_ref, _) => TraitSource(trait_ref.def_id),
        }
    }

    fn to_trait_data(&self) -> Option<(ast::DefId,MethodIndex)> {
        match self.kind {
            InherentImplProbe(..) |
            ObjectProbe(..) => {
                None
            }
            ExtensionImplProbe(_, ref trait_ref, _, method_num) |
            WhereClauseProbe(ref trait_ref, method_num) => {
                Some((trait_ref.def_id, method_num))
            }
        }
    }
}

impl Repr for Probe {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("Probe(xform_self_ty={}, kind={})",
                self.xform_self_ty.repr(tcx),
                self.kind.repr(tcx))
    }
}

impl Repr for ProbeKind {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            InherentImplProbe(ref a, ref b) =>
                format!("InherentImplProbe({},{})", a.repr(tcx), b.repr(tcx)),
            ObjectProbe(ref a) =>
                format!("ObjectProbe({})", a.repr(tcx)),
            ExtensionImplProbe(ref a, ref b, ref c, ref d) =>
                format!("ExtensionImplProbe({},{},{},{})", a.repr(tcx), b.repr(tcx),
                        c.repr(tcx), d),
            WhereClauseProbe(ref a, ref b) =>
                format!("WhereClauseProbe({},{})", a.repr(tcx), b),
        }
    }
}

impl Repr for ProbeStep {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("ProbeStep({},{})",
                self.self_ty.repr(tcx),
                self.adjustment)
    }
}

impl Repr for PickAdjustment {
    fn repr(&self, _tcx: &ty::ctxt) -> String {
        format!("{}", self)
    }
}

impl Repr for PickKind {
    fn repr(&self, _tcx: &ty::ctxt) -> String {
        format!("{}", self)
    }
}

impl Repr for Pick {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("Pick(method_ty={}, adjustment={}, kind={})",
                self.method_ty.repr(tcx),
                self.adjustment,
                self.kind)
    }
}
