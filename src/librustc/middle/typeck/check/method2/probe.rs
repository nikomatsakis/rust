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
use util::ppaux::Repr;

pub struct ProbeContext<'a,'tcx:'a> {
    fcx: &'a FnCtxt<'a, 'tcx>,
    span: Span,
    method_name: ast::Name,
    deref_args: check::DerefArgs,
    self_tys: Rc<Vec<ty::t>>,
    inherent_probes: Vec<Probe>,
    extension_probes: Vec<Probe>,
    impl_dups: HashSet<ast::DefId>,
    static_candidates: Vec<CandidateSource>,
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
    UnboxedClosureImplProbe(ast::DefId),
    WhereClauseProbe(Rc<ty::TraitRef>, MethodIndex),
}

pub struct Pick {
    method_ty: Rc<ty::Method>,
    adjustment: PickAdjustment,
    kind: PickKind,
}

pub enum PickKind {
    InherentImplPick(/* Impl */ ast::DefId),
    ObjectPick(MethodObject),
    ExtensionImplPick(/* Impl */ ast::DefId, MethodIndex),
    UnboxedClosureImplPick(ast::DefId),
    WhereClausePick(Rc<ty::TraitRef>, MethodIndex),
}

pub type PickResult = Result<Pick, MethodError>;

// This is a kind of "abstracted" version of ty::AutoAdjustment.  The
// difference is that it doesn't embed any regions or other
// specifics. The "confirmation" step recreates those details as
// needed.
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
               deref_args: check::DerefArgs)
               -> ProbeContext<'a,'tcx>
    {
        let mut self_tys = Vec::new();
        check::autoderef(
            fcx, span, self_ty, None, NoPreference,
            |t, _| { self_tys.push(t); Some(()) });

        ProbeContext {
            fcx: fcx,
            span: span,
            method_name: method_name,
            deref_args: deref_args,
            inherent_probes: Vec::new(),
            extension_probes: Vec::new(),
            impl_dups: HashSet::new(),
            self_tys: Rc::new(Vec::new()),
            static_candidates: Vec::new(),
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

    pub fn assemble_inherent_probes(&mut self,
                                    restrict_to_trait: Option<ast::DefId>) {
        let self_tys = self.self_tys.clone();
        for &t in self_tys.iter() {
            self.assemble_probe(t, restrict_to_trait);
        }
    }

    fn assemble_probe(&mut self, self_ty: ty::t, restrict_to_trait: Option<ast::DefId>) {
        match ty::get(self_ty).sty {
            ty::ty_trait(box ty::TyTrait { def_id, ref substs, bounds, .. }) => {
                if restrict_to_trait.is_none() {
                    self.assemble_inherent_probes_from_object(self_ty, def_id, substs, bounds);
                    self.assemble_inherent_impl_probes_for_type(def_id);
                }
            }
            ty::ty_enum(did, _) |
            ty::ty_struct(did, _) |
            ty::ty_unboxed_closure(did, _, _) => {
                if restrict_to_trait.is_none() {
                    self.assemble_inherent_impl_probes_for_type(did);
                }
            }
            ty::ty_param(p) => {
                self.assemble_inherent_probes_from_param(self_ty, restrict_to_trait, p);
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
                    *n.fty.sig.inputs.get_mut(0) = ty::mk_uniq(tcx, self_ty);
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
                                           rcvr_ty: ty::t,
                                           restrict_to_trait: Option<ast::DefId>,
                                           param_ty: ty::ParamTy) {
        let ty::ParamTy { space, idx: index, .. } = param_ty;
        let bounds =
            self.fcx.inh.param_env.bounds.get(space, index).trait_bounds
            .as_slice();
        self.elaborate_bounds(bounds, |this, trait_ref, m, method_num| {
            if Some(trait_ref.def_id) == restrict_to_trait {
                return;
            }

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
                                                         expr_id: ast::NodeId) {
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
        debug!("assemble_extension_probes_for_trait: trait_def_id={}", trait_def_id);

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
                                                       method,
                                                       matching_index);
    }

    fn assemble_extension_probes_for_trait_impls(&mut self,
                                                 trait_def_id: ast::DefId,
                                                 method: Rc<ty::Method>,
                                                 method_index: uint) {
        ty::populate_implementations_for_trait_if_necessary(self.tcx(),
                                                            trait_def_id);

        let trait_impls = self.tcx().trait_impls.borrow();
        let impl_def_ids = match trait_impls.find(&trait_def_id) {
            None => { return; }
            Some(impls) => impls,
        };

        for &impl_def_id in impl_def_ids.borrow().iter() {
            let impl_pty = check::impl_self_ty(self.fcx, self.span, impl_def_id);
            let impl_substs = impl_pty.substs;

            let impl_trait_ref =
                ty::impl_trait_ref(self.tcx(), impl_def_id)
                .unwrap() // we know this is a trait impl
                .subst(self.tcx(), &impl_substs);

            // Determine the receiver type that the method itself expects.
            let xform_self_ty =
                self.xform_self_ty(&method, &impl_substs);

            self.extension_probes.push(Probe {
                xform_self_ty: xform_self_ty,
                method_ty: method.clone(),
                kind: ExtensionImplProbe(impl_def_id, impl_trait_ref, impl_substs, method_index)
            });
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // THE ACTUAL SEARCH

    pub fn pick(mut self) -> PickResult {
        let self_tys = self.self_tys.clone();
        for (index, &self_ty) in self_tys.iter().enumerate() {
            match self.pick_step(self_ty, index) {
                Some(r) => { return r; }
                None => { }
            }
        }

        Err(NoMatch(self.static_candidates))
    }

    pub fn pick_no_autoderef(mut self) -> PickResult {
        let self_ty: ty::t = (*self.self_tys)[0];
        match self.pick_step(self_ty, 0) {
            Some(r) => r,
            None => Err(NoMatch(self.static_candidates))
        }
    }

    fn pick_step(&mut self, self_ty: ty::t, autoderefs: uint) -> Option<PickResult> {
        match self.deref_args {
            check::DontDerefArgs => {
                match self.pick_autoderefd_method(self_ty, autoderefs) {
                    Some(result) => return Some(result),
                    None => {}
                }

                match self.pick_autoptrd_method(self_ty, autoderefs) {
                    Some(result) => return Some(result),
                    None => {}
                }
            }

            check::DoDerefArgs => {
                match self.pick_autoptrd_method(self_ty, autoderefs) {
                    Some(result) => return Some(result),
                    None => {}
                }

                match self.pick_autoderefd_method(self_ty, autoderefs) {
                    Some(result) => return Some(result),
                    None => {}
                }
            }
        }

        // If we are searching for an overloaded deref, no
        // need to try coercing a `~[T]` to an `&[T]` and
        // searching for an overloaded deref on *that*.
        if !self.is_overloaded_deref() {
            match self.pick_autofatptrd_method(self_ty, autoderefs) {
                Some(result) => return Some(result),
                None => {}
            }
        }

        None
    }

    fn pick_autoptrd_method(&mut self,
                            self_ty: ty::t,
                            autoderefs: uint)
                            -> Option<PickResult>
    {
        if ty::type_is_error(self_ty) {
            return None;
        }

        let tcx = self.tcx();
        self.search_mutabilities(
            autoderefs,
            [ast::MutImmutable, ast::MutMutable],
            |m| AutoRef(m, box AutoDeref(autoderefs)),
            |m,r| ty::mk_rptr(tcx, r, ty::mt {ty:self_ty, mutbl:m}))
    }

    fn search_mutabilities(&mut self,
                           autoderefs: uint,
                           mutbls: &[ast::Mutability],
                           mk_adjustment: |ast::Mutability| -> PickAdjustment,
                           mk_autoref_ty: |ast::Mutability, ty::Region| -> ty::t)
                           -> Option<PickResult>
    {
        let region = self.infcx().next_region_var(infer::Autoref(self.span));

        // Search through mutabilities in order to find one where pick works:
        mutbls
            .iter()
            .flat_map(|&m| {
                let autoref_ty = mk_autoref_ty(m, region);
                self.pick_method(autoref_ty)
                    .map(|r| self.adjust(r, mk_adjustment(m)))
                    .into_iter()
            })
            .nth(0)
    }

    fn pick_autofatptrd_method(&mut self,
                               self_ty: ty::t,
                               autoderefs: uint)
                               -> Option<PickResult>
    {
        fail!("NYI")
    }

    fn pick_autoderefd_method(&mut self,
                              self_ty: ty::t,
                              autoderefs: uint)
                              -> Option<PickResult>
    {
        // Hacky. For overloaded derefs, there may be an adjustment
        // added to the expression from the outside context, so we do not store
        // an explicit adjustment, but rather we hardwire the single deref
        // that occurs in trans and mem_categorization.
        if self.is_overloaded_deref() {
            return None;
        }

        let (self_ty, auto_deref_ref) = self.consider_reborrow(self_ty, autoderefs);

        self.pick_method(self_ty).map(|r| self.adjust(r, AutoDeref(autoderefs)))
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

        if applicable_probes.len() > 1 {
            applicable_probes.retain(|&p| self.winnow_probe(self_ty, p));
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
        infer::can_mk_subty(self.infcx(), self_ty, probe.xform_self_ty).is_ok()
    }

    fn winnow_probe(&self, self_ty: ty::t, probe: &Probe) -> bool {
        match probe.kind {
            InherentImplProbe(impl_def_id, ref substs) |
            ExtensionImplProbe(impl_def_id, _, ref substs, _) => {
                // Check whether the impl imposes obligations we have to worry about.
                let obligations = traits::impl_obligations(self.tcx(),
                                                           traits::ObligationCause::misc(self.span),
                                                           impl_def_id,
                                                           substs);
                let mut selcx = traits::SelectionContext::new(self.infcx(),
                                                              &self.fcx.inh.param_env,
                                                              self.fcx);
                obligations.all(|o| selcx.evaluate_obligation_intracrate(o))
            }

            ObjectProbe(_) |
            UnboxedClosureImplProbe(_) |
            WhereClauseProbe(_, _) => {
                // These cannot be "winnowed" any further.
                true
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // MISCELLANY

    fn is_overloaded_deref(&self) -> bool {
        false
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
        let xform_self_ty = method.fty.sig.inputs[0].subst(self.tcx(), substs);
        self.replace_late_bound_regions_with_fresh_var(method.fty.sig.binder_id, &xform_self_ty)
    }

    fn replace_late_bound_regions_with_fresh_var<T>(&self, binder_id: ast::NodeId, value: &T) -> T
        where T : TypeFoldable + Repr
    {
        let (_, value) = replace_late_bound_regions(
            self.fcx.tcx(),
            binder_id,
            value,
            |br| self.fcx.infcx().next_region_var(infer::LateBoundRegion(self.span, br)));
        value
    }

    fn consider_reborrow(&self,
                         self_ty: ty::t,
                         autoderefs: uint)
                         -> (ty::t, ty::AutoDerefRef) {
        /*!
         * In the event that we are invoking a method with a receiver
         * of a borrowed type like `&T`, `&mut T`, or `&mut [T]`,
         * we will "reborrow" the receiver implicitly.  For example, if
         * you have a call `r.inc()` and where `r` has type `&mut T`,
         * then we treat that like `(&mut *r).inc()`.  This avoids
         * consuming the original pointer.
         *
         * You might think that this would be a natural byproduct of
         * the auto-deref/auto-ref process.  This is true for `Box<T>`
         * but not for an `&mut T` receiver.  With `Box<T>`, we would
         * begin by testing for methods with a self type `Box<T>`,
         * then autoderef to `T`, then autoref to `&mut T`.  But with
         * an `&mut T` receiver the process begins with `&mut T`, only
         * without any autoadjustments.
         */

        let tcx = self.tcx();
        return match ty::get(self_ty).sty {
            ty::ty_rptr(_, self_mt) => {
                let region =
                    self.infcx().next_region_var(infer::Autoref(self.span));
                (ty::mk_rptr(tcx, region, self_mt),
                 ty::AutoDerefRef {
                     autoderefs: autoderefs + 1,
                     autoref: Some(ty::AutoPtr(region, self_mt.mutbl, None))})
            }
            _ => {
                (self_ty,
                 ty::AutoDerefRef {
                     autoderefs: autoderefs,
                     autoref: None})
            }
        };
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
                ObjectProbe(ref obj) => {
                    ObjectPick((*obj).clone())
                }
                ExtensionImplProbe(def_id, _, _, index) => {
                    ExtensionImplPick(def_id, index)
                }
                UnboxedClosureImplProbe(def_id) => {
                    UnboxedClosureImplPick(def_id)
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
            ExtensionImplProbe(_, ref trait_ref, _, _) => TraitSource(trait_ref.def_id),
            UnboxedClosureImplProbe(def_id) => TraitSource(def_id),
            WhereClauseProbe(ref trait_ref, index) => TraitSource(trait_ref.def_id),
        }
    }
}
