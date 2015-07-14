// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use astconv::AstConv;
use check::{FnCtxt, Inherited, blank_fn_ctxt, regionck};
use constrained_type_params::{identify_constrained_type_params, Parameter};
use CrateCtxt;
use middle::subst::{self, TypeSpace, FnSpace, ParamSpace, SelfSpace};
use middle::traits;
use middle::ty::{self, Ty};
use middle::ty_fold::{TypeFolder};
use middle::wf;

use std::cell::RefCell;
use std::collections::HashSet;
use syntax::ast;
use syntax::ast_util::local_def;
use syntax::codemap::{DUMMY_SP, Span};
use syntax::parse::token::special_idents;
use syntax::ptr::P;
use syntax::visit;
use syntax::visit::Visitor;

pub struct CheckTypeWellFormedVisitor<'ccx, 'tcx:'ccx> {
    ccx: &'ccx CrateCtxt<'ccx, 'tcx>
}

impl<'ccx, 'tcx> CheckTypeWellFormedVisitor<'ccx, 'tcx> {
    pub fn new(ccx: &'ccx CrateCtxt<'ccx, 'tcx>) -> CheckTypeWellFormedVisitor<'ccx, 'tcx> {
        CheckTypeWellFormedVisitor { ccx: ccx }
    }

    fn tcx(&self) -> &ty::ctxt<'tcx> {
        self.ccx.tcx
    }

    /// Checks that the field types (in a struct def'n) or argument types (in an enum def'n) are
    /// well-formed, meaning that they do not require any constraints not declared in the struct
    /// definition itself. For example, this definition would be illegal:
    ///
    ///     struct Ref<'a, T> { x: &'a T }
    ///
    /// because the type did not declare that `T:'a`.
    ///
    /// We do this check as a pre-pass before checking fn bodies because if these constraints are
    /// not included it frequently leads to confusing errors in fn bodies. So it's better to check
    /// the types first.
    fn check_item_well_formed(&mut self, item: &ast::Item) {
        let ccx = self.ccx;
        debug!("check_item_well_formed(it.id={}, it.ident={})",
               item.id,
               ccx.tcx.item_path_str(local_def(item.id)));

        match item.node {
            /// Right now we check that every default trait implementation
            /// has an implementation of itself. Basically, a case like:
            ///
            /// `impl Trait for T {}`
            ///
            /// has a requirement of `T: Trait` which was required for default
            /// method implementations. Although this could be improved now that
            /// there's a better infrastructure in place for this, it's being left
            /// for a follow-up work.
            ///
            /// Since there's such a requirement, we need to check *just* positive
            /// implementations, otherwise things like:
            ///
            /// impl !Send for T {}
            ///
            /// won't be allowed unless there's an *explicit* implementation of `Send`
            /// for `T`
            ast::ItemImpl(_, ast::ImplPolarity::Positive, _,
                          ref trait_ref, ref self_ty, ref impl_items) => {
                self.check_impl(item, self_ty, trait_ref, impl_items);
            }
            ast::ItemImpl(_, ast::ImplPolarity::Negative, _, Some(_), _, _) => {
                // TODO what amount of WF checking do we need here?

                let trait_ref = ccx.tcx.impl_trait_ref(local_def(item.id)).unwrap();
                ccx.tcx.populate_implementations_for_trait_if_necessary(trait_ref.def_id);
                match ccx.tcx.lang_items.to_builtin_kind(trait_ref.def_id) {
                    Some(ty::BoundSend) | Some(ty::BoundSync) => {}
                    Some(_) | None => {
                        if !ccx.tcx.trait_has_default_impl(trait_ref.def_id) {
                            span_err!(ccx.tcx.sess, item.span, E0192,
                                      "negative impls are only allowed for traits with \
                                       default impls (e.g., `Send` and `Sync`)")
                        }
                    }
                }
            }
            ast::ItemFn(..) => {
                self.check_item_type(item);
            }
            ast::ItemStatic(..) => {
                self.check_item_type(item);
            }
            ast::ItemConst(..) => {
                self.check_item_type(item);
            }
            ast::ItemStruct(ref struct_def, ref ast_generics) => {
                self.check_type_defn(item, |fcx| {
                    vec![struct_variant(fcx, &**struct_def)]
                });

                self.check_variances_for_type_defn(item, ast_generics);
            }
            ast::ItemEnum(ref enum_def, ref ast_generics) => {
                self.check_type_defn(item, |fcx| {
                    enum_variants(fcx, enum_def)
                });

                self.check_variances_for_type_defn(item, ast_generics);
            }
            ast::ItemTrait(_, _, _, ref items) => {
                let trait_predicates =
                    ccx.tcx.lookup_predicates(local_def(item.id));
                reject_non_type_param_bounds(ccx.tcx, item.span, &trait_predicates);
                if ccx.tcx.trait_has_default_impl(local_def(item.id)) {
                    if !items.is_empty() {
                        span_err!(ccx.tcx.sess, item.span, E0380,
                                  "traits with default impls (`e.g. unsafe impl \
                                  Trait for ..`) must have no methods or associated items")
                    }
                }
            }
            _ => {}
        }
    }

    fn with_fcx<F>(&mut self, item: &ast::Item, mut f: F) where
        F: for<'fcx> FnMut(&FnCtxt<'fcx, 'tcx>) -> Vec<Ty<'tcx>>,
    {
        let ccx = self.ccx;
        let item_def_id = local_def(item.id);
        let type_scheme = ccx.tcx.lookup_item_type(item_def_id);
        let type_predicates = ccx.tcx.lookup_predicates(item_def_id);
        reject_non_type_param_bounds(ccx.tcx, item.span, &type_predicates);
        let param_env = ccx.tcx.construct_parameter_environment(item.span,
                                                                &type_scheme.generics,
                                                                &type_predicates,
                                                                item.id);
        let tables = RefCell::new(ty::Tables::empty());
        let inh = Inherited::new(ccx.tcx, &tables, param_env);
        let fcx = blank_fn_ctxt(ccx, &inh, ty::FnConverging(type_scheme.ty), item.id);
        let wf_tys = f(&fcx);
        fcx.select_all_obligations_or_error();
        regionck::regionck_item(&fcx, item, &wf_tys);
    }

    /// In a type definition, we check that to ensure that the types of the fields are well-formed.
    fn check_type_defn<F>(&mut self, item: &ast::Item, mut lookup_fields: F) where
        F: for<'fcx> FnMut(&FnCtxt<'fcx, 'tcx>) -> Vec<AdtVariant<'tcx>>,
    {
        self.with_fcx(item, |fcx| {
            let variants = lookup_fields(fcx);

            for variant in &variants {
                // For DST, all intermediate types must be sized.
                if let Some((_, fields)) = variant.fields.split_last() {
                    for field in fields {
                        fcx.register_builtin_bound(
                            field.ty,
                            ty::BoundSized,
                            traits::ObligationCause::new(field.span,
                                                         fcx.body_id,
                                                         traits::FieldSized));
                    }
                }

                // All field types must be well-formed.
                for field in &variant.fields {
                    let cause =
                        traits::ObligationCause::new(field.span,
                                                     fcx.body_id,
                                                     traits::MiscObligation);
                    fcx.register_predicate(
                        traits::Obligation::new(cause,
                                                ty::Predicate::WellFormed(field.ty)));
                }
            }

            // TODO WF check where-clauses

            vec![] // no implied bounds in a struct def'n
        });
    }

    fn check_item_type(&mut self,
                       item: &ast::Item)
    {
        debug!("check_item_type: {:?}", item);

        self.with_fcx(item, |fcx| {
            let type_scheme = fcx.tcx().lookup_item_type(local_def(item.id));
            let item_ty = fcx.instantiate_type_scheme(item.span,
                                                      &fcx.inh
                                                          .infcx
                                                          .parameter_environment
                                                          .free_substs,
                                                      &type_scheme.ty);

            fcx.register_wf_obligation(item_ty, item.span);

            vec![] // no implied bounds in a const etc
        });
    }

    fn check_impl(&mut self,
                  item: &ast::Item,
                  ast_self_ty: &ast::Ty,
                  ast_trait_ref: &Option<ast::TraitRef>,
                  impl_items: &[P<ast::ImplItem>])
    {
        debug!("check_impl: {:?}", item);

        self.with_fcx(item, |fcx| {
            let mut implied_bounds = vec![];

            let free_substs = &fcx.inh.infcx.parameter_environment.free_substs;

            // Find the impl self type as seen from the "inside" --
            // that is, with all type parameters converted from bound
            // to free.
            let self_ty = fcx.tcx().node_id_to_type(item.id);
            let self_ty = fcx.instantiate_type_scheme(item.span, free_substs, &self_ty);
            fcx.register_wf_obligation(self_ty, ast_self_ty.span);

            implied_bounds.push(self_ty);

            match *ast_trait_ref {
                Some(ref ast_trait_ref) => {
                    let trait_ref = fcx.tcx().impl_trait_ref(local_def(item.id)).unwrap();
                    let trait_ref =
                        fcx.instantiate_type_scheme(
                            ast_trait_ref.path.span, free_substs, &trait_ref);
                    let obligations =
                        wf::trait_where_clause_obligations(fcx.infcx(), fcx.body_id,
                                                           trait_ref, ast_trait_ref.path.span);
                    for obligation in obligations {
                        fcx.register_predicate(obligation);
                    }
                    for &ty in trait_ref.substs.types.get_slice(TypeSpace) {
                        fcx.register_wf_obligation(ty, ast_trait_ref.path.span);
                        implied_bounds.push(ty);
                    }
                }
                None => { }
            }

            // TODO WF check where-clauses

            // go over the items defined in the impl and check that they, too, are well-formed
            for impl_item in impl_items {
                match fcx.tcx().impl_or_trait_item(local_def(impl_item.id)) {
                    ty::ConstTraitItem(assoc_const) => {
                        let ty = fcx.instantiate_type_scheme(impl_item.span,
                                                             free_substs,
                                                             &assoc_const.ty);
                        fcx.register_wf_obligation(ty, impl_item.span);
                    }
                    ty::MethodTraitItem(_) =>
                        (), // TODO handle methods
                    ty::TypeTraitItem(assoc_type) => {
                        let ty = fcx.instantiate_type_scheme(impl_item.span,
                                                             free_substs,
                                                             &assoc_type.ty);
                        fcx.register_wf_obligation(ty.unwrap(), impl_item.span);
                    }
                }
            }

            // impls can assume that self + types appearing in a trait
            // reference are well-formed whenever something is
            // projected out
            implied_bounds
        });
    }

    fn check_variances_for_type_defn(&self,
                                     item: &ast::Item,
                                     ast_generics: &ast::Generics)
    {
        let item_def_id = local_def(item.id);
        let ty_predicates = self.tcx().lookup_predicates(item_def_id);
        let variances = self.tcx().item_variances(item_def_id);

        let mut constrained_parameters: HashSet<_> =
            variances.types
                     .iter_enumerated()
                     .filter(|&(_, _, &variance)| variance != ty::Bivariant)
                     .map(|(space, index, _)| self.param_ty(ast_generics, space, index))
                     .map(|p| Parameter::Type(p))
                     .collect();

        identify_constrained_type_params(self.tcx(),
                                         ty_predicates.predicates.as_slice(),
                                         None,
                                         &mut constrained_parameters);

        for (space, index, _) in variances.types.iter_enumerated() {
            let param_ty = self.param_ty(ast_generics, space, index);
            if constrained_parameters.contains(&Parameter::Type(param_ty)) {
                continue;
            }
            let span = self.ty_param_span(ast_generics, item, space, index);
            self.report_bivariance(span, param_ty.name);
        }

        for (space, index, &variance) in variances.regions.iter_enumerated() {
            if variance != ty::Bivariant {
                continue;
            }

            assert_eq!(space, TypeSpace);
            let span = ast_generics.lifetimes[index].lifetime.span;
            let name = ast_generics.lifetimes[index].lifetime.name;
            self.report_bivariance(span, name);
        }
    }

    fn param_ty(&self,
                ast_generics: &ast::Generics,
                space: ParamSpace,
                index: usize)
                -> ty::ParamTy
    {
        let name = match space {
            TypeSpace => ast_generics.ty_params[index].ident.name,
            SelfSpace => special_idents::type_self.name,
            FnSpace => self.tcx().sess.bug("Fn space occupied?"),
        };

        ty::ParamTy { space: space, idx: index as u32, name: name }
    }

    fn ty_param_span(&self,
                     ast_generics: &ast::Generics,
                     item: &ast::Item,
                     space: ParamSpace,
                     index: usize)
                     -> Span
    {
        match space {
            TypeSpace => ast_generics.ty_params[index].span,
            SelfSpace => item.span,
            FnSpace => self.tcx().sess.span_bug(item.span, "Fn space occupied?"),
        }
    }

    fn report_bivariance(&self,
                         span: Span,
                         param_name: ast::Name)
    {
        span_err!(self.tcx().sess, span, E0392,
            "parameter `{}` is never used", param_name);

        let suggested_marker_id = self.tcx().lang_items.phantom_data();
        match suggested_marker_id {
            Some(def_id) => {
                self.tcx().sess.fileline_help(
                    span,
                    &format!("consider removing `{}` or using a marker such as `{}`",
                             param_name,
                             self.tcx().item_path_str(def_id)));
            }
            None => {
                // no lang items, no help!
            }
        }
    }
}

// Reject any predicates that do not involve a type parameter.
fn reject_non_type_param_bounds<'tcx>(tcx: &ty::ctxt<'tcx>,
                                      span: Span,
                                      predicates: &ty::GenericPredicates<'tcx>) {
    for predicate in &predicates.predicates {
        match predicate {
            &ty::Predicate::Trait(ty::Binder(ref tr)) => {
                let found_param = tr.input_types().iter()
                                    .flat_map(|ty| ty.walk())
                                    .any(is_ty_param);
                if !found_param { report_bound_error(tcx, span, tr.self_ty() )}
            }
            &ty::Predicate::TypeOutlives(ty::Binder(ty::OutlivesPredicate(ty, _))) => {
                let found_param = ty.walk().any(|t| is_ty_param(t));
                if !found_param { report_bound_error(tcx, span, ty) }
            }
            _ => {}
        };
    }

    fn report_bound_error<'t>(tcx: &ty::ctxt<'t>,
                          span: Span,
                          bounded_ty: ty::Ty<'t>) {
        span_err!(tcx.sess, span, E0193,
            "cannot bound type `{}`, where clause \
                bounds may only be attached to types involving \
                type parameters",
                bounded_ty)
    }

    fn is_ty_param(ty: ty::Ty) -> bool {
        match &ty.sty {
            &ty::TyParam(_) => true,
            _ => false
        }
    }
}

fn reject_shadowing_type_parameters<'tcx>(tcx: &ty::ctxt<'tcx>,
                                          span: Span,
                                          generics: &ty::Generics<'tcx>) {
    let impl_params = generics.types.get_slice(subst::TypeSpace).iter()
        .map(|tp| tp.name).collect::<HashSet<_>>();

    for method_param in generics.types.get_slice(subst::FnSpace) {
        if impl_params.contains(&method_param.name) {
            span_err!(tcx.sess, span, E0194,
                "type parameter `{}` shadows another type parameter of the same name",
                          method_param.name);
        }
    }
}

impl<'ccx, 'tcx, 'v> Visitor<'v> for CheckTypeWellFormedVisitor<'ccx, 'tcx> {
    fn visit_item(&mut self, i: &ast::Item) {
        self.check_item_well_formed(i);
        visit::walk_item(self, i);
    }

    fn visit_fn(&mut self,
                fk: visit::FnKind<'v>, fd: &'v ast::FnDecl,
                b: &'v ast::Block, span: Span, id: ast::NodeId) {

        // TODO with implied region bounds, of course:
        // TODO check argument types
        // TODO check return type
        // TODO check where-clauses
        // TODO check types in fn body? probably leave that to check/mod...?

        match fk {
            visit::FkFnBlock | visit::FkItemFn(..) => {}
            visit::FkMethod(..) => {
                match self.tcx().impl_or_trait_item(local_def(id)) {
                    ty::ImplOrTraitItem::MethodTraitItem(ty_method) => {
                        reject_shadowing_type_parameters(self.tcx(), span, &ty_method.generics)
                    }
                    _ => {}
                }
            }
        }
        visit::walk_fn(self, fk, fd, b, span)
    }

    fn visit_trait_item(&mut self, trait_item: &'v ast::TraitItem) {
        if let ast::MethodTraitItem(_, None) = trait_item.node {
            match self.tcx().impl_or_trait_item(local_def(trait_item.id)) {
                ty::ImplOrTraitItem::MethodTraitItem(ty_method) => {
                    reject_non_type_param_bounds(
                        self.tcx(),
                        trait_item.span,
                        &ty_method.predicates);
                    reject_shadowing_type_parameters(
                        self.tcx(),
                        trait_item.span,
                        &ty_method.generics);
                }
                _ => {}
            }
        }

        visit::walk_trait_item(self, trait_item)
    }
}

///////////////////////////////////////////////////////////////////////////
// ADT

struct AdtVariant<'tcx> {
    fields: Vec<AdtField<'tcx>>,
}

struct AdtField<'tcx> {
    ty: Ty<'tcx>,
    span: Span,
}

fn struct_variant<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                            struct_def: &ast::StructDef)
                            -> AdtVariant<'tcx> {
    let fields =
        struct_def.fields
        .iter()
        .map(|field| {
            let field_ty = fcx.tcx().node_id_to_type(field.node.id);
            let field_ty = fcx.instantiate_type_scheme(field.span,
                                                       &fcx.inh
                                                           .infcx
                                                           .parameter_environment
                                                           .free_substs,
                                                       &field_ty);
            AdtField { ty: field_ty, span: field.span }
        })
        .collect();
    AdtVariant { fields: fields }
}

fn enum_variants<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>,
                           enum_def: &ast::EnumDef)
                           -> Vec<AdtVariant<'tcx>> {
    enum_def.variants.iter()
        .map(|variant| {
            match variant.node.kind {
                ast::TupleVariantKind(ref args) if !args.is_empty() => {
                    let ctor_ty = fcx.tcx().node_id_to_type(variant.node.id);

                    // the regions in the argument types come from the
                    // enum def'n, and hence will all be early bound
                    let arg_tys = fcx.tcx().no_late_bound_regions(&ctor_ty.fn_args()).unwrap();
                    AdtVariant {
                        fields: args.iter().enumerate().map(|(index, arg)| {
                            let arg_ty = arg_tys[index];
                            let arg_ty =
                                fcx.instantiate_type_scheme(variant.span,
                                                            &fcx.inh
                                                                .infcx
                                                                .parameter_environment
                                                                .free_substs,
                                                            &arg_ty);
                            AdtField {
                                ty: arg_ty,
                                span: arg.ty.span
                            }
                        }).collect()
                    }
                }
                ast::TupleVariantKind(_) => {
                    AdtVariant {
                        fields: Vec::new()
                    }
                }
                ast::StructVariantKind(ref struct_def) => {
                    struct_variant(fcx, &**struct_def)
                }
            }
        })
        .collect()
}
