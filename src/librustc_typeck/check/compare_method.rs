// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::infer;
use middle::traits;
use middle::ty::{mod};
use middle::subst::{mod, Subst};
use util::ppaux::{mod, Repr};

use syntax::ast;
use syntax::codemap::{Span};
use syntax::parse::token;

/// Checks that a method from an impl conforms to the signature of
/// the same method as declared in the trait.
///
/// # Parameters
///
/// - impl_m: type of the method we are checking
/// - impl_m_span: span to use for reporting errors
/// - impl_m_body_id: id of the method body
/// - trait_m: the method in the trait
/// - impl_trait_ref: the TraitRef corresponding to the trait implementation

pub fn compare_impl_method<'tcx>(tcx: &ty::ctxt<'tcx>,
                                 impl_m: &ty::Method<'tcx>,
                                 impl_m_span: Span,
                                 impl_m_body_id: ast::NodeId,
                                 trait_m: &ty::Method<'tcx>,
                                 impl_trait_ref: &ty::TraitRef<'tcx>) {
    debug!("compare_impl_method(impl_trait_ref={})",
           impl_trait_ref.repr(tcx));

    debug!("impl_trait_ref (liberated) = {}",
           impl_trait_ref.repr(tcx));

    let infcx = infer::new_infer_ctxt(tcx);

    let trait_to_impl_substs = &impl_trait_ref.substs;

    // Try to give more informative error messages about self typing
    // mismatches.  Note that any mismatch will also be detected
    // below, where we construct a canonical function type that
    // includes the self parameter as a normal parameter.  It's just
    // that the error messages you get out of this code are a bit more
    // inscrutable, particularly for cases where one method has no
    // self.
    match (&trait_m.explicit_self, &impl_m.explicit_self) {
        (&ty::StaticExplicitSelfCategory,
         &ty::StaticExplicitSelfCategory) => {}
        (&ty::StaticExplicitSelfCategory, _) => {
            tcx.sess.span_err(
                impl_m_span,
                format!("method `{}` has a `{}` declaration in the impl, \
                        but not in the trait",
                        token::get_name(trait_m.name),
                        ppaux::explicit_self_category_to_str(
                            &impl_m.explicit_self)).as_slice());
            return;
        }
        (_, &ty::StaticExplicitSelfCategory) => {
            tcx.sess.span_err(
                impl_m_span,
                format!("method `{}` has a `{}` declaration in the trait, \
                        but not in the impl",
                        token::get_name(trait_m.name),
                        ppaux::explicit_self_category_to_str(
                            &trait_m.explicit_self)).as_slice());
            return;
        }
        _ => {
            // Let the type checker catch other errors below
        }
    }

    let num_impl_m_type_params = impl_m.generics.types.len(subst::FnSpace);
    let num_trait_m_type_params = trait_m.generics.types.len(subst::FnSpace);
    if num_impl_m_type_params != num_trait_m_type_params {
        span_err!(tcx.sess, impl_m_span, E0049,
            "method `{}` has {} type parameter{} \
             but its trait declaration has {} type parameter{}",
            token::get_name(trait_m.name),
            num_impl_m_type_params,
            if num_impl_m_type_params == 1 {""} else {"s"},
            num_trait_m_type_params,
            if num_trait_m_type_params == 1 {""} else {"s"});
        return;
    }

    if impl_m.fty.sig.0.inputs.len() != trait_m.fty.sig.0.inputs.len() {
        span_err!(tcx.sess, impl_m_span, E0050,
            "method `{}` has {} parameter{} \
             but the declaration in trait `{}` has {}",
            token::get_name(trait_m.name),
            impl_m.fty.sig.0.inputs.len(),
            if impl_m.fty.sig.0.inputs.len() == 1 {""} else {"s"},
            ty::item_path_str(tcx, trait_m.def_id),
            trait_m.fty.sig.0.inputs.len());
        return;
    }

    // This code is best explained by example. Consider a trait:
    //
    //     trait Trait<'t,T> {
    //          fn method<'a,M>(t: &'t T, m: &'a M) -> Self;
    //     }
    //
    // And an impl:
    //
    //     impl<'i, 'j, U> Trait<'j, &'i U> for Foo {
    //          fn method<'b,N>(t: &'j &'i U, m: &'b N) -> Foo;
    //     }
    //
    // We wish to decide if those two method types are compatible.
    //
    // We start out with trait_to_impl_substs, that maps the trait
    // type parameters to impl type parameters. This is taken from the
    // impl trait reference:
    //
    //     trait_to_impl_substs = {'t => 'j, T => &'i U, Self => Foo}
    //
    // We create a mapping `dummy_substs` that maps from the impl type
    // parameters to fresh types and regions. For type parameters,
    // this is the identity transform, but we could as well use any
    // skolemized types. For regions, we convert from bound to free
    // regions (Note: but only early-bound regions, i.e., those
    // declared on the impl or used in type parameter bounds).
    //
    //     impl_to_skol_substs = {'i => 'i0, U => U0, N => N0 }
    //
    // Now we can apply skol_substs to the type of the impl method
    // to yield a new function type in terms of our fresh, skolemized
    // types:
    //
    //     <'b> fn(t: &'i0 U0, m: &'b) -> Foo
    //
    // We now want to extract and substitute the type of the *trait*
    // method and compare it. To do so, we must create a compound
    // substitution by combining trait_to_impl_substs and
    // impl_to_skol_substs, and also adding a mapping for the method
    // type parameters. We extend the mapping to also include
    // the method parameters.
    //
    //     trait_to_skol_substs = { T => &'i0 U0, Self => Foo, M => N0 }
    //
    // Applying this to the trait method type yields:
    //
    //     <'a> fn(t: &'i0 U0, m: &'a) -> Foo
    //
    // This type is also the same but the name of the bound region ('a
    // vs 'b).  However, the normal subtyping rules on fn types handle
    // this kind of equivalency just fine.
    //
    // We now use these subsititions to ensure that all declared bounds are
    // satisfied by the implementation's method.
    //
    // We do this by creating a parameter environment which contains a
    // substition corresponding to impl_to_skol_substs. We then build
    // trait_to_skol_substs and use it to convert the predicates contained
    // in the trait_m.generics to the skolemized form.
    //
    // Finally we register each of these predicates as an obligation in
    // a fresh FulfillmentCtxt, and invoke select_all_or_error.
    //
    // FIXME(jroesch): Currently the error reporting is not correctly attached
    // to a span and results in terrible error reporting.

    // Create a parameter environment that represents the implementation's
    // method.
    let impl_env = ty::ParameterEnvironment::for_item(tcx, impl_m.def_id.node);

    // Create mapping from impl to skolemized.
    let impl_to_skol_substs = &impl_env.free_substs;

    // Create mapping from trait to skolemized.
    let trait_to_skol_substs =
        trait_to_impl_substs
        .subst(tcx, impl_to_skol_substs)
        .with_method(impl_to_skol_substs.types.get_slice(subst::FnSpace).to_vec(),
                     impl_to_skol_substs.regions().get_slice(subst::FnSpace).to_vec());
    debug!("compare_impl_method: trait_to_skol_substs={}",
           trait_to_skol_substs.repr(tcx));

    // Construct trait parameter environment and then shift it into the skolemized viewpoint.
    let trait_param_env =
        ty::construct_parameter_environment(tcx,
                                            &trait_m.generics,
                                            impl_m_body_id);
    let trait_param_env =
        trait_param_env.subst(tcx, &trait_to_skol_substs);
    debug!("compare_impl_method: trait_param_env={}",
           trait_param_env.repr(tcx));

    // Create a fresh fulfillment context.
    let mut fulfill_cx = traits::FulfillmentContext::new();

    // Create obligations for each predicate declared by the impl
    // definition in the context of the trait's parameter
    // environment. We can't just use `impl_env.caller_bounds`,
    // however, because we want to replace all late-bound regions with
    // region variables.
    let impl_bounds =
        impl_m.generics.to_bounds(tcx, impl_to_skol_substs);
    let (impl_bounds, _) =
        infcx.replace_late_bound_regions_with_fresh_var(
            impl_m_span,
            infer::HigherRankedType,
            &ty::Binder(impl_bounds)); // TODO I think this is right?
    debug!("compare_impl_method: impl_bounds={}",
           impl_bounds.repr(tcx));
    for predicate in impl_bounds.predicates.into_iter() {
        fulfill_cx.register_predicate(
            tcx,
            traits::Obligation::new(traits::ObligationCause::dummy(),
                                    predicate));
    }

    // Check that all obligations are satisfied by the implementation's
    // version.
    match fulfill_cx.select_all_or_error(&infcx, &trait_param_env, tcx) {
        Err(ref errors) => { traits::report_fulfillment_errors(&infcx, errors) }
        Ok(_) => {}
    }

    // Compute skolemized form of impl and trait method tys.
    let impl_fty = ty::mk_bare_fn(tcx, None, impl_m.fty.clone());
    let impl_fty = impl_fty.subst(tcx, impl_to_skol_substs);
    let trait_fty = ty::mk_bare_fn(tcx, None, trait_m.fty.clone());
    let trait_fty = trait_fty.subst(tcx, &trait_to_skol_substs);

    // Check the impl method type IM is a subtype of the trait method
    // type TM. To see why this makes sense, think of a vtable. The
    // expected type of the function pointers in the vtable is the
    // type TM of the trait method.  The actual type will be the type
    // IM of the impl method. Because we know that IM <: TM, that
    // means that anywhere a TM is expected, a IM will do instead. In
    // other words, anyone expecting to call a method with the type
    // from the trait, can safely call a method with the type from the
    // impl instead.
    debug!("checking trait method for compatibility: impl ty {}, trait ty {}",
           impl_fty.repr(tcx),
           trait_fty.repr(tcx));
    match infer::mk_subty(&infcx, false, infer::MethodCompatCheck(impl_m_span),
                          impl_fty, trait_fty) {
        Ok(()) => {}
        Err(ref terr) => {
            span_err!(tcx.sess, impl_m_span, E0053,
                "method `{}` has an incompatible type for trait: {}",
                token::get_name(trait_m.name),
                ty::type_err_to_str(tcx, terr));
            ty::note_and_explain_type_err(tcx, terr);
        }
    }

    // Finally, resolve all regions. This catches wily misuses of lifetime
    // parameters.
    infcx.resolve_regions_and_report_errors(impl_m_body_id);
}
