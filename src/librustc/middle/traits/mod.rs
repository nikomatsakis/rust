// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
 * Trait Resolution. See doc.rs.
 */

use middle::subst;
use middle::ty;
use middle::typeck::infer::InferCtxt;
use std::rc::Rc;
use syntax::ast;
use syntax::codemap::Span;

pub use self::util::Supertraits;
pub use self::util::supertraits;

mod coherence;
mod resolve;
mod util;

/**
 * An `Obligation` represents the requirement to eventually find an
 * implementation for a given trait reference. The `resolution` field
 * remains unfulfilled so long as there is insufficient type
 * information to make a decision. Once sufficient type information is
 * available, resolution should always be possible, though this may
 * not be the case if there are overlapping impls (however, the
 * coherence check should detect such cases).
 */
#[deriving(Clone)]
pub struct Obligation {
    pub span: Span,
    pub recursion_depth: uint,
    pub trait_ref: Rc<ty::TraitRef>,
}

pub type Obligations = subst::VecPerParamSpace<Obligation>;

/**
 * The eventual resolution to an obligation.
 */
#[deriving(Show,Clone)]
pub enum Resolution<R> {
    /// Successful resolution: found an impl.
    ResolvedTo(R),

    /// No implementation exists (or could exist).
    ResolvedToUnimpl,

    /// Unable to determine whether an implementation exists or not;
    /// recursion depth exceeded.
    ResolvedToOverflow,
}

pub type VtableOriginResolution = Resolution<VtableOrigin>;

/**
 * Given the successful resolution of an obligation, the
 * `VtableOrigin` indicates where the vtable comes from.
 *
 * For example, the vtable may be tied to a specific impl (case A),
 * or it may be relative to some bound that is in scope (case B).
 *
 *
 * ```
 * impl<T:Clone> Clone<T> for Option<T> { ... } // Impl_1
 * impl<T:Clone> Clone<T> for Box<T> { ... }    // Impl_2
 * impl Clone for int { ... }             // Impl_3
 *
 * fn foo<T:Clone>(concrete: Option<Box<int>>,
 *                 param: T,
 *                 mixed: Option<T>) {
 *
 *    // Case A: Vtable points at a specific impl. Only possible when
 *    // type is concretely known. If the impl itself has bounded
 *    // type parameters, Vtable will carry resolutions for those as well:
 *    concrete.clone(); // Vtable(Impl_1, [Vtable(Impl_2, [Vtable(Impl_3)])])
 *
 *    // Case B: Vtable must be provided by caller. This applies when
 *    // type is a type parameter.
 *    param.clone();    // VtableParam(Oblig_1)
 *
 *    // Case C: A mix of cases A and B.
 *    mixed.clone();    // Vtable(Impl_1, [VtableParam(Oblig_1)])
 * }
 *
 */
#[deriving(Show,Clone)]
pub enum VtableOrigin {
    /// Successful resolution to a particular impl with particular
    /// substitutions applied (aka, a vtable).
    ///
    /// Perhaps surprisingly, successful resolution can still yield
    /// type errors. This occurs when the output type parameters
    /// given in the obligation don't match what the impl requires;
    /// for example, an obligation like `Iterator<uint> for Vec<int>`
    /// would resolve, but yield a type error because `uint != int`.
    ///
    /// Because resolution is run speculatively, these type errors are
    /// not reported but rather recorded. If the resolution winds up
    /// being committed, the caller is responsible for reporting the
    /// type error eventually.
    Vtable(Vtable, Option<ty::type_err>),

    // Vtable automatically generated for an unboxed closure. The def
    // ID is the ID of the closure expression.
    VtableUnboxedClosure(ast::DefId),

    /// Successful resolution for a builtin trait.
    VtableParam(VtableParam, Option<ty::type_err>),

    /// Successful resolution for a builtin trait.
    Builtin,
}

pub type VtableOrigins = subst::VecPerParamSpace<VtableOrigin>;

/**
 * Identifiers a particular impl in the source, along with a set of
 * substitutions from the impl's type/lifetime parameters.
 *
 * The `obligations` vector identifiers a nested set of obligations.
 */
#[deriving(Clone)]
pub struct Vtable {
    pub impl_def_id: ast::DefId,
    pub substs: subst::Substs,
    pub origins: VtableOrigins,
}

/**
 * A vtable provided as a parameter by the caller. For example, in a
 * function like `fn foo<T:Eq>(...)`, if the `eq()` method is invoked
 * on an instance of `T`, the vtable would be of type `VtableParam`.
 */
#[deriving(Clone)]
pub struct VtableParam {
    // In the above example, this would `Eq`
    pub bound: Rc<ty::TraitRef>,
    pub path: VtablePath,
}

/**
 * A path through the obligation tree for the function. See `doc.rs`.
 */
#[deriving(Show,Clone,Encodable,Decodable)]
pub struct VtablePath {
    pub space: subst::ParamSpace,
    pub obligation: uint,
    pub supertraits: Vec<uint>,
}

#[deriving(PartialEq,Eq,Show)]
pub enum ImplEvaluation {
    DefinitelyApplicable,
    MaybeApplicable,
    NotApplicable,
    Overflow
}

pub fn try_resolve_obligation(infcx: &InferCtxt,
                              param_env: &ty::ParameterEnvironment,
                              obligation: &Obligation)
                              -> Option<Resolution<VtableOrigin>>
{
    /*!
     * Attempts to resolve the obligation given. Returns `None` if
     * we are unable to resolve, either because of ambiguity or
     * due to insufficient inference.
     */

    let rcx = resolve::ResolutionContext::new(infcx, param_env);
    infcx.commit(|| rcx.try_resolve_obligation(obligation))
}

pub fn evaluate_obligation(infcx: &InferCtxt,
                           param_env: &ty::ParameterEnvironment,
                           obligation: &Obligation)
                           -> ImplEvaluation
{
    /*!
     * Attempts to resolve the obligation given. Returns `None` if
     * we are unable to resolve, either because of ambiguity or
     * due to insufficient inference.
     */

    let rcx = resolve::ResolutionContext::new(infcx, param_env);
    rcx.evaluate_obligation(obligation).to_impl_evaluation()
}

pub fn evaluate_impl(infcx: &InferCtxt,
                     param_env: &ty::ParameterEnvironment,
                     span: Span,
                     impl_def_id: ast::DefId,
                     self_ty: ty::t)
                     -> ImplEvaluation
{
    /*!
     * Attempts to resolve *all* the obligations given. If *all* are
     * successful, returns success. Otherwise:
     * - If any overflow, returns overflow.
     * - If any are known not to be implemented,
     * - Otherwise, at least one is not known to succ or not, returns None.
     */

    let rcx = resolve::ResolutionContext::new(infcx, param_env);
    rcx.evaluate_impl(impl_def_id, span, 0, self_ty)
}

pub fn match_inherent_impl(infcx: &InferCtxt,
                           param_env: &ty::ParameterEnvironment,
                           span: Span,
                           impl_def_id: ast::DefId,
                           self_ty: ty::t)
                           -> Option<Resolution<Vtable>>
{
    /*!
     * Matches the self type of the inherent impl `impl_def_id`
     * against `self_ty` and returns the resulting resolution.
     * This routine modifies the surrounding type context (for
     * example, it may unify variables).
     */

    // This routine is only suitable for inherent impls. This is
    // because it does not attempt to unify the output type parameters
    // from the trait ref against the values from the obligation.
    // (These things do not apply to inherent impls, for which there
    // is no trait ref nor obligation.)
    //
    // Matching against non-inherent impls should be done with
    // `try_resolve_obligation()`.
    assert!(ty::impl_trait_ref(infcx.tcx, impl_def_id).is_none());

    let rcx = resolve::ResolutionContext::new(infcx, param_env);
    rcx.match_impl(impl_def_id, span, 0, self_ty)
}

pub fn is_orphan_impl(tcx: &ty::ctxt,
                      impl_def_id: ast::DefId)
                      -> bool
{
    /*!
     * True if neither the trait nor self type is local.
     */
    !coherence::impl_is_local(tcx, impl_def_id)
}

pub fn overlapping_impls(infcx: &InferCtxt,
                         impl1_def_id: ast::DefId,
                         impl2_def_id: ast::DefId)
                         -> bool
{
    /*!
     * True if there exist types that satisfy both of the two given impls.
     */
    coherence::impl_can_satisfy(infcx, impl1_def_id, impl2_def_id) &&
    coherence::impl_can_satisfy(infcx, impl2_def_id, impl1_def_id)
}

pub fn obligations_for_generics(tcx: &ty::ctxt,
                                span: Span,
                                generics: &ty::Generics,
                                substs: &subst::Substs)
                                -> subst::VecPerParamSpace<Obligation>
{
    /*!
     * Given a set of generic parameter definitions `generics`, along
     * with an appropriate set of substitutions, returns
     */

    util::obligations(tcx, span, 0, generics, substs)
}

impl Obligation {
    pub fn new(span: Span, trait_ref: Rc<ty::TraitRef>) -> Obligation {
        Obligation { span: span,
                     recursion_depth: 0,
                     trait_ref: trait_ref }
    }

    pub fn self_ty(&self) -> ty::t {
        self.trait_ref.self_ty()
    }
}

impl ImplEvaluation {
    pub fn potentially_applicable(self) -> bool {
        match self {
            DefinitelyApplicable => true,
            MaybeApplicable => true,
            NotApplicable => false,
            Overflow => true
        }
    }
}

trait ToImplEvaluation {
    fn to_impl_evaluation(&self) -> ImplEvaluation;
}
