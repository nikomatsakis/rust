// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use infer::InferCtxt;
use hir::def_id::DefId;
use ty::{self, CanonicalVar, Ty, TyCtxt};
use ty::fold::{TypeFoldable, TypeFolder};

use rustc_data_structures::indexed_vec::IndexVec;
use rustc_data_structures::fx::FxHashMap;

/// A "canonicalized" type `V` is one where all free inference
/// variables have been rewriten to "canonical vars". These are
/// numbered starting from 0 in order of first appearance.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Canonical<V> {
    pub variables: IndexVec<CanonicalVar, CanonicalVarInfo>,
    pub value: V,
}

/// When you canonicalize a value `V`, you get back a `Canonical<V>`
/// formed by replacing unbound inference variables and things with
/// `CanonicalVar`. This struct maps those canonical variables back to
/// the things that were removed; with it, you can reconstruct the
/// original `V`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalVarValues<'tcx> {
    pub var_values: IndexVec<CanonicalVar, CanonicalVarValue<'tcx>>,
}

/// After you canonicalize, we also return some extra information
/// about closures and generators, for example what `Fn` traits a
/// closure implements (if it has been inferred thus far). This
/// information is needed by the trait checker and becomes part of the
/// query environment. They are effectively "extra facts".
pub struct CanonicalClosureFacts<'tcx> {
    pub closure_kinds: FxHashMap<DefId, ty::ClosureKind>,
    pub generator_sigs: FxHashMap<DefId, ty::PolyGenSig<'tcx>>,
}

/// Information about a canonical variable that is included with the
/// canonical value. This is sufficient information for code to create
/// a copy of the canonical value in some other inference context,
/// with fresh inference variables replacing the canonical values.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalVarInfo {
    pub kind: CanonicalVarKind,
    pub universe: ty::UniverseIndex,
}

/// Describes the "kind" of the canonical variable. This is a "kind"
/// in the type-theory sense of the term -- i.e., a "meta" type system
/// that analyzes type-like values.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CanonicalVarKind {
    /// Some kind of type inference variable.
    Ty(CanonicalTyVarKind),

    /// Region variable `'?R`.
    Region,
}

/// Rust actually has more than one category of type variables;
/// notably, the type variables we create for literals (e.g., 22 or
/// 22.) can only be instantiated with integral/float types (e.g.,
/// usize or f32). In order to faithfully reproduce a type, we need to
/// know what set of types a given type variable can be unified with.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CanonicalTyVarKind {
    /// General type variable `?T` that can be unified with arbitrary types.
    General,

    /// Integral type variable `?I` (that can only be unified with integral types).
    Int,

    /// Floating-point type variable `?F` (that can only be unified with float types).
    Float,
}

/// The value for a canonical variable.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CanonicalVarValue<'tcx> {
    /// Value from a Type/Int/Float type-variable `?T`.
    Ty(Ty<'tcx>),

    /// Region variable `'?R`.
    Region(ty::Region<'tcx>),
}

impl<'cx, 'gcx, 'tcx> InferCtxt<'cx, 'gcx, 'tcx> {
    pub fn canonicalize<V>(&self, value: &V) -> (Canonical<V>,
                                                 CanonicalClosureFacts<'tcx>,
                                                 CanonicalVarValues<'tcx>)
    where
        V: TypeFoldable<'tcx>,
    {
        let mut canonicalizer = Canonicalizer {
            infcx: self,
            variables: IndexVec::default(),
            indices: FxHashMap::default(),
            var_values: IndexVec::default(),
            closure_kinds: FxHashMap::default(),
            generator_sigs: FxHashMap::default(),
        };
        let out_value = value.fold_with(&mut canonicalizer);
        let canonical_value = Canonical {
            variables: canonicalizer.variables,
            value: out_value,
        };
        let canonical_closure_facts = CanonicalClosureFacts {
            closure_kinds: canonicalizer.closure_kinds,
            generator_sigs: canonicalizer.generator_sigs,
        };
        let canonical_var_values = CanonicalVarValues {
            var_values: canonicalizer.var_values,
        };
        (canonical_value, canonical_closure_facts, canonical_var_values)
    }
}

struct Canonicalizer<'cx, 'gcx: 'tcx, 'tcx: 'cx> {
    infcx: &'cx InferCtxt<'cx, 'gcx, 'tcx>,
    variables: IndexVec<CanonicalVar, CanonicalVarInfo>,
    indices: FxHashMap<CanonicalVarValue<'tcx>, CanonicalVar>,
    var_values: IndexVec<CanonicalVar, CanonicalVarValue<'tcx>>,
    closure_kinds: FxHashMap<DefId, ty::ClosureKind>,
    generator_sigs: FxHashMap<DefId, ty::PolyGenSig<'tcx>>,
}

impl<'cx, 'gcx, 'tcx> TypeFolder<'gcx, 'tcx> for Canonicalizer<'cx, 'gcx, 'tcx> {
    fn tcx<'b>(&'b self) -> TyCtxt<'b, 'gcx, 'tcx> {
        self.infcx.tcx
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        match *r {
            ty::ReLateBound(..) => {
                // leave bound regions alone
                r
            }

            ty::ReStatic |
            ty::ReEarlyBound(..) |
            ty::ReFree(_) |
            ty::ReScope(_) |
            ty::ReVar(_) |
            ty::ReSkolemized(..) |
            ty::ReEmpty |
            ty::ReErased => {
                // replace all free regions with 'erased
                let info = CanonicalVarInfo {
                    kind: CanonicalVarKind::Region,
                    universe: ty::UniverseIndex::ROOT, // TODO
                };
                let cvar = self.canonical_var(info, CanonicalVarValue::Region(r));
                self.tcx().mk_region(ty::ReCanonical(cvar))
            }

            ty::ReCanonical(_) => {
                bug!("canonical region encountered during canonicalization")
            }
        }
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        if !t.needs_infer() && !t.has_erasable_regions()
            && !(t.has_closure_types() && self.infcx.in_progress_tables.is_some())
        {
            return t;
        }

        match t.sty {
            ty::TyInfer(ty::TyVar(_)) => {
                self.canonicalize_ty_var(
                    CanonicalTyVarKind::General,
                    ty::UniverseIndex::ROOT, // TODO
                    t,
                )
            }

            ty::TyInfer(ty::IntVar(_)) => {
                self.canonicalize_ty_var(
                    CanonicalTyVarKind::Int,
                    ty::UniverseIndex::ROOT, // TODO
                    t,
                )
            }

            ty::TyInfer(ty::FloatVar(_)) => {
                self.canonicalize_ty_var(
                    CanonicalTyVarKind::Float,
                    ty::UniverseIndex::ROOT, // TODO
                    t,
                )
            }

            ty::TyInfer(ty::FreshTy(_)) |
            ty::TyInfer(ty::FreshIntTy(_)) |
            ty::TyInfer(ty::FreshFloatTy(_)) => {
                bug!("encountered a fresh type during canonicalization")
            }

            ty::TyInfer(ty::CanonicalTy(_)) => {
                bug!("encountered a canonical type during canonicalization")
            }

            ty::TyClosure(def_id, ..) => {
                if let Some(kind) = self.infcx.closure_kind(def_id) {
                    self.closure_kinds.insert(def_id, kind);
                }
                t.super_fold_with(self)
            }

            ty::TyGenerator(def_id, ..) => {
                if let Some(gen_sig) = self.infcx.generator_sig(def_id) {
                    self.generator_sigs.insert(def_id, gen_sig);
                }
                t.super_fold_with(self)
            }

            ty::TyBool |
            ty::TyChar |
            ty::TyInt(..) |
            ty::TyUint(..) |
            ty::TyFloat(..) |
            ty::TyAdt(..) |
            ty::TyStr |
            ty::TyError |
            ty::TyArray(..) |
            ty::TySlice(..) |
            ty::TyRawPtr(..) |
            ty::TyRef(..) |
            ty::TyFnDef(..) |
            ty::TyFnPtr(_) |
            ty::TyDynamic(..) |
            ty::TyNever |
            ty::TyTuple(..) |
            ty::TyProjection(..) |
            ty::TyForeign(..) |
            ty::TyParam(..) |
            ty::TyAnon(..) => t.super_fold_with(self),
        }
    }
}

impl<'cx, 'gcx, 'tcx> Canonicalizer<'cx, 'gcx, 'tcx> {
    fn canonical_var(
        &mut self,
        info: CanonicalVarInfo,
        cvv: CanonicalVarValue<'tcx>,
    ) -> CanonicalVar {
        let Canonicalizer {
            indices,
            variables,
            var_values,
            ..
        } = self;

        indices
            .entry(cvv)
            .or_insert_with(|| {
                let cvar1 = variables.push(info);
                let cvar2 = var_values.push(cvv);
                assert_eq!(cvar1, cvar2);
                cvar1
            })
            .clone()
    }

    fn canonicalize_ty_var(
        &mut self,
        ty_kind: CanonicalTyVarKind,
        universe: ty::UniverseIndex,
        ty_var: Ty<'tcx>,
    ) -> Ty<'tcx> {
        let bound_to = self.infcx.shallow_resolve(ty_var);
        if bound_to != ty_var {
            self.fold_ty(bound_to)
        } else {
            let info = CanonicalVarInfo {
                kind: CanonicalVarKind::Ty(ty_kind),
                universe,
            };
            let cvar = self.canonical_var(info, CanonicalVarValue::Ty(ty_var));
            self.tcx().mk_infer(ty::InferTy::CanonicalTy(cvar))
        }
    }
}
