// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! New recursive solver modeled on Chalk's recursive solver. Most of
//! the guts are broken up into modules; see the comments in those modules.

#![feature(match_default_bindings)]
#![feature(underscore_lifetimes)]

#[macro_use] extern crate log;
#[macro_use] extern crate rustc;
extern crate rustc_data_structures;

use rustc::infer::InferCtxt;
use rustc::ty::{self, CanonicalVar};
use rustc_data_structures::fx::FxHashMap;
use std::collections::BTreeMap;

mod canonical;
use self::canonical::{Canonical, CanonicalVarValue};

mod fallible;
use self::fallible::Fallible;

mod search_graph;
use self::search_graph::{DepthFirstNumber, SearchGraph};

mod stack;
use self::stack::Stack;

/// A Solver is the basic context in which you can propose goals for a given
/// program. **All questions posed to the solver are in canonical, closed form,
/// so that each question is answered with effectively a "clean slate"**. This
/// allows for better caching, and simplifies management of the inference
/// context.
pub struct Solver<'cx, 'gcx: 'tcx, 'tcx: 'cx> {
    infcx: &'cx InferCtxt<'cx, 'gcx, 'tcx>,
    stack: Stack,
    search_graph: SearchGraph<'tcx>,

    caching_enabled: bool,

    /// The cache contains **fully solved** goals, whose results are
    /// not dependent on the stack in anyway.
    cache: FxHashMap<PredicateAtomGoal<'tcx>, Fallible<Solution<'tcx>>>,
}

/// Internally to the solver, a `Goal` is used to mean something we
/// are trying to prove. It is like an obligation, but stripped of
/// the `cause`.
struct Goal<'tcx, G> {
    param_env: ty::ParamEnv<'tcx>,
    goal: G,
}

/// The main top-line goals we try to prove.
type PredicateAtomGoal<'tcx> = Goal<'tcx, ty::PredicateAtom<'tcx>>;

/// The `minimums` struct is used while solving to track whether we encountered
/// any cycles in the process.
#[derive(Copy, Clone, Debug)]
struct Minimums {
    positive: DepthFirstNumber,
}

impl Minimums {
    fn new() -> Self {
        Minimums {
            positive: DepthFirstNumber::MAX,
        }
    }

    fn update_from(&mut self, minimums: Minimums) {
        self.positive = ::std::cmp::min(self.positive, minimums.positive);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Solution<'tcx> {
    Ambiguous,
    Unique(Canonical<ConstrainedCanonicalVarSubstitution<'tcx>>),
}

/// Combines a `CanonicalVarSubstitution` with region predicates.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ConstrainedCanonicalVarSubstitution<'tcx> {
    pub subst: CanonicalVarSubstitution<'tcx>,
    // TODO pub constraints: Vec<InEnvironment<Constraint>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct CanonicalVarSubstitution<'tcx> {
    /// Map free variable with given index to the value with the same
    /// index. Naturally, the kind of the variable must agree with
    /// the kind of the value.
    ///
    /// This is a map because the substitution is not necessarily
    /// complete. We use a btree map to ensure that the result is in a
    /// deterministic order.
    pub parameters: BTreeMap<CanonicalVar, CanonicalVarValue<'tcx>>,
}
