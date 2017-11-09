// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The search graph encodes the proof search that we are currently
//! doing. When cycles are encountered, it rolls back.

use ::fallible::*;
use ::stack::StackDepth;
use ::{Minimums, Solution};

use rustc::ty;
use rustc_data_structures::fx::FxHashMap;
use std::ops::{Add, Index, IndexMut};

pub(super) struct SearchGraph<'tcx> {
    indices: FxHashMap<ty::PredicateAtom<'tcx>, DepthFirstNumber>,
    nodes: Vec<Node<'tcx>>,
}

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(super) struct DepthFirstNumber {
    index: usize,
}

pub(super) struct Node<'tcx> {
    pub goal: ty::PredicateAtom<'tcx>,

    pub solution: Fallible<Solution<'tcx>>,

    /// This is `Some(X)` if we are actively exploring this node, or
    /// `None` otherwise.
    pub stack_depth: Option<StackDepth>,

    /// While this node is on the stack, this field will be set to
    /// contain our own depth-first number. Once the node is popped
    /// from the stack, it contains the DFN of the minimal ancestor
    /// that the table reached (or MAX if no cycle was encountered).
    pub links: Minimums,
}

impl<'tcx> SearchGraph<'tcx> {
    pub fn new() -> Self {
        SearchGraph {
            indices: FxHashMap::default(),
            nodes: vec![],
        }
    }

    pub fn lookup(&self, goal: &ty::PredicateAtom<'tcx>) -> Option<DepthFirstNumber> {
        self.indices.get(goal).cloned()
    }

    /// Insert a new search node in the tree. The node will be in the initial
    /// state for a search node:
    ///
    /// - stack depth as given
    /// - links set to its own DFN
    /// - solution is initially `NoSolution`
    pub fn insert(&mut self, goal: &ty::PredicateAtom<'tcx>, stack_depth: StackDepth) -> DepthFirstNumber {
        let dfn = DepthFirstNumber {
            index: self.nodes.len(),
        };
        let node = Node {
            goal: goal.clone(),
            solution: Err(NoSolution),
            stack_depth: Some(stack_depth),
            links: Minimums { positive: dfn },
        };
        self.nodes.push(node);
        let previous_index = self.indices.insert(goal.clone(), dfn);
        assert!(previous_index.is_none());
        dfn
    }

    /// Clears all nodes with a depth-first number greater than or equal `dfn`.
    pub fn rollback_to(&mut self, dfn: DepthFirstNumber) {
        debug!("rollback_to(dfn={:?})", dfn);
        self.indices.retain(|_key, value| *value < dfn);
        self.nodes.truncate(dfn.index);
    }

    /// Removes all nodes with a depth-first-number greater than or
    /// equal to `dfn`, adding their final solutions into the cache.
    pub fn move_to_cache(
        &mut self,
        dfn: DepthFirstNumber,
        cache: &mut FxHashMap<ty::PredicateAtom<'tcx>, Fallible<Solution<'tcx>>>,
    ) {
        debug!("move_to_cache(dfn={:?})", dfn);
        self.indices.retain(|_key, value| *value < dfn);
        for node in self.nodes.drain(dfn.index..) {
            assert!(node.stack_depth.is_none());
            assert!(node.links.positive >= dfn);
            debug!("caching solution {:?} for {:?}", node.solution, node.goal);
            cache.insert(node.goal, node.solution);
        }
    }
}

impl<'tcx> Index<DepthFirstNumber> for SearchGraph<'tcx> {
    type Output = Node<'tcx>;

    fn index(&self, table_index: DepthFirstNumber) -> &Node<'tcx> {
        &self.nodes[table_index.index]
    }
}

impl<'tcx> IndexMut<DepthFirstNumber> for SearchGraph<'tcx> {
    fn index_mut(&mut self, table_index: DepthFirstNumber) -> &mut Node<'tcx> {
        &mut self.nodes[table_index.index]
    }
}

impl DepthFirstNumber {
    pub const MAX: DepthFirstNumber = DepthFirstNumber { index: ::std::usize::MAX };
}

impl Add<usize> for DepthFirstNumber {
    type Output = DepthFirstNumber;

    fn add(self, v: usize) -> DepthFirstNumber {
        DepthFirstNumber { index: self.index + v }
    }
}
