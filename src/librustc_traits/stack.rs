use ::fallible::*;
use ::PredicateAtomGoal;

use rustc::infer::InferCtxt;
use rustc::ty;
use std::mem;
use std::ops::Index;
use std::ops::IndexMut;
use std::usize;

pub(crate) struct Stack {
    entries: Vec<StackEntry>,
    overflow_depth: usize,
}

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct StackDepth {
    depth: usize,
}

/// The data we actively keep for each goal on the stack.
pub struct StackEntry {
    /// Was this a coinductive goal?
    coinductive_goal: bool,

    /// Initially false, set to true when some subgoal depends on us.
    cycle: bool,
}

impl<'tcx> Stack {
    pub(crate) fn new(overflow_depth: usize) -> Self {
        Stack {
            entries: vec![],
            overflow_depth: overflow_depth,
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn push(&mut self,
                infcx: &InferCtxt<'_, '_, 'tcx>,
                goal: &PredicateAtomGoal<'tcx>)
                -> CanOverflow<StackDepth> {
        let depth = StackDepth {
            depth: self.entries.len(),
        };

        if depth.depth >= self.overflow_depth {
            // This should perhaps be a result or something, though
            // really I'd prefer to move to subgoal abstraction for
            // guaranteeing termination. -nmatsakis
            return Err(Overflow);
        }

        let coinductive_goal = self.coinductive_predicate(infcx, goal.goal);
        self.entries.push(StackEntry { coinductive_goal, cycle: false });
        Ok(depth)
    }

    fn coinductive_predicate(&self,
                             infcx: &InferCtxt<'_, '_, 'tcx>,
                             predicate: ty::PredicateAtom<'tcx>)
                             -> bool {
        let result = match predicate {
            ty::PredicateAtom::Trait(ref data) => {
                infcx.tcx.trait_is_auto(data.def_id)
            }
            _ => {
                false
            }
        };
        debug!("coinductive_predicate({:?}) = {:?}", predicate, result);
        result
    }

    pub(crate) fn pop(&mut self, depth: StackDepth) {
        assert_eq!(
            depth.depth + 1,
            self.entries.len(),
            "mismatched stack push/pop"
        );
        self.entries.pop();
    }

    /// True if all the goals from the top of the stack down to (and
    /// including) the given depth are coinductive.
    pub(crate) fn coinductive_cycle_from(&self, depth: StackDepth) -> bool {
        self.entries[depth.depth..].iter().all(|entry| entry.coinductive_goal)
    }
}

impl StackEntry {
    pub(crate) fn flag_cycle(&mut self) {
        self.cycle = true;
    }

    pub(crate) fn read_and_reset_cycle_flag(&mut self) -> bool {
        mem::replace(&mut self.cycle, false)
    }
}

impl Index<StackDepth> for Stack {
    type Output = StackEntry;

    fn index(&self, depth: StackDepth) -> &StackEntry {
        &self.entries[depth.depth]
    }
}

impl IndexMut<StackDepth> for Stack {
    fn index_mut(&mut self, depth: StackDepth) -> &mut StackEntry {
        &mut self.entries[depth.depth]
    }
}
