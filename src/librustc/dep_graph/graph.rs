// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use hir::def_id::DefId;
use rustc_data_structures::fx::FxHashMap;
use session::config::OutputType;
use std::cell::{Ref, RefCell};
use std::rc::Rc;
use std::sync::Arc;

use super::dep_node::{DepNode, WorkProductId};
use super::query::DepGraphQuery;
use super::raii;
use super::safe::DepGraphSafe;
use super::thread::{DepGraphThreadData, DepMessage};

#[derive(Clone)]
pub struct DepGraph {
    data: Rc<DepGraphData>
}

pub struct DepNodeIndex {
    index: usize
}

struct DepGraphData {
    enabled: bool,

    nodes: RefCell<DepGraphNodes>,

    /// When we load, there may be `.o` files, cached mir, or other such
    /// things available to us. If we find that they are not dirty, we
    /// load the path to the file storing those work-products here into
    /// this map. We can later look for and extract that data.
    previous_work_products: RefCell<FxHashMap<Arc<WorkProductId>, WorkProduct>>,

    /// Work-products that we generate in this run.
    work_products: RefCell<FxHashMap<Arc<WorkProductId>, WorkProduct>>,
}

struct DepGraphNodes {
    node_data: Vec<DepNodeData>,

    /// Hash-set used to canonicalize these vectors.
    predecessors: FxHashSet<Rc<Vec<DepNodeIndex>>>,

    task_stack: Vec<TaskStackEntry>,

    /// Anonymous nodes are named by their predecessors.  This map
    /// goes from a (canonically sorted) set of predecessors to an
    /// anonymous node index, so we can re-use indices that occur
    /// regularly.
    anon_node_map: FxHashMap<Rc<Vec<DepNode<DefId>>>, DepNodeIndex>,

    /// Quickly look up the named node.
    named_node_map: FxHashMap<DepNode<DefId>>, DepNodeIndex>,
}

struct DepNodeData {
    opt_name: Option<DepNode<DefId>>,
    predecessors: Rc<Vec<DepNodeIndex>>,
}

/// For each active task, we push one of these entries, which
/// accumulates a list of dep-nodes that were accessed. The set is
/// used to quickly check if a given pred has been accessed already;
/// the vec stores the list of preds in the order in which they were
/// accessed (it's important to preserve that ordering to prevent us
/// from doing extra work and so forth).
struct TaskStackEntry {
    predecessors: Vec<DepNodeIndex>,
    predecessor_set: FxHashSet<DepNodeIndex>,
}

impl DepGraph {
    pub fn new(enabled: bool) -> DepGraph {
        DepGraph {
            data: Rc::new(DepGraphData {
                thread: DepGraphThreadData::new(enabled),
                previous_work_products: RefCell::new(FxHashMap()),
                work_products: RefCell::new(FxHashMap()),
            })
        }
    }

    /// True if we are actually building the full dep-graph.
    #[inline]
    pub fn is_fully_enabled(&self) -> bool {
        self.data.thread.is_fully_enabled()
    }

    pub fn query(&self) -> DepGraphQuery<DefId> {
        self.data.thread.query()
    }

    /// Executes `op`, ignoring any dependencies. Used to "hack" the
    /// system -- use with care! Once red-green system is in place,
    /// probably not much needed anymore.
    pub fn with_ignore<OP,R>(&self, op: OP) -> R
        where OP: FnOnce() -> R
    {
        if !self.enabled {
            op()
        } else {
            self.nodes.borrow_mut().push_task();
            let result = op();
            let _ = self.nodes.borrow_mut().pop_task(None);
            result
        }
    }

    /// Starts a new dep-graph task. Dep-graph tasks are specified
    /// using a free function (`task`) and **not** a closure -- this
    /// is intentional because we want to exercise tight control over
    /// what state they have access to. In particular, we want to
    /// prevent implicit 'leaks' of tracked state into the task (which
    /// could then be read without generating correct edges in the
    /// dep-graph -- see the [README] for more details on the
    /// dep-graph). To this end, the task function gets exactly two
    /// pieces of state: the context `cx` and an argument `arg`. Both
    /// of these bits of state must be of some type that implements
    /// `DepGraphSafe` and hence does not leak.
    ///
    /// The choice of two arguments is not fundamental. One argument
    /// would work just as well, since multiple values can be
    /// collected using tuples. However, using two arguments works out
    /// to be quite convenient, since it is common to need a context
    /// (`cx`) and some argument (e.g., a `DefId` identifying what
    /// item to process).
    ///
    /// For cases where you need some other number of arguments:
    ///
    /// - If you only need one argument, just use `()` for the `arg`
    ///   parameter.
    /// - If you need 3+ arguments, use a tuple for the
    ///   `arg` parameter.
    ///
    /// [README]: README.md
    pub fn with_task<C, A, R>(&self, key: DepNode<DefId>, cx: C, arg: A, task: fn(C, A) -> R) -> R
        where C: DepGraphSafe, A: DepGraphSafe
    {
        self.with_task_internal(Some(key), cx, arg, task)
    }

    /// Like `with_task`, but it creates an **anonymous task**. The
    /// only way to name this task later is through its
    /// `DepNodeIndex`.
    pub fn with_anon_task<C, A, R>(&self,
                                   cx: C,
                                   arg: A,
                                   task: fn(C, A) -> R)
                                   -> (R, DepNodeIndex)
        where C: DepGraphSafe, A: DepGraphSafe
    {
        self.with_task_internal(None, cx, arg, task)
    }

    fn with_task_internal<C, A, R>(&self,
                                   key: Option<DepNode<DefId>>,
                                   cx: C,
                                   arg: A,
                                   task: fn(C, A) -> R)
                                   -> (R, DepNodeIndex)
        where C: DepGraphSafe, A: DepGraphSafe
    {
        if !self.enabled {
            return (task(cx, arg), DepNodeIndex::dummy())
        } else {
            self.nodes.borrow_mut().push_task();
            let result = task(cx, arg);
            let node_index = self.nodes.borrow_mut().pop_task(key);
            (result, node_index)
        }
    }

    /// Indicates that the current task read the data at `v`.
    pub fn read(&self, v: DepNodeIndex) {
        if self.enabled {
            self.nodes.borrow_mut().read(v);
        } else {
            debug_assert!(v.is_dummy());
        }
    }

    /// Indicates that a previous work product exists for `v`. This is
    /// invoked during initial start-up based on what nodes are clean
    /// (and what files exist in the incr. directory).
    pub fn insert_previous_work_product(&self, v: &Arc<WorkProductId>, data: WorkProduct) {
        debug!("insert_previous_work_product({:?}, {:?})", v, data);
        self.data.previous_work_products.borrow_mut()
                                        .insert(v.clone(), data);
    }

    /// Indicates that we created the given work-product in this run
    /// for `v`. This record will be preserved and loaded in the next
    /// run.
    pub fn insert_work_product(&self, v: &Arc<WorkProductId>, data: WorkProduct) {
        debug!("insert_work_product({:?}, {:?})", v, data);
        self.data.work_products.borrow_mut()
                               .insert(v.clone(), data);
    }

    /// Check whether a previous work product exists for `v` and, if
    /// so, return the path that leads to it. Used to skip doing work.
    pub fn previous_work_product(&self, v: &Arc<WorkProductId>) -> Option<WorkProduct> {
        self.data.previous_work_products.borrow()
                                        .get(v)
                                        .cloned()
    }

    /// Access the map of work-products created during this run. Only
    /// used during saving of the dep-graph.
    pub fn work_products(&self) -> Ref<FxHashMap<Arc<WorkProductId>, WorkProduct>> {
        self.data.work_products.borrow()
    }

    /// Access the map of work-products created during the cached run. Only
    /// used during saving of the dep-graph.
    pub fn previous_work_products(&self) -> Ref<FxHashMap<Arc<WorkProductId>, WorkProduct>> {
        self.data.previous_work_products.borrow()
    }
}

impl DepGraphNodes {
    fn push_task(&mut self) {
        self.task_stack.push(TaskStackEntry {
            predecessors: vec![],
            predecessor_set: FxHashSet(),
        });
    }

    /// Finishes the current task and creates a node to represent it.
    /// The node will be anonymous if `opt_name` is `None`, and named
    /// otherwise.
    fn pop_task(&mut self, opt_name: Option<DepNode<DefId>>) -> DepNodeIndex {
        let entry = self.task_stack.pop().unwrap();

        // Canonicalize the vector of predecessors.
        let predecessors = if let Some(s) = self.predecessors.get(&entry.predecessors) {
            s.clone()
        } else {
            let vec = Rc::new(entry.predecessors);
            self.predecessors.insert(vec);
            vec.clone()
        };

        // Check if a suitable anonymous node already exists.
        //
        // Micro-optimization: this could be improved by taking
        // advantage of the fact that vectors of predecessors are
        // interned above.
        if opt_name.is_none() {
            if let Some(&index) = self.anon_node_map.get(&predecessors) {
                return index;
            }
        }

        // Otherwise, we have to make a new node. If this is a named node,
        // it should not already exist.
        let index = DepNodeIndex { index: self.node_data.len() };
        if let Some(n) = opt_name {
            let prev = self.named_node_map.insert(n, index);
            assert!(prev.is_none(), "created named node {:?} twice", n);
        }
        self.node_data.push(DepNodeData { opt_name, predecessors });

        index
    }

    fn read(&mut self, v: DepNodeIndex) {
        if let Some(top) = self.task_stack.last_mut() {
            if top.predecessor_set.insert(v) {
                top.predecessors.push(v);
            }
        }
    }
}

/// A "work product" is an intermediate result that we save into the
/// incremental directory for later re-use. The primary example are
/// the object files that we save for each partition at code
/// generation time.
///
/// Each work product is associated with a dep-node, representing the
/// process that produced the work-product. If that dep-node is found
/// to be dirty when we load up, then we will delete the work-product
/// at load time. If the work-product is found to be clean, then we
/// will keep a record in the `previous_work_products` list.
///
/// In addition, work products have an associated hash. This hash is
/// an extra hash that can be used to decide if the work-product from
/// a previous compilation can be re-used (in addition to the dirty
/// edges check).
///
/// As the primary example, consider the object files we generate for
/// each partition. In the first run, we create partitions based on
/// the symbols that need to be compiled. For each partition P, we
/// hash the symbols in P and create a `WorkProduct` record associated
/// with `DepNode::TransPartition(P)`; the hash is the set of symbols
/// in P.
///
/// The next time we compile, if the `DepNode::TransPartition(P)` is
/// judged to be clean (which means none of the things we read to
/// generate the partition were found to be dirty), it will be loaded
/// into previous work products. We will then regenerate the set of
/// symbols in the partition P and hash them (note that new symbols
/// may be added -- for example, new monomorphizations -- even if
/// nothing in P changed!). We will compare that hash against the
/// previous hash. If it matches up, we can reuse the object file.
#[derive(Clone, Debug, RustcEncodable, RustcDecodable)]
pub struct WorkProduct {
    /// Extra hash used to decide if work-product is still suitable;
    /// note that this is *not* a hash of the work-product itself.
    /// See documentation on `WorkProduct` type for an example.
    pub input_hash: u64,

    /// Saved files associated with this CGU
    pub saved_files: Vec<(OutputType, String)>,
}
