// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

pub use self::Node::*;
pub use self::PathElem::*;

use syntax::abi;
use syntax::ast::*;
use syntax::ast_util;
use syntax::codemap::{DUMMY_SP, Span, Spanned};
use syntax::fold::Folder;
use syntax::parse::token;
use syntax::print::pprust;
use syntax::visit::{self, Visitor};
use util::nodemap::{NodeMap, FnvHashMap};

use arena::TypedArena;
use std::cell::RefCell;
use std::fmt;
use std::io;
use std::iter::{self, repeat};
use std::mem;
use std::slice;
use self::parent::ParentNodeWalker;

pub mod blocks;
mod parent;
mod collect;

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum ItemOrBlockId {
    Item(ItemId),
    Block(NodeId),
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum PathElem {
    PathMod(Name),
    PathName(Name)
}

impl PathElem {
    pub fn name(&self) -> Name {
        match *self {
            PathMod(name) | PathName(name) => name
        }
    }
}

impl fmt::Display for PathElem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let slot = token::get_name(self.name());
        write!(f, "{}", slot)
    }
}

#[derive(Clone)]
pub struct LinkedPathNode<'a> {
    node: PathElem,
    next: LinkedPath<'a>,
}

#[derive(Copy, Clone)]
pub struct LinkedPath<'a>(Option<&'a LinkedPathNode<'a>>);

impl<'a> LinkedPath<'a> {
    pub fn empty() -> LinkedPath<'a> {
        LinkedPath(None)
    }

    pub fn from(node: &'a LinkedPathNode) -> LinkedPath<'a> {
        LinkedPath(Some(node))
    }
}

impl<'a> Iterator for LinkedPath<'a> {
    type Item = PathElem;

    fn next(&mut self) -> Option<PathElem> {
        match self.0 {
            Some(node) => {
                *self = node.next;
                Some(node.node)
            }
            None => None
        }
    }
}

/// The type of the iterator used by with_path.
pub type PathElems<'a, 'b> = iter::Chain<iter::Cloned<slice::Iter<'a, PathElem>>, LinkedPath<'b>>;

pub fn path_to_string<PI: Iterator<Item=PathElem>>(path: PI) -> String {
    let itr = token::get_ident_interner();

    path.fold(String::new(), |mut s, e| {
        let e = itr.get(e.name());
        if !s.is_empty() {
            s.push_str("::");
        }
        s.push_str(&e[..]);
        s
    })
}

// Nodes for things that have ItemId's, which is actually not just
// ast::Item.
#[derive(Copy, Clone, Debug)]
pub enum ItemNode<'ast> {
    Item(&'ast Item),
    ForeignItem(&'ast ForeignItem),
    TraitItem(&'ast TraitItem),
    ImplItem(&'ast ImplItem),
    ClosureItem(&'ast Expr), // must be an ExprClosure
    Variant(&'ast Variant),
    /// NodeStructCtor represents a tuple struct.
    StructCtor(&'ast StructDef),
}

/// Represents an entry and its parent ItemId.
/// The odd layout is to bring down the total size.
#[derive(Copy, Clone, Debug)]
enum ItemMapEntry<'ast> {
    Item(ItemId, &'ast Item),
    ForeignItem(ItemId, &'ast ForeignItem),
    TraitItem(ItemId, &'ast TraitItem),
    ImplItem(ItemId, &'ast ImplItem),
    Variant(ItemId, &'ast Variant),
    ClosureItem(ItemId, &'ast Expr),
    StructCtor(ItemId, &'ast StructDef),

    /// Roots for node trees.
    RootCrate,
    RootInlinedParent(&'ast InlinedParent)
}

impl<'ast> ItemMapEntry<'ast> {
    fn from_item_node(parent: ItemId, n: ItemNode<'ast>) -> ItemMapEntry<'ast> {
        match n {
            ItemNode::Item(n) => ItemMapEntry::Item(parent, n),
            ItemNode::ForeignItem(n) => ItemMapEntry::ForeignItem(parent, n),
            ItemNode::TraitItem(n) => ItemMapEntry::TraitItem(parent, n),
            ItemNode::ImplItem(n) => ItemMapEntry::ImplItem(parent, n),
            ItemNode::Variant(n) => ItemMapEntry::Variant(parent, n),
            ItemNode::StructCtor(n) => ItemMapEntry::StructCtor(parent, n),
        }
    }

    fn to_item_node(&self) -> Option<ItemNode<'ast>> {
        match *self {
            ItemMapEntry::Item(parent, n) => Some(ItemNode::Item(n)),
            ItemMapEntry::ForeignItem(parent, n) => Some(ItemNode::ForeignItem(n)),
            ItemMapEntry::TraitItem(parent, n) => Some(ItemNode::TraitItem(n)),
            ItemMapEntry::ImplItem(parent, n) => Some(ItemNode::ImplItem(n)),
            ItemMapEntry::Variant(parent, n) => Some(ItemNode::Variant(n)),
            ItemMapEntry::StructCtor(parent, n) => Some(ItemNode::StructCtor(n)),
            ItemMapEntry::RootCrate => None,
            ItemMapEntry::RootInlinedParent(..) => None,
        }
    }
}

// Nodes for things that do not have ItemIds.
#[derive(Copy, Clone, Debug)]
pub enum Node<'ast> {
    NodeExpr(&'ast Expr),
    NodeStmt(&'ast Stmt),
    NodeArg(&'ast Pat),
    NodeLocal(&'ast Pat),
    NodePat(&'ast Pat),
    NodeBlock(&'ast Block),
    NodeLifetime(&'ast Lifetime),
}

/// Represents an entry and its parent NodeID.
/// The odd layout is to bring down the total size.
#[derive(Copy, Clone, Debug)]
struct MapEntry<'ast> {
    // NB: This is DUMMY_NODE_ID if the node is either vacant or has
    // an item for a parent. In the latter case, check the
    // item_parent_map.
    parent_node: NodeId,
    kind: MapEntryKind<'ast>,
}

#[derive(Copy, Clone, Debug)]
enum MapEntryKind<'ast> {
    /// Placeholder for holes in the map.
    NotPresent,

    /// All the node types, with a parent ID.
    Expr(&'ast Expr),
    Stmt(&'ast Stmt),
    Arg(&'ast Pat),
    Local(&'ast Pat),
    Pat(&'ast Pat),
    Block(&'ast Block),
    Lifetime(&'ast Lifetime),
}

#[derive(Debug)]
struct InlinedParent {
    path: Vec<PathElem>,
    ii: InlinedItem
}

impl<'ast> MapEntry<'ast> {
    fn from_node(p: NodeId, node: Node<'ast>) -> MapEntry<'ast> {
        MapEntry {
            parent_node: p,
            kind: match node {
                NodeExpr(n) => MapEntryKind::Expr(n),
                NodeStmt(n) => MapEntryKind::Stmt(n),
                NodeArg(n) => MapEntryKind::Arg(n),
                NodeLocal(n) => MapEntryKind::Local(n),
                NodePat(n) => MapEntryKind::Pat(n),
                NodeBlock(n) => MapEntryKind::Block(n),
                NodeLifetime(n) => MapEntryKind::Lifetime(n)
            }
        }
    }

    fn to_node(self) -> Option<Node<'ast>> {
        Some(match self.kind {
            MapEntryKind::Expr(n) => NodeExpr(n),
            MapEntryKind::Stmt(n) => NodeStmt(n),
            MapEntryKind::Arg(n) => NodeArg(n),
            MapEntryKind::Local(n) => NodeLocal(n),
            MapEntryKind::Pat(n) => NodePat(n),
            MapEntryKind::Block(n) => NodeBlock(n),
            MapEntryKind::Lifetime(n) => NodeLifetime(n),
            _ => return None
        })
    }
}

/// Stores a crate and any number of inlined items from other crates.
pub struct Forest {
    krate: Crate,
    inlined_items: TypedArena<InlinedParent>
}

impl Forest {
    pub fn new(krate: Crate) -> Forest {
        Forest {
            krate: krate,
            inlined_items: TypedArena::new()
        }
    }

    pub fn krate<'ast>(&'ast self) -> &'ast Crate {
        &self.krate
    }
}

/// Represents a mapping from Node IDs to AST elements and their parent
/// Node IDs
pub struct Map<'ast> {
    /// The backing storage for all the AST nodes.
    forest: &'ast Forest,

    /// NodeIds are sequential integers from 0, so we can be
    /// super-compact by storing them in a vector. Not everything with
    /// a NodeId is in the map, but empirically the occupancy is about
    /// 75-80%, so there's not too much overhead (certainly less than
    /// a hashmap, since they (at the time of writing) have a maximum
    /// of 75% occupancy).
    ///
    /// Also, indexing is pretty quick when you've got a vector and
    /// plain old integers.
    map: RefCell<Vec<MapEntry<'ast>>>,

    /// For those nodes whose parent is an item, the ItemId is stored
    /// in this sparse map, rather than being placed into the dense
    /// map above.
    item_parent_map: RefCell<NodeMap<ItemId>>,

    /// Items themselves (and item-like things) are relatively few, so
    /// they are stored in this sparse map.
    item_map: RefCell<FnvHashMap<ItemId, ItemMapEntry<'ast>>>,
}

impl<'ast> Map<'ast> {
    fn entry_count(&self) -> usize {
        self.map.borrow().len()
    }

    fn find_entry(&self, id: NodeId) -> Option<MapEntry<'ast>> {
        self.map.borrow().get(id as usize).cloned()
    }

    fn find_item_entry(&self, id: ItemId) -> Option<ItemMapEntry<'ast>> {
        self.item_map.borrow().get(&id).cloned()
    }

    pub fn krate(&self) -> &'ast Crate {
        &self.forest.krate
    }

    /// Retrieve the Node corresponding to `id`, panicking if it cannot
    /// be found.
    pub fn get(&self, id: NodeId) -> Node<'ast> {
        match self.find(id) {
            Some(node) => node,
            None => panic!("couldn't find node id {} in the AST map", id)
        }
    }

    /// Retrieve the ItemNode corresponding to `id`, panicking if it cannot
    /// be found.
    pub fn get_item(&self, id: ItemId) -> ItemNode<'ast> {
        match self.find_item(id) {
            Some(node) => node,
            None => panic!("couldn't find item id {:?} in the AST map", id)
        }
    }

    /// Retrieve the Node corresponding to `id`, returning None if
    /// cannot be found.
    pub fn find(&self, id: NodeId) -> Option<Node<'ast>> {
        self.find_entry(id).and_then(|x| x.to_node())
    }

    /// Retrieve the ItemNode corresponding to `id`, returning None if
    /// cannot be found.
    pub fn find_item(&self, id: ItemId) -> Option<ItemNode<'ast>> {
        self.item_map.borrow().get(&id).and_then(|me| me.to_item_node())
    }

    /// Yields an iterator that walks up the parents of a given node-id.
    fn walk_parents<'map>(&'map self, id: NodeId) -> ParentNodeWalker<'map, 'ast> {
        ParentNodeWalker::new(self, id)
    }

    /// Retrieve the NodeId for `id`'s parent item, or `id` itself if no
    /// parent item is in this map. The "parent item" is the closest parent node
    /// in the AST which is recorded by the map and is an item, either an item
    /// in a module, trait, or impl.
    pub fn get_enclosing_item(&self, mut id: NodeId) -> ItemId {
        let mut walker = self.walk_parents(id);
        while let Some(_) = walker.next() { /* drain the iterator to find the enclosing item */ }
        walker.item_id().unwrap()
    }

    /// Returns the nearest enclosing scope. A scope is an item or block.
    /// FIXME it is not clear to me that all items qualify as scopes - statics
    /// and associated types probably shouldn't, for example. Behaviour in this
    /// regard should be expected to be highly unstable.
    pub fn get_enclosing_scope(&self, id0: NodeId) -> Option<ItemOrBlockId> {
        let mut walker = self.walk_parents(id0);
        let map = self.map.borrow();
        while let Some(id) = walker.next() {
            match map[id as usize].kind {
                MapEntryKind::Block(_) => { return Some(ItemOrBlockId::Block(id)); }
                _ => { }
            }
        }
        walker.item_id().map(ItemOrBlockId::Item)
    }

    /// Returns the immediate parent of an item, not considering inlined/cross-crate items.
    fn get_item_parent(&self, id: ItemId) -> ItemId {
        match self.find_item_entry(id).unwrap() {
            ItemMapEntry::Item(parent, _) => parent,
            ItemMapEntry::ForeignItem(parent, _) => parent,
            ItemMapEntry::TraitItem(parent, _) => parent,
            ItemMapEntry::ImplItem(parent, _) => parent,
            ItemMapEntry::Variant(parent, _) => parent,
            ItemMapEntry::RootCrate | ItemMapEntry::RootInlinedParent(..) =>
                panic!("get_parent called on item without parent")
        }
    }

    pub fn get_parent_did(&self, id: NodeId) -> DefId {
        let parent = self.get_enclosing_item(id);
        match self.find_item_entry(parent) {
            Some(ItemMapEntry::RootInlinedParent(&InlinedParent {ii: IITraitItem(did, _), ..})) =>
                did,
            Some(ItemMapEntry::RootInlinedParent(&InlinedParent {ii: IIImplItem(did, _), ..})) =>
                did,
            _ =>
                ast_util::local_def(parent)
        }
    }

    pub fn get_foreign_abi(&self, id: NodeId) -> abi::Abi {
        let parent = self.get_enclosing_item(id);
        let abi = match self.find_item_entry(parent) {
            Some(ItemMapEntry::Item(_, i)) => {
                match i.node {
                    ItemForeignMod(ref nm) => Some(nm.abi),
                    _ => None
                }
            }
            /// Wrong but OK, because the only inlined foreign items are intrinsics.
            Some(ItemMapEntry::RootInlinedParent(_)) => Some(abi::RustIntrinsic),
            _ => None
        };
        match abi {
            Some(abi) => abi,
            None => panic!("expected foreign mod or inlined parent, found {}",
                          self.item_id_to_string(parent))
        }
    }

    pub fn get_foreign_vis(&self, id: ItemId) -> Visibility {
        let vis = self.expect_foreign_item(id).vis;
        match self.find_item(self.get_item_parent(id)) {
            Some(ItemNode::Item(i)) => vis.inherit_from(i.vis),
            _ => vis
        }
    }

    pub fn expect_item(&self, id: ItemId) -> &'ast Item {
        match self.find_item(id) {
            Some(ItemNode::Item(item)) => item,
            _ => panic!("expected item, found {}", self.item_id_to_string(id))
        }
    }

    pub fn expect_struct(&self, id: ItemId) -> &'ast StructDef {
        match self.find_item(id) {
            Some(ItemNode::Item(i)) => {
                match i.node {
                    ItemStruct(ref struct_def, _) => &**struct_def,
                    _ => panic!("struct ID bound to non-struct")
                }
            }
            Some(ItemNode::Variant(variant)) => {
                match variant.node.kind {
                    StructVariantKind(ref struct_def) => &**struct_def,
                    _ => panic!("struct ID bound to enum variant that isn't struct-like"),
                }
            }
            _ => panic!(format!("expected struct, found {}", self.item_id_to_string(id))),
        }
    }

    pub fn expect_variant(&self, id: ItemId) -> &'ast Variant {
        match self.find_item(id) {
            Some(ItemNode::Variant(variant)) => variant,
            _ => panic!(format!("expected variant, found {}", self.item_id_to_string(id))),
        }
    }

    pub fn expect_foreign_item(&self, id: ItemId) -> &'ast ForeignItem {
        match self.find_item(id) {
            Some(ItemNode::ForeignItem(item)) => item,
            _ => panic!("expected foreign item, found {}", self.item_id_to_string(id))
        }
    }

    pub fn expect_expr(&self, id: NodeId) -> &'ast Expr {
        match self.find(id) {
            Some(NodeExpr(expr)) => expr,
            _ => panic!("expected expr, found {}", self.node_to_string(id))
        }
    }

    /// returns the name associated with the given NodeId's AST
    pub fn get_path_elem(&self, id: ItemId) -> PathElem {
        let node = self.find_item_entry(id).unwrap();
        match node {
            ItemMapEntry::Item(_, item) => {
                match item.node {
                    ItemMod(_) | ItemForeignMod(_) => {
                        PathMod(item.ident.name)
                    }
                    _ => PathName(item.ident.name)
                }
            }
            ItemMapEntry::ForeignItem(_, i) => PathName(i.ident.name),
            ItemMapEntry::ImplItem(_, ii) => PathName(ii.ident.name),
            ItemMapEntry::TraitItem(_, ti) => PathName(ti.ident.name),
            ItemMapEntry::Variant(_, v) => PathName(v.node.name.name),

            ItemMapEntry::RootCrate | ItemMapEntry::RootInlinedParent(..) =>
                panic!("no path elem for {:?}", node)
        }
    }

    pub fn with_path<T, F>(&self, id: ItemId, f: F) -> T where
        F: FnOnce(PathElems) -> T,
    {
        self.with_path_next(id, LinkedPath::empty(), f)
    }

    pub fn path_to_string(&self, id: ItemId) -> String {
        self.with_path(id, |path| path_to_string(path))
    }

    fn path_to_str_with_ident(&self, id: ItemId, i: Ident) -> String {
        self.with_path(id, |path| {
            path_to_string(path.chain(Some(PathName(i.name))))
        })
    }

    fn with_path_next<T, F>(&self, id: ItemId, next: LinkedPath, f: F) -> T where
        F: FnOnce(PathElems) -> T,
    {
        let parent = self.get_item_parent(id);
        let parent = match self.find_item_entry(id) {
            Some(ItemMapEntry::ForeignItem(..)) | Some(ItemMapEntry::Variant(..)) => {
                // Anonymous extern items, enum variants and struct ctors
                // go in the parent scope.
                self.get_item_parent(parent)
            }
            // But tuple struct ctors don't have names, so use the path of its
            // parent, the struct item. Similarly with closure expressions.
            Some(ItemMapEntry::StructCtor(..)) | Some(ItemMapEntry::ClosureItem(..)) => {
                return self.with_path_next(parent, next, f);
            }
            _ => parent
        };
        if parent == id {
            match self.find_item_entry(id) {
                Some(ItemMapEntry::RootInlinedParent(data)) => {
                    f(data.path.iter().cloned().chain(next))
                }
                _ => f([].iter().cloned().chain(next))
            }
        } else {
            self.with_path_next(parent, LinkedPath::from(&LinkedPathNode {
                node: self.get_path_elem(id),
                next: next
            }), f)
        }
    }

    /// Given a node ID, get a list of of attributes associated with the AST
    /// corresponding to the Node ID
    pub fn attrs(&self, id: ItemId) -> &'ast [Attribute] {
        let attrs = match self.find_item(id) {
            Some(ItemNode::Item(i)) => Some(&i.attrs[..]),
            Some(ItemNode::ForeignItem(fi)) => Some(&fi.attrs[..]),
            Some(ItemNode::TraitItem(ref ti)) => Some(&ti.attrs[..]),
            Some(ItemNode::ImplItem(ref ii)) => Some(&ii.attrs[..]),
            Some(ItemNode::Variant(ref v)) => Some(&v.node.attrs[..]),
            // unit/tuple structs take the attributes straight from
            // the struct definition.
            Some(ItemNode::StructCtor(_)) => {
                return self.attrs(self.get_item_parent(id));
            }
            Some(ItemNode::ClosureItem(..)) |
            None =>
                None,
        };
        attrs.unwrap_or(&[])
    }

    /// Returns an iterator that yields the node id's with paths that
    /// match `parts`.  (Requires `parts` is non-empty.)
    ///
    /// For example, if given `parts` equal to `["bar", "quux"]`, then
    /// the iterator will produce node id's for items with paths
    /// such as `foo::bar::quux`, `bar::quux`, `other::bar::quux`, and
    /// any other such items it can find in the map.
    pub fn nodes_matching_suffix<'a>(&'a self, parts: &'a [String])
                                 -> ItemsMatchingSuffix<'a, 'ast> {
        ItemsMatchingSuffix {
            map: self,
            item_name: parts.last().unwrap(),
            in_which: &parts[..parts.len() - 1],
            keys: self.item_map.borrow().keys().into_iter().cloned().collect(),
        }
    }

    pub fn opt_item_span(&self, id: ItemId) -> Option<Span> {
        let sp = match self.find_item(id) {
            Some(ItemNode::Item(item)) => item.span,
            Some(ItemNode::ForeignItem(foreign_item)) => foreign_item.span,
            Some(ItemNode::TraitItem(trait_method)) => trait_method.span,
            Some(ItemNode::ImplItem(ref impl_item)) => impl_item.span,
            Some(ItemNode::Variant(variant)) => variant.span,
            Some(ItemNode::StructCtor(_)) => self.expect_item(self.get_item_parent(id)).span,
            Some(ItemNode::ClosureItem(expr)) => expr.span,
            None => return None,
        };
        Some(sp)
    }

    pub fn opt_span(&self, id: NodeId) -> Option<Span> {
        let sp = match self.find(id) {
            Some(NodeExpr(expr)) => expr.span,
            Some(NodeStmt(stmt)) => stmt.span,
            Some(NodeArg(pat)) | Some(NodeLocal(pat)) => pat.span,
            Some(NodePat(pat)) => pat.span,
            Some(NodeBlock(block)) => block.span,
            _ => return None,
        };
        Some(sp)
    }

    pub fn span(&self, id: NodeId) -> Span {
        self.opt_span(id)
            .unwrap_or_else(|| panic!("AstMap.span: could not find span for id {:?}", id))
    }

    pub fn def_id_span(&self, def_id: DefId, fallback: Span) -> Span {
        if def_id.krate == LOCAL_CRATE {
            self.opt_item_span(def_id.item).unwrap_or(fallback)
        } else {
            fallback
        }
    }

    pub fn node_to_string(&self, id: NodeId) -> String {
        node_id_to_string(self, id, true)
    }

    pub fn item_id_to_string(&self, id: ItemId) -> String {
        item_id_to_string(self, id, true)
    }

    pub fn node_to_user_string(&self, id: NodeId) -> String {
        node_id_to_string(self, id, false)
    }
}

pub struct ItemsMatchingSuffix<'a, 'ast:'a> {
    map: &'a Map<'ast>,
    item_name: &'a String,
    in_which: &'a [String],
    keys: Vec<ItemId>,
}

impl<'a, 'ast> ItemsMatchingSuffix<'a, 'ast> {
    /// Returns true only if some suffix of the module path for parent
    /// matches `self.in_which`.
    ///
    /// In other words: let `[x_0,x_1,...,x_k]` be `self.in_which`;
    /// returns true if parent's path ends with the suffix
    /// `x_0::x_1::...::x_k`.
    fn suffix_matches(&self, parent: ItemId) -> bool {
        let mut cursor = parent;
        for part in self.in_which.iter().rev() {
            let (mod_id, mod_name) = match find_first_mod_parent(self.map, cursor) {
                None => return false,
                Some((node_id, name)) => (node_id, name),
            };
            if &part[..] != mod_name.as_str() {
                return false;
            }
            cursor = self.map.get_item_parent(mod_id);
        }
        return true;

        // Finds the first mod in parent chain for `id`, along with
        // that mod's name.
        //
        // If `id` itself is a mod named `m` with parent `p`, then
        // returns `Some(id, m, p)`.  If `id` has no mod in its parent
        // chain, then returns `None`.
        fn find_first_mod_parent<'a>(map: &'a Map, mut id: ItemId) -> Option<(ItemId, Name)> {
            loop {
                match map.find_item(id) {
                    None => return None,
                    Some(ItemNode::Item(item)) if item_is_mod(&*item) =>
                        return Some((id, item.ident.name)),
                    _ => {}
                }
                let parent = map.get_item_parent(id);
                if parent == id { return None }
                id = parent;
            }

            fn item_is_mod(item: &Item) -> bool {
                match item.node {
                    ItemMod(_) => true,
                    _ => false,
                }
            }
        }
    }

    // We are looking at some node `n` with a given name and parent
    // id; do their names match what I am seeking?
    fn matches_names(&self, parent_of_n: ItemId, name: Name) -> bool {
        name.as_str() == &self.item_name[..] &&
            self.suffix_matches(parent_of_n)
    }
}

impl<'a, 'ast> Iterator for ItemsMatchingSuffix<'a, 'ast> {
    type Item = ItemId;

    fn next(&mut self) -> Option<ItemId> {
        loop {
            let id = match self.keys.pop() {
                Some(id) => id,
                None => { return None; }
            };
            let name = match self.map.find_item_entry(id) {
                Some(ItemMapEntry::Item(_, n))       => n.name(),
                Some(ItemMapEntry::ForeignItem(_, n))=> n.name(),
                Some(ItemMapEntry::TraitItem(_, n))  => n.name(),
                Some(ItemMapEntry::ImplItem(_, n))   => n.name(),
                Some(ItemMapEntry::Variant(_, n))    => n.name(),
                _ => continue,
            };
            if self.matches_names(self.map.get_item_parent(id), name) {
                return Some(id)
            }
        }
    }
}

trait Named {
    fn name(&self) -> Name;
}

impl<T:Named> Named for Spanned<T> { fn name(&self) -> Name { self.node.name() } }

impl Named for Item { fn name(&self) -> Name { self.ident.name } }
impl Named for ForeignItem { fn name(&self) -> Name { self.ident.name } }
impl Named for Variant_ { fn name(&self) -> Name { self.name.name } }
impl Named for TraitItem { fn name(&self) -> Name { self.ident.name } }
impl Named for ImplItem { fn name(&self) -> Name { self.ident.name } }

pub trait FoldOps {
    fn new_id(&self, id: NodeId) -> NodeId {
        id
    }
    fn new_def_id(&self, def_id: DefId) -> DefId {
        def_id
    }
    fn new_span(&self, span: Span) -> Span {
        span
    }
}

/// A Folder that updates IDs and Span's according to fold_ops.
struct IdAndSpanUpdater<F> {
    fold_ops: F
}

impl<F: FoldOps> Folder for IdAndSpanUpdater<F> {
    fn new_id(&mut self, id: NodeId) -> NodeId {
        self.fold_ops.new_id(id)
    }

    fn new_span(&mut self, span: Span) -> Span {
        self.fold_ops.new_span(span)
    }
}

pub fn map_crate<'ast, F: FoldOps>(forest: &'ast mut Forest, fold_ops: F) -> Map<'ast> {
    // Replace the crate with an empty one to take it out.
    let krate = mem::replace(&mut forest.krate, Crate {
        module: Mod {
            inner: DUMMY_SP,
            items: vec![],
        },
        attrs: vec![],
        config: vec![],
        exported_macros: vec![],
        span: DUMMY_SP
    });
    forest.krate = IdAndSpanUpdater { fold_ops: fold_ops }.fold_crate(krate);

    let mut collector = collect::NodeCollector::for_krate();
    visit::walk_crate(&mut collector, &forest.krate);
    let (map, item_parent_map, item_map) = collector.take();

    if log_enabled!(::log::DEBUG) {
        // This only makes sense for ordered stores; note the
        // enumerate to count the number of entries.
        let (entries_less_1, _) = map.iter().filter(|&x| {
            match *x {
                NotPresent => false,
                _ => true
            }
        }).enumerate().last().expect("AST map was empty after folding?");

        let entries = entries_less_1 + 1;
        let vector_length = map.len();
        debug!("The AST map has {} entries with a maximum of {}: occupancy {:.1}%",
              entries, vector_length, (entries as f64 / vector_length as f64) * 100.);
    }

    Map {
        forest: forest,
        map: RefCell::new(map),
        item_parent_map: RefCell::new(item_parent_map),
        item_map: RefCell::new(item_map),
    }
}

/// Used for items loaded from external crate that are being inlined into this
/// crate.  The `path` should be the path to the item but should not include
/// the item itself.
pub fn map_decoded_item<'ast, F: FoldOps>(map: &Map<'ast>,
                                          path: Vec<PathElem>,
                                          ii: InlinedItem,
                                          fold_ops: F)
                                          -> &'ast InlinedItem {
    let mut fld = IdAndSpanUpdater { fold_ops: fold_ops };
    let ii = match ii {
        IIItem(i) => IIItem(fld.fold_item(i).expect_one("expected one item")),
        IITraitItem(d, ti) => {
            IITraitItem(fld.fold_ops.new_def_id(d),
                        fld.fold_trait_item(ti).expect_one("expected one trait item"))
        }
        IIImplItem(d, ii) => {
            IIImplItem(fld.fold_ops.new_def_id(d),
                       fld.fold_impl_item(ii).expect_one("expected one impl item"))
        }
        IIForeign(i) => IIForeign(fld.fold_foreign_item(i))
    };

    let ii_parent = map.forest.inlined_items.alloc(InlinedParent {
        path: path,
        ii: ii
    });

    let the_map = map.map.borrow_mut();
    let the_item_map = map.item_map.borrow_mut();
    let the_item_parent_map = map.item_parent_map.borrow_mut();

    let ii_parent_id = fld.new_item_id(DUMMY_ITEM_ID);
    let mut collector =
        collect::NodeCollector::for_inlined_item(
            ii_parent_id,
            ii_parent,
            mem::replace(&mut *the_map, vec![]),
            mem::replace(&mut *the_item_parent_map, NodeMap()),
            mem::replace(&mut *the_item_map, FnvHashMap()));
    visit::walk_inlined_item(&mut collector, &ii_parent.ii);
    let (map, item_parent_map, item_map) = collector.take();
    *the_map = map;
    *the_item_parent_map = item_parent_map;
    *the_item_map = item_map;

    &ii_parent.ii
}

pub trait NodePrinter {
    fn print_item_node(&mut self, node: &ItemNode) -> io::Result<()>;
    fn print_node(&mut self, node: &Node) -> io::Result<()>;
}

impl<'a> NodePrinter for pprust::State<'a> {
    fn print_item_node(&mut self, item: &ItemNode) -> io::Result<()> {
        match *item {
            ItemNode::Item(a)        => self.print_item(&*a),
            ItemNode::ForeignItem(a) => self.print_foreign_item(&*a),
            ItemNode::TraitItem(a)   => self.print_trait_item(a),
            ItemNode::ImplItem(a)    => self.print_impl_item(a),
            ItemNode::Variant(a)     => self.print_variant(&*a),
            ItemNode::ClosureItem(a) => self.print_expr(&*a),
            ItemNode::StructCtor(_)  => panic!("cannot print isolated StructCtor"),
        }
    }
    fn print_node(&mut self, node: &Node) -> io::Result<()> {
        match *node {
            NodeExpr(a)        => self.print_expr(&*a),
            NodeStmt(a)        => self.print_stmt(&*a),
            NodePat(a)         => self.print_pat(&*a),
            NodeBlock(a)       => self.print_block(&*a),
            NodeLifetime(a)    => self.print_lifetime(&*a),

            // these cases do not carry enough information in the
            // ast_map to reconstruct their full structure for pretty
            // printing.
            NodeLocal(_)       => panic!("cannot print isolated Local"),
            NodeArg(_)         => panic!("cannot print isolated Arg"),
        }
    }
}

fn item_id_to_string(map: &Map, id: ItemId, include_id: bool) -> String {
    let id_str = format!(" (id={:?})", id);
    let id_str = if include_id { &id_str[..] } else { "" };
    match map.find_item(id) {
        Some(ItemNode::Item(item)) => {
            let path_str = map.path_to_str_with_ident(id, item.ident);
            let item_str = match item.node {
                ItemExternCrate(..) => "extern crate",
                ItemUse(..) => "use",
                ItemStatic(..) => "static",
                ItemConst(..) => "const",
                ItemFn(..) => "fn",
                ItemMod(..) => "mod",
                ItemForeignMod(..) => "foreign mod",
                ItemTy(..) => "ty",
                ItemEnum(..) => "enum",
                ItemStruct(..) => "struct",
                ItemTrait(..) => "trait",
                ItemImpl(..) => "impl",
                ItemDefaultImpl(..) => "default impl",
                ItemMac(..) => "macro"
            };
            format!("{} {}{}", item_str, path_str, id_str)
        }
        Some(ItemNode::ForeignItem(item)) => {
            let path_str = map.path_to_str_with_ident(id, item.ident);
            format!("foreign item {}{}", path_str, id_str)
        }
        Some(ItemNode::ImplItem(ii)) => {
            match ii.node {
                ConstImplItem(..) => {
                    format!("assoc const {} in {}{}",
                            token::get_ident(ii.ident),
                            map.path_to_string(id),
                            id_str)
                }
                MethodImplItem(..) => {
                    format!("method {} in {}{}",
                            token::get_ident(ii.ident),
                            map.path_to_string(id), id_str)
                }
                TypeImplItem(_) => {
                    format!("assoc type {} in {}{}",
                            token::get_ident(ii.ident),
                            map.path_to_string(id),
                            id_str)
                }
                MacImplItem(ref mac) => {
                    format!("method macro {}{}",
                            pprust::mac_to_string(mac), id_str)
                }
            }
        }
        Some(ItemNode::TraitItem(ti)) => {
            let kind = match ti.node {
                ConstTraitItem(..) => "assoc constant",
                MethodTraitItem(..) => "trait method",
                TypeTraitItem(..) => "assoc type",
            };

            format!("{} {} in {}{}",
                    kind,
                    token::get_ident(ti.ident),
                    map.path_to_string(id),
                    id_str)
        }
        Some(ItemNode::Variant(ref variant)) => {
            format!("variant {} in {}{}",
                    token::get_ident(variant.node.name),
                    map.path_to_string(id), id_str)
        }
        Some(ItemNode::StructCtor(_)) => {
            format!("struct_ctor {}{}", map.path_to_string(id), id_str)
        }
        None => {
            format!("unknown node{}", id_str)
        }
    }
}

fn node_id_to_string(map: &Map, id: NodeId, include_id: bool) -> String {
    let id_str = format!(" (id={})", id);
    let id_str = if include_id { &id_str[..] } else { "" };

    match map.find(id) {
        Some(NodeExpr(ref expr)) => {
            format!("expr {}{}", pprust::expr_to_string(&**expr), id_str)
        }
        Some(NodeStmt(ref stmt)) => {
            format!("stmt {}{}", pprust::stmt_to_string(&**stmt), id_str)
        }
        Some(NodeArg(ref pat)) => {
            format!("arg {}{}", pprust::pat_to_string(&**pat), id_str)
        }
        Some(NodeLocal(ref pat)) => {
            format!("local {}{}", pprust::pat_to_string(&**pat), id_str)
        }
        Some(NodePat(ref pat)) => {
            format!("pat {}{}", pprust::pat_to_string(&**pat), id_str)
        }
        Some(NodeBlock(ref block)) => {
            format!("block {}{}", pprust::block_to_string(&**block), id_str)
        }
        Some(NodeLifetime(ref l)) => {
            format!("lifetime {}{}",
                    pprust::lifetime_to_string(&**l), id_str)
        }
        None => {
            format!("unknown node{}", id_str)
        }
    }
}

