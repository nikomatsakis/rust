// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

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

use super::{MapEntry, MapEntryKind};
use super::{InlinedParent};
use super::{ItemNode, ItemMapEntry};
use super::{Node};

/// A Visitor that walks over an AST and collects Node's into an AST Map.
struct NodeCollector<'ast> {
    map: Vec<MapEntry<'ast>>,
    item_parent_map: NodeMap<ItemId>,
    item_map: FnvHashMap<ItemId, ItemMapEntry<'ast>>,
    parent_node: NodeId,
    parent_item: ItemId,
}

impl<'ast> NodeCollector<'ast> {
    pub fn for_krate() -> NodeCollector<'ast> {
        let mut collector = NodeCollector {
            map: vec![],
            item_parent_map: NodeMap(),
            item_map: FnvHashMap(),
            parent_node: DUMMY_NODE_ID,
            parent_item: CRATE_ITEM_ID,
        };
        collector.insert_item_entry(CRATE_ITEM_ID, ItemMapEntry::RootCrate);
        collector
    }

    pub fn for_inlined_item(id: ItemId,
                            p: &'ast InlinedParent,
                            map: Vec<MapEntry<'ast>>,
                            item_parent_map: NodeMap<ItemId>,
                            item_map: FnvHashMap<ItemId, ItemMapEntry<'ast>>)
                            -> NodeCollector<'ast> {
        let mut collector = NodeCollector {
            map: map,
            item_parent_map: item_parent_map,
            item_map: item_map,
            parent_node: DUMMY_NODE_ID,
            parent_item: id,
        };

        collector.insert_item_entry(CRATE_ITEM_ID, ItemMapEntry::RootInlinedParent(p));

        // Methods get added to the AST map when their impl is visited.  Since we
        // don't decode and instantiate the impl, but just the method, we have to
        // add it to the table now. Likewise with foreign items.
        match p.ii {
            IIItem(_) => {}
            IITraitItem(_, ref ti) => {
                collector.insert_item(ti.id, ItemNode::TraitItem(ti));
            }
            IIImplItem(_, ref ii) => {
                collector.insert_item(ii.id, ItemNode::ImplItem(ii));
            }
            IIForeign(ref i) => {
                collector.insert_item(i.id, ItemNode::ForeignItem(i));
            }
        }

        collector
    }

    fn take(self) -> (Vec<MapEntry<'ast>>,
                      NodeMap<ItemId>,
                      FnvHashMap<ItemId, ItemMapEntry<'ast>>) {
        (self.map, self.item_parent_map, self.item_map)
    }

    fn insert_entry(&mut self, id: NodeId, entry: MapEntry<'ast>) {
        debug!("ast_map: {:?} => {:?}", id, entry);
        let len = self.map.len();
        if id as usize >= len {
            let empty = MapEntry { parent_node: DUMMY_NODE_ID, kind: MapEntryKind::NotPresent };
            self.map.extend(repeat(empty).take(id as usize - len + 1));
        }
        self.map[id as usize] = entry;
    }

    fn insert_item_entry(&mut self, id: ItemId, entry: ItemMapEntry<'ast>) {
        debug!("ast_map: {:?} => {:?}", id, entry);
        let prev = self.item_map.insert(id, entry);
        assert!(prev.is_none());
    }

    fn insert(&mut self, id: NodeId, node: Node<'ast>) {
        let entry = MapEntry::from_node(self.parent_node, node);
        if self.parent_node == DUMMY_NODE_ID {
            self.item_parent_map.insert(id, self.parent_item);
        }
        self.insert_entry(id, entry);
    }

    fn insert_item(&mut self, id: ItemId, item_node: ItemNode<'ast>) {
        let entry = ItemMapEntry::from_item_node(self.parent_item, item_node);
        self.insert_item_entry(id, entry);
    }

    fn visit_fn_decl(&mut self, decl: &'ast FnDecl) {
        for a in &decl.inputs {
            self.insert(a.id, Node::NodeArg(&*a.pat));
        }
    }
}

impl<'ast> Visitor<'ast> for NodeCollector<'ast> {
    fn visit_item(&mut self, i: &'ast Item) {
        self.insert_item(i.id, ItemNode::Item(i));

        let parent_item = self.parent_item;
        self.parent_item = i.id;

        match i.node {
            ItemImpl(_, _, _, _, _, ref impl_items) => {
                for ii in impl_items {
                    self.insert_item(ii.id, ItemNode::ImplItem(ii));
                }
            }
            ItemEnum(ref enum_definition, _) => {
                for v in &enum_definition.variants {
                    self.insert_item(v.node.id, ItemNode::Variant(&**v));
                }
            }
            ItemForeignMod(ref nm) => {
                for nitem in &nm.items {
                    self.insert_item(nitem.id, ItemNode::ForeignItem(&**nitem));
                }
            }
            ItemStruct(ref struct_def, _) => {
                // If this is a tuple-like struct, register the constructor.
                match struct_def.ctor_id {
                    Some(ctor_id) => {
                        self.insert_item(ctor_id, ItemNode::StructCtor(&**struct_def));
                    }
                    None => {}
                }
            }
            ItemTrait(_, _, ref bounds, ref trait_items) => {
                for ti in trait_items {
                    self.insert_item(ti.id, ItemNode::TraitItem(ti));
                }
            }
            ItemUse(ref view_path) => {
                match view_path.node {
                    ViewPathList(_, ref paths) => {
                        for path in paths {
                            self.insert_item(path.node.id(), ItemNode::Item(i));
                        }
                    }
                    _ => ()
                }
            }
            _ => {}
        }
        visit::walk_item(self, i);
        self.parent_item = parent_item;
    }

    fn visit_trait_item(&mut self, ti: &'ast TraitItem) {
        let parent_item = self.parent_item;
        self.parent_item = ti.id;
        visit::walk_trait_item(self, ti);
        self.parent_item = parent_item;
    }

    fn visit_impl_item(&mut self, ii: &'ast ImplItem) {
        let parent_item = self.parent_item;
        self.parent_item = ii.id;

        visit::walk_impl_item(self, ii);

        self.parent_item = parent_item;
    }

    fn visit_pat(&mut self, pat: &'ast Pat) {
        self.insert(pat.id, match pat.node {
            // Note: this is at least *potentially* a pattern...
            PatIdent(..) => Node::NodeLocal(pat),
            _ => Node::NodePat(pat)
        });

        let parent_node = self.parent_node;
        self.parent_node = pat.id;
        visit::walk_pat(self, pat);
        self.parent_node = parent_node;
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        self.insert(expr.id, Node::NodeExpr(expr));
        let parent_node = self.parent_node;
        self.parent_node = expr.id;

        match expr.node {
            ExprClosure(item_id, _, _, _) => {
                self.insert_item(item_id, ItemNode::ClosureItem(expr));
            }
            _ => { }
        }

        visit::walk_expr(self, expr);
        self.parent_node = parent_node;
    }

    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        let id = ast_util::stmt_id(stmt);
        self.insert(id, Node::NodeStmt(stmt));
        let parent_node = self.parent_node;
        self.parent_node = id;
        visit::walk_stmt(self, stmt);
        self.parent_node = parent_node;
    }

    fn visit_fn(&mut self, fk: visit::FnKind<'ast>, fd: &'ast FnDecl,
                b: &'ast Block, s: Span, id: ItemId) {
        match fk {
            visit::FkFnBlock(..) => {
                // Don't adjust parent_item for closures...this is
                // somewhat fishy, I'm modeling what the AST map did
                // before the itemid/nodeid split. (Note that the
                // parent node here will already be the closure
                // expression.)
                self.visit_fn_decl(fd);
                visit::walk_fn(self, fk, fd, b, s);
            }
            visit::FkItemFn(..) | visit::FkMethod(..) => {
                let parent_item = self.parent_item;
                self.parent_item = id;
                self.visit_fn_decl(fd);
                visit::walk_fn(self, fk, fd, b, s);
                self.parent_item = parent_item;
            }
        }
    }

    fn visit_ty(&mut self, ty: &'ast Ty) {
        let parent_node = self.parent_node;
        self.parent_node = ty.id;
        match ty.node {
            TyBareFn(ref fd) => {
                self.visit_fn_decl(&*fd.decl);
            }
            _ => {}
        }
        visit::walk_ty(self, ty);
        self.parent_node = parent_node;
    }

    fn visit_block(&mut self, block: &'ast Block) {
        self.insert(block.id, Node::NodeBlock(block));
        let parent_node = self.parent_node;
        self.parent_node = block.id;
        visit::walk_block(self, block);
        self.parent_node = parent_node;
    }

    fn visit_lifetime_ref(&mut self, lifetime: &'ast Lifetime) {
        self.insert(lifetime.id, Node::NodeLifetime(lifetime));
    }

    fn visit_lifetime_def(&mut self, def: &'ast LifetimeDef) {
        self.visit_lifetime_ref(&def.lifetime);
    }
}
