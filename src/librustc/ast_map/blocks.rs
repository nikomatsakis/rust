// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This module provides a simplified abstraction for working with
//! code blocks identified by their integer node-id.  In particular,
//! it captures a common set of attributes that all "function-like
//! things" (represented by `FnLike` instances) share.  For example,
//! all `FnLike` instances have a type signature (be it explicit or
//! inferred).  And all `FnLike` instances have a body, i.e. the code
//! that is run when the function-like thing it represents is invoked.
//!
//! With the above abstraction in place, one can treat the program
//! text as a collection of blocks of code (and most such blocks are
//! nested within a uniquely determined `FnLike`), and users can ask
//! for the `Code` associated with a particular ItemId.

pub use self::Code::*;

use ast_map::{self, ItemNode};
use syntax::abi;
use syntax::ast::{Block, FnDecl, ItemId};
use syntax::ast;
use syntax::codemap::Span;
use syntax::visit;

/// An FnLikeItemNode is a Item that is like a fn, in that it has a decl
/// and a body (as well as a ItemId, a span, etc).
///
/// More specifically, it is one of either:
///   - A function item,
///   - A closure expr (i.e. an ExprClosure), or
///   - The default implementation for a trait method.
///
/// To construct one, use the `Code::from_node` function.
#[derive(Copy, Clone)]
pub struct FnLikeItemNode<'a> { node: ast_map::ItemNode<'a> }

/// MaybeFnLike wraps a method that indicates if an object
/// corresponds to some FnLikeItemNode.
pub trait MaybeFnLike { fn is_fn_like(&self) -> bool; }

/// Components shared by fn-like things (fn items, methods, closures).
pub struct FnParts<'a> {
    pub decl: &'a FnDecl,
    pub body: &'a Block,
    pub kind: visit::FnKind<'a>,
    pub span: Span,
    pub id:   ItemId,
}

impl MaybeFnLike for ast::Item {
    fn is_fn_like(&self) -> bool {
        match self.node { ast::ItemFn(..) => true, _ => false, }
    }
}

impl MaybeFnLike for ast::TraitItem {
    fn is_fn_like(&self) -> bool {
        match self.node { ast::MethodTraitItem(_, Some(_)) => true, _ => false, }
    }
}

impl MaybeFnLike for ast::Expr {
    fn is_fn_like(&self) -> bool {
        match self.node {
            ast::ExprClosure(..) => true,
            _ => false,
        }
    }
}

/// Carries either an FnLikeItemNode or a Block, as these are the two
/// constructs that correspond to "code" (as in, something from which
/// we can construct a control-flow graph).
#[derive(Copy, Clone)]
pub enum Code<'a> {
    FnLikeCode(FnLikeItemNode<'a>),
    BlockCode(&'a Block),
}

impl<'a> Code<'a> {
    pub fn id(&self) -> ast_map::ItemOrBlockId {
        match *self {
            FnLikeCode(node) => ast_map::ItemOrBlockId::Item(node.id()),
            BlockCode(block) => ast_map::ItemOrBlockId::Block(block.id),
        }
    }

    /// Attempts to construct a Code from presumed FnLike or Block node input.
    pub fn from_item_node(node: ItemNode) -> Option<Code> {
        FnLikeItemNode::from_node(node).map(|fn_like| FnLikeCode(fn_like))
    }
}

/// These are all the components one can extract from a fn item for
/// use when implementing FnLikeItemNode operations.
struct ItemFnParts<'a> {
    ident:    ast::Ident,
    decl:     &'a ast::FnDecl,
    unsafety: ast::Unsafety,
    constness: ast::Constness,
    abi:      abi::Abi,
    vis:      ast::Visibility,
    generics: &'a ast::Generics,
    body:     &'a Block,
    id:       ast::ItemId,
    span:     Span
}

/// These are all the components one can extract from a closure expr
/// for use when implementing FnLikeItemNode operations.
struct ClosureParts<'a> {
    decl: &'a FnDecl,
    body: &'a Block,
    id: ItemId,
    span: Span
}

impl<'a> ClosureParts<'a> {
    fn new(d: &'a FnDecl, b: &'a Block, id: ItemId, s: Span) -> ClosureParts<'a> {
        ClosureParts { decl: d, body: b, id: id, span: s }
    }
}

impl<'a> FnLikeItemNode<'a> {
    /// Attempts to construct a FnLikeItemNode from presumed FnLike node input.
    pub fn from_node(node: ItemNode) -> Option<FnLikeItemNode> {
        let fn_like = match node {
            ItemNode::Item(item) => item.is_fn_like(),
            ItemNode::TraitItem(tm) => tm.is_fn_like(),
            ItemNode::ImplItem(_) => true,
            ItemNode::ClosureItem(e) => e.is_fn_like(),
            _ => false
        };
        if fn_like {
            Some(FnLikeItemNode {
                node: node
            })
        } else {
            None
        }
    }

    pub fn to_fn_parts(self) -> FnParts<'a> {
        FnParts {
            decl: self.decl(),
            body: self.body(),
            kind: self.kind(),
            span: self.span(),
            id:   self.id(),
        }
    }

    pub fn body(self) -> &'a Block {
        self.handle(|i: ItemFnParts<'a>|  &*i.body,
                    |_, _, _: &'a ast::MethodSig, _, body: &'a ast::Block, _|  body,
                    |c: ClosureParts<'a>| c.body)
    }

    pub fn decl(self) -> &'a FnDecl {
        self.handle(|i: ItemFnParts<'a>|  &*i.decl,
                    |_, _, sig: &'a ast::MethodSig, _, _, _|  &sig.decl,
                    |c: ClosureParts<'a>| c.decl)
    }

    pub fn span(self) -> Span {
        self.handle(|i: ItemFnParts|     i.span,
                    |_, _, _: &'a ast::MethodSig, _, _, span| span,
                    |c: ClosureParts|    c.span)
    }

    pub fn id(self) -> ItemId {
        self.handle(|i: ItemFnParts|     i.id,
                    |id, _, _: &'a ast::MethodSig, _, _, _| id,
                    |c: ClosureParts|    c.id)
    }

    pub fn kind(self) -> visit::FnKind<'a> {
        let item = |p: ItemFnParts<'a>| -> visit::FnKind<'a> {
            visit::FkItemFn(p.ident, p.generics, p.unsafety, p.constness, p.abi, p.vis)
        };
        let closure = |cp: ClosureParts| {
            visit::FkFnBlock(cp.id)
        };
        let method = |_, ident, sig: &'a ast::MethodSig, vis, _, _| {
            visit::FkMethod(ident, sig, vis)
        };
        self.handle(item, method, closure)
    }

    fn handle<A, I, M, C>(self, item_fn: I, method: M, closure: C) -> A where
        I: FnOnce(ItemFnParts<'a>) -> A,
        M: FnOnce(ItemId,
                  ast::Ident,
                  &'a ast::MethodSig,
                  Option<ast::Visibility>,
                  &'a ast::Block,
                  Span)
                  -> A,
        C: FnOnce(ClosureParts<'a>) -> A,
    {
        match self.node {
            ItemNode::Item(i) => match i.node {
                ast::ItemFn(ref decl, unsafety, constness, abi, ref generics, ref block) =>
                    item_fn(ItemFnParts {
                        id: i.id,
                        ident: i.ident,
                        decl: &**decl,
                        unsafety: unsafety,
                        body: &**block,
                        generics: generics,
                        abi: abi,
                        vis: i.vis,
                        constness: constness,
                        span: i.span
                    }),
                _ => panic!("item FnLikeItemNode that is not fn-like"),
            },
            ItemNode::TraitItem(ti) => match ti.node {
                ast::MethodTraitItem(ref sig, Some(ref body)) => {
                    method(ti.id, ti.ident, sig, None, body, ti.span)
                }
                _ => panic!("trait method FnLikeItemNode that is not fn-like"),
            },
            ItemNode::ImplItem(ii) => {
                match ii.node {
                    ast::MethodImplItem(ref sig, ref body) => {
                        method(ii.id, ii.ident, sig, Some(ii.vis), body, ii.span)
                    }
                    _ => {
                        panic!("impl method FnLikeItemNode that is not fn-like")
                    }
                }
            }
            ItemNode::ClosureItem(e) => match e.node {
                ast::ExprClosure(item_id, _, ref decl, ref block) =>
                    closure(ClosureParts::new(&**decl, &**block, item_id, e.span)),
                _ => panic!("expr FnLikeItemNode that is not fn-like"),
            },
            _ => panic!("other FnLikeItemNode that is not fn-like"),
        }
    }
}
