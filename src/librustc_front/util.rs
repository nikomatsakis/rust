// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use hir;
use hir::*;
use syntax::ast::{Ident, NodeId, DUMMY_NODE_ID};
use syntax::codemap::Span;
use syntax::ptr::P;
use syntax::owned_slice::OwnedSlice;

pub fn walk_pat<F>(pat: &Pat, mut it: F) -> bool
    where F: FnMut(&Pat) -> bool
{
    // FIXME(#19596) this is a workaround, but there should be a better way
    fn walk_pat_<G>(pat: &Pat, it: &mut G) -> bool
        where G: FnMut(&Pat) -> bool
    {
        if !(*it)(pat) {
            return false;
        }

        match pat.node {
            PatIdent(_, _, Some(ref p)) => walk_pat_(&**p, it),
            PatStruct(_, ref fields, _) => {
                fields.iter().all(|field| walk_pat_(&*field.node.pat, it))
            }
            PatEnum(_, Some(ref s)) | PatTup(ref s) => {
                s.iter().all(|p| walk_pat_(&**p, it))
            }
            PatBox(ref s) | PatRegion(ref s, _) => {
                walk_pat_(&**s, it)
            }
            PatVec(ref before, ref slice, ref after) => {
                before.iter().all(|p| walk_pat_(&**p, it)) &&
                slice.iter().all(|p| walk_pat_(&**p, it)) &&
                after.iter().all(|p| walk_pat_(&**p, it))
            }
            PatWild |
            PatLit(_) |
            PatRange(_, _) |
            PatIdent(_, _, _) |
            PatEnum(_, _) |
            PatQPath(_, _) => {
                true
            }
        }
    }

    walk_pat_(pat, &mut it)
}

pub fn binop_to_string(op: BinOp_) -> &'static str {
    match op {
        BiAdd => "+",
        BiSub => "-",
        BiMul => "*",
        BiDiv => "/",
        BiRem => "%",
        BiAnd => "&&",
        BiOr => "||",
        BiBitXor => "^",
        BiBitAnd => "&",
        BiBitOr => "|",
        BiShl => "<<",
        BiShr => ">>",
        BiEq => "==",
        BiLt => "<",
        BiLe => "<=",
        BiNe => "!=",
        BiGe => ">=",
        BiGt => ">",
    }
}

pub fn stmt_id(s: &Stmt) -> NodeId {
    match s.node {
        StmtDecl(_, id) => id,
        StmtExpr(_, id) => id,
        StmtSemi(_, id) => id,
    }
}

pub fn lazy_binop(b: BinOp_) -> bool {
    match b {
        BiAnd => true,
        BiOr => true,
        _ => false,
    }
}

pub fn is_shift_binop(b: BinOp_) -> bool {
    match b {
        BiShl => true,
        BiShr => true,
        _ => false,
    }
}

pub fn is_comparison_binop(b: BinOp_) -> bool {
    match b {
        BiEq | BiLt | BiLe | BiNe | BiGt | BiGe => true,
        BiAnd |
        BiOr |
        BiAdd |
        BiSub |
        BiMul |
        BiDiv |
        BiRem |
        BiBitXor |
        BiBitAnd |
        BiBitOr |
        BiShl |
        BiShr => false,
    }
}

/// Returns `true` if the binary operator takes its arguments by value
pub fn is_by_value_binop(b: BinOp_) -> bool {
    !is_comparison_binop(b)
}

/// Returns `true` if the unary operator takes its argument by value
pub fn is_by_value_unop(u: UnOp) -> bool {
    match u {
        UnNeg | UnNot => true,
        _ => false,
    }
}

pub fn unop_to_string(op: UnOp) -> &'static str {
    match op {
        UnDeref => "*",
        UnNot => "!",
        UnNeg => "-",
    }
}

pub fn is_path(e: P<Expr>) -> bool {
    match e.node {
        ExprPath(..) => true,
        _ => false,
    }
}

pub fn empty_generics() -> Generics {
    Generics {
        lifetimes: Vec::new(),
        ty_params: OwnedSlice::empty(),
        where_clause: WhereClause {
            id: DUMMY_NODE_ID,
            predicates: Vec::new(),
        },
    }
}

// convert a span and an identifier to the corresponding
// 1-segment path
pub fn ident_to_path(s: Span, ident: Ident) -> Path {
    hir::Path {
        span: s,
        global: false,
        segments: vec!(hir::PathSegment {
            identifier: ident,
            parameters: hir::AngleBracketedParameters(hir::AngleBracketedParameterData {
                lifetimes: Vec::new(),
                types: OwnedSlice::empty(),
                bindings: OwnedSlice::empty(),
            }),
        }),
    }
}
