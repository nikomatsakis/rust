// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
use self::Context::*;

use rustc::session::Session;

use rustc::dep_graph::DepNode;
use rustc::hir::map::Map;
use rustc::hir::intravisit::{self, Visitor, NestedVisitMode};
use rustc::hir;
use syntax_pos::Span;

#[derive(Clone, Copy, PartialEq)]
enum Context {
    Normal,
    Loop,
    Closure,
}

#[derive(Copy, Clone)]
struct CheckLoopVisitor<'a, 'ast: 'a> {
    sess: &'a Session,
    map: &'a Map<'ast>,
    cx: Context,
}

pub fn check_crate(sess: &Session, map: &Map) {
    let _task = map.dep_graph.in_task(DepNode::CheckLoops);
    let krate = map.krate();
    krate.visit_all_item_likes(&mut CheckLoopVisitor {
        sess: sess,
        map: map,
        cx: Normal,
    }.as_deep_visitor());
}

impl<'a, 'ast> Visitor<'ast> for CheckLoopVisitor<'a, 'ast> {
    fn nested_visit_map(&mut self) -> Option<(&hir::map::Map<'ast>, NestedVisitMode)> {
        Some((&self.map, NestedVisitMode::OnlyBodies))
    }

    fn visit_item(&mut self, i: &'ast hir::Item) {
        self.with_context(Normal, |v| intravisit::walk_item(v, i));
    }

    fn visit_impl_item(&mut self, i: &'ast hir::ImplItem) {
        self.with_context(Normal, |v| intravisit::walk_impl_item(v, i));
    }

    fn visit_expr(&mut self, e: &'ast hir::Expr) {
        match e.node {
            hir::ExprWhile(ref e, ref b, _) => {
                self.visit_expr(&e);
                self.with_context(Loop, |v| v.visit_block(&b));
            }
            hir::ExprLoop(ref b, _) => {
                self.with_context(Loop, |v| v.visit_block(&b));
            }
            hir::ExprClosure(.., b, _) => {
                self.with_context(Closure, |v| v.visit_body(b));
            }
            hir::ExprBreak(_) => self.require_loop("break", e.span),
            hir::ExprAgain(_) => self.require_loop("continue", e.span),
            _ => intravisit::walk_expr(self, e),
        }
    }
}

impl<'a, 'ast> CheckLoopVisitor<'a, 'ast> {
    fn with_context<F>(&mut self, cx: Context, f: F)
        where F: FnOnce(&mut CheckLoopVisitor<'a, 'ast>)
    {
        let old_cx = self.cx;
        self.cx = cx;
        f(self);
        self.cx = old_cx;
    }

    fn require_loop(&self, name: &str, span: Span) {
        match self.cx {
            Loop => {}
            Closure => {
                struct_span_err!(self.sess, span, E0267, "`{}` inside of a closure", name)
                .span_label(span, &format!("cannot break inside of a closure"))
                .emit();
            }
            Normal => {
                struct_span_err!(self.sess, span, E0268, "`{}` outside of loop", name)
                .span_label(span, &format!("cannot break outside of a loop"))
                .emit();
            }
        }
    }
}
