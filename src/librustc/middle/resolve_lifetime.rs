// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
 * Name resolution for lifetimes.
 *
 * Name resolution for lifetimes follows MUCH simpler rules than the
 * full resolve. For example, lifetime names are never exported or
 * used between functions, and they operate in a purely top-down
 * way. Therefore we break lifetime name resolution into a separate pass.
 */

use driver::session;
use std::hashmap::HashMap;
use syntax::ast;
use syntax::codemap::Span;
use syntax::opt_vec;
use syntax::opt_vec::OptVec;
use syntax::parse::token::special_idents;
use syntax::visit;
use syntax::visit::Visitor;

pub type NamedRegionMap = HashMap<ast::NodeId, ast::DefRegion>;

struct LifetimeContext {
    sess: session::Session,
    lifetime_map: @mut NamedRegionMap,
}

enum ScopeChain<'self> {
    ItemScope(&'self OptVec<ast::Lifetime>),
    FnScope(&'self OptVec<ast::Lifetime>, &'self ScopeChain<'self>),
    BlockScope(ast::NodeId, &'self ScopeChain<'self>),
    RootScope
}

pub fn crate(sess: session::Session,
             crate: @ast::Crate)
             -> @mut NamedRegionMap {
    let mut ctxt = LifetimeContext {
        sess: sess,
        lifetime_map: @mut HashMap::new()
    };
    visit::walk_crate(&mut ctxt, crate, &RootScope);
    sess.abort_if_errors();
    ctxt.lifetime_map
}

impl<'self> Visitor<&'self ScopeChain<'self>> for LifetimeContext {
    fn visit_item(&mut self,
                  item: @ast::item,
                  _: &'self ScopeChain<'self>) {
        let scope = match item.node {
            ast::item_fn(*) | // fn lifetimes get added in visit_fn below
            ast::item_mod(*) |
            ast::item_mac(*) |
            ast::item_foreign_mod(*) |
            ast::item_static(*) => {
                RootScope
            }
            ast::item_ty(_, ref generics) |
            ast::item_enum(_, ref generics) |
            ast::item_struct(_, ref generics) |
            ast::item_impl(ref generics, _, _, _) |
            ast::item_trait(ref generics, _, _) => {
                ItemScope(&generics.lifetimes)
            }
        };
        visit::walk_item(self, item, &scope)
    }

    fn visit_fn(&mut self,
                fk: &visit::fn_kind,
                fd: &ast::fn_decl,
                b: &ast::Block,
                s: Span,
                n: ast::NodeId,
                scope: &'self ScopeChain<'self>) {
        match *fk {
            visit::fk_item_fn(_, generics, _, _) |
            visit::fk_method(_, generics, _) => {
                let scope1 = FnScope(&generics.lifetimes, scope);
                visit::walk_fn(self, fk, fd, b, s, n, &scope1);
            }
            visit::fk_anon(*) | visit::fk_fn_block(*) => {
                visit::walk_fn(self, fk, fd, b, s, n, scope);
            }
        }
    }

    fn visit_ty(&mut self,
                ty: &ast::Ty,
                scope: &'self ScopeChain<'self>) {
        match ty.node {
            ast::ty_closure(@ast::TyClosure { lifetimes: ref lifetimes, _ }) |
            ast::ty_bare_fn(@ast::TyBareFn { lifetimes: ref lifetimes, _ }) => {
                let scope1 = FnScope(lifetimes, scope);
                visit::walk_ty(self, ty, &scope1);
            }
            _ => {
                visit::walk_ty(self, ty, scope);
            }
        }
    }

    fn visit_ty_method(&mut self,
                       m: &ast::TypeMethod,
                       scope: &'self ScopeChain<'self>) {
        let scope1 = FnScope(&m.generics.lifetimes, scope);
        visit::walk_ty_method(self, m, &scope1);
    }

    fn visit_block(&mut self,
                   b: &ast::Block,
                   scope: &'self ScopeChain<'self>) {
        let scope1 = BlockScope(b.id, scope);
        visit::walk_block(self, b, &scope1);
    }

    fn visit_lifetime_ref(&mut self,
                          lifetime_ref: &ast::Lifetime,
                          scope: &'self ScopeChain<'self>) {
        if lifetime_ref.ident == special_idents::statik {
            self.lifetime_map.insert(lifetime_ref.id, ast::DefStaticRegion);
            return;
        }

        // Walk back up the scopes, searching for `lifetime_ref`.
        //
        // `depth` - tracks the number of fn scopes (binding scopes) that we pass
        //           through.
        //
        // `free` - tracks the outermost block that we pass through
        let mut depth = 0;
        let mut scope = scope;
        let mut free = None;
        loop {
            match *scope {
                BlockScope(id, s) => {
                    free = Some(id);
                    scope = s;
                }

                RootScope => {
                    break;
                }

                ItemScope(lifetimes) => {
                    if search_lifetimes(self, lifetimes, lifetime_ref,
                                        depth, free) {
                        return;
                    }

                    break;
                }

                FnScope(lifetimes, s) => {
                    if search_lifetimes(self, lifetimes, lifetime_ref,
                                        depth, free) {
                        return;
                    }

                    depth += 1;
                    scope = s;
                }
            }
        }

        self.sess.span_err(
            lifetime_ref.span,
            fmt!("use of undeclared lifetime name `'%s`",
                 self.sess.str_of(lifetime_ref.ident)));

        fn search_lifetimes(this: &LifetimeContext,
                            lifetimes: &OptVec<ast::Lifetime>,
                            lifetime_ref: &ast::Lifetime,
                            depth: uint,
                            free: Option<ast::NodeId>)
                            -> bool {
            for lifetime_decl in lifetimes.iter() {
                if lifetime_decl.ident == lifetime_ref.ident {
                    let def = match free {
                        None => ast::DefBoundRegion(depth, lifetime_decl.id),
                        Some(f) => ast::DefFreeRegion(f, lifetime_decl.id)
                    };
                    this.lifetime_map.insert(lifetime_ref.id, def);
                    return true;
                }
            }
            return false;
        }
    }
}
