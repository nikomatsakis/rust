// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


/*!
 * # Categorization
 *
 * The job of the categorization module is to analyze an expression to
 * determine what kind of memory is used in evaluating it (for example,
 * where dereferences occur and what kind of pointer is dereferenced;
 * whether the memory is mutable; etc)
 *
 * Categorization effectively transforms all of our expressions into
 * expressions of the following forms (the actual enum has many more
 * possibilities, naturally, but they are all variants of these base
 * forms):
 *
 *     E = rvalue    // some computed rvalue
 *       | x         // address of a local variable, arg, or upvar
 *       | *E        // deref of a ptr
 *       | E.comp    // access to an interior component
 *
 * Imagine a routine ToAddr(Expr) that evaluates an expression and returns an
 * address where the result is to be found.  If Expr is an lvalue, then this
 * is the address of the lvalue.  If Expr is an rvalue, this is the address of
 * some temporary spot in memory where the result is stored.
 *
 * Now, cat_expr() classies the expression Expr and the address A=ToAddr(Expr)
 * as follows:
 *
 * - cat: what kind of expression was this?  This is a subset of the
 *   full expression forms which only includes those that we care about
 *   for the purpose of the analysis.
 * - mutbl: mutability of the address A
 * - ty: the type of data found at the address A
 *
 * The resulting categorization tree differs somewhat from the expressions
 * themselves.  For example, auto-derefs are explicit.  Also, an index a[b] is
 * decomposed into two operations: a derefence to reach the array data and
 * then an index to jump forward to the relevant item.
 */

use core::prelude::*;

use middle::ty;
use middle::typeck;
use util::ppaux::{ty_to_str, region_to_str};
use util::common::indenter;

use core::uint;
use syntax::ast::{m_imm, m_const, m_mutbl};
use syntax::ast;
use syntax::codemap::span;
use syntax::print::pprust;

#[deriving_eq]
pub enum categorization {
    cat_rvalue,                        // result of eval'ing some misc expr
    cat_static_item,
    cat_implicit_self,
    cat_copied_upvar(ast::node_id),    // upvar copied into @fn or ~fn env
    cat_local(ast::node_id),           // local variable
    cat_arg(ast::node_id, ast::rmode), // formal argument
    cat_stack_upvar(cmt),              // upvar in stack closure
    cat_deref(cmt, uint, ptr_kind),    // deref of a ptr
    cat_interior(cmt, interior_kind),          // something interior
    cat_discr(cmt, ast::node_id),      // match discriminant (see preserve())
    cat_self(ast::node_id),            // explicit `self`
}

// different kinds of pointers:
#[deriving_eq]
pub enum ptr_kind {
    uniq_ptr(ast::mutability),
    gc_ptr(ast::mutability),
    region_ptr(ast::mutability, ty::Region),
    unsafe_ptr
}

// We use the term "interior" to mean "something reachable from the
// base without a pointer dereference", e.g. a field
#[deriving_eq]
pub enum interior_kind {
    interior_tuple,                  // elt in a tuple
    interior_anon_field,             // anonymous field (in e.g.
                                 // struct Foo(int, int);
    interior_variant(ast::def_id),   // internals to a variant of given enum
    interior_field(ast::ident,       // name of field
               ast::mutability), // declared mutability of field
    interior_index(ty::t,            // type of vec/str/etc being deref'd
               ast::mutability)  // mutability of vec content
}

#[deriving_eq]
pub enum MutabilityCategory {
    McImmutable, // Immutable.
    McReadOnly,  // Read-only (`const`)
    McDeclared,  // Directly declared as mutable.
    McInherited  // Inherited from the fact that owner is mutable.
}

// a complete categorization of a value indicating where it originated
// and how it is located, as well as the mutability of the memory in
// which the value is stored.
//
// note: cmt stands for "categorized mutable type".
#[deriving_eq]
pub struct cmt_ {
    id: ast::node_id,          // id of expr/pat producing this value
    span: span,                // span of same expr/pat
    cat: categorization,       // categorization of expr
    mutbl: MutabilityCategory, // mutability of expr as lvalue
    ty: ty::t                  // type of the expr
}

pub type cmt = @cmt_;

// We pun on *T to mean both actual deref of a ptr as well
// as accessing of components:
pub enum deref_kind {deref_ptr(ptr_kind), deref_interior(interior_kind)}

// Categorizes a derefable type.  Note that we include vectors and strings as
// derefable (we model an index as the combination of a deref and then a
// pointer adjustment).
pub fn opt_deref_kind(t: ty::t) -> Option<deref_kind> {
    match ty::get(t).sty {
        ty::ty_uniq(mt) => {
            Some(deref_ptr(uniq_ptr(mt.mutbl)))
        }

        ty::ty_evec(_, ty::vstore_uniq) |
        ty::ty_estr(ty::vstore_uniq) |
        ty::ty_closure(ty::ClosureTy {sigil: ast::OwnedSigil, _}) => {
            Some(deref_ptr(uniq_ptr(m_imm)))
        }

        ty::ty_rptr(r, mt) |
        ty::ty_evec(mt, ty::vstore_slice(r)) => {
            Some(deref_ptr(region_ptr(mt.mutbl, r)))
        }

        ty::ty_estr(ty::vstore_slice(r)) |
        ty::ty_closure(ty::ClosureTy {sigil: ast::BorrowedSigil,
                                      region: r, _}) => {
            Some(deref_ptr(region_ptr(ast::m_imm, r)))
        }

        ty::ty_box(mt) |
        ty::ty_evec(mt, ty::vstore_box) => {
            Some(deref_ptr(gc_ptr(mt.mutbl)))
        }

        ty::ty_estr(ty::vstore_box) |
        ty::ty_closure(ty::ClosureTy {sigil: ast::ManagedSigil, _}) => {
            Some(deref_ptr(gc_ptr(ast::m_imm)))
        }

        ty::ty_ptr(*) => {
            Some(deref_ptr(unsafe_ptr))
        }

        ty::ty_enum(did, _) => {
            Some(deref_interior(interior_variant(did)))
        }

        ty::ty_struct(_, _) => {
            Some(deref_interior(interior_anon_field))
        }

        ty::ty_evec(mt, ty::vstore_fixed(_)) => {
            Some(deref_interior(interior_index(t, mt.mutbl)))
        }

        ty::ty_estr(ty::vstore_fixed(_)) => {
            Some(deref_interior(interior_index(t, m_imm)))
        }

        _ => None
    }
}

pub fn deref_kind(tcx: ty::ctxt, t: ty::t) -> deref_kind {
    match opt_deref_kind(t) {
      Some(k) => k,
      None => {
        tcx.sess.bug(
            fmt!("deref_cat() invoked on non-derefable type %s",
                 ty_to_str(tcx, t)));
      }
    }
}

pub fn cat_expr(tcx: ty::ctxt,
                method_map: typeck::method_map,
                expr: @ast::expr)
             -> cmt {
    let mcx = &mem_categorization_ctxt {
        tcx: tcx, method_map: method_map
    };
    return mcx.cat_expr(expr);
}

pub fn cat_expr_unadjusted(tcx: ty::ctxt,
                           method_map: typeck::method_map,
                           expr: @ast::expr)
                        -> cmt {
    let mcx = &mem_categorization_ctxt {
        tcx: tcx, method_map: method_map
    };
    return mcx.cat_expr_unadjusted(expr);
}

pub fn cat_expr_autoderefd(
    tcx: ty::ctxt,
    method_map: typeck::method_map,
    expr: @ast::expr,
    autoderefs: uint) -> cmt
{
    let mcx = &mem_categorization_ctxt {
        tcx: tcx, method_map: method_map
    };
    return mcx.cat_expr_autoderefd(expr, autoderefs);
}

pub fn cat_def(
    tcx: ty::ctxt,
    method_map: typeck::method_map,
    expr_id: ast::node_id,
    expr_span: span,
    expr_ty: ty::t,
    def: ast::def) -> cmt {

    let mcx = &mem_categorization_ctxt {
        tcx: tcx, method_map: method_map
    };
    return mcx.cat_def(expr_id, expr_span, expr_ty, def);
}

pub fn cat_variant<N:ast_node>(
    tcx: ty::ctxt,
    method_map: typeck::method_map,
    arg: N,
    enum_did: ast::def_id,
    cmt: cmt) -> cmt {

    let mcx = &mem_categorization_ctxt {
        tcx: tcx, method_map: method_map
    };
    return mcx.cat_variant(arg, enum_did, cmt);
}

pub trait ast_node {
    fn id(&self) -> ast::node_id;
    fn span(&self) -> span;
}

impl ast_node for @ast::expr {
    fn id(&self) -> ast::node_id { self.id }
    fn span(&self) -> span { self.span }
}

impl ast_node for @ast::pat {
    fn id(&self) -> ast::node_id { self.id }
    fn span(&self) -> span { self.span }
}

pub trait get_type_for_node {
    fn ty<N:ast_node>(&self, node: N) -> ty::t;
}

impl get_type_for_node for ty::ctxt {
    fn ty<N:ast_node>(&self, node: N) -> ty::t {
        ty::node_id_to_type(*self, node.id())
    }
}

pub struct mem_categorization_ctxt {
    tcx: ty::ctxt,
    method_map: typeck::method_map,
}

impl ToStr for MutabilityCategory {
    pure fn to_str(&self) -> ~str {
        fmt!("%?", *self)
    }
}

pub impl MutabilityCategory {
    static fn from_mutbl(&self, m: ast::mutability) -> MutabilityCategory {
        match m {
            m_imm => McImmutable,
            m_const => McReadOnly,
            m_mutbl => McDeclared
        }
    }

    fn inherit(&self) -> MutabilityCategory {
        match *self {
            McImmutable => McImmutable,
            McReadOnly => McReadOnly,
            McDeclared => McInherited,
            McInherited => McInherited
        }
    }

    fn is_mutable(&self) -> bool {
        match *self {
            McImmutable | McReadOnly => false,
            McDeclared | McInherited => true
        }
    }

    fn is_immutable(&self) -> bool {
        match *self {
            McImmutable => true,
            McReadOnly | McDeclared | McInherited => false
        }
    }

    fn to_user_str(&self) -> ~str {
        match *self {
            McDeclared | McInherited => ~"mutable",
            McImmutable => ~"immutable",
            McReadOnly => ~"const"
        }
    }
}

pub impl mem_categorization_ctxt {
    fn cat_expr(&self, expr: @ast::expr) -> cmt {
        match self.tcx.adjustments.find(&expr.id) {
            None => {
                // No adjustments.
                self.cat_expr_unadjusted(expr)
            }

            Some(@ty::AutoAddEnv(*)) => {
                // Convert a bare fn to a closure by adding NULL env.
                // Result is an rvalue.
                let expr_ty = ty::expr_ty_adjusted(self.tcx, expr);
                self.cat_rvalue(expr, expr_ty)
            }

            Some(
                @ty::AutoDerefRef(
                    ty::AutoDerefRef {
                        autoref: Some(_), _})) => {
                // Equivalent to &*expr or something similar.
                // Result is an rvalue.
                let expr_ty = ty::expr_ty_adjusted(self.tcx, expr);
                self.cat_rvalue(expr, expr_ty)
            }

            Some(
                @ty::AutoDerefRef(
                    ty::AutoDerefRef {
                        autoref: None, autoderefs: autoderefs})) => {
                // Equivalent to *expr or something similar.
                self.cat_expr_autoderefd(expr, autoderefs)
            }
        }
    }

    fn cat_expr_autoderefd(&self,
                           expr: @ast::expr,
                           autoderefs: uint) -> cmt {
        let mut cmt = self.cat_expr_unadjusted(expr);
        for uint::range(1, autoderefs+1) |deref| {
            cmt = self.cat_deref(expr, cmt, deref);
        }
        return cmt;
    }

    fn cat_expr_unadjusted(&self, expr: @ast::expr) -> cmt {
        debug!("cat_expr: id=%d expr=%s",
               expr.id, pprust::expr_to_str(expr, self.tcx.sess.intr()));

        let tcx = self.tcx;
        let expr_ty = tcx.ty(expr);
        match expr.node {
          ast::expr_unary(ast::deref, e_base) => {
            if self.method_map.contains_key(&expr.id) {
                return self.cat_rvalue(expr, expr_ty);
            }

            let base_cmt = self.cat_expr(e_base);
            self.cat_deref(expr, base_cmt, 0)
          }

          ast::expr_field(base, f_name, _) => {
            // Method calls are now a special syntactic form,
            // so `a.b` should always be a field.
            assert !self.method_map.contains_key(&expr.id);

            let base_cmt = self.cat_expr(base);
            self.cat_field(expr, base_cmt, f_name, expr.id)
          }

          ast::expr_index(base, _) => {
            if self.method_map.contains_key(&expr.id) {
                return self.cat_rvalue(expr, expr_ty);
            }

            let base_cmt = self.cat_expr(base);
            self.cat_index(expr, base_cmt)
          }

          ast::expr_path(_) => {
            let def = self.tcx.def_map.get(&expr.id);
            self.cat_def(expr.id, expr.span, expr_ty, def)
          }

          ast::expr_paren(e) => self.cat_expr_unadjusted(e),

          ast::expr_addr_of(*) | ast::expr_call(*) | ast::expr_swap(*) |
          ast::expr_assign(*) | ast::expr_assign_op(*) |
          ast::expr_fn_block(*) | ast::expr_ret(*) | ast::expr_loop_body(*) |
          ast::expr_do_body(*) | ast::expr_unary(*) |
          ast::expr_method_call(*) | ast::expr_copy(*) | ast::expr_cast(*) |
          ast::expr_vstore(*) | ast::expr_vec(*) | ast::expr_tup(*) |
          ast::expr_if(*) | ast::expr_log(*) | ast::expr_binary(*) |
          ast::expr_while(*) | ast::expr_block(*) | ast::expr_loop(*) |
          ast::expr_match(*) | ast::expr_lit(*) | ast::expr_break(*) |
          ast::expr_mac(*) | ast::expr_again(*) | ast::expr_struct(*) |
          ast::expr_repeat(*) | ast::expr_inline_asm(*) => {
            return self.cat_rvalue(expr, expr_ty);
          }
        }
    }

    fn cat_def(&self,
               id: ast::node_id,
               span: span,
               expr_ty: ty::t,
               def: ast::def) -> cmt {
        match def {
          ast::def_fn(*) | ast::def_static_method(*) | ast::def_mod(_) |
          ast::def_foreign_mod(_) | ast::def_const(_) |
          ast::def_use(_) | ast::def_variant(*) |
          ast::def_ty(_) | ast::def_prim_ty(_) |
          ast::def_ty_param(*) | ast::def_struct(*) |
          ast::def_typaram_binder(*) | ast::def_region(_) |
          ast::def_label(_) | ast::def_self_ty(*) => {
            @cmt_ {
                id:id,
                span:span,
                cat:cat_static_item,
                mutbl: McImmutable,
                ty:expr_ty
            }
          }

          ast::def_arg(vid, mode, mutbl) => {
            // Idea: make this could be rewritten to model by-ref
            // stuff as `&const` and `&mut`?

            // m: mutability of the argument
            let m = if mutbl {McDeclared} else {McImmutable};
            let mode = ty::resolved_mode(self.tcx, mode);
            @cmt_ {
                id: id,
                span: span,
                cat: cat_arg(vid, mode),
                mutbl: m,
                ty:expr_ty
            }
          }

          ast::def_self(self_id, is_implicit) => {
            let cat = if is_implicit {
                cat_implicit_self
            } else {
                cat_self(self_id)
            };

            @cmt_ {
                id:id,
                span:span,
                cat:cat,
                mutbl: McImmutable,
                ty:expr_ty
            }
          }

          ast::def_upvar(upvar_id, inner, fn_node_id, _) => {
            let ty = ty::node_id_to_type(self.tcx, fn_node_id);
            let sigil = ty::ty_closure_sigil(ty);
            match sigil {
                ast::BorrowedSigil => {
                    let upcmt = self.cat_def(id, span, expr_ty, *inner);
                    @cmt_ {
                        id:id,
                        span:span,
                        cat:cat_stack_upvar(upcmt),
                        mutbl:upcmt.mutbl,
                        ty:upcmt.ty
                    }
                }
                ast::OwnedSigil | ast::ManagedSigil => {
                    // FIXME #2152 allow mutation of moved upvars
                    @cmt_ {
                        id:id,
                        span:span,
                        cat:cat_copied_upvar(upvar_id),
                        mutbl:McImmutable,
                        ty:expr_ty
                    }
                }
            }
          }

          ast::def_local(vid, mutbl) => {
            let m = if mutbl {McDeclared} else {McImmutable};
            @cmt_ {
                id:id,
                span:span,
                cat:cat_local(vid),
                mutbl:m,
                ty:expr_ty
            }
          }

          ast::def_binding(vid, _) => {
            // by-value/by-ref bindings are local variables
            @cmt_ {
                id:id,
                span:span,
                cat:cat_local(vid),
                mutbl:McImmutable,
                ty:expr_ty
            }
          }
        }
    }

    fn cat_variant<N:ast_node>(&self,
                                arg: N,
                                enum_did: ast::def_id,
                                cmt: cmt) -> cmt {
        @cmt_ {
            id: arg.id(),
            span: arg.span(),
            cat: cat_interior(cmt, interior_variant(enum_did)),
            mutbl: cmt.mutbl.inherit(),
            ty: self.tcx.ty(arg)
        }
    }

    fn cat_rvalue<N:ast_node>(&self, elt: N, expr_ty: ty::t) -> cmt {
        @cmt_ {
            id:elt.id(),
            span:elt.span(),
            cat:cat_rvalue,
            mutbl:McImmutable,
            ty:expr_ty
        }
    }

    /// inherited mutability: used in cases where the mutability of a
    /// component is inherited from the base it is a part of. For
    /// example, a record field is mutable if it is declared mutable
    /// or if the container is mutable.
    fn inherited_mutability(&self,
                            base_m: MutabilityCategory,
                            interior_m: ast::mutability) -> MutabilityCategory
    {
        match interior_m {
            m_imm => base_m.inherit(),
            m_const => McReadOnly,
            m_mutbl => McDeclared
        }
    }

    /// The `field_id` parameter is the ID of the enclosing expression or
    /// pattern. It is used to determine which variant of an enum is in use.
    fn cat_field<N:ast_node>(&self,
                             node: N,
                             base_cmt: cmt,
                             f_name: ast::ident,
                             field_id: ast::node_id) -> cmt {
        let f_mutbl = match field_mutbl(self.tcx, base_cmt.ty,
                                        f_name, field_id) {
            Some(f_mutbl) => f_mutbl,
            None => {
                self.tcx.sess.span_bug(
                    node.span(),
                    fmt!("Cannot find field `%s` in type `%s`",
                         *self.tcx.sess.str_of(f_name),
                         ty_to_str(self.tcx, base_cmt.ty)));
            }
        };
        let m = self.inherited_mutability(base_cmt.mutbl, f_mutbl);
        let f_interior = interior_field(f_name, f_mutbl);
        @cmt_ {
            id: node.id(),
            span: node.span(),
            cat: cat_interior(base_cmt, f_interior),
            mutbl: m,
            ty: self.tcx.ty(node)
        }
    }

    fn cat_deref_fn<N:ast_node>(&self,
                                node: N,
                                base_cmt: cmt,
                                deref_cnt: uint) -> cmt
    {
        // Bit of a hack: the "dereference" of a function pointer like
        // `@fn()` is a mere logical concept. We interpret it as
        // dereferencing the environment pointer; of course, we don't
        // know what type lies at the other end, so we just call it
        // `()` (the empty tuple).

        let mt = ty::mt {ty: ty::mk_tup(self.tcx, ~[]),
                         mutbl: m_imm};
        return self.cat_deref_common(node, base_cmt, deref_cnt, mt);
    }

    fn cat_deref<N:ast_node>(&self,
                             node: N,
                             base_cmt: cmt,
                             deref_cnt: uint) -> cmt
    {
        let mt = match ty::deref(self.tcx, base_cmt.ty, true) {
            Some(mt) => mt,
            None => {
                self.tcx.sess.span_bug(
                    node.span(),
                    fmt!("Explicit deref of non-derefable type: %s",
                         ty_to_str(self.tcx, base_cmt.ty)));
            }
        };

        return self.cat_deref_common(node, base_cmt, deref_cnt, mt);
    }

    fn cat_deref_common<N:ast_node>(&self,
                                    node: N,
                                    base_cmt: cmt,
                                    deref_cnt: uint,
                                    mt: ty::mt) -> cmt
    {
        match deref_kind(self.tcx, base_cmt.ty) {
            deref_ptr(ptr) => {
                // for unique ptrs, we inherit mutability from the
                // owning reference.
                let m = match ptr {
                    uniq_ptr(*) => {
                        self.inherited_mutability(base_cmt.mutbl, mt.mutbl)
                    }
                    gc_ptr(*) | region_ptr(_, _) | unsafe_ptr => {
                        MutabilityCategory::from_mutbl(mt.mutbl)
                    }
                };

                @cmt_ {
                    id:node.id(),
                    span:node.span(),
                    cat:cat_deref(base_cmt, deref_cnt, ptr),
                    mutbl:m,
                    ty:mt.ty
                }
            }

            deref_interior(interior) => {
                let m = self.inherited_mutability(base_cmt.mutbl, mt.mutbl);
                @cmt_ {
                    id:node.id(),
                    span:node.span(),
                    cat:cat_interior(base_cmt, interior),
                    mutbl:m,
                    ty:mt.ty
                }
            }
        }
    }

    fn cat_index<N:ast_node>(&self,
                              elt: N,
                              base_cmt: cmt) -> cmt {
        let mt = match ty::index(self.tcx, base_cmt.ty) {
          Some(mt) => mt,
          None => {
            self.tcx.sess.span_bug(
                elt.span(),
                fmt!("Explicit index of non-index type `%s`",
                     ty_to_str(self.tcx, base_cmt.ty)));
          }
        };

        return match deref_kind(self.tcx, base_cmt.ty) {
          deref_ptr(ptr) => {
            // for unique ptrs, we inherit mutability from the
            // owning reference.
            let m = match ptr {
              uniq_ptr(*) => {
                self.inherited_mutability(base_cmt.mutbl, mt.mutbl)
              }
              gc_ptr(_) | region_ptr(_, _) | unsafe_ptr => {
                MutabilityCategory::from_mutbl(mt.mutbl)
              }
            };

            // the deref is explicit in the resulting cmt
            let deref_cmt = @cmt_ {
                id:elt.id(),
                span:elt.span(),
                cat:cat_deref(base_cmt, 0u, ptr),
                mutbl:m,
                ty:mt.ty
            };

            interior(elt, deref_cmt, base_cmt.ty, m, mt)
          }

          deref_interior(_) => {
            // fixed-length vectors have no deref
            let m = self.inherited_mutability(base_cmt.mutbl, mt.mutbl);
            interior(elt, base_cmt, base_cmt.ty, m, mt)
          }
        };

        fn interior<N: ast_node>(elt: N, of_cmt: cmt,
                                 vect: ty::t, mutbl: MutabilityCategory,
                                 mt: ty::mt) -> cmt
        {
            let interior = interior_index(vect, mt.mutbl);
            @cmt_ {
                id:elt.id(),
                span:elt.span(),
                cat:cat_interior(of_cmt, interior),
                mutbl:mutbl,
                ty:mt.ty
            }
        }
    }

    fn cat_tuple_elt<N:ast_node>(&self,
                                  elt: N,
                                  cmt: cmt) -> cmt {
        @cmt_ {
            id: elt.id(),
            span: elt.span(),
            cat: cat_interior(cmt, interior_tuple),
            mutbl: cmt.mutbl.inherit(),
            ty: self.tcx.ty(elt)
        }
    }

    fn cat_anon_struct_field<N:ast_node>(&self,
                                          elt: N,
                                          cmt: cmt) -> cmt {
        @cmt_ {
            id: elt.id(),
            span: elt.span(),
            cat: cat_interior(cmt, interior_anon_field),
            mutbl: cmt.mutbl.inherit(),
            ty: self.tcx.ty(elt)
        }
    }

    fn cat_pattern(&self,
                   cmt: cmt,
                   pat: @ast::pat,
                   op: &fn(cmt, @ast::pat))
    {
        // Here, `cmt` is the categorization for the value being
        // matched and pat is the pattern it is being matched against.
        //
        // In general, the way that this works is that we walk down
        // the pattern, constructing a cmt that represents the path
        // that will be taken to reach the value being matched.
        //
        // When we encounter named bindings, we take the cmt that has
        // been built up and pass it off to guarantee_valid() so that
        // we can be sure that the binding will remain valid for the
        // duration of the arm.
        //
        // The correspondence between the id in the cmt and which
        // pattern is being referred to is somewhat...subtle.  In
        // general, the id of the cmt is the id of the node that
        // produces the value.  For patterns, that's actually the
        // *subpattern*, generally speaking.
        //
        // To see what I mean about ids etc, consider:
        //
        //     let x = @@3;
        //     match x {
        //       @@y { ... }
        //     }
        //
        // Here the cmt for `y` would be something like
        //
        //     local(x)->@->@
        //
        // where the id of `local(x)` is the id of the `x` that appears
        // in the match, the id of `local(x)->@` is the `@y` pattern,
        // and the id of `local(x)->@->@` is the id of the `y` pattern.


        let tcx = self.tcx;
        debug!("cat_pattern: id=%d pat=%s cmt=%s",
               pat.id, pprust::pat_to_str(pat, tcx.sess.intr()),
               self.cmt_to_repr(cmt));
        let _i = indenter();

        op(cmt, pat);

        match pat.node {
          ast::pat_wild => {
            // _
          }

          ast::pat_enum(_, None) => {
            // variant(*)
          }
          ast::pat_enum(_, Some(ref subpats)) => {
            match self.tcx.def_map.find(&pat.id) {
                Some(ast::def_variant(enum_did, _)) => {
                    // variant(x, y, z)
                    for subpats.each |subpat| {
                        let subcmt = self.cat_variant(*subpat, enum_did, cmt);
                        self.cat_pattern(subcmt, *subpat, op);
                    }
                }
                Some(ast::def_struct(*)) => {
                    for subpats.each |subpat| {
                        let cmt_field = self.cat_anon_struct_field(*subpat,
                                                                   cmt);
                        self.cat_pattern(cmt_field, *subpat, op);
                    }
                }
                _ => {
                    self.tcx.sess.span_bug(
                        pat.span,
                        ~"enum pattern didn't resolve to enum or struct");
                }
            }
          }

          ast::pat_ident(_, _, Some(subpat)) => {
              self.cat_pattern(cmt, subpat, op);
          }

          ast::pat_ident(_, _, None) => {
              // nullary variant or identifier: ignore
          }

          ast::pat_struct(_, ref field_pats, _) => {
            // {f1: p1, ..., fN: pN}
            for field_pats.each |fp| {
                let cmt_field = self.cat_field(fp.pat, cmt, fp.ident, pat.id);
                self.cat_pattern(cmt_field, fp.pat, op);
            }
          }

          ast::pat_tup(ref subpats) => {
            // (p1, ..., pN)
            for subpats.each |subpat| {
                let subcmt = self.cat_tuple_elt(*subpat, cmt);
                self.cat_pattern(subcmt, *subpat, op);
            }
          }

          ast::pat_box(subpat) | ast::pat_uniq(subpat) |
          ast::pat_region(subpat) => {
            // @p1, ~p1
            let subcmt = self.cat_deref(subpat, cmt, 0);
            self.cat_pattern(subcmt, subpat, op);
          }

          ast::pat_vec(ref before, slice, ref after) => {
              for before.each |pat| {
                  let elt_cmt = self.cat_index(*pat, cmt);
                  self.cat_pattern(elt_cmt, *pat, op);
              }
              for slice.each |slice_pat| {
                  let slice_ty = self.tcx.ty(*slice_pat);
                  let slice_cmt = self.cat_rvalue(*slice_pat, slice_ty);
                  self.cat_pattern(slice_cmt, *slice_pat, op);
              }
              for after.each |pat| {
                  let elt_cmt = self.cat_index(*pat, cmt);
                  self.cat_pattern(elt_cmt, *pat, op);
              }
          }

          ast::pat_lit(_) | ast::pat_range(_, _) => {
              /*always ok*/
          }
        }
    }

    fn cat_to_repr(&self, cat: categorization) -> ~str {
        match cat {
          cat_static_item => ~"static_item",
          cat_implicit_self => ~"implicit-self",
          cat_stack_upvar(_) => ~"stack-upvar",
          cat_rvalue => ~"rvalue",
          cat_copied_upvar(_) |
          cat_local(*) |
          cat_self(*) |
          cat_arg(*) => fmt!("%?", cat),
          cat_deref(cmt, derefs, ptr) => {
            fmt!("%s->(%s, %u)", self.cat_to_repr(cmt.cat),
                 self.ptr_sigil(ptr), derefs)
          }
          cat_interior(cmt, interior) => {
            fmt!("%s.%s", self.cat_to_repr(cmt.cat),
                 self.interior_to_repr(interior))
          }
          cat_discr(cmt, _) => self.cat_to_repr(cmt.cat)
        }
    }

    fn mut_to_str(&self, mutbl: ast::mutability) -> ~str {
        match mutbl {
          m_mutbl => ~"mutable",
          m_const => ~"const",
          m_imm => ~"immutable"
        }
    }

    fn ptr_sigil(&self, ptr: ptr_kind) -> ~str {
        match ptr {
          uniq_ptr(_) => ~"~",
          gc_ptr(_) => ~"@",
          region_ptr(_, _) => ~"&",
          unsafe_ptr => ~"*"
        }
    }

    fn interior_to_repr(&self, interior: interior_kind) -> ~str {
        match interior {
          interior_field(fld, _) => copy *self.tcx.sess.str_of(fld),
          interior_index(*) => ~"[]",
          interior_tuple => ~"()",
          interior_anon_field => ~"<anonymous field>",
          interior_variant(_) => ~"<enum>"
        }
    }

    fn cmt_to_repr(&self, cmt: cmt) -> ~str {
        fmt!("{%s id:%d m:%? ty:%s}",
             self.cat_to_repr(cmt.cat),
             cmt.id,
             cmt.mutbl,
             ty_to_str(self.tcx, cmt.ty))
    }

    fn cmt_to_str(&self, cmt: cmt) -> ~str {
        let mut_str = cmt.mutbl.to_user_str();
        match cmt.cat {
          cat_static_item => ~"static item",
          cat_implicit_self => ~"self reference",
          cat_copied_upvar(_) => {
              ~"captured outer variable in a heap closure"
          }
          cat_rvalue => ~"non-lvalue",
          cat_local(_) => mut_str + ~" local variable",
          cat_self(_) => ~"self value",
          cat_arg(*) => ~"argument",
          cat_deref(_, _, pk) => fmt!("dereference of %s %s pointer",
                                      mut_str, self.ptr_sigil(pk)),
          cat_stack_upvar(_) => {
            ~"captured outer " + mut_str + ~" variable in a stack closure"
          }
          cat_interior(_, interior_field(*)) => mut_str + ~" field",
          cat_interior(_, interior_tuple) => ~"tuple content",
          cat_interior(_, interior_anon_field) => ~"anonymous field",
          cat_interior(_, interior_variant(_)) => ~"enum content",
          cat_interior(_, interior_index(t, _)) => {
            match ty::get(t).sty {
              ty::ty_evec(*) => mut_str + ~" vec content",
              ty::ty_estr(*) => mut_str + ~" str content",
              _ => mut_str + ~" indexed content"
            }
          }
          cat_discr(cmt, _) => {
            self.cmt_to_str(cmt)
          }
        }
    }

    fn region_to_str(&self, r: ty::Region) -> ~str {
        region_to_str(self.tcx, r)
    }
}

/// The node_id here is the node of the expression that references the field.
/// This function looks it up in the def map in case the type happens to be
/// an enum to determine which variant is in use.
pub fn field_mutbl(tcx: ty::ctxt,
                   base_ty: ty::t,
                   f_name: ast::ident,
                   node_id: ast::node_id)
                -> Option<ast::mutability> {
    // Need to refactor so that struct/enum fields can be treated uniformly.
    match /*bad*/copy ty::get(base_ty).sty {
      ty::ty_struct(did, _) => {
        for ty::lookup_struct_fields(tcx, did).each |fld| {
            if fld.ident == f_name {
                let m = match fld.mutability {
                  ast::struct_mutable => ast::m_mutbl,
                  ast::struct_immutable => ast::m_imm
                };
                return Some(m);
            }
        }
      }
      ty::ty_enum(*) => {
        match tcx.def_map.get(&node_id) {
          ast::def_variant(_, variant_id) => {
            for ty::lookup_struct_fields(tcx, variant_id).each |fld| {
                if fld.ident == f_name {
                    let m = match fld.mutability {
                      ast::struct_mutable => ast::m_mutbl,
                      ast::struct_immutable => ast::m_imm
                    };
                    return Some(m);
                }
            }
          }
          _ => {}
        }
      }
      _ => { }
    }

    return None;
}

