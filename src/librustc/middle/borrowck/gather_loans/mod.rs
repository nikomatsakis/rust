// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ----------------------------------------------------------------------
// Gathering loans
//
// The borrow check proceeds in two phases. In phase one, we gather the full
// set of loans that are required at any point.  These are sorted according to
// their associated scopes.  In phase two, checking loans, we will then make
// sure that all of these loans are honored.

use middle::borrowck::*;
use middle::borrowck::move_data::MoveData;
use euv = middle::expr_use_visitor;
use mc = middle::mem_categorization;
use middle::pat_util;
use middle::ty::{ty_region};
use middle::ty;
use middle::typeck::MethodCall;
use util::common::indenter;
use util::ppaux::{Repr};

use syntax::ast;
use syntax::ast_util;
use syntax::ast_util::IdRange;
use syntax::codemap::Span;
use syntax::print::pprust;
use syntax::visit;
use syntax::visit::{Visitor, FnKind};
use syntax::ast::{Expr, FnDecl, Block, NodeId, Stmt, Pat, Local};

use std::rc::Rc;

mod lifetime;
mod restrictions;
mod gather_moves;
mod move_error;

pub fn gather_loans_in_fn(bccx: &BorrowckCtxt,
                          decl: &ast::FnDecl,
                          body: &ast::Block)
                          -> (Vec<Loan>, move_data::MoveData)
{
    let mut typer = ty::TcxTyper::new(bccx.tcx, bccx.method_map);
    let mut glcx = GatherLoanCtxt {
        bccx: bccx,
        all_loans: Vec::new(),
        item_ub: body.id,
        move_data: MoveData::new(),
        move_error_collector: move_error::MoveErrorCollector::new(),
    };
    glcx.gather_fn_arg_patterns(decl, body);

    {
        let mut euv = ExprUseVisitor::new(&mut glcx, typer);
        euv.walk_fn(decl, body);
    }

    glcx.report_potential_errors();
    let GatherLoanCtxt { all_loans, move_data, .. } = glcx;
    (all_loans, move_data)
}

struct GatherLoanCtxt<'a> {
    bccx: &'a BorrowckCtxt<'a>,
    move_data: move_data::MoveData,
    move_error_collector: move_error::MoveErrorCollector,
    all_loans: Vec<Loan>,
    item_ub: ast::NodeId,
}

impl euv::Delegate for GatherLoanCtxt<'a> {
    fn consume(&mut self,
               consume_id: ast::NodeId,
               consume_span: Span,
               cmt: mc::cmt,
               mode: ConsumeMode) {
        match mode {
            Copy => { return; }
            Move => { }
        }

        gather_moves::gather_move_from_expr(
            this.bccx, &this.move_data, &this.move_error_collector,
            consume_id, cmt);
    }

    fn borrow(&mut self,
              borrow_id: ast::NodeId,
              borrow_span: Span,
              cmt: mc::cmt,
              loan_region: ty::Region,
              bk: ty::BorrowKind,
              loan_cause: LoanCause)
    {
        self.guarantee_valid(borrow_id,
                             borrow_span,
                             cmt,
                             bk,
                             loan_region,
                             loan_cause);
    }

    fn mutate(&mut self,
              assignment_id: ast::NodeId,
              assignment_span: Span,
              assignee_cmt: mc::cmt)
    {
        match opt_loan_path(cmt) {
            Some(lp) => {
                gather_moves::gather_assignment(this.bccx, &this.move_data,
                                                assignment_id, assignment_span,
                                                lp, assignee_cmt.id);
            }
            None => {
                // This can occur with e.g. `*foo() = 5`.  In such
                // cases, there is no need to check for conflicts
                // with moves etc, just ignore.
            }
        }
    }

    fn decl_without_init(&mut self, id: ast::NodeId, span: Span) {
        gather_moves::gather_decl(self.bccx, &self.move_data, id, span, id);
    }
}

fn add_pat_to_id_range(this: &mut GatherLoanCtxt,
                       p: &ast::Pat) {
    // NB: This visitor function just adds the pat ids into the id
    // range. We gather loans that occur in patterns using the
    // `gather_pat()` method below. Eventually these two should be
    // brought together.
    this.id_range.add(p.id);
    visit::walk_pat(this, p, ());
}

/// Implements the A-* rules in doc.rs.
fn check_aliasability(bccx: &BorrowckCtxt,
                      borrow_span: Span,
                      loan_cause: LoanCause,
                      cmt: mc::cmt,
                      req_kind: ty::BorrowKind)
                      -> Result<(),()> {

    match (cmt.freely_aliasable(bccx.tcx), req_kind) {
        (None, _) => {
            /* Uniquely accessible path -- OK for `&` and `&mut` */
            Ok(())
        }
        (Some(mc::AliasableStatic(safety)), ty::ImmBorrow) => {
            // Borrow of an immutable static item:
            match safety {
                mc::InteriorUnsafe => {
                    // If the static item contains an Unsafe<T>, it has interior mutability.
                    // In such cases, we cannot permit it to be borrowed, because the
                    // static item resides in immutable memory and mutating it would
                    // cause segfaults.
                    bccx.tcx.sess.span_err(borrow_span,
                                           format!("borrow of immutable static items with \
                                                    unsafe interior is not allowed"));
                    Err(())
                }
                mc::InteriorSafe => {
                    // Immutable static can be borrowed, no problem.
                    Ok(())
                }
            }
        }
        (Some(mc::AliasableStaticMut(..)), _) => {
            // Even touching a static mut is considered unsafe. We assume the
            // user knows what they're doing in these cases.
            Ok(())
        }
        (Some(alias_cause), ty::UniqueImmBorrow) |
        (Some(alias_cause), ty::MutBorrow) => {
            bccx.report_aliasability_violation(
                        borrow_span,
                        BorrowViolation(loan_cause),
                        alias_cause);
            Err(())
        }
        (_, _) => {
            Ok(())
        }
    }
}

impl<'a> GatherLoanCtxt<'a> {
    pub fn tcx(&self) -> &'a ty::ctxt { self.bccx.tcx }

    fn guarantee_valid(&mut self,
                       borrow_id: ast::NodeId,
                       borrow_span: Span,
                       cmt: mc::cmt,
                       req_kind: ty::BorrowKind,
                       loan_region: ty::Region,
                       cause: LoanCause) {
        /*!
         * Guarantees that `addr_of(cmt)` will be valid for the duration of
         * `static_scope_r`, or reports an error.  This may entail taking
         * out loans, which will be added to the `req_loan_map`.  This can
         * also entail "rooting" GC'd pointers, which means ensuring
         * dynamically that they are not freed.
         */

        debug!("guarantee_valid(borrow_id={:?}, cmt={}, \
                req_mutbl={:?}, loan_region={:?})",
               borrow_id,
               cmt.repr(self.tcx()),
               req_kind,
               loan_region);

        // a loan for the empty region can never be dereferenced, so
        // it is always safe
        if loan_region == ty::ReEmpty {
            return;
        }

        let root_ub = { *self.repeating_ids.last().unwrap() }; // FIXME(#5074)

        // Check that the lifetime of the borrow does not exceed
        // the lifetime of the data being borrowed.
        if lifetime::guarantee_lifetime(self.bccx, self.item_ub, root_ub,
                                        borrow_span, cause, cmt.clone(), loan_region,
                                        req_kind).is_err() {
            return; // reported an error, no sense in reporting more.
        }

        // Check that we don't allow mutable borrows of non-mutable data.
        if check_mutability(self.bccx, borrow_span, cause,
                            cmt.clone(), req_kind).is_err() {
            return; // reported an error, no sense in reporting more.
        }

        // Check that we don't allow mutable borrows of aliasable data.
        if check_aliasability(self.bccx, borrow_span, cause,
                              cmt.clone(), req_kind).is_err() {
            return; // reported an error, no sense in reporting more.
        }

        // Compute the restrictions that are required to enforce the
        // loan is safe.
        let restr = restrictions::compute_restrictions(
            self.bccx, borrow_span, cause,
            cmt.clone(), loan_region, self.restriction_set(req_kind));

        // Create the loan record (if needed).
        let loan = match restr {
            restrictions::Safe => {
                // No restrictions---no loan record necessary
                return;
            }

            restrictions::SafeIf(loan_path, restrictions) => {
                let loan_scope = match loan_region {
                    ty::ReScope(id) => id,
                    ty::ReFree(ref fr) => fr.scope_id,

                    ty::ReStatic => {
                        // If we get here, an error must have been
                        // reported in
                        // `lifetime::guarantee_lifetime()`, because
                        // the only legal ways to have a borrow with a
                        // static lifetime should not require
                        // restrictions. To avoid reporting derived
                        // errors, we just return here without adding
                        // any loans.
                        return;
                    }

                    ty::ReEmpty |
                    ty::ReLateBound(..) |
                    ty::ReEarlyBound(..) |
                    ty::ReInfer(..) => {
                        self.tcx().sess.span_bug(
                            cmt.span,
                            format!("invalid borrow lifetime: {:?}", loan_region));
                    }
                };
                debug!("loan_scope = {:?}", loan_scope);

                let gen_scope = self.compute_gen_scope(borrow_id, loan_scope);
                debug!("gen_scope = {:?}", gen_scope);

                let kill_scope = self.compute_kill_scope(loan_scope, &*loan_path);
                debug!("kill_scope = {:?}", kill_scope);

                if req_kind == ty::MutBorrow {
                    self.mark_loan_path_as_mutated(&*loan_path);
                }

                Loan {
                    index: self.all_loans.len(),
                    loan_path: loan_path,
                    cmt: cmt,
                    kind: req_kind,
                    gen_scope: gen_scope,
                    kill_scope: kill_scope,
                    span: borrow_span,
                    restrictions: restrictions,
                    cause: cause,
                }
            }
        };

        debug!("guarantee_valid(borrow_id={:?}), loan={}",
               borrow_id, loan.repr(self.tcx()));

        // let loan_path = loan.loan_path;
        // let loan_gen_scope = loan.gen_scope;
        // let loan_kill_scope = loan.kill_scope;
        self.all_loans.push(loan);

        // if loan_gen_scope != borrow_id {
            // FIXME(#6268) Nested method calls
            //
            // Typically, the scope of the loan includes the point at
            // which the loan is originated. This
            // This is a subtle case. See the test case
            // <compile-fail/borrowck-bad-nested-calls-free.rs>
            // to see what we are guarding against.

            //let restr = restrictions::compute_restrictions(
            //    self.bccx, borrow_span, cmt, RESTR_EMPTY);
            //let loan = {
            //    let all_loans = &mut *self.all_loans; // FIXME(#5074)
            //    Loan {
            //        index: all_loans.len(),
            //        loan_path: loan_path,
            //        cmt: cmt,
            //        mutbl: ConstMutability,
            //        gen_scope: borrow_id,
            //        kill_scope: kill_scope,
            //        span: borrow_span,
            //        restrictions: restrictions
            //    }
        // }

        fn check_mutability(bccx: &BorrowckCtxt,
                            borrow_span: Span,
                            cause: LoanCause,
                            cmt: mc::cmt,
                            req_kind: ty::BorrowKind)
                            -> Result<(),()> {
            //! Implements the M-* rules in doc.rs.

            match req_kind {
                ty::UniqueImmBorrow | ty::ImmBorrow => {
                    match cmt.mutbl {
                        // I am intentionally leaving this here to help
                        // refactoring if, in the future, we should add new
                        // kinds of mutability.
                        mc::McImmutable | mc::McDeclared | mc::McInherited => {
                            // both imm and mut data can be lent as imm;
                            // for mutable data, this is a freeze
                            Ok(())
                        }
                    }
                }

                ty::MutBorrow => {
                    // Only mutable data can be lent as mutable.
                    if !cmt.mutbl.is_mutable() {
                        Err(bccx.report(BckError { span: borrow_span,
                                                   cause: cause,
                                                   cmt: cmt,
                                                   code: err_mutbl }))
                    } else {
                        Ok(())
                    }
                }
            }
        }
    }

    fn restriction_set(&self, req_kind: ty::BorrowKind) -> RestrictionSet {
        match req_kind {
            // If borrowing data as immutable, no mutation allowed:
            ty::ImmBorrow => RESTR_MUTATE,

            // If borrowing data as mutable, no mutation nor other
            // borrows allowed:
            ty::MutBorrow => RESTR_MUTATE | RESTR_FREEZE,

            // If borrowing data as unique imm, no mutation nor other
            // borrows allowed:
            ty::UniqueImmBorrow => RESTR_MUTATE | RESTR_FREEZE,
        }
    }

    pub fn mark_loan_path_as_mutated(&self, loan_path: &LoanPath) {
        //! For mutable loans of content whose mutability derives
        //! from a local variable, mark the mutability decl as necessary.

        match *loan_path {
            LpVar(local_id) => {
                self.tcx().used_mut_nodes.borrow_mut().insert(local_id);
            }
            LpExtend(ref base, mc::McInherited, _) => {
                self.mark_loan_path_as_mutated(&**base);
            }
            LpExtend(_, mc::McDeclared, _) |
            LpExtend(_, mc::McImmutable, _) => {
                // Nothing to do.
            }
        }
    }

    pub fn compute_gen_scope(&self,
                             borrow_id: ast::NodeId,
                             loan_scope: ast::NodeId)
                             -> ast::NodeId {
        //! Determine when to introduce the loan. Typically the loan
        //! is introduced at the point of the borrow, but in some cases,
        //! notably method arguments, the loan may be introduced only
        //! later, once it comes into scope.

        if self.bccx.tcx.region_maps.is_subscope_of(borrow_id, loan_scope) {
            borrow_id
        } else {
            loan_scope
        }
    }

    pub fn compute_kill_scope(&self, loan_scope: ast::NodeId, lp: &LoanPath)
                              -> ast::NodeId {
        //! Determine when the loan restrictions go out of scope.
        //! This is either when the lifetime expires or when the
        //! local variable which roots the loan-path goes out of scope,
        //! whichever happens faster.
        //!
        //! It may seem surprising that we might have a loan region
        //! larger than the variable which roots the loan-path; this can
        //! come about when variables of `&mut` type are re-borrowed,
        //! as in this example:
        //!
        //!     fn counter<'a>(v: &'a mut Foo) -> &'a mut uint {
        //!         &mut v.counter
        //!     }
        //!
        //! In this case, the reference (`'a`) outlives the
        //! variable `v` that hosts it. Note that this doesn't come up
        //! with immutable `&` pointers, because borrows of such pointers
        //! do not require restrictions and hence do not cause a loan.

        let rm = &self.bccx.tcx.region_maps;
        let lexical_scope = rm.var_scope(lp.node_id());
        if rm.is_subscope_of(lexical_scope, loan_scope) {
            lexical_scope
        } else {
            assert!(self.bccx.tcx.region_maps.is_subscope_of(loan_scope, lexical_scope));
            loan_scope
        }
    }

    fn gather_pat(&mut self,
                  discr_cmt: mc::cmt,
                  root_pat: @ast::Pat,
                  arm_match_ids: Option<(ast::NodeId, ast::NodeId)>) {
        /*!
         * Walks patterns, examining the bindings to determine if they
         * cause borrows (`ref` bindings, vector patterns) or
         * moves (non-`ref` bindings with linear type).
         */

        self.bccx.cat_pattern(discr_cmt, root_pat, |cmt, pat| {
            match pat.node {
              ast::PatIdent(bm, _, _) if self.pat_is_binding(pat) => {
                // Each match binding is effectively an assignment.
                let tcx = self.bccx.tcx;
                pat_util::pat_bindings(&tcx.def_map, pat, |_, id, span, _| {
                    gather_moves::gather_assignment(self.bccx,
                                                    &self.move_data,
                                                    id,
                                                    span,
                                                    Rc::new(LpVar(id)),
                                                    id);
                });

                match bm {
                  ast::BindByRef(mutbl) => {
                    // ref x or ref x @ p --- creates a ptr which must
                    // remain valid for the scope of the match

                    // find the region of the resulting pointer (note that
                    // the type of such a pattern will *always* be a
                    // region pointer)
                    let scope_r =
                        ty_region(self.tcx(), pat.span,
                                  ty::node_id_to_type(self.tcx(), pat.id));

                    // if the scope of the region ptr turns out to be
                    // specific to this arm, wrap the categorization
                    // with a cat_discr() node.  There is a detailed
                    // discussion of the function of this node in
                    // `lifetime.rs`:
                    let cmt_discr = match arm_match_ids {
                        None => cmt,
                        Some((arm_id, match_id)) => {
                            let arm_scope = ty::ReScope(arm_id);
                            if self.bccx.is_subregion_of(scope_r, arm_scope) {
                                self.bccx.cat_discr(cmt, match_id)
                            } else {
                                cmt
                            }
                        }
                    };
                    self.guarantee_valid(pat.id,
                                         pat.span,
                                         cmt_discr,
                                         mutbl,
                                         scope_r,
                                         RefBinding);
                  }
                  ast::BindByValue(_) => {
                      // No borrows here, but there may be moves
                      if self.bccx.is_move(pat.id) {
                          gather_moves::gather_move_from_pat(
                              self.bccx, &self.move_data,
                              &self.move_error_collector, pat, cmt);
                      }
                  }
                }
              }

              ast::PatVec(_, Some(slice_pat), _) => {
                  // The `slice_pat` here creates a slice into the
                  // original vector.  This is effectively a borrow of
                  // the elements of the vector being matched.

                  let (slice_cmt, slice_borrow_kind, slice_r) = {
                      match self.bccx.mc().cat_slice_pattern(cmt, slice_pat) {
                          Ok(v) => v,
                          Err(()) => {
                              self.tcx().sess.span_bug(slice_pat.span,
                                                       "Err from mc")
                          }
                      }
                  };

                  // Note: We declare here that the borrow occurs upon
                  // entering the `[...]` pattern. This implies that
                  // something like `[a, ..b]` where `a` is a move is
                  // illegal, because the borrow is already in effect.
                  // In fact such a move would be safe-ish, but it
                  // effectively *requires* that we use the nulling
                  // out semantics to indicate when a value has been
                  // moved, which we are trying to move away from.
                  // Otherwise, how can we indicate that the first
                  // element in the vector has been moved?
                  // Eventually, we could perhaps modify this rule to
                  // permit `[..a, b]` where `b` is a move, because in
                  // that case we can adjust the length of the
                  // original vec accordingly, but we'd have to make
                  // trans do the right thing, and it would only work
                  // for `~` vectors. It seems simpler to just require
                  // that people call `vec.pop()` or `vec.unshift()`.
                  self.guarantee_valid(pat.id, pat.span,
                                       slice_cmt, slice_borrow_kind, slice_r,
                                       RefBinding);
              }

              _ => {}
            }
        })
    }

    pub fn pat_is_binding(&self, pat: &ast::Pat) -> bool {
        pat_util::pat_is_binding(&self.bccx.tcx.def_map, pat)
    }

    pub fn report_potential_errors(&self) {
        self.move_error_collector.report_potential_errors(self.bccx);
    }
}

/// Context used while gathering loans on static initializers
///
/// This visitor walks static initializer's expressions and makes
/// sure the loans being taken are sound.
struct StaticInitializerCtxt<'a> {
    bccx: &'a BorrowckCtxt<'a>,
    id_range: IdRange,
    item_ub: ast::NodeId,
}

impl<'a> visit::Visitor<()> for StaticInitializerCtxt<'a> {
    fn visit_expr(&mut self, ex: &Expr, _: ()) {
        match ex.node {
            ast::ExprAddrOf(mutbl, base) => {
                let base_cmt = self.bccx.cat_expr(base);
                let borrow_kind = ty::BorrowKind::from_mutbl(mutbl);
                // Check that we don't allow borrows of unsafe static items.
                if check_aliasability(self.bccx, ex.span, AddrOf, base_cmt, borrow_kind).is_err() {
                    return; // reported an error, no sense in reporting more.
                }
            }
            _ => {}
        }

        visit::walk_expr(self, ex, ());
    }
}

pub fn gather_loans_in_static_initializer(bccx: &mut BorrowckCtxt, expr: &ast::Expr) {

    debug!("gather_loans_in_static_initializer(expr={})", expr.repr(bccx.tcx));

    let mut sicx = StaticInitializerCtxt {
        bccx: bccx,
        id_range: IdRange::max(),
        item_ub: expr.id,
    };

    sicx.visit_expr(expr, ());
}
