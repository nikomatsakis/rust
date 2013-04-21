// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::prelude::*;

use mc = middle::mem_categorization;
use middle::borrowck::*;
use middle::ty;
use syntax::ast;
use syntax::ast::{m_imm, m_mutbl, m_const};
use syntax::codemap::span;

pub mod mutate;
pub mod freeze;
pub mod alias;
pub mod reserve;

pub struct ComputeLoansContext {
    bccx: @BorrowckCtxt,

    // Innermost loop or fn body. This is the longest we can root
    // things.
    root_ub: ast::node_id,

    // Enclosing fn body.
    item_ub: ast::node_id,

    // Scope after which the loan will be in effect (generally the id
    // of the `&` expression)
    gen_scope: ast::node_id,

    // Span of the code that is triggering these loans
    span: span,

    // Optional override for root scope.
    // See with_discr() below
    discr_scope: Option<ast::node_id>
}

pub enum LoansOrRoot {
    Loans(@LoanPath, ~[Loan]),
    Root(root_map_key, Option<Loan>, RootInfo),
    Safe
}

// Defined in mutate.rs
pub trait Mutate {
    fn mutate(&self,
              cmt: mc::cmt,
              loan_region: ty::Region,
              totality: PartialTotal) -> BckResult<LoansOrRoot>;
}

// Defined in freeze.rs
pub trait Freeze {
    fn freeze(&self,
              cmt: mc::cmt,
              loan_region: ty::Region,
              totality: PartialTotal) -> BckResult<LoansOrRoot>;
}

// Defined in alias.rs
pub trait Alias {
    fn alias(&self,
             cmt: mc::cmt,
             loan_region: ty::Region,
             totality: PartialTotal) -> BckResult<LoansOrRoot>;
}

// Defined in reserve.rs
pub trait Reserve {
    fn reserve(&self,
               cmt: mc::cmt,
               loan_region: ty::Region,
               reason: ReserveReason) -> BckResult<LoansOrRoot>;
}

// Helpers used by all of the above functions:
pub impl ComputeLoansContext {
    fn tcx(&self) -> ty::ctxt {
        self.bccx.tcx
    }

    fn loan_variable(
        &self,
        cmt: mc::cmt,
        loan_region: ty::Region,
        kind: LoanKind,
        local_id: ast::node_id) -> BckResult<LoansOrRoot>
    {
        if_ok!(self.check_cmt_scope(cmt, loan_region));
        self.loan_variable_without_checking_scope(cmt, loan_region,
                                                  kind, local_id)
    }

    fn loan_variable_without_checking_scope(
        &self,
        cmt: mc::cmt,
        loan_region: ty::Region,
        kind: LoanKind,
        local_id: ast::node_id) -> BckResult<LoansOrRoot>
    {
        let loan_scope_id = self.loan_scope_id(cmt, loan_region);
        let lp = @LpVar(local_id);
        Ok(Loans(lp, ~[Loan {lp: lp,
                             cmt: cmt,
                             kind: kind,
                             gen_scope: self.gen_scope,
                             kill_scope: loan_scope_id,
                             span: self.span}]))
    }

    fn add_loan(
        &self,
        +lr: LoansOrRoot,
        +cmt: mc::cmt,
        +loan_region: ty::Region,
        +kind: LoanKind,
        +lp_elem: LoanPathElem) -> LoansOrRoot
    {
        match lr {
            Loans(base_lp, loans) => {
                let loan_scope_id = self.loan_scope_id(cmt, loan_region);
                let lp = @LpExtend(base_lp, cmt.mutbl, lp_elem);
                Loans(
                    lp,
                    vec::append_one(loans, Loan {
                        lp: lp,
                        cmt: cmt,
                        kind: kind,
                        gen_scope: self.gen_scope,
                        kill_scope: loan_scope_id,
                        span: self.span}))
            }

            Safe => Safe,

            Root(k, l, r) => Root(k, l, r)
        }
    }

    fn loan_scope_id(&self,
                     cmt: mc::cmt,
                     loan_region: ty::Region) -> ast::node_id {
        match loan_region {
            ty::re_scope(id) => id,
            ty::re_free(ref fr) => fr.scope_id,
            _ => {
                self.bccx.tcx.sess.span_bug(
                    cmt.span,
                    fmt!("Cannot issue loan for scope region: %?",
                         loan_region));
            }
        }
    }

    fn root(
        &self,
        +_cmt: mc::cmt,      // *foo
        +cmt_base: mc::cmt,  // foo
        +loan_region: ty::Region,
        +derefs: uint,
        +opt_dyna: Option<DynaFreezeKind>) -> LoansOrRoot
    {
        let loan_scope_id = match loan_region {
            ty::re_scope(id) => id,
            _ => {
                self.bccx.tcx.sess.span_bug(
                    cmt_base.span,
                    fmt!("Cannot issue root for scope region: %?",
                         loan_region));
            }
        };

        // Expand the root scope when matching inside the arm
        // of a match statement (see fn with_discr() for details)
        let root_scope = match self.discr_scope {
            None => loan_scope_id,
            Some(s) => s
        };

        // If we are going to be dynamically freezing an `@mut` box,
        // we still record a loan for the box path we know is frozen.
        // This allows us to make a best effort to report errors, even
        // though we can't catch *all* errors due to the possibility
        // of aliased paths.
        let opt_loan = match opt_dyna {
            None => None,
            Some(dyna) => {
                let lk = match dyna {
                    DynaMut => MutLoan(m_mutbl, Total),
                    DynaImm => MutLoan(m_imm, Total)
                };
                opt_loan_path(cmt_base).map(|&lp| {
                    Loan {lp: lp,
                          cmt: cmt_base,
                          kind: lk,
                          gen_scope: self.gen_scope,
                          kill_scope: loan_scope_id,
                          span: self.span}
                })
            }
        };

        let rm_key = root_map_key {id: cmt_base.id, derefs: derefs};
        Root(rm_key,
             opt_loan,
             RootInfo {scope: root_scope, freeze: opt_dyna})
    }

    fn check_mutable(&self, cmt: mc::cmt) -> BckResult<()>
    {
        match cmt.mutbl {
            mc::McDeclared | mc::McInherited => Ok(()),
            mc::McImmutable => Err(BckError {cmt: cmt,
                                             span: self.span,
                                             code: err_mutbl(m_imm)}),
            mc::McReadOnly => Err(BckError {cmt: cmt,
                                            span: self.span,
                                            code: err_mutbl(m_const)}),
        }
    }

    fn check_immutable(&self, cmt: mc::cmt) -> BckResult<()>
    {
        match cmt.mutbl {
            mc::McImmutable => Ok(()),
            mc::McDeclared | mc::McInherited => {
                Err(BckError {cmt: cmt,
                              span: self.span,
                              code: err_mutbl(m_mutbl)})
            }
            mc::McReadOnly => Err(BckError {cmt: cmt,
                                            span: self.span,
                                            code: err_mutbl(m_const)}),
        }
    }

    fn cmt_scope(&self, cmt: mc::cmt) -> ty::Region {
        /*!
         *
         * Returns the maximal region scope for the which the
         * lvalue `cmt` is guaranteed to be valid.
         */

        match cmt.cat {
            mc::cat_rvalue => {
                self.bccx.tcx.region_maps.encl_region(cmt.id)
            }

            mc::cat_implicit_self |
            mc::cat_copied_upvar(_) => {
                ty::re_scope(self.item_ub)
            }

            mc::cat_static_item => {
                ty::re_static
            }

            mc::cat_local(local_id) |
            mc::cat_arg(local_id, _) |
            mc::cat_self(local_id) => {
                self.bccx.tcx.region_maps.encl_region(local_id)
            }

            mc::cat_stack_upvar(cmt) => self.cmt_scope(cmt),

            mc::cat_deref(cmt, _, mc::uniq_ptr(*)) => self.cmt_scope(cmt),

            mc::cat_deref(cmt, _, mc::gc_ptr(*)) => self.cmt_scope(cmt),

            mc::cat_deref(_, _, mc::unsafe_ptr(*)) => ty::re_static,

            mc::cat_deref(_, _, mc::region_ptr(_, r)) => r,

            mc::cat_interior(cmt, _) => self.cmt_scope(cmt),

            mc::cat_discr(cmt, _) => self.cmt_scope(cmt),
        }
    }

    fn check_cmt_scope(&self,
                       cmt: mc::cmt,
                       loan_region: ty::Region) -> BckResult<()>
    {
        let cmt_scope = self.cmt_scope(cmt);
        self.check_scope(cmt, loan_region, cmt_scope)
    }

    fn check_scope(&self,
                   cmt: mc::cmt,
                   loan_region: ty::Region,
                   max_scope: ty::Region) -> BckResult<()>
    {
        if !self.bccx.is_subregion_of(loan_region, max_scope) {
            return Err(BckError {
                cmt: cmt,
                span: self.span,
                code: err_out_of_scope(max_scope, loan_region)
            });
        }
        return Ok(());
    }

    fn mutate_or_freeze_mut_borrowed_ptr(
        &self,
        cmt: mc::cmt,
        loan_region: ty::Region,
        cmt_base: mc::cmt,
        pointer_mutbl: ast::mutability,
        pointer_region: ty::Region,
        lk: LoanKind) -> BckResult<LoansOrRoot>
    {
        assert!(pointer_mutbl == ast::m_mutbl);

        if_ok!(self.check_scope(cmt, loan_region, pointer_region));
        let loans = if_ok!(self.reserve(cmt_base, loan_region,
                                        ReserveForBorrowedMut));
        Ok(self.add_loan(loans, cmt, loan_region, lk, LpDeref))
    }

    fn root_managed_ptr(
        &self,
        cmt: mc::cmt,
        loan_region: ty::Region,
        cmt_base: mc::cmt,
        derefs: uint) -> BckResult<LoansOrRoot>
    {
        let cmt_scope = self.cmt_scope(cmt);

        let omit_root = (
            // See rule Freeze-Imm-Managed-Ptr-2 in doc.rs
            self.bccx.is_subregion_of(loan_region, cmt_scope) &&
            cmt.mutbl.is_immutable() &&
            !self.is_moved(cmt)
        );

        if !omit_root {
            // See rule Freeze-Imm-Managed-Ptr-1 in doc.rs
            Ok(self.root(cmt, cmt_base, loan_region, derefs, None))
        } else {
            Ok(Safe)
        }
    }

    fn mutate_or_freeze_mut_managed_ptr(
        &self,
        cmt: mc::cmt,
        loan_region: ty::Region,
        dyna: DynaFreezeKind,
        cmt_base: mc::cmt,
        derefs: uint,
        pointer_mutbl: ast::mutability) -> BckResult<LoansOrRoot>
    {
        assert!(pointer_mutbl == ast::m_mutbl);
        Ok(self.root(cmt, cmt_base, loan_region, derefs, Some(dyna)))
    }

    fn alias_or_freeze_item_scope(
        &self,
        cmt: mc::cmt,
        loan_region: ty::Region) -> BckResult<LoansOrRoot>
    {
        if_ok!(self.check_scope(cmt, loan_region,
                                ty::re_scope(self.item_ub)));
        Ok(Safe)
    }

    fn alias_or_freeze_rvalue(
        &self,
        cmt: mc::cmt,
        loan_region: ty::Region) -> BckResult<LoansOrRoot>
    {
        assert!(cmt.mutbl.is_immutable());

        // When we're in a 'const &x = ...' context, self.root_ub is
        // zero and the rvalue is static, not bound to a scope.
        let scope_region = if self.root_ub == 0 {
            ty::re_static
        } else {
            debug!("scope_region thing: %? ", cmt.id);
            ty::re_scope(self.bccx.tcx.region_maps.cleanup_scope(cmt.id))
        };

        if_ok!(self.check_scope(cmt, loan_region, scope_region));
        Ok(Safe)
    }

    fn is_moved(
        &self,
        cmt: mc::cmt) -> bool
    {
        match cmt.cat {
            mc::cat_rvalue => false,
            mc::cat_static_item => false,
            mc::cat_implicit_self => false,
            mc::cat_copied_upvar(_) => false,
            mc::cat_local(id) |
            mc::cat_self(id) |
            mc::cat_arg(id, _) => {
                self.bccx.moved_variables_set.contains(&id)
            }
            mc::cat_stack_upvar(cmt_base) => self.is_moved(cmt_base),
            mc::cat_deref(cmt_base, _, _) => self.is_moved(cmt_base),
            mc::cat_interior(cmt_base, _) => self.is_moved(cmt_base),
            mc::cat_discr(cmt_base, _) => self.is_moved(cmt_base),
        }
    }

    fn with_discr<R>(
        &self,
        match_id: ast::node_id,
        op: &fn(&ComputeLoansContext) -> R) -> R
    {
        // Subtle: in a match, we must ensure that each binding
        // variable remains valid for the duration of the arm in
        // which it appears, presuming that this arm is taken.
        // But it is inconvenient in trans to root something just
        // for one arm.  Therefore, we insert a cat_discr(),
        // basically a special kind of category that says "if this
        // value must be dynamically rooted, root it for the scope
        // `match_id`.
        //
        // As an example, consider this scenario:
        //
        //    let mut x = @Some(3);
        //    match *x { Some(y) {...} None {...} }
        //
        // Technically, the value `x` need only be rooted
        // in the `some` arm.  However, we evaluate `x` in trans
        // before we know what arm will be taken, so we just
        // always root it for the duration of the match.
        //
        // As a second example, consider *this* scenario:
        //
        //    let x = @mut @Some(3);
        //    match x { @@Some(y) {...} @@None {...} }
        //
        // Here again, `x` need only be rooted in the `some` arm.
        // In this case, the value which needs to be rooted is
        // found only when checking which pattern matches: but
        // this check is done before entering the arm.  Therefore,
        // even in this case we just choose to keep the value
        // rooted for the entire match.  This means the value will be
        // rooted even if the none arm is taken.  Oh well.
        //
        // At first, I tried to optimize the second case to only
        // root in one arm, but the result was suboptimal: first,
        // it interfered with the construction of phi nodes in the
        // arm, as we were adding code to root values before the
        // phi nodes were added.  This could have been addressed
        // with a second basic block.  However, the naive approach
        // also yielded suboptimal results for patterns like:
        //
        //    let x = @mut @...;
        //    match x { @@some_variant(y) | @@some_other_variant(y) =>
        //
        // The reason is that we would root the value once for
        // each pattern and not once per arm.  This is also easily
        // fixed, but it's yet more code for what is really quite
        // the corner case.
        //
        // Nonetheless, if you decide to optimize this case in the
        // future, you need only adjust where the cat_discr()
        // node appears to draw the line between what will be rooted
        // in the *arm* vs the *match*.

        let match_rooting_ctxt = ComputeLoansContext {
            discr_scope: Some(match_id), ..*self
        };
        op(&match_rooting_ctxt)
    }
}

pub fn opt_loan_path(cmt: mc::cmt) -> Option<@LoanPath> {
    /*!
     *
     * Computes the `LoanPath` (if any) for a `cmt`.  Normally
     * loan paths are built up by `freeze()`, `mutate()`, etc
     * as we traversed the `cmt`, but sometimes we just want to
     * compute the loan path for a `cmt` in isolation.
     */

    match cmt.cat {
        mc::cat_rvalue |
        mc::cat_static_item |
        mc::cat_copied_upvar(_) |
        mc::cat_implicit_self |
        mc::cat_arg(_, ast::by_ref) => {
            None
        }

        mc::cat_local(id) |
        mc::cat_arg(id, ast::by_copy) |
        mc::cat_self(id) => {
            Some(@LpVar(id))
        }

        mc::cat_deref(cmt_base, _, _) => {
            opt_loan_path(cmt_base).map(
                |&lp| @LpExtend(lp, cmt.mutbl, LpDeref))
        }

        mc::cat_interior(cmt_base, ik) => {
            opt_loan_path(cmt_base).map(
                |&lp| @LpExtend(lp, cmt.mutbl, LpInterior(ik)))
        }

        mc::cat_stack_upvar(cmt_base) |
        mc::cat_discr(cmt_base, _) => {
            opt_loan_path(cmt_base)
        }
    }
}