// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The `reachable_check` issues "unreachable code warnings".
//! Eventually it will also be responsible for checking coercions into
//! the `!` type.
//!
//! The checks works by propagating two values. First, on the way
//! **down** the tree, we compute "reachability". This indicates where
//! there may exist a path from the entry of the function to the given
//! expression etc. This is updated as we go, so if you have something
//! like
//!
//!     foo(return, 22)
//!
//! the `return` expression would be considered reachable, but the
//! `22` will not (even though their parent, the `foo()` call, is
//! reachable). Naturally this requires visiting the tree in
//! 'execution order' (more or less) -- reverse post-order of the CFG,
//! anyhow.
//!
//! As we do this walk, on the way back **up** the tree, we return
//! **divergence** information. The divergence indicates whether the
//! subexpression diverges (i.e., returns, breaks, or otherwise
//! performs some abnormal control flow).
//!
//! In its simplest form, divergence would just be a yes/no thing, but
//! we actually use a 3-valued form: no/fresh/stale, where both
//! fresh/stale indicate that the subexpression definitely diverged.
//! The difference has to do with warnings: a "fresh" divergence is
//! one where we have not yet issued a warning.
//!
//! To issue unreachable code warnings, we track at each point the
//! current *reachability* as well as the current *divergence*. The
//! divergence indicates whether the expression we are visiting has a
//! subexpression that diverges. If this divergence is "fresh", then
//! the next "action" that takes place (e.g., the next subexpression
//! that we visit) will be flagged as unreachable (with a lint), and
//! the divegence is changed to stale.
use std::fmt;
use super::*;

impl<'a, 'gcx, 'tcx> FnCtxt<'a, 'gcx, 'tcx> {
    pub fn reachable_check(&self, body: &'gcx hir::Body) {
        let _diverges = body.value.eval(self, Reachable::Yes);
    }

    /// Records a lint that `expr` is unreachable if `diverges`
    /// indicaes fresh divergence. In that case, returns
    /// `Diverges::Stale`; else just returns `diverges`
    /// unchanged. This is a typically used to report a warning at the
    /// first place where something is evaluated after a diverging
    /// expression. See `ReachableFromCx::warn_if_freshly_diverged()`
    /// for more comments.
    fn add_lint_if_freshly_diverged(&self, diverges: Diverges, expr: &Eval) -> Diverges {
        debug!("add_lint_if_freshly_diverged(diveges={:?}, expr={:?})",
               diverges, expr);

        match diverges {
            Diverges::No | Diverges::Stale => diverges,
            Diverges::Fresh => {
                self.tables.borrow_mut().lints.add_lint(
                    lint::builtin::UNREACHABLE_CODE,
                    expr.id(),
                    expr.span(),
                    format!("unreachable {}", expr.kind()));

                Diverges::Stale
            }
        }
    }
}

/// Tracks the reachable/diverges state for a given HIR node (the
/// `source`).  When first created, the diverges is `No`. For each
/// subexpression that gets evaluated, you can invoke `always_eval()`.
/// This will analyze the subexpression and update the
/// reachable/diverges state. It may also issue warnings if the
/// previously evaluated expression had freshly diverged.
///
/// Usually, there comes a point in the execution (typically at the
/// end) where the subexpression state is "consumed". For example, if
/// you write `a + b`, then the values for `a` and `b` would be
/// computed, but then both values are "consumed" when they get added
/// together to produce a new value. This "consume" point in execution
/// can be signalled by calling `consume()`, though typically one
/// invokes `ret_after_consume()`, which will both `consume()` and
/// then return the final `diverges` state ready to be propagated up
/// the tree.
///
/// In some cases, e.g. blocks or `match` expressions, one wishes to
/// pass the results of a final subexpression back up the tree without
/// it being `consumed`. For this there exist other `ret_*()` methods;
/// see their comments for more info.
struct ReachableFromCx<'src, 'fcx, 'gcx: 'tcx, 'tcx: 'fcx> {
    fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
    source: &'src Eval,
    reachable: Reachable,
    diverges: Diverges,
}

impl<'src, 'fcx, 'gcx, 'tcx> fmt::Debug for ReachableFromCx<'src, 'fcx, 'gcx, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ReachableFromCx")
         .field("source.id", &self.source.id())
         .field("reachable", &self.reachable)
         .field("diverges", &self.diverges)
         .finish()
    }
}

impl<'src, 'fcx, 'gcx, 'tcx> ReachableFromCx<'src, 'fcx, 'gcx, 'tcx> {
    fn new(source: &'src Eval,
           fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
           reachable: Reachable)
           -> Self
    {
        ReachableFromCx { fcx, source, reachable, diverges: Diverges::No }
    }

    /// Issues a warning that `expr` is unreachable if our current
    /// status is that we have freshly diverged. This will be the
    /// case if the last thing we evaluated started out reachable and
    /// returned a status that it freshly diverged.
    ///
    /// Let's work through an example. Imagine we are evaluating
    /// this tuple:
    ///
    ///     (foo(return, 22), None, return)
    ///
    /// We will create a `ReachableFromCx` for the tuple which will
    /// start out with `Diverges::No` and (let's say) `Reachable::Yes`:
    ///
    /// - We will then invoke `eval` on `foo(return, 22)`, which will
    ///   create a nested `ReachableFromCx` with the same values.
    ///   - We will then invoke `always_eval()` on `return`. This will return
    ///     `Diverges::Fresh`.
    ///   - The context for the call to `foo()` will update its settings
    ///     to `Reachable::No` and `Diverges::Fresh`. This indicates that the
    ///     last evaluated thing has diverged, and that we are now in dead code.
    ///   - We will then invoke `always_eval()` on `22`. Because `self.diverges`
    ///     is `Diverges::Fresh`, we will trigger a warning that `22` is dead
    ///     code and update the state to `Diverges::Stale`.
    ///   - This `Diverges::Stale` will ultimately be returned.
    /// - The outer context can now update its state to `Reachable::No` and
    ///   `Diverges::Stale`. Because the state is stale, no further warnings
    ///   are issued.
    /// - When we evaluate `return`, the result is a "fresh"
    ///   divergence, but because the return is unreachable to
    ///   start, it gets converted to `Diverges::Stale`.
    fn warn_if_freshly_diverged(&mut self, expr: &Eval) {
        debug!("{:?}::warn_if_freshly_diverged(expr={:?})",
               self, expr);

        self.diverges = self.fcx.add_lint_if_freshly_diverged(self.diverges, expr);
    }

    /// Invoke `always_eval()` on a sequence of things.
    fn always_eval_all<'a, S, I>(mut self, exprs: I) -> Self
        where I: IntoIterator<Item = &'a S>, S: Eval + 'a,
    {
        for s in exprs {
            self = self.always_eval(s);
        }
        self
    }

    /// Indicates that the next thing which happens is that `expr` is
    /// evaluated.  If we are currently in a freshly diverged state,
    /// this will result in a warning that `expr` is unreachable.
    ///
    /// Returns a new `ReachableFromCx` with an updated
    /// diverges/reachability state taking into accounts the
    /// divergence of `expr`.
    fn always_eval(mut self, expr: &Eval) -> Self {
        self.warn_if_freshly_diverged(expr);

        let expr_diverges = expr.eval(self.fcx, self.reachable).under(self.reachable);
        self.diverges = self.diverges.or(expr_diverges);
        self.reachable = self.reachable.after(self.diverges);

        self
    }

    /// Indicates that the next thing which happens is that `expr` *may*
    /// be evaluated. If we are currently in a freshly diverged state,
    /// this will result in a warning that `expr` is unreachable.
    ///
    /// Returns a new context. Because `expr` is only conditionally
    /// evaluated, the reachability state of this context is always the
    /// same. But the divergence may go from fresh to stale, since we
    /// did issue a warning.
    ///
    /// Note that this helper is not used to encode ifs/matches (for
    /// those, see `ret_after_match()`), but instead used for special
    /// forms like `&&` that only conditionally evaluate some of their
    /// operands. It is basically a convenience form; those
    /// expressions could be modeled more precisely with a nested
    /// context and a `ret_after_match()` call.
    fn maybe_eval(mut self, expr: &Eval) -> Self {
        self.warn_if_freshly_diverged(expr);

        // Even if `source` diverges, this expression may not, since
        // `source` is only conditionally evaluated. Similarly, the reachability
        // result from `source` doesn't matter.
        let _expr_diverges = expr.eval(self.fcx, self.reachable);

        self
    }

    /// Indicates that the evaluations which have happened so far are
    /// "consumed" by the parent expression, which means we possibly
    /// issue an unreachable code warning for the parent expression.
    /// This is typically invoked by `ret_after_consume()` below,
    /// although in some places we invoke it earlier.
    ///
    /// Example:
    ///
    ///     while <cond> { ... }
    ///
    /// The code for `ExprWhile` first evaluates `<cond>` and then
    /// invokes `consume()`, which reflects the fact that during
    /// execution we will test the result of `<cond>` and only execute
    /// the body if it is true. As a result, if `<cond>` leaves us in
    /// a freshly diverged state (e.g., `while (return) {...}`), then
    /// the `while` loop be flagged as unreachable (rather than the
    /// body).
    fn consume(mut self) -> Self {
        self.warn_if_freshly_diverged(self.source);
        self
    }

    /// Calling `ret_after_consume()` indicates that the various
    /// evaluated subexpressions are used to construct a result, and
    /// then checks the final return type of the source (which may be
    /// `!`). Returns a final divergence state suitable for
    /// propagating upwards.
    ///
    /// Equivalent to `self.consume().ret_without_consume()`, so see
    /// those methods for more information.
    fn ret_after_consume(self) -> Diverges {
        self.consume().ret_without_consume()
    }

    /// Calling `ret_without_consume()` returns the final divergence
    /// state for the source. This is derived from the current
    /// divergence state (reflecting any subexpressions that have been
    /// evaluated) combined with the type of the source; if the type
    /// is `!`, then the source is considered to freshly diverged (but
    /// only if some subexpression has not already diverged).
    ///
    /// The name `ret_without_consume()` is meant to signal that the
    /// nested subexpressions will not be considered "consumed". This
    /// affects where the unreachable code warnings are emitted. In
    /// general, `ret_after_consume()` is what you want, but in some cases
    /// it may not be. The canonical example is a block expression:
    ///
    ///     let x = {
    ///         return;
    ///     };
    ///
    /// Here, the final state of the block expression after processing
    /// its statement will be `Diverges::Fresh`. If we invoke
    /// `ret_after_consume()`, that would indicate that the block is
    /// "processing" its result in some way, and hence warn that the
    /// block is unreachable. But we want to propagate the fresh
    /// divergence state and hence warn that the assignment to `x` is
    /// unreachable.
    fn ret_without_consume(self) -> Diverges {
        // Check the type of this expression. If its type is `!`, then
        // it is known to diverge. If the current point (end of the
        // expr) is still considered reachable, then set diverges to
        // always.
        let ty = self.fcx.node_type(self.source.id());
        let ty = self.fcx.shallow_resolve(ty);
        if ty.is_never() {
            // If self.diverges is already `Stale`,
            // just return that. Otherwise we get
            // multiple warnings on the way "up" the tree,
            // e.g.:
            //
            //      foo(return return x)
            //
            // or
            //
            //      let x: ! = return; // warns about assignment to `x`
            //      use(x); // would warn here too
            self.diverges.or(Diverges::Fresh)
        } else {
            self.diverges
        }
    }

    /// Indicates that we consume our evaluations up till this point
    /// and then choose (and branch to) one of the arms. As a result,
    /// if all of the arms diverge, our state will be diverging, and
    /// so forth. The results of the arms are not considered consumed,
    /// so if they are fresh divergences, whatever comes after the
    /// source will be flagged as unreachable.
    fn ret_after_match<S: Arm>(mut self, arms: &[S]) -> Diverges {
        // "Consume" whatever expressions we have evaluated so far,
        // which correspond to the match discriminant. This means
        // that if you have something like
        //
        //     match (return) { ... }
        //
        // the `match` is signaled as unreachable. (Similarly for an
        // `if (return) { ... }`.)
        self = self.consume();

        let arms_diverge = if arms.is_empty() {
            // An empty match `match x { }` is static proof that the
            // current path is unreachable (even if it was not
            // previously considered to *be* unreachable). It is
            // debatable if dead-code warnings are desired in this
            // situation or not!  We currently consider it a *fresh*
            // divergence, though, so warnings will be issued for
            // something like
            //
            //     foo(match x { })
            //
            // which seems reasonable, since `foo(return)` would warn.
            Diverges::Fresh
        } else {
            // For non-empty matches, the arms as a whole diverge only
            // if all the arms individually diverge.
            arms.iter()
                .map(|arm| arm.eval(self.fcx, self.reachable))
                .fold(Diverges::Stale, Diverges::and)
        };

        // The match itself diverges if the condition diverges
        // (`self.diverges`) or the arms as a whole diverge.
        self.diverges.or(arms_diverge)
    }
}

/// Given to an expression to indicate whether it is considered
/// reachable from the function start.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Reachable {
    /// Might be reachable (the normal case).
    Yes,

    /// This code is dead (and a dead-code warning was issued in the past).
    No,
}

impl Reachable {
    /// Let `self` by the reachability of some expr `X`, which has divergence `d`.
    /// Returns the reachability of things that come after `X`. Basically
    /// this will return `Reachable::No` if either `X` was not reachable or `X`
    /// diverged.
    fn after(self, d: Diverges) -> Reachable {
        match d {
            Diverges::No => self,
            Diverges::Fresh | Diverges::Stale => Reachable::No
        }
    }
}

/// An expression **diverges** if it has type `!`, or if it will
/// always execute some subexpression with type `!`.
///
/// For example, `return` and `Some(return)` both diverge, as does
/// `Some({return; 22})` -- note that the last expression has type
/// `Option<i32>`, so a diverging expression does not always have an
/// uninhabited true. In contrast, `if foo { return } else { 22 }`
/// does not diverge, because the `return` may not execute. This
/// judgement is done without any "value" analysis, so `if true {
/// return } else { 22 }` also is not considered to diverge.
///
/// Divergence is used to check coercions **into** the type `!`. Such
/// a coercion is legal if the source expression diverges.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Diverges {
    // NB: The ordering of these variants is important,
    // due to the definition of `and` and `or` below.

    /// This expression is not known to diverge (the normal case).
    No,

    /// This expression diverges and no warning has yet been issued.
    Fresh,

    /// Some part of this expression diverges, but we already issued a warning.
    Stale,
}

impl Diverges {
    /// If code that is known to be dead diverges, we treat that as a
    /// stale divergence.
    fn under(self, r: Reachable) -> Diverges {
        match r {
            Reachable::Yes => self,
            Reachable::No => match self {
                Diverges::No => Diverges::No,
                Diverges::Fresh | Diverges::Stale => Diverges::Stale,
            }
        }
    }

    /// Returns a diverging result if both `self` and `d` indicate
    /// diverging. Used to combine match arms or other alternatives.
    fn and(self, d: Diverges) -> Diverges {
        cmp::min(self, d)
    }

    /// Returns a diverging result if either `self` or `d` diverges
    /// (the result is fresh only if both are fresh, to avoid
    /// overloading with warnings). Used to combine divergence values
    /// from things in a sequence.
    fn or(self, d: Diverges) -> Diverges {
        cmp::max(self, d)
    }
}

trait Eval: Arm {
    fn span(&self) -> Span;

    fn id(&self) -> ast::NodeId;

    fn kind(&self) -> &'static str;
}

trait Arm: fmt::Debug {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              reachable: Reachable)
                              -> Diverges;
}

impl Eval for hir::Expr {
    fn span(&self) -> Span {
        self.span
    }

    fn id(&self) -> ast::NodeId {
        self.id
    }

    fn kind(&self) -> &'static str {
        "expression"
    }
}

impl Arm for hir::Expr {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              reachable: Reachable)
                              -> Diverges
    {
        let cx = ReachableFromCx::new(self, fcx, reachable);
        match self.node {
            hir::ExprBox(ref subexpr) =>
                cx.always_eval(subexpr)
                  .ret_after_consume(),

            hir::ExprLit(..) |
            hir::ExprPath(_) |
            hir::ExprInlineAsm(..) |
            hir::ExprClosure(..) |
            hir::ExprAgain(_) =>
                cx.ret_after_consume(),

            hir::ExprBinary(op, ref lhs, ref rhs) |
            hir::ExprAssignOp(op, ref lhs, ref rhs) => match op.node {
                hir::BiAnd |
                hir::BiOr =>
                    cx.always_eval(lhs)
                      .maybe_eval(rhs)
                      .ret_after_consume(),

                hir::BiAdd |
                hir::BiSub |
                hir::BiMul |
                hir::BiDiv |
                hir::BiRem |
                hir::BiBitXor |
                hir::BiBitAnd |
                hir::BiBitOr |
                hir::BiShl |
                hir::BiShr |
                hir::BiEq |
                hir::BiLt |
                hir::BiLe |
                hir::BiNe |
                hir::BiGe |
                hir::BiGt =>
                    cx.always_eval(lhs).always_eval(rhs).ret_after_consume(),
            },

            hir::ExprUnary(_, ref oprnd) =>
                cx.always_eval(oprnd).ret_after_consume(),

            hir::ExprAddrOf(_, ref oprnd) =>
                cx.always_eval(oprnd).ret_after_consume(),

            hir::ExprBreak(_, ref expr_opt) |
            hir::ExprRet(ref expr_opt) =>
                cx.always_eval_all(expr_opt)
                  .ret_after_consume(),

            hir::ExprAssign(ref lhs, ref rhs) =>
                cx.always_eval(lhs)
                  .always_eval(rhs)
                  .ret_after_consume(),

            hir::ExprIf(ref cond, ref then_expr, ref opt_else_expr) =>
                cx.always_eval(cond)
                  .ret_after_match(&[Some(then_expr), opt_else_expr.as_ref()]),

            hir::ExprWhile(ref cond, ref body, _name) =>
                cx.always_eval(cond)
                  .consume() // warn that `while (return) { .. }` is unreachable
                  .maybe_eval(body) // body diverging does not cause the `while{}` to diverge
                  .ret_without_consume(), // already consumed above

            hir::ExprLoop(ref body, _name, _source) => {
                // Use `maybe_eval` even though the body is always
                // evaluated because we do not (necessarily) consider
                // the loop to diverge even if the body diverges.
                //
                // We rely instead on the judgement of the
                // type-checker, which will have assigned this loop a
                // type of `!` if there is no `break` that targets it
                // (or if all of those breaks give a source expression
                // of type `!`).
                //
                // Note that this is not maximally precise as the
                // `break` could be dead. In other words, this loop
                // is not considered to diverge:
                //
                //     loop { return; break; }
                cx.maybe_eval(body)
                  .ret_after_consume()
            }

            hir::ExprMatch(ref discrim, ref arms, _source) =>
                cx.always_eval(discrim)
                  .ret_after_match(arms),

            hir::ExprBlock(ref b) =>
                cx.ret_after_match(&[b]),

            hir::ExprCall(ref callee, ref args) =>
                cx.always_eval(callee).always_eval_all(args).ret_after_consume(),

            hir::ExprMethodCall(_, _, ref args) =>
                cx.always_eval_all(args).ret_after_consume(),

            hir::ExprCast(ref e, _) |
            hir::ExprType(ref e, _) =>
                cx.always_eval(e).ret_after_consume(),

            hir::ExprArray(ref args) =>
                cx.always_eval_all(args).ret_after_consume(),

            hir::ExprRepeat(ref element, _count) =>
                cx.always_eval(element).ret_after_consume(),

            hir::ExprTup(ref elts) =>
                cx.always_eval_all(elts).ret_after_consume(),

            hir::ExprStruct(_, ref fields, ref base_expr) =>
                cx.always_eval_all(fields).always_eval_all(base_expr).ret_after_consume(),

            hir::ExprField(ref base, _) |
            hir::ExprTupField(ref base, _) =>
                cx.always_eval(base).ret_after_consume(),

            hir::ExprIndex(ref base, ref idx) =>
                cx.always_eval(base).always_eval(idx).ret_after_consume(),
        }
    }
}

impl Eval for hir::Block {
    fn span(&self) -> Span {
        self.span
    }

    fn id(&self) -> ast::NodeId {
        self.id
    }

    fn kind(&self) -> &'static str {
        "block"
    }
}

impl Arm for hir::Block {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              reachable: Reachable)
                              -> Diverges
    {
        // Subtle point: we invoke `ret_without_consume()` in a block,
        // unlike most things, which call `ret_after_consume()`. This
        // is because we do not want blocks to be signaled as
        // unreachable, but rather the context in which they
        // appear. Consider:
        //
        //     foo({ return; })
        //
        // Here, the final statement will be the `return`, and it will
        // set the diverging status to "fresh". If we called `make()`,
        // the *block* would get an "unreachable block" warning,
        // because it would be assumed that it is "using" this value.
        // Instead, we call `ret()` and hence the block propagates the
        // "fresh" status up to `foo()`, and hence the `foo`
        // expression is signaled as unreachable.
        return ReachableFromCx::new(self, fcx, reachable)
            .always_eval_all(self.stmts.iter().filter(is_not_item_stmt))
            .always_eval_all(&self.expr)
            .ret_without_consume();

        fn is_not_item_stmt(stmt: &&hir::Stmt) -> bool {
            match stmt.node {
                hir::StmtDecl(ref decl, _) => match decl.node {
                    hir::DeclLocal(_) => true,
                    hir::DeclItem(_) => false,
                },
                hir::StmtExpr(..) | hir::StmtSemi(..) => true,
            }
        }
    }
}

impl<T: Eval> Eval for P<T> {
    fn span(&self) -> Span {
        (**self).span()
    }

    fn id(&self) -> ast::NodeId {
        (**self).id()
    }

    fn kind(&self) -> &'static str {
        (**self).kind()
    }
}

impl<T: Arm> Arm for P<T> {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              reachable: Reachable)
                              -> Diverges
    {
        (**self).eval(fcx, reachable)
    }
}

impl<'a, T: Eval> Eval for &'a T {
    fn span(&self) -> Span {
        (**self).span()
    }

    fn id(&self) -> ast::NodeId {
        (**self).id()
    }

    fn kind(&self) -> &'static str {
        (**self).kind()
    }
}

impl<'a, T: Arm> Arm for &'a T {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              reachable: Reachable)
                              -> Diverges
    {
        (**self).eval(fcx, reachable)
    }
}

impl<T: Arm> Arm for Option<T> {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              reachable: Reachable)
                              -> Diverges
    {
        if let Some(ref v) = *self {
            v.eval(fcx, reachable)
        } else {
            Diverges::No
        }
    }
}

impl Arm for hir::Arm {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              mut reachable: Reachable)
                              -> Diverges
    {
        let mut guard_diverges = if let Some(ref guard) = self.guard {
            guard.eval(fcx, reachable).under(reachable)
        } else {
            Diverges::No
        };

        // if the guard diveges, we want to warn that the arm body is unreachable
        guard_diverges = fcx.add_lint_if_freshly_diverged(guard_diverges, &self.body);
        reachable = reachable.after(guard_diverges);

        // check whether the body diverges
        let body_diverges = self.body.eval(fcx, reachable);

        // the final result: this arm is diverging if the guard
        // diverges or body diveges
        guard_diverges.or(body_diverges)
    }
}

impl Eval for hir::Field {
    fn span(&self) -> Span {
        self.expr.span
    }

    fn id(&self) -> ast::NodeId {
        self.expr.id
    }

    fn kind(&self) -> &'static str {
        "expression"
    }
}

impl Arm for hir::Field {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              reachable: Reachable)
                              -> Diverges
    {
        self.expr.eval(fcx, reachable)
    }
}

impl Eval for hir::Stmt {
    fn span(&self) -> Span {
        self.span
    }

    fn id(&self) -> ast::NodeId {
        self.node.id()
    }

    fn kind(&self) -> &'static str {
        "statement"
    }
}

impl Arm for hir::Stmt {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              reachable: Reachable)
                              -> Diverges
    {
        match self.node {
            hir::StmtDecl(ref decl, _) => match decl.node {
                hir::DeclLocal(ref l) => l.eval(fcx, reachable),
                hir::DeclItem(_) => Diverges::No,
            },
            hir::StmtExpr(ref expr, _) | hir::StmtSemi(ref expr, _) => expr.eval(fcx, reachable),
        }
    }
}

impl Eval for hir::Local {
    fn span(&self) -> Span {
        self.pat.span
    }

    fn id(&self) -> ast::NodeId {
        self.id
    }

    fn kind(&self) -> &'static str {
        "code"
    }
}

impl Arm for hir::Local {
    fn eval<'fcx, 'gcx, 'tcx>(&self,
                              fcx: &'fcx FnCtxt<'fcx, 'gcx, 'tcx>,
                              reachable: Reachable)
                              -> Diverges
    {
        // A `hir::Local` corresponds to something like this:
        //
        //     let s = <expr>;
        //
        // if `<expr>` should freshly diverge, we will flag the local
        // as containing unreachable code (specifically, the `s`).
        ReachableFromCx::new(self, fcx, reachable)
            .always_eval_all(&self.init)
            .ret_after_consume()
    }
}
