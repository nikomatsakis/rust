/*!
 * A different sort of visitor for walking fn bodies.  Unlike the
 * normal visitor, which just walks the entire body in one shot, the
 * `ExprUseVisitor` determines how expressions are being used.
 */

use mc = middle::mem_categorization;
use middle::freevars;
use middle::pat_util;
use middle::ty;
use middle::typeck;
use syntax::ast;
use syntax::ast_util;
use syntax::codemap::{Span, Spanned};
use util::ppaux::Repr;

#[deriving(Eq)]
pub enum LoanCause {
    ClosureCapture(Span),
    BorrowExpr(@ast::Expr),
    AutoRef(@ast::Expr),
    RefBinding(@ast::Pat),
    OverloadedOperator(@ast::Expr),
}

#[deriving(Eq)]
enum ConsumeMode {
    Copy,    // reference to x where x has a type that copies
    Move,    // reference to x where x has a type that moves
}

trait Delegate {
    // The value found at `cmt` is either copied or moved, depending
    // on mode.
    fn consume(&mut self,
               cmt: mc::cmt,
               mode: ConsumeMode)
    { }

    // The value found at `borrow` is being borrowed at the point
    // `borrow_id` for the region `loan_region` with kind `bk`.
    fn borrow(&mut self,
              cmt: mc::cmt,
              borrow_id: ast::NodeId,
              loan_region: ty::Region,
              bk: ty::BorrowKind,
              loan_cause: LoanCause)
    { }

    // Like borrow, but as a result of an autoref.
    fn auto_ref(&mut self,
                cmt: mc::cmt,
                expr: @ast::Expr,
                auto_ref: &ty::AutoRef)
    { }

    // The local variable `id` is declared but not initialized.
    fn uninit(&mut self,
              id: ast::NodeId,
              span: Span)
    { }

    // The path at `cmt` is being assigned to.
    fn mutate(&mut self,
              cmt: mc::cmt)
    { }
}

pub struct ExprUseVisitor<D,TYPER> {
    mc: mc::MemCategorizationContext<TYPER>,
    method_map: typeck::MethodMap,
    delegate: D,
}

// If the TYPER results in an error, it's because the type check
// failed (or will fail, when the error is uncovered and reported
// during writeback). In this case, we just ignore this part of the
// code.
macro_rules! ignore_err(
    ($inp: expr) => (
        match $inp {
            Ok(v) => v,
            Err(()) => return
        }
    )
)

impl<D:Delegate,TYPER:mc::Typer> ExprUseVisitor<D,TYPER> {
    fn tcx<'a>(&'a self) -> &'a ty::ctxt {
        self.mc.typer.tcx()
    }

    fn expect_unadjusted(&self, expr: &ast::Expr) {
        /*!
         * We don't actually put adjustments on any old expression.
         * Sometimes it's easier to just assume that the result is not
         * adjusted. In those places where we make this assumption, we
         * invoke this method to double-check.
         */

        if self.tcx().adjustments.borrow().contains_key(&expr.id) {
            self.tcx().sess.span_bug(
                expr.span,
                format!("Did not expect an adjustment on an \
                         explicitly borrowed expression"));
        }
    }

    fn delegate_consume(&mut self, cmt: mc::cmt) {
        let mode = copy_or_move(self.tcx(), cmt.ty);
        self.delegate.consume(cmt, mode);
    }

    fn consume_exprs(&mut self, exprs: &Vec<@ast::Expr>) {
        for &expr in exprs.iter() {
            self.consume_expr(expr);
        }
    }

    fn consume_expr(&mut self, expr: @ast::Expr) {
        let cmt = ignore_err!(self.mc.cat_expr(expr));
        self.delegate_consume(cmt);

        match expr.node {
            ast::ExprParen(subexpr) => {
                self.consume_expr(subexpr);
            }

            _ => {
                self.walk_expr(expr)
            }
        }
    }

    fn mutate_expr(&mut self, expr: @ast::Expr) {
        let cmt = ignore_err!(self.mc.cat_expr(expr));
        self.delegate.mutate(cmt);
        self.walk_expr(expr);
    }

    fn borrow_expr(&mut self,
                   expr: @ast::Expr,
                   r: ty::Region,
                   bk: ty::BorrowKind,
                   cause: LoanCause) {
        let cmt = ignore_err!(self.mc.cat_expr(expr));
        self.delegate.borrow(cmt, expr.id, r, bk, cause);

        // Note: Unlike consume, we can ignore ExprParen. cat_expr
        // already skips over them, and walk will uncover any
        // attachments or whatever.
        self.walk_expr(expr)
    }

    fn select_from_expr(&mut self, expr: @ast::Expr) {
        self.walk_expr(expr)
    }

    fn walk_expr(&mut self, expr: @ast::Expr) {
        self.adjust(expr);

        match expr.node {
            ast::ExprParen(subexpr) => {
                self.walk_expr(subexpr)
            }

            ast::ExprPath(..) => { }

            ast::ExprUnary(ast::UnDeref, base) => {      // *base
                if !self.walk_overloaded_operator(expr, [base]) {
                    self.select_from_expr(base);
                }
            }

            ast::ExprField(base, _, _) => {         // base.f
                self.select_from_expr(base);
            }

            ast::ExprIndex(lhs, rhs) => {           // lhs[rhs]
                if !self.walk_overloaded_operator(expr, [lhs, rhs]) {
                    self.select_from_expr(lhs);
                    self.consume_expr(rhs);
                }
            }

            ast::ExprCall(callee, ref args) => {    // callee(args)
                self.consume_exprs(args);
            }

            ast::ExprMethodCall(_, _, ref args) => { // callee.m(args)
                self.consume_exprs(args);
            }

            ast::ExprStruct(_, ref fields, opt_with) => {
                self.walk_struct_expr(expr, fields, opt_with);
            }

            ast::ExprTup(ref exprs) => {
                self.consume_exprs(exprs);
            }

            ast::ExprIf(cond_expr, then_blk, opt_else_expr) => {
                self.consume_expr(cond_expr);
                self.walk_block(then_blk);
                for else_expr in opt_else_expr.iter() {
                    self.consume_expr(*else_expr);
                }
            }

            ast::ExprMatch(discr, ref arms) => {
                // treatment of the discriminant is handled while
                // walking the arms:
                let discr_cmt = ignore_err!(self.mc.cat_expr(discr));
                for arm in arms.iter() {
                    self.walk_arm(discr_cmt, arm);
                }
            }

            ast::ExprVec(ref exprs) => {
                self.consume_exprs(exprs);
            }

            ast::ExprAddrOf(m, base) => {   // &base
                // make sure that the thing we are pointing out stays valid
                // for the lifetime `scope_r` of the resulting ptr:
                let expr_ty = ty::expr_ty(self.tcx(), expr);
                if !ty::type_is_bot(expr_ty) {
                    let r = ty::ty_region(self.tcx(), expr.span, expr_ty);
                    let bk = ty::BorrowKind::from_mutbl(m);
                    self.borrow_expr(base, r, bk, BorrowExpr(expr));
                } else {
                    self.walk_expr(base);
                }
            }

            ast::ExprInlineAsm(..) |
            ast::ExprBreak(..) |
            ast::ExprAgain(..) |
            ast::ExprLit(..) => {}

            ast::ExprLoop(blk, _) => {
                self.walk_block(blk);
            }

            ast::ExprWhile(cond_expr, blk) => {
                self.consume_expr(cond_expr);
                self.walk_block(blk);
            }

            ast::ExprForLoop(..) => fail!("non-desugared expr_for_loop"),

            ast::ExprUnary(_, lhs) => {
                if !self.walk_overloaded_operator(expr, [lhs]) {
                    self.consume_expr(lhs);
                }
            }

            ast::ExprBinary(_, lhs, rhs) => {
                if !self.walk_overloaded_operator(expr, [lhs, rhs]) {
                    self.consume_expr(lhs);
                    self.consume_expr(rhs);
                }
            }

            ast::ExprBlock(blk) => {
                self.walk_block(blk);
            }

            ast::ExprRet(ref opt_expr) => {
                for expr in opt_expr.iter() {
                    self.consume_expr(*expr);
                }
            }

            ast::ExprAssign(lhs, rhs) => {
                self.mutate_expr(lhs);
                self.consume_expr(rhs);
            }

            ast::ExprCast(base, _) => {
                self.consume_expr(base);
            }

            ast::ExprAssignOp(_, lhs, rhs) => {
                // FIXME(#4712) --- Overloaded operators?
                //
                // if !self.walk_overloaded_operator(expr, [lhs, rhs])
                // {
                self.consume_expr(lhs);
                self.consume_expr(rhs);
                // }
            }

            ast::ExprRepeat(base, count) => {
                self.consume_expr(base);
                self.consume_expr(count);
            }

            ast::ExprFnBlock(..) |
            ast::ExprProc(..) => {
                self.walk_captures(expr)
            }

            ast::ExprVstore(base, _) => {
                self.consume_expr(base);
            }

            ast::ExprBox(place, base) => {
                self.consume_expr(place);
                self.consume_expr(base);
            }

            ast::ExprMac(..) => {
                self.tcx().sess.span_bug(
                    expr.span,
                    "macro expression remains after expansion");
            }
        }
    }

    fn walk_stmt(&mut self, stmt: &ast::Stmt) {
        match stmt.node {
            ast::StmtDecl(decl, id) => {
                match decl.node {
                    ast::DeclLocal(local) => {
                        self.walk_local(local);
                    }

                    ast::DeclItem(_) => {
                        // we don't visit nested items in this visitor,
                        // only the fn body we were given.
                    }
                }
            }

            ast::StmtExpr(expr, _) |
            ast::StmtSemi(expr, _) => {
                self.consume_expr(expr);
            }

            ast::StmtMac(..) => {
                self.tcx().sess.span_bug(
                    stmt.span,
                    format!("unexpanded stmt macro"));
            }
        }
    }

    fn walk_local(&mut self, local: @ast::Local) {
        match local.init {
            None => {
                pat_util::pat_bindings(self.tcx().def_map, local.pat, |_, id, span, _| {
                    self.delegate.uninit(id, span);
                })
            }

            Some(expr) => {
                // Variable declarations with
                // initializers are considered
                // "assigns", which is handled by
                // `gather_pat`:
                let init_cmt = ignore_err!(self.mc.cat_expr(expr));
                self.walk_pat(init_cmt, local.pat);
            }
        }
    }

    fn walk_block(&mut self, blk: &ast::Block) {
        /*!
         * Indicates that the value of `blk` will be consumed,
         * meaning either copied or moved depending on its type.
         */

        debug!("walk_block(blk.id={:?})", blk.id);

        for stmt in blk.stmts.iter() {
            self.walk_stmt(*stmt);
        }

        for tail_expr in blk.expr.iter() {
            self.consume_expr(*tail_expr);
        }
    }

    fn walk_struct_expr(&mut self,
                        expr: @ast::Expr,
                        fields: &Vec<ast::Field>,
                        opt_with: Option<@ast::Expr>) {
        // Consume the expressions supplying values for each field.
        for field in fields.iter() {
            self.consume_expr(field.expr);
        }

        let with_expr = match opt_with {
            Some(w) => { w }
            None => { return; }
        };

        let with_cmt = ignore_err!(self.mc.cat_expr(with_expr));

        // Select just those fields of the `with`
        // expression that will actually be used
        let with_fields = match ty::get(with_cmt.ty).sty {
            ty::ty_struct(did, ref substs) => {
                ty::struct_fields(self.tcx(), did, substs)
            }
            ref r => {
                self.tcx().sess.span_bug(
                    with_expr.span,
                    format!("with expression doesn't evaluate to a struct"));
            }
        };

        // Consume those fields of the with expression that are needed.
        for with_field in with_fields.iter() {
            if !contains_field_named(with_field, fields) {
                let cmt_field = self.mc.cat_field(with_expr,
                                                  with_cmt,
                                                  with_field.ident,
                                                  with_field.mt.ty);
                self.delegate_consume(cmt_field);
            }
        }

        fn contains_field_named(field: &ty::field,
                                fields: &Vec<ast::Field>)
                                -> bool
        {
            fields.iter().any(
                |f| f.ident.node.name == field.ident.name)
        }
    }

    // Invoke the appropriate delegate calls for anything that gets
    // consumed or borrowed as part of the automatic adjustment
    // process.
    fn adjust(&mut self, expr: @ast::Expr) {
        match self.tcx().adjustments.borrow().find_copy(&expr.id) {
            None => { }
            Some(adjustment) => {
                match *adjustment {
                    ty::AutoAddEnv(..) |
                    ty::AutoObject(..) => {
                        // Creating an object or closure consumes the
                        // input and stores it into the resulting rvalue.
                        let cmt_unadjusted =
                            ignore_err!(self.mc.cat_expr_unadjusted(expr));
                        self.delegate_consume(cmt_unadjusted);
                    }
                    ty::AutoDerefRef(ty::AutoDerefRef {
                        autoref: None, ..
                    }) => {
                        // Just adding autoderefs doesn't do anything but
                        // produce a new, derived lvalue.
                    }
                    ty::AutoDerefRef(ty::AutoDerefRef {
                        autoref: Some(ref auto_ref),
                        autoderefs: n
                    }) => {
                        // Adding an autoref on the other hand creates
                        // a borrow.
                        let cmt_derefd =
                            ignore_err!(self.mc.cat_expr_autoderefd(expr, n));
                        self.delegate.auto_ref(cmt_derefd, expr, auto_ref);
                    }
                }
            }
        }
    }

    fn walk_overloaded_operator(&mut self,
                                expr: @ast::Expr,
                                args: &[@ast::Expr])
                                -> bool
    {
        let method_call = typeck::MethodCall::expr(expr.id);
        if !self.method_map.borrow().contains_key(&method_call) {
            return false;
        }

        // For overloaded operators, we always autoref the results
        // for the duration of the call itself.
        let r = ty::ReScope(expr.id);
        let bk = ty::ImmBorrow;
        let cause = OverloadedOperator(expr);

        for &arg in args.iter() {
            self.borrow_expr(arg, r, bk, cause);
        }
        return true;
    }

    fn walk_arm(&mut self, discr_cmt: mc::cmt, arm: &ast::Arm) {
        for &pat in arm.pats.iter() {
            self.walk_pat(discr_cmt, pat);
        }

        for guard in arm.guard.iter() {
            self.consume_expr(*guard);
        }

        self.consume_expr(arm.body);
    }

    fn walk_pat(&mut self, discr_cmt: mc::cmt, pat: @ast::Pat) {
        let delegate = &mut self.delegate;
        let def_map = self.mc.typer.tcx().def_map;
        ignore_err!(self.mc.cat_pattern(discr_cmt, pat, |mc, pat_cmt, pat| {
            if pat_util::pat_is_binding(def_map, pat) {
                match pat.node {
                    ast::PatIdent(ast::BindByRef(m), _, _) => {
                        let (r, bk) = {
                            let tcx = mc.typer.tcx();
                            let pat_ty = ty::node_id_to_type(tcx, pat.id);
                            (ty::ty_region(tcx, pat.span, pat_ty),
                             ty::BorrowKind::from_mutbl(m))
                        };
                        delegate.borrow(pat_cmt, pat.id, r, bk, RefBinding(pat));
                    }
                    ast::PatIdent(ast::BindByValue(_), _, _) => {
                        let mode = copy_or_move(mc.typer.tcx(), pat_cmt.ty);
                        delegate.consume(pat_cmt, mode);
                    }
                    _ => {
                        mc.typer.tcx().sess.span_bug(
                            pat.span,
                            "binding pattern not an identifier");
                    }
                }
            }
        }));
    }

    fn walk_captures(&mut self, closure_expr: @ast::Expr) {
        debug!("walk_captures({})", closure_expr.repr(self.tcx()));

        let fn_ty = ty::node_id_to_type(self.tcx(), closure_expr.id);
        let freevars = freevars::get_freevars(self.tcx(), closure_expr.id);
        match ty::ty_closure_store(fn_ty) {
            ty::RegionTraitStore(..) => {
                self.walk_by_ref_captures(closure_expr, freevars);
            }
            ty::UniqTraitStore => {
                self.walk_by_value_captures(closure_expr, freevars);
            }
        }
    }

    fn walk_by_ref_captures(&mut self,
                            closure_expr: @ast::Expr,
                            freevars: &Vec<@freevars::freevar_entry>) {
        for freevar in freevars.iter() {
            let id_var = ast_util::def_id_of_def(freevar.def).node;
            let cmt_var = ignore_err!(self.cat_captured_var(closure_expr.id,
                                                            closure_expr.span,
                                                            freevar.def));

            // Lookup the kind of borrow the callee requires, as
            // inferred by regionbk
            let upvar_id = ty::UpvarId { var_id: id_var,
                                         closure_expr_id: closure_expr.id };
            let upvar_borrow = self.tcx().upvar_borrow_map.borrow()
                                   .get_copy(&upvar_id);

            self.delegate.borrow(cmt_var,
                                 closure_expr.id,
                                 upvar_borrow.region,
                                 upvar_borrow.kind,
                                 ClosureCapture(freevar.span));
        }
    }

    fn walk_by_value_captures(&mut self,
                              closure_expr: @ast::Expr,
                              freevars: &Vec<@freevars::freevar_entry>) {
        for freevar in freevars.iter() {
            let id_var = ast_util::def_id_of_def(freevar.def).node;
            let cmt_var = ignore_err!(self.cat_captured_var(closure_expr.id,
                                                            closure_expr.span,
                                                            freevar.def));
            self.delegate_consume(cmt_var);
        }
    }

    fn cat_captured_var(&mut self,
                        closure_id: ast::NodeId,
                        closure_span: Span,
                        upvar_def: ast::Def)
                        -> mc::McResult<mc::cmt> {
        // Create the cmt for the variable being borrowed, from the
        // caller's perspective
        let var_id = ast_util::def_id_of_def(upvar_def).node;
        let var_ty = ty::node_id_to_type(self.tcx(), var_id);
        self.mc.cat_def(closure_id, closure_span, var_ty, upvar_def)
    }
}

fn copy_or_move(tcx: &ty::ctxt, ty: ty::t) -> ConsumeMode {
    if ty::type_moves_by_default(tcx, ty) { Move } else { Copy }
}

