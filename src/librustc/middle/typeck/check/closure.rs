/*!
 * Closure inference. The goal of this pass is to examine how free variables are used
 * within closure bodies and deduce from this:
 *
 * - Whether the closure ought to be `&self`, `&mut self`, or `self`.
 * - The appropriate mode for each variable.
 */

use middle::expr_use_visitor as euv;
use middle::freevars;
use middle::mem_categorization as mc;
use middle::ty;

///////////////////////////////////////////////////////////////////////////
// Type definitions

pub struct ClosureInference<'fcx> {
    fcx: &'fcx FnCtxt,
}

struct ClosureSummary {
    closure_expr_id: ast::NodeId,
    free_variables: HashMap<ty::UpvarId, FreeVariableUse>,
}

struct FreeVariableUse {
    consumed: Option<ast::NodeId>,
    borrowed: Option<(ast::NodeId, ty::BorrowKind)>,
}

///////////////////////////////////////////////////////////////////////////
// Public methods

impl<'fcx> ClosureInference<'fcx> {
    pub fn new(fcx: &'fcx FnCtxt) -> ClosureInference {
        ClosureInference { fcx: fcx }
    }

    pub fn analyze_fn(&mut self, id: ast::NodeId, blk: &ast::Block) {
    }
}

///////////////////////////////////////////////////////////////////////////
// Implementation details

impl<'fcx> Visitor<()> for ClosureInference<'fcx> {
    fn visit_fn(&mut self, fk: &visit::FnKind, fd: &ast::FnDecl,
                b: &ast::Block, s: Span, id: ast::NodeId, e: ()) {
        match fk {
            FkItemFn(..) | FkMethod(..) => {
                // Ignore nested items.
                return;
            }

            FkFnBlock => {
                let mut summary = ClosureSummary::new(id);
                let mut euv = euv::ExprUseVisitor::new(&mut summary, self);
                euv.walk_fn(fd, b);
            }
        }

        visit::walk_fn(self, fk, fd, b, s, id, e);
    }
}

impl ClosureSummary {
    fn new(id: ast::NodeId) -> ClosureSummary {
        ClosureSummary { closure_expr_id: id, free_variables: HashMap::new() }
    }

    fn free_variable_use(&mut self, upvar_id: ty::UpvarId) -> &mut FreeVariableUse {
        self.free_variables.find_or_insert_with(
            upvar_id,
            |_| FreeVariableUse { consumed: None,
                                  borrowed: None })
    }

    fn mark_cmt_consumed(&mut self, consume_id: ast::NodeId, cmt: mc::cmt) {
        // Look for some code that consumes an upvar or part of an upvar.
        let guarantor = cmt.guarantor();
        match guarantor.cat {
            mc::cat_copied_upvar(CopiedUpvar{upvar_id, ..}, _) |
            mc::cat_upvar(upvar_id, _) => {
                let free_variable_use = self.free_variable_use(upvar_id);
                if free_variable_use.consumed.is_none() {
                    free_variable_use.consumed = Some(consume_id);
                }
            }

            _ => { }
        }
    }

    fn mark_cmt_borrowed(&mut self,
                         borrow_id: ast::NodeId,
                         cmt: mc::cmt,
                         bk: ty::BorrowKind) {
        // Look for some code that consumes an upvar or part of an
        // upvar.
        match cmt.cat {
            mc::cat_rvalue(..) |
            mc::cat_static_item |
            mc::cat_local(..) |
            mc::cat_arg(..) => {
                // Ignore borrows that terminate in a non-upvar.
            }

            mc::cat_copied_upvar(CopiedUpvar{upvar_id, ..}, _) => {
                let free_variable_use = self.free_variable_use(upvar_id);

                // Check whether the upvar is already recorded with a
                // more restrictive borrow. If not, then update with
                // the current borrow.
                let needs_update = match free_variable_use.borrowed {
                    None => { true }
                    Some((bk1, _)) => most_restrictive(bk, bk1) != bk1
                };
                if needs_update {
                    free_variable_use.borrowed = Some((borrow_id, bk));
                }
            }

            mc::cat_upvar(upvar_id, _) => {
                // this should just never happen
                fail!("BAD");
            }

            mc::cat_deref(_, _, mc::UnsafePtr(..)) => {
            }

            mc::cat_deref(_, _, mc::GcPtr(..)) => {
            }

            mc::cat_deref(cmt1, _, mc::BorrowedPtr(bk1, _)) |
            mc::cat_deref(cmt1, _, mc::Implicit(bk1, _)) => {
                // Intuition:
                //
                //     fn foo(x: &mut T) {
                //         something(|| &*x)
                //     }
                //
                // Here, we are doing a shared borrow of `*x`.
                // In terms of the variables at hand:
                //
                //     cmt  = *x
                //     bk   = ty::ImmBorrow
                //     cmt1 = x
                //     bk1  = ty::MutBorrow
                //
                // If we convert `x` into a by-ref upvar `u_x`, the
                // only thing we need to make this legal is for `u_x`
                // to have type `&&mut T`. This is because we are
                // doing a shared borrow. In fact, in general, so long
                // as there is no type error, we know that `bk` is
                // less restrictive than `bk1` (i.e., if `bk1` is
                // `&T`, `bk` must be `&T`).  So we could just recurse
                // here with `bk`. But instead we use the least
                // restrictive so that, if the user screws up, we
                // don't infer that we need `&mut self` when we only
                // close over shared references.
                self.mark_cmt_borrowed(borrow_id, cmt1, least_restrictive(bk, bk1));
            }

            mc::cat_deref(cmt1, _, mc::OwnedPtr) |
            mc::cat_interior(cmt1, _) |
            mc::cat_downcast(cmt1) |
            mc::cat_discr(cmt1, _) => {
                self.mark_cmt_borrowed(borrow_id, cmt1, bk)
            }
        }
    }


    fn mark_cmt_assigned(&mut self,
                         assign_id: ast::NodeId,
                         cmt: mc::cmt) {
        // It doesn't affect the end results of the analysis to
        // conflate assignment and mutable borrows. The only negative
        // result might be if we were trying to explain the results of
        // the analysis to the end user, though we can probably come
        // up with an appropriate vague error message.
        self.mark_cmt_borrowed(assign_id, cmt, ty::MutBorrow)
    }
}

impl euv::Delegate for ClosureSummary {
    fn consume(&mut self,
               consume_id: ast::NodeId,
               consume_span: Span,
               cmt: mc::cmt,
               mode: ConsumeMode) {
        self.mark_cmt_consumed(consume_id, cmt);
    }

    fn consume_pat(&mut self,
                   consume_pat: &ast::Pat,
                   cmt: mc::cmt,
                   mode: ConsumeMode) {
        self.mark_cmt_consumed(consume_pat.id, cmt);
    }

    fn borrow(&mut self,
              _borrow_id: ast::NodeId,
              _borrow_span: Span,
              cmt: mc::cmt,
              _loan_region: ty::Region,
              bk: ty::BorrowKind,
              _loan_cause: LoanCause) {
        self.mark_cmt_borrowed(cmt, bk);
    }

    fn decl_without_init(&mut self,
                         _id: ast::NodeId,
                         _span: Span) {
        // don't care
    }

    fn mutate(&mut self,
              _assignment_id: ast::NodeId,
              _assignment_span: Span,
              assignee_cmt: mc::cmt,
              _mode: MutateMode) {
        self.mark_cmt_assigned(assignee_cmt);
    }
}

fn least_restrictive(bk1: ty::BorrowKind,
                     bk2: ty::BorrowKind)
                     -> ty::BorrowKind
{
    match (bk1, bk2) {
        (ty::ImmBorrow, _) => ty::ImmBorrow,
        (_, ty::ImmBorrow) => ty::ImmBorrow,

        (ty::UniqueImmBorrow, _) => ty::UniqueImmBorrow,
        (_, ty::UniqueImmBorrow) => ty::UniqueImmBorrow,

        (ty::MutBorrow, ty::MutBorrow) => ty::MutBorrow,
    }
}

fn most_restrictive(bk1: ty::BorrowKind,
                     bk2: ty::BorrowKind)
                     -> ty::BorrowKind
{
    match (bk1, bk2) {
        (ty::MutBorrow, _) => ty::MutBorrow,
        (_, ty::MutBorrow) => ty::MutBorrow,

        (ty::UniqueImmBorrow, _) => ty::UniqueImmBorrow,
        (_, ty::UniqueImmBorrow) => ty::UniqueImmBorrow,

        (ty::ImmBorrow, ty::ImmBorrow) => ty::ImmBorrow,
    }
}

