//! This pass removes the unwind branch of all the terminators when the no-landing-pads option is
//! specified.

use crate::transform::{MirPass, MirSource};
use rustc::mir::visit::MutVisitor;
use rustc::mir::LocalDecls;
use rustc::mir::*;
use rustc::ty::{self, Ty, TyCtxt};
use rustc_target::spec::abi::Abi;

pub struct NoLandingPads;

impl MirPass<'tcx> for NoLandingPads {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, _: MirSource<'tcx>, body: &mut Body<'tcx>) {
        no_landing_pads(tcx, body)
    }
}

pub fn no_landing_pads<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    if !tcx.sess.panic_unwinds() {
        // By default, if we see a call to an unknown callee with
        // non-Rust ABI, we will not remove the landing
        // entirely. Instead, we branch to a block that aborts.
        //
        // The reasoning here is:
        //
        // * With `-Cpanic=abort`, we turn all panics into abort at the source.
        // * But if the unwinding comes from a foreign source, we have
        //   to abort when we reach Rust code instead.
        //
        // Note that we don't actually *create* the abort block yet,
        // but we still know in advance what its index will be. So we
        // can create branches to it and -- if any branches were built
        // -- we can unwind.
        let mut abort_block = Some(body.basic_blocks().next_index());
        if tcx.sess.force_no_landing_pads() {
            debug!("no_landing_pads: -Zno-landing-pads");
            abort_block = None;
        }

        let (basic_blocks, local_decls) = body.basic_blocks_and_local_decls_mut();
        let mut pads = RemoveLandingPads::new(tcx, local_decls, abort_block);
        for (bb, data) in basic_blocks.iter_enumerated_mut() {
            pads.visit_basic_block_data(bb, data);
        }

        if pads.branched_to_abort_block {
            debug!("no_landing_pads: branched_to_abort_block=true");

            // Might be useful to have more than one abort block,
            // actually, so that we can have precise spaces?
            let source_info = SourceInfo { span: body.span, scope: OUTERMOST_SOURCE_SCOPE };
            let abort_block_data = BasicBlockData {
                statements: Vec::default(),
                terminator: Some(Terminator { source_info, kind: TerminatorKind::Abort }),
                is_cleanup: true,
            };
            let abort_block_created = body.basic_blocks_mut().push(abort_block_data);
            debug!("no_landing_pads: added block {:?}", abort_block_created);
            assert_eq!(Some(abort_block_created), abort_block);
        }
    }
}

struct RemoveLandingPads<'me, 'tcx> {
    tcx: TyCtxt<'tcx>,
    local_decls: &'me LocalDecls<'tcx>,
    abort_block: Option<BasicBlock>,
    branched_to_abort_block: bool,
}

impl<'me, 'tcx> RemoveLandingPads<'me, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        local_decls: &'me LocalDecls<'tcx>,
        abort_block: Option<BasicBlock>,
    ) -> Self {
        RemoveLandingPads { tcx, local_decls, abort_block, branched_to_abort_block: false }
    }
}

impl<'tcx> RemoveLandingPads<'_, 'tcx> {
    fn callee_should_abort(&self, callee_ty: Ty<'tcx>) -> bool {
        debug!("callee_should_abort(callee_ty = {:?})", callee_ty);

        // Rust ABIs are always implemented in Rust and
        // hence panics/unwinds will abort within.
        let callee_abi = callee_ty.fn_sig(self.tcx).abi();
        if let Abi::Rust | Abi::RustCall = callee_abi {
            debug!("callee_should_abort: false because of Rust ABI");
            return false;
        }

        // Other ABIs could be defined elsewhere. Check if we know
        // exactly which callee we have and how it was defined.
        if let ty::FnDef(def_id, _) = callee_ty.kind {
            if !self.tcx.is_foreign_item(def_id) {
                // This was defined in Rust. Therefore, any panics or
                // unwinds it generates will be translated to aborts.
                debug!("callee_should_abort: false because not foreign item");
                return false;
            }
        }

        // Otherwise, we must assume it *may* unwind.
        debug!("callee_should_abort: true");
        true
    }
}

impl<'tcx> MutVisitor<'tcx> for RemoveLandingPads<'_, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator_kind(&mut self, kind: &mut TerminatorKind<'tcx>, location: Location) {
        debug!("no_landing_pads: visit_terminator_kind(kind={:?}, location={:?}", kind, location);

        // Check for a call to a non-Rust function.
        if let Some(abort_block) = self.abort_block {
            if let TerminatorKind::Call { func, cleanup, .. } = kind {
                let func_ty = func.ty(self.local_decls, self.tcx);
                if self.callee_should_abort(func_ty) {
                    debug!("no_landing_pads: rewriting {:?} to {:?}", location, abort_block);
                    *cleanup = Some(abort_block);
                    self.branched_to_abort_block = true;
                    return;
                }
            }
        }

        // Otherwise, just remove unwinding.
        if let Some(unwind) = kind.unwind_mut() {
            unwind.take();
        }
    }
}
