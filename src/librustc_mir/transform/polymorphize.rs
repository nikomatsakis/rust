// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// The visitors in this module collect sizes and counts of the most important
// pieces of MIR. The resulting numbers are good approximations but not
// completely accurate (some things might be counted twice, others missed).

use rustc::hir::def_id::DefId;
use rustc::mir::visit as mir_visit;
use rustc::mir::visit::Visitor;
use rustc::mir::BasicBlock;
use rustc::mir::Location;
use rustc::mir::TerminatorKind;
use rustc::mir::{Mir, Operand, ProjectionElem};
use rustc::mir::{Place, PlaceElem};
use rustc::mir::{Rvalue, Statement, StatementKind};
use rustc::ty::fold::TypeFoldable;
use rustc::ty::fold::TypeVisitor;
use rustc::ty::subst::{Substs, UnpackedKind};
use rustc::ty::Instance;
use rustc::ty::InstanceDef;
use rustc::ty::layout::SizeSkeleton;
use rustc::ty::{self, Ty, TyCtxt};
use std::collections::BTreeMap;
use syntax_pos::Span;

pub fn polymorphize_analysis<'me, 'gcx>(tcx: TyCtxt<'me, 'gcx, 'gcx>, (): ()) {
    if !tcx.sess.opts.debugging_opts.polymorphize {
        return;
    }

    let mut visitors: BTreeMap<_, _> = tcx
        .body_owners()
        .map(|mir_def_id| (mir_def_id, DependencyVisitor::new(tcx, mir_def_id)))
        .collect();

    for mir_def_id in tcx.body_owners() {
        debug!("polymorphize_analysis: (interfunction propagation) mir_def_id={:?}", mir_def_id);

        // Need to create a fresh copy of the visitor for this Mir so that we can add to it and
        // avoid borrow checking errors - not great.
        let mut fresh = visitors[&mir_def_id].clone();

        for call_edge in &visitors[&mir_def_id].call_edges {
            debug!("polymorphize_analysis: call_edge.callee={:?}", call_edge.callee);
            for dependency in &visitors[&call_edge.callee].dependencies {
                debug!("polymorphize_analysis: dependency={:?}", dependency);
                let unpacked_kind = call_edge.substs
                    .type_for_def(
                        tcx
                        .generics_of(call_edge.callee)
                        .type_param(&dependency.param_ty, tcx)
                    ).unpack();
                debug!("polymorphize_analysis: unpacked_kind={:?}", unpacked_kind);
                if let UnpackedKind::Type(ty) = unpacked_kind {
                    fresh.visit_ty(ty, dependency.span, dependency.kind);
                }
            }
        }

        visitors.entry(mir_def_id).and_modify(|visitor| {
            *visitor = fresh;
        });
    }

    for (_, visitor) in &visitors {
        let message = if visitor.dependencies.is_empty() {
            "no polymorphic dependencies found"
        } else {
            "some polymorphic dependencies found"
        };

        let mut err = tcx
            .sess
            .struct_span_err(visitor.mir.span, message);

        for dependency in &visitor.dependencies {
            err.span_label(
                dependency.span,
                format!(
                    "depends on type `{:?}` for `{:?}`",
                    dependency.param_ty, dependency.kind
                ),
            );
        }

        for call_edge in &visitor.call_edges {
            err.span_label(
                call_edge.span,
                format!(
                    "invokes `{:?}` with substitutions `{:?}`",
                    call_edge.callee, call_edge.substs
                ),
            );
        }

        err.emit();
    }
}

#[derive(Clone)]
struct DependencyVisitor<'me, 'gcx> {
    mir: &'me Mir<'gcx>,
    param_env: ty::ParamEnv<'gcx>,
    tcx: TyCtxt<'me, 'gcx, 'gcx>,
    dependencies: Vec<Dependency>,
    call_edges: Vec<CallEdge<'gcx>>,
}

#[derive(Copy, Clone, Debug)]
pub struct Dependency {
    span: Span,
    param_ty: ty::ParamTy,
    kind: DependencyKind,
}

#[derive(Copy, Clone, Debug)]
pub enum DependencyKind {
    /// We depend on knowing the size and/or alignment of the type;
    /// this can occur when e.g. a value of this type.
    SizeAlignment,

    /// We invoke trait methods where the impl includes this type
    /// parameter in its input types.
    TraitMethod,
}

#[derive(Copy, Clone, Debug)]
struct CallEdge<'gcx> {
    span: Span,
    callee: DefId,
    substs: &'gcx Substs<'gcx>,
}

impl DependencyVisitor<'me, 'gcx> {
    fn new(tcx: TyCtxt<'me, 'gcx, 'gcx>, mir_def_id: DefId) -> Self {
        debug!("new: mir_def_id={:?}", mir_def_id);
        let mir = tcx.optimized_mir(mir_def_id);
        let param_env = tcx.param_env(mir_def_id);
        let mut visitor = Self {
            mir,
            param_env,
            tcx,
            dependencies: vec![],
            call_edges: vec![],
        };

        // compute the initial set of dependencies and call-edges
        visitor.visit_mir(mir);

        visitor
    }

    fn record_dependency(
        &mut self,
        span: Span,
        value: impl TypeFoldable<'gcx>,
        kind: DependencyKind,
    ) {
        struct DependencyRecorder<'me> {
            dependencies: &'me mut Vec<Dependency>,
            span: Span,
            kind: DependencyKind,
        }

        impl<'me, 'gcx> TypeVisitor<'gcx> for DependencyRecorder<'me> {
            fn visit_ty(&mut self, ty: Ty<'gcx>) -> bool {
                // Need to walk the type to find out if there is a type parameter anywhere
                // in the type.
                for ty in ty.walk() {
                    if let ty::TyKind::Param(param_ty) = ty.sty {
                        self.dependencies.push(Dependency {
                            span: self.span,
                            param_ty,
                            kind: self.kind,
                        });
                    }
                }

                false
            }
        }

        value.visit_with(&mut DependencyRecorder {
            dependencies: &mut self.dependencies,
            span,
            kind,
        });
    }

    /// Indicates that the current MIR invokes the given item with the given substs.
    /// We should therefore take the dependencies from there and transfer them in here.
    fn record_call(&mut self, span: Span, callee: DefId, substs: &'gcx Substs<'gcx>) {
        self.call_edges.push(CallEdge {
            span,
            callee,
            substs,
        });
    }

    fn visit_call(
        &mut self,
        span: Span,
        def_id: DefId,
        substs: &'gcx Substs<'gcx>,
    ) {
        match Instance::resolve(self.tcx, self.param_env, def_id, substs) {
            None => self.record_dependency(span, substs, DependencyKind::TraitMethod),
            Some(instance) => match instance.def {
                InstanceDef::Item(def_id) => self.record_call(span, def_id, substs),
                _ => self.record_dependency(span, substs, DependencyKind::TraitMethod),
            },
        }
    }

    fn visit_ty(&mut self, ty: Ty<'gcx>, span: Span, kind: DependencyKind) {
        debug!("visit_ty: ty={:?} ty.has_param_types()={:?}", ty, ty.has_param_types());
        if !ty.has_param_types() {
            return;
        }

        match SizeSkeleton::compute(ty, self.tcx, self.param_env) {
            Ok(SizeSkeleton::Known(_)) => {
                debug!("visit_ty: known size, skipping");
            },
            _ =>  {
                debug!("visit_ty: recording dependency");
                self.record_dependency(span, ty, kind);
            }
        }
    }
}

impl mir_visit::Visitor<'gcx> for DependencyVisitor<'_, 'gcx> {
    fn visit_mir(&mut self, mir: &Mir<'gcx>) {
        // since the `super_mir` method does not traverse the MIR of
        // promoted rvalues, (but we still want to gather statistics
        // on the structures represented there) we manually traverse
        // the promoted rvalues here.
        for promoted_mir in &mir.promoted {
            self.visit_mir(promoted_mir);
        }

        self.super_mir(mir);
    }

    fn visit_statement(
        &mut self,
        block: BasicBlock,
        statement: &Statement<'gcx>,
        location: Location,
    ) {
        debug!("visit_statement: statement={:?} location={:?}", statement, location);
        match statement.kind {
            StatementKind::Assign(..) => (),
            StatementKind::FakeRead(..) => (),
            StatementKind::Retag { .. } => (),
            StatementKind::EscapeToRaw { .. } => (),
            StatementKind::SetDiscriminant { .. } => (),
            StatementKind::StorageLive(..) => (),
            StatementKind::StorageDead(..) => (),
            StatementKind::InlineAsm { .. } => (),
            StatementKind::AscribeUserType(..) => (),
            StatementKind::Nop => (),
        }
        self.super_statement(block, statement, location);
    }

    fn visit_terminator_kind(
        &mut self,
        block: BasicBlock,
        kind: &TerminatorKind<'gcx>,
        location: Location,
    ) {
        match kind {
            TerminatorKind::Goto { .. } => (),
            TerminatorKind::SwitchInt { .. } => (),
            TerminatorKind::Resume => (),
            TerminatorKind::Abort => (),
            TerminatorKind::Return => (),
            TerminatorKind::Unreachable => (),
            TerminatorKind::Drop { .. } => {}
            TerminatorKind::DropAndReplace { .. } => {}
            TerminatorKind::Call {
                func,
                ..
            } => match func.ty(self.mir, self.tcx).sty {
                ty::FnDef(def_id, substs) => self.visit_call(
                    self.mir.source_info(location).span,
                    def_id,
                    substs,
                ),
                ty::FnPtr(..) => (), // not interesting
                _ => unimplemented!(),
            },
            TerminatorKind::Assert { .. } => {}
            TerminatorKind::Yield { .. } => {}
            TerminatorKind::GeneratorDrop => (),
            TerminatorKind::FalseEdges { .. } => (),
            TerminatorKind::FalseUnwind { .. } => (),
        }

        self.super_terminator_kind(block, kind, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'gcx>, location: Location) {
        debug!("visit_rvalue: rvalue={:?} location={:?}", rvalue, location);
        match rvalue {
            Rvalue::Use(..) => (),
            Rvalue::Repeat(..) => (),
            Rvalue::Ref(..) => (),
            Rvalue::Len(..) => (),
            Rvalue::Cast(..) => (),
            Rvalue::BinaryOp(..) => (),
            Rvalue::CheckedBinaryOp(..) => (),
            Rvalue::UnaryOp(..) => (),
            Rvalue::Discriminant(..) => (),
            Rvalue::NullaryOp(..) => (),
            Rvalue::Aggregate(..) => (),
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_operand(&mut self, operand: &Operand<'gcx>, location: Location) {
        debug!("visit_operand: operand={:?} location={:?}", operand, location);
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let ty = place.ty(self.mir, self.tcx).to_ty(self.tcx);
                debug!("visit_operand: place={:?}", place);
                self.visit_ty(
                    ty,
                    self.mir.source_info(location).span,
                    DependencyKind::SizeAlignment
                );
            },
            Operand::Constant(..) => (),
        }
        self.super_operand(operand, location);
    }

    fn visit_place(
        &mut self,
        place: &Place<'gcx>,
        context: mir_visit::PlaceContext<'gcx>,
        location: Location,
    ) {
        match place {
            Place::Local(..) => (),
            Place::Static(..) => (),
            Place::Promoted(..) => (),
            Place::Projection(..) => (),
        }
        self.super_place(place, context, location);
    }

    fn visit_projection_elem(&mut self, place: &PlaceElem<'gcx>, location: Location) {
        match place {
            ProjectionElem::Deref => (),
            ProjectionElem::Subslice { .. } => (),
            ProjectionElem::Field(..) => (),
            ProjectionElem::Index(..) => (),
            ProjectionElem::ConstantIndex { .. } => (),
            ProjectionElem::Downcast(..) => (),
        }
        self.super_projection_elem(place, location);
    }
}
