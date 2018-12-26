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
use rustc::ty::layout::{LayoutError, SizeSkeleton};
use rustc::ty::subst::Subst;
use rustc::ty::subst::Substs;
use rustc::ty::Instance;
use rustc::ty::InstanceDef;
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

    // FIXME: Most inefficient fixed-point iteration possible
    let mut changed = true;
    while changed {
        changed = false;

        for mir_def_id in tcx.body_owners() {
            debug!(
                "polymorphize_analysis: (interfunction propagation) mir_def_id={:?}",
                mir_def_id
            );

            let call_edges = visitors[&mir_def_id].call_edges.clone();
            for call_edge in &call_edges {
                debug!(
                    "polymorphize_analysis: call_edge.callee={:?}",
                    call_edge.callee
                );

                let substituted_dependencies: Vec<_>;
                if call_edge.callee.is_local() {
                    substituted_dependencies = visitors[&call_edge.callee]
                        .dependencies
                        .iter()
                        .map(|dependency| dependency.subst(tcx, call_edge.substs))
                        .collect();
                } else {
                    // FIXME: cross-crate dependencies. For now, assume that they depend
                    // on.. something.
                    substituted_dependencies = vec![Dependency {
                        span: call_edge.span,
                        kind: DependencyKind::OtherMethod(call_edge.substs),
                    }];
                }

                for dependency in substituted_dependencies {
                    if visitors
                        .get_mut(&mir_def_id)
                        .unwrap()
                        .record_dependency(dependency.span, dependency.kind)
                    {
                        changed = true;
                    }
                }
            }
        }
    }

    for (_, visitor) in &visitors {
        let message = if visitor.dependencies.is_empty() {
            "no polymorphic dependencies found"
        } else {
            "some polymorphic dependencies found"
        };

        let mut err = tcx.sess.struct_span_err(visitor.mir.span, message);

        for dependency in &visitor.dependencies {
            err.span_label(
                dependency.span,
                format!("depends on `{:?}`", dependency.kind),
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
    dependencies: Vec<Dependency<'gcx>>,
    call_edges: Vec<CallEdge<'gcx>>,
}

#[derive(Copy, Clone, Debug)]
pub struct Dependency<'gcx> {
    span: Span,
    kind: DependencyKind<'gcx>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DependencyKind<'gcx> {
    /// We depend on knowing the size and/or alignment of the type;
    /// this can occur when e.g. a value of this type.
    SizeAlignment(Ty<'gcx>),

    /// An unresolved instance
    TraitMethod(DefId, &'gcx Substs<'gcx>),

    /// Call to some wacky thing (e.g., drop glue) that references
    /// type parameters.
    OtherMethod(&'gcx Substs<'gcx>),
}

BraceStructTypeFoldableImpl! {
    impl<'tcx> TypeFoldable<'tcx> for Dependency<'tcx> {
        span, kind
    }
}

EnumTypeFoldableImpl! {
    impl<'tcx> TypeFoldable<'tcx> for DependencyKind<'tcx> {
        (DependencyKind::SizeAlignment)(a),
        (DependencyKind::TraitMethod)(a, b),
        (DependencyKind::OtherMethod)(a),
    }
}

#[derive(Copy, Clone, Debug)]
struct CallEdge<'gcx> {
    span: Span,

    /// DefId of an inherent method or free fn that we invoke.
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

    fn has_dependency(&mut self, kind: &DependencyKind<'gcx>) -> bool {
        self.dependencies.iter().any(|d| d.kind == *kind)
    }

    fn push_dependency_if_new(&mut self, span: Span, kind: DependencyKind<'gcx>) -> bool {
        // F<IXME: O(n^2) code here
        if !self.has_dependency(&kind) {
            self.dependencies.push(Dependency { span, kind });
            true
        } else {
            false
        }
    }

    fn has_call_edge(&mut self, def_id: DefId, substs: &'gcx Substs<'gcx>) -> bool {
        self.call_edges
            .iter()
            .any(|e| e.callee == def_id && e.substs == substs)
    }

    fn push_call_edge_if_new(
        &mut self,
        span: Span,
        callee: DefId,
        substs: &'gcx Substs<'gcx>,
    ) -> bool {
        // FIXME: O(n^2) code here
        if !self.has_call_edge(callee, substs) {
            self.call_edges.push(CallEdge {
                span,
                callee,
                substs,
            });
            true
        } else {
            false
        }
    }

    fn record_dependency(&mut self, span: Span, kind: DependencyKind<'gcx>) -> bool {
        match kind {
            DependencyKind::SizeAlignment(ty) => {
                match SizeSkeleton::compute(ty, self.tcx, self.param_env) {
                    Ok(SizeSkeleton::Known(_)) => {
                        debug!("visit_ty: known size, skipping");
                        false
                    }
                    _ => {
                        debug!("visit_ty: recording dependency");
                        self.push_dependency_if_new(span, kind)
                    }
                }
            }

            DependencyKind::TraitMethod(def_id, substs) => {
                self.record_call_dependency(span, def_id, substs)
            }

            DependencyKind::OtherMethod(substs) => {
                substs.needs_subst() && self.push_dependency_if_new(span, kind)
            }
        }
    }

    fn record_call_dependency(
        &mut self,
        span: Span,
        def_id: DefId,
        substs: &'gcx Substs<'gcx>,
    ) -> bool {
        match Instance::resolve(self.tcx, self.param_env, def_id, substs) {
            None => self.push_dependency_if_new(span, DependencyKind::TraitMethod(def_id, substs)),
            Some(instance) => match instance.def {
                InstanceDef::Item(def_id) => {
                    self.push_call_edge_if_new(span, def_id, instance.substs)
                }
                _ => self.record_dependency(span, DependencyKind::OtherMethod(instance.substs)),
            },
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
        debug!(
            "visit_statement: statement={:?} location={:?}",
            statement, location
        );
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
            TerminatorKind::Call { func, .. } => match func.ty(self.mir, self.tcx).sty {
                ty::FnDef(def_id, substs) => {
                    self.record_call_dependency(
                        self.mir.source_info(location).span,
                        def_id,
                        substs,
                    );
                }
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
        debug!(
            "visit_operand: operand={:?} location={:?}",
            operand, location
        );
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let ty = place.ty(self.mir, self.tcx).to_ty(self.tcx);
                debug!("visit_operand: place={:?}", place);
                self.record_dependency(
                    self.mir.source_info(location).span,
                    DependencyKind::SizeAlignment(ty),
                );
            }
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
            Place::Projection(proj) => match proj.elem {
                ProjectionElem::Field(..) => {
                    let ty = proj.base.ty(self.mir, self.tcx).to_ty(self.tcx);
                    match self.tcx.layout_of(self.param_env.and(ty)) {
                        Ok(..) => (),
                        Err(LayoutError::SizeOverflow(..)) => (),
                        Err(LayoutError::Unknown(ty)) => {
                            self.record_dependency(
                                self.mir.source_info(location).span,
                                DependencyKind::SizeAlignment(ty),
                            );
                        },
                    }
                },
                _ => {},
            },
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
