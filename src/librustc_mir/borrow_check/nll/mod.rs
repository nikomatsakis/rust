// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::borrow_set::BorrowSet;
use rustc::hir::def_id::DefId;
use rustc::mir::{ClosureRegionRequirements, ClosureOutlivesSubject, Local, Location, Mir};
use rustc::infer::InferCtxt;
use rustc::ty::{self, RegionKind, RegionVid};
use rustc::util::nodemap::FxHashMap;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::io;
use transform::MirSource;
use util::liveness::{LivenessResults, LocalSet};
use dataflow::FlowAtLocation;
use dataflow::MaybeInitializedPlaces;
use dataflow::move_paths::MoveData;

use util as mir_util;
use util::pretty::{self, ALIGN};
use self::mir_util::PassWhere;

mod constraint_generation;
pub mod explain_borrow;
mod facts;
pub(crate) mod region_infer;
mod renumber;
mod subtype_constraint_generation;
pub(crate) mod type_check;
mod universal_regions;

use self::region_infer::RegionInferenceContext;
use self::universal_regions::UniversalRegions;

#[derive(Abomonation, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct BorrowRegionVid {
    pub(crate) region_vid: RegionVid,
}

/// The "facts" which are the basis of the NLL borrow analysis.
#[derive(Default)]
crate struct AllFacts {
    // For each `&'a T` rvalue at point P, include ('a, B, P).
    //
    // XXX Universal regions?
    crate borrow_region: Vec<(RegionVid, BorrowRegionVid, Location)>,

    // `cfg_edge(P,Q)` for each edge P -> Q in the control flow
    crate cfg_edge: Vec<(Location, Location)>,

    // `killed(B,P)` when some prefix of the path borrowed at B is assigned at point P
    crate killed: Vec<(BorrowRegionVid, Location)>,

    // `outlives(R1, P, R2, Q)` when we require `R1@P: R2@Q`
    crate outlives: Vec<(RegionVid, Location, RegionVid, Location)>,

    // `use_live(X, P)` when the variable X is "use-live" on entry to P
    //
    // This could (should?) eventually be propagated by the timely dataflow code.
    crate use_live: Vec<(Local, Location)>,

    // `drop_live(X, P)` when the variable X is "drop-live" on entry to P
    //
    // This could (should?) eventually be propagated by the timely dataflow code.
    crate drop_live: Vec<(Local, Location)>,

    // `covariant_region(X, R)` when the type of X includes X in a contravariant position
    crate covariant_region: Vec<(Local, RegionVid)>,

    // `contravariant_region(X, R)` when the type of X includes X in a contravariant position
    crate contravariant_region: Vec<(Local, RegionVid)>,

    // `drop_region(X, R)` when the region R must be live when X is dropped
    crate drop_region: Vec<(Local, RegionVid)>,
}

/// Rewrites the regions in the MIR to use NLL variables, also
/// scraping out the set of universal regions (e.g., region parameters)
/// declared on the function. That set will need to be given to
/// `compute_regions`.
pub(in borrow_check) fn replace_regions_in_mir<'cx, 'gcx, 'tcx>(
    infcx: &InferCtxt<'cx, 'gcx, 'tcx>,
    def_id: DefId,
    param_env: ty::ParamEnv<'tcx>,
    mir: &mut Mir<'tcx>,
) -> UniversalRegions<'tcx> {
    debug!("replace_regions_in_mir(def_id={:?})", def_id);

    // Compute named region information. This also renumbers the inputs/outputs.
    let universal_regions = UniversalRegions::new(infcx, def_id, param_env);

    // Replace all remaining regions with fresh inference variables.
    renumber::renumber_mir(infcx, mir);

    let source = MirSource::item(def_id);
    mir_util::dump_mir(infcx.tcx, None, "renumber", &0, source, mir, |_, _| Ok(()));

    universal_regions
}

/// Computes the (non-lexical) regions from the input MIR.
///
/// This may result in errors being reported.
pub(in borrow_check) fn compute_regions<'cx, 'gcx, 'tcx>(
    infcx: &InferCtxt<'cx, 'gcx, 'tcx>,
    def_id: DefId,
    universal_regions: UniversalRegions<'tcx>,
    mir: &Mir<'tcx>,
    param_env: ty::ParamEnv<'gcx>,
    flow_inits: &mut FlowAtLocation<MaybeInitializedPlaces<'cx, 'gcx, 'tcx>>,
    move_data: &MoveData<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
) -> (
    RegionInferenceContext<'tcx>,
    Option<ClosureRegionRequirements<'gcx>>,
) {
    // Run the MIR type-checker.
    let liveness = &LivenessResults::compute(mir);
    let constraint_sets = &type_check::type_check(
        infcx,
        param_env,
        mir,
        def_id,
        &universal_regions,
        &liveness,
        flow_inits,
        move_data,
    );

    // Create the region inference context, taking ownership of the region inference
    // data that was contained in `infcx`.
    let var_origins = infcx.take_region_var_origins();
    let mut regioncx = RegionInferenceContext::new(var_origins, universal_regions, mir);

    // Generate various constraints.
    subtype_constraint_generation::generate(&mut regioncx, mir, constraint_sets);
    constraint_generation::generate_constraints(infcx, &mut regioncx, &mir, borrow_set);

    // Solve the region constraints.
    let closure_region_requirements = regioncx.solve(infcx, &mir, def_id);

    // Dump MIR results into a file, if that is enabled. This let us
    // write unit-tests, as well as helping with debugging.
    dump_mir_results(
        infcx,
        liveness,
        borrow_set,
        &mir,
        def_id,
        &regioncx,
        &closure_region_requirements,
    );

    // We also have a `#[rustc_nll]` annotation that causes us to dump
    // information
    dump_annotation(infcx, &mir, def_id, &regioncx, &closure_region_requirements);

    (regioncx, closure_region_requirements)
}

fn dump_mir_results<'a, 'gcx, 'tcx>(
    infcx: &InferCtxt<'a, 'gcx, 'tcx>,
    liveness: &LivenessResults,
    borrow_set: &BorrowSet<'tcx>,
    mir: &Mir<'tcx>,
    mir_def_id: DefId,
    regioncx: &RegionInferenceContext,
    closure_region_requirements: &Option<ClosureRegionRequirements>,
) {
    let source = MirSource::item(mir_def_id);
    if !mir_util::dump_enabled(infcx.tcx, "nll", source) {
        return;
    }

    let regular_liveness_per_location: FxHashMap<_, _> = mir.basic_blocks()
        .indices()
        .flat_map(|bb| {
            let mut results = vec![];
            liveness
                .regular
                .simulate_block(&mir, bb, |location, local_set| {
                    results.push((location, local_set.clone()));
                });
            results
        })
        .collect();

    let drop_liveness_per_location: FxHashMap<_, _> = mir.basic_blocks()
        .indices()
        .flat_map(|bb| {
            let mut results = vec![];
            liveness
                .drop
                .simulate_block(&mir, bb, |location, local_set| {
                    results.push((location, local_set.clone()));
                });
            results
        })
        .collect();

    mir_util::dump_mir(infcx.tcx, None, "nll", &0, source, mir, |pass_where, out| {
        match pass_where {
            // Before the CFG, dump out the values for each region variable.
            PassWhere::BeforeCFG => {
                regioncx.dump_mir(out)?;

                if let Some(closure_region_requirements) = closure_region_requirements {
                    writeln!(out, "|")?;
                    writeln!(out, "| Free Region Constraints")?;
                    for_each_region_constraint(closure_region_requirements, &mut |msg| {
                        writeln!(out, "| {}", msg)
                    })?;
                }
            }

            // Before each basic block, dump out the values
            // that are live on entry to the basic block.
            PassWhere::BeforeBlock(bb) => {
                let s = live_variable_set(&liveness.regular.ins[bb], &liveness.drop.ins[bb]);
                writeln!(out, "    | Live variables on entry to {:?}: {}", bb, s)?;
            }

            PassWhere::BeforeLocation(location) => {
                let s = live_variable_set(
                    &regular_liveness_per_location[&location],
                    &drop_liveness_per_location[&location],
                );
                writeln!(
                    out,
                    "{:ALIGN$} | Live variables on entry to {:?}: {}",
                    "",
                    location,
                    s,
                    ALIGN = ALIGN
                )?;

                let live_borrow_results = regioncx.live_borrow_results().unwrap();

                writeln!(
                    out,
                    "{:ALIGN$} | Borrows in scope on entry to {:?}: {:?}",
                    "",
                    location,
                    live_borrow_results.borrows_in_scope_at(location),
                    ALIGN = ALIGN,
                )?;

                for (borrow, region_vids) in live_borrow_results.restricts_at(location).iter() {
                    let borrow_location = borrow_set[*borrow].reserve_location;
                    writeln!(
                        out,
                        "{:ALIGN$} | Borrow {:?} from {:?} in scope due to regions {:?}",
                        "",
                        borrow,
                        borrow_location,
                        region_vids,
                        ALIGN = ALIGN
                    )?;
                }

                let live_regions = live_borrow_results.regions_live_at(location);
                if !live_regions.is_empty() {
                    writeln!(
                        out,
                        "{:ALIGN$} | Live regions on entry: {:?}",
                        "",
                        live_regions,
                        ALIGN = ALIGN,
                    )?;
                }

                let activations = borrow_set.activations_at_location(location);
                if !activations.is_empty() {
                    writeln!(
                        out,
                        "{:ALIGN$} | Activates: {:?}",
                        "",
                        activations,
                        ALIGN = ALIGN,
                    )?;
                }

                for (r1, p1, r2) in live_borrow_results.superset(location) {
                    writeln!(
                        out,
                        "{:ALIGN$} | ({:?} @ {:?}) <= ({:?} @ {:?})",
                        "",
                        r1,
                        p1,
                        r2,
                        location,
                        ALIGN = ALIGN,
                    )?;
                }
            }

            PassWhere::AfterLocation(_) | PassWhere::AfterCFG => {}
        }
        Ok(())
    });

    // Also dump the inference graph constraints as a graphviz file.
    let _: io::Result<()> = do_catch! {{
        let mut file =
            pretty::create_dump_file(infcx.tcx, "regioncx.dot", None, "nll", &0, source)?;
        regioncx.dump_graphviz(&mut file)?;
    }};
}

fn dump_annotation<'a, 'gcx, 'tcx>(
    infcx: &InferCtxt<'a, 'gcx, 'tcx>,
    mir: &Mir<'tcx>,
    mir_def_id: DefId,
    regioncx: &RegionInferenceContext,
    closure_region_requirements: &Option<ClosureRegionRequirements>,
) {
    let tcx = infcx.tcx;
    let base_def_id = tcx.closure_base_def_id(mir_def_id);
    if !tcx.has_attr(base_def_id, "rustc_regions") {
        return;
    }

    // When the enclosing function is tagged with `#[rustc_regions]`,
    // we dump out various bits of state as warnings. This is useful
    // for verifying that the compiler is behaving as expected.  These
    // warnings focus on the closure region requirements -- for
    // viewing the intraprocedural state, the -Zdump-mir output is
    // better.

    if let Some(closure_region_requirements) = closure_region_requirements {
        let mut err = tcx.sess
            .diagnostic()
            .span_note_diag(mir.span, "External requirements");

        regioncx.annotate(&mut err);

        err.note(&format!(
            "number of external vids: {}",
            closure_region_requirements.num_external_vids
        ));

        // Dump the region constraints we are imposing *between* those
        // newly created variables.
        for_each_region_constraint(closure_region_requirements, &mut |msg| {
            err.note(msg);
            Ok(())
        }).unwrap();

        err.emit();
    } else {
        let mut err = tcx.sess
            .diagnostic()
            .span_note_diag(mir.span, "No external requirements");
        regioncx.annotate(&mut err);
        err.emit();
    }
}

fn for_each_region_constraint(
    closure_region_requirements: &ClosureRegionRequirements,
    with_msg: &mut dyn FnMut(&str) -> io::Result<()>,
) -> io::Result<()> {
    for req in &closure_region_requirements.outlives_requirements {
        let subject: &dyn Debug = match &req.subject {
            ClosureOutlivesSubject::Region(subject) => subject,
            ClosureOutlivesSubject::Ty(ty) => ty,
        };
        with_msg(&format!(
            "where {:?}: {:?}",
            subject,
            req.outlived_free_region,
        ))?;
    }
    Ok(())
}

/// Right now, we piggy back on the `ReVar` to store our NLL inference
/// regions. These are indexed with `RegionVid`. This method will
/// assert that the region is a `ReVar` and extract its internal index.
/// This is reasonable because in our MIR we replace all universal regions
/// with inference variables.
pub trait ToRegionVid {
    fn to_region_vid(self) -> RegionVid;
}

impl<'tcx> ToRegionVid for &'tcx RegionKind {
    fn to_region_vid(self) -> RegionVid {
        if let ty::ReVar(vid) = self {
            *vid
        } else {
            bug!("region is not an ReVar: {:?}", self)
        }
    }
}

impl ToRegionVid for RegionVid {
    fn to_region_vid(self) -> RegionVid {
        self
    }
}

fn live_variable_set(regular: &LocalSet, drops: &LocalSet) -> String {
    // sort and deduplicate:
    let all_locals: BTreeSet<_> = regular.iter().chain(drops.iter()).collect();

    // construct a string with each local, including `(drop)` if it is
    // only dropped, versus a regular use.
    let mut string = String::new();
    for local in all_locals {
        string.push_str(&format!("{:?}", local));

        if !regular.contains(&local) {
            assert!(drops.contains(&local));
            string.push_str(" (drop)");
        }

        string.push_str(", ");
    }

    let len = if string.is_empty() {
        0
    } else {
        string.len() - 2
    };

    format!("[{}]", &string[..len])
}
