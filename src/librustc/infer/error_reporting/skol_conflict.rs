// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Error Reporting for Anonymous Region Lifetime Errors
//! where both the regions are anonymous.
use infer::InferCtxt;
use ty;
use ty::error::TypeError;
use infer;
use infer::region_inference::RegionResolutionError::*;
use infer::region_inference::RegionResolutionError;

impl<'a, 'gcx, 'tcx> InferCtxt<'a, 'gcx, 'tcx> {
    pub fn try_report_skol_conflict(&self, error: &RegionResolutionError<'tcx>) -> bool {
        let (origin, sub, sup) = match *error {
            ConcreteFailure(ref origin, sub, sup) if sub.is_late_bound() =>
                (origin, sub, sup),
            ConcreteFailure(ref origin, sub, sup) if sup.is_late_bound() =>
                (origin, sub, sup),
            SubSupConflict(_, ref sub_origin, sub, _, sup) if sub.is_late_bound() =>
                (sub_origin, sub, sup),
            SubSupConflict(_, _, sub, ref sup_origin, sup) if sup.is_late_bound() =>
                (sup_origin, sub, sup),
            _ =>
                return false, // inapplicable
        };

        match *origin {
            infer::Subtype(ref trace) => {
                // FIXME This is bogus: we can't really tell from this
                // information whether it is "overly" polymorphic or what. We
                // should change how this error is reported altogether. But it
                // will do for now.
                let terr = match (sub, sup) {
                    (&ty::ReLateBound(_, br_sub), r) =>
                        TypeError::RegionsInsufficientlyPolymorphic(br_sub, r),
                    (r, &ty::ReLateBound(_, br_sup)) =>
                        TypeError::RegionsInsufficientlyPolymorphic(br_sup, r),
                    _ => span_bug!(origin.span(), "at least one side must be skolemized")
                };
                self.report_and_explain_type_error(trace.clone(), &terr).emit();
                true
            }
            _ => false,
        }
    }
}
