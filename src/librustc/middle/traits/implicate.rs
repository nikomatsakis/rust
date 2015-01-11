// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

pub struct Implicator<'cx, 'tcx:'cx> {
    tcx: &'cx ty::ctxt<'tcx>,
    stack: Vec<ty::Predicate<'tcx>>,
    visited: HashSet<ty::Predicate<'tcx>>,
}

pub fn implicate_predicates<'cx, 'tcx>(
    tcx: &'cx ty::ctxt<'tcx>,
    mut predicates: Vec<ty::Predicate<'tcx>>)
    -> Implicator<'cx, 'tcx>
{
    let visited: HashSet<ty::Predicate<'tcx>> =
        predicates.iter()
                  .map(|b| (*b).clone())
                  .collect();

    predicates.reverse();

    Implicator { tcx: tcx, stack: predicates, visited: visited }
}

impl<'cx, 'tcx> Implicator<'cx, 'tcx> {
    pub fn filter_to_traits(self) -> Supertraits<'cx, 'tcx> {
        Supertraits { elaborator: self }
    }

    fn push(&mut self, predicate: &ty::Predicate<'tcx>) {
        match *predicate {
            ty::Predicate::Trait(ref data) => {
                let mut predicates =
                    ty::predicates_for_trait_ref(self.tcx,
                                                 &data.to_poly_trait_ref());

                // Only keep those bounds that we haven't already
                // seen.  This is necessary to prevent infinite
                // recursion in some cases.  One common case is when
                // people define `trait Sized: Sized { }` rather than `trait
                // Sized { }`.
                predicates.retain(|r| self.visited.insert(r.clone()));

                self.stack.extend(predicates.into_iter().rev());
            }
            ty::Predicate::Equate(..) => {
                // Currently, we do not "elaborate" predicates like
                // `X == Y`, though conceivably we might. For example,
                // `&X == &Y` implies that `X == Y`.
            }
            ty::Predicate::Projection(..) => {
                // Nothing to elaborate in a projection predicate.
            }
            ty::Predicate::RegionOutlives(..) => { }
            ty::Predicate::TypeOutlives(..) => {
                // A predicate like `T : 'a` implies two things:
                //
                // 1. `T` is well-formed
                // 2.
                // Currently, we do not "elaborate" predicates like
                // `'a : 'b` or `T : 'a`.  We could conceivably do
                // more here.  For example,
                //
                //     &'a int : 'b
                //
                // implies that
                //
                //     'a : 'b
                //
                // and we could get even more if we took WF
                // constraints into account. For example,
                //
                //     &'a &'b int : 'c
                //
                // implies that
                //
                //     'b : 'a
                //     'a : 'c
            }
        }
    }
}

impl<'cx, 'tcx> Iterator for Implicator<'cx, 'tcx> {
    type Item = ty::Predicate<'tcx>;

    fn next(&mut self) -> Option<ty::Predicate<'tcx>> {
        self.stack.pop().map(|next_predicate| {
            self.push(&next_predicate);
            next_predicate
        })
    }
}
