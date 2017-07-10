// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Error Reporting for Anonymous Region Lifetime Errors.
use hir;
use infer::InferCtxt;
use ty::{self, Region};
use infer::region_inference::RegionResolutionError::*;
use infer::region_inference::RegionResolutionError;
use hir::map as hir_map;
use hir::def_id::DefId;
use middle::resolve_lifetime as rl;
use hir::intravisit::{self, Visitor, NestedVisitorMap};

struct FindNestedTypeVisitor<'a, 'gcx: 'a + 'tcx, 'tcx: 'a> {
    infcx: &'a InferCtxt<'a, 'gcx, 'tcx>,
    hir_map: &'a hir::map::Map<'gcx>,
}

impl<'a, 'gcx, 'tcx> Visitor<'gcx> for FindNestedTypeVisitor<'a, 'gcx, 'tcx> {
   fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'gcx> {
        NestedVisitorMap::OnlyBodies(&self.hir_map)
      }

    fn visit_ty(&mut self, ty: &'gcx hir::Ty) {
        intravisit::walk_ty(self, ty);
    }

}

impl<'a, 'gcx, 'tcx> InferCtxt<'a, 'gcx, 'tcx> {
    // This method walks the Type of the function body arguments using
    // `fold_regions()` function and returns the
    // &hir::Arg of the function argument corresponding to the anonymous
    // region and the Ty corresponding to the named region.
    // Currently only the case where the function declaration consists of
    // one named region and one anonymous region is handled.
    // Consider the example `fn foo<'a>(x: &'a i32, y: &i32) -> &'a i32`
    // Here, we would return the hir::Arg for y, we return the type &'a
    // i32, which is the type of y but with the anonymous region replaced
    // with 'a, the corresponding bound region and is_first which is true if
    // the hir::Arg is the first argument in the function declaration.
    fn find_arg_with_anonymous_region
        (&self,
         anon_region: Region<'tcx>,
         named_region: Region<'tcx>)
         -> Option<(&hir::Arg, ty::Ty<'tcx>, ty::BoundRegion, bool)> {

        match *anon_region {
            ty::ReFree(ref free_region) => {

                let id = free_region.scope;
                let node_id = self.tcx.hir.as_local_node_id(id).unwrap();
                let body_id = self.tcx.hir.maybe_body_owned_by(node_id).unwrap();
                let body = self.tcx.hir.body(body_id);
                if let Some(tables) = self.in_progress_tables {
                    body.arguments
                        .iter()
                        .enumerate()
                        .filter_map(|(index, arg)| {
                            let ty = tables.borrow().node_id_to_type(arg.id);
                            let mut found_anon_region = false;
                            let new_arg_ty = self.tcx
                                .fold_regions(&ty, &mut false, |r, _| if *r == *anon_region {
                                    found_anon_region = true;
                                    named_region
                                } else {
                                    r
                                });
                            if found_anon_region {
                                let is_first = index == 0;
                                Some((arg, new_arg_ty, free_region.bound_region, is_first))
                            } else {
                                None
                            }
                        })
                        .next()
                } else {
                    None
                }
            }
            _ => None,

        }
    }

    // This method generates the error message for the case when
    // the function arguments consist of a named region and an anonymous
    // region and corresponds to `ConcreteFailure(..)`
    pub fn try_report_named_anon_conflict(&self, error: &RegionResolutionError<'tcx>) -> bool {

        let (span, sub, sup) = match *error {
            ConcreteFailure(ref origin, sub, sup) => (origin.span(), sub, sup),
            _ => return false, // inapplicable
        };

        // Determine whether the sub and sup consist of one named region ('a)
        // and one anonymous (elided) region. If so, find the parameter arg
        // where the anonymous region appears (there must always be one; we
        // only introduced anonymous regions in parameters) as well as a
        // version new_ty of its type where the anonymous region is replaced
        // with the named one.
        let (named, (arg, new_ty, br, is_first), scope_def_id) =
            if sub.is_named_region() && self.is_suitable_anonymous_region(sup).is_some() {
                (sub,
                 self.find_arg_with_anonymous_region(sup, sub).unwrap(),
                 self.is_suitable_anonymous_region(sup).unwrap())
            } else if sup.is_named_region() && self.is_suitable_anonymous_region(sub).is_some() {
                (sup,
                 self.find_arg_with_anonymous_region(sub, sup).unwrap(),
                 self.is_suitable_anonymous_region(sub).unwrap())
            } else {
                return false; // inapplicable
            };

        // Here, we check for the case where the anonymous region
        // is in the return type.
        // FIXME(#42703) - Need to handle certain cases here.
        let ret_ty = self.tcx.type_of(scope_def_id);
        match ret_ty.sty {
            ty::TyFnDef(_, _) => {
                let sig = ret_ty.fn_sig(self.tcx);
                let late_bound_regions = self.tcx
                    .collect_referenced_late_bound_regions(&sig.output());
                if late_bound_regions.iter().any(|r| *r == br) {
                    return false;
                } else {
                }
            }
            _ => {}
        }

        // Here we check for the case where anonymous region
        // corresponds to self and if yes, we display E0312.
        // FIXME(#42700) - Need to format self properly to
        // enable E0621 for it.
        if is_first &&
           self.tcx
               .opt_associated_item(scope_def_id)
               .map(|i| i.method_has_self_argument)
               .unwrap_or(false) {
            return false;
        }

        let (error_var, span_label_var) = if let Some(simple_name) = arg.pat.simple_name() {
            (format!("the type of `{}`", simple_name), format!("the type of `{}`", simple_name))
        } else {
            (format!("parameter type"), format!("type"))
        };


        struct_span_err!(self.tcx.sess,
                         span,
                         E0621,
                         "explicit lifetime required in {}",
                         error_var)
                .span_label(arg.pat.span,
                            format!("consider changing {} to `{}`", span_label_var, new_ty))
                .span_label(span, format!("lifetime `{}` required", named))
                .emit();

        return true;

    }

    // This method returns whether the given Region is Anonymous
    // and returns the DefId corresponding to the region.
    pub fn is_suitable_anonymous_region(&self, region: Region<'tcx>) -> Option<DefId> {

        match *region {
            ty::ReFree(ref free_region) => {
                match free_region.bound_region {
                    ty::BrAnon(..) => {
                        let anonymous_region_binding_scope = free_region.scope;
                        let node_id = self.tcx
                            .hir
                            .as_local_node_id(anonymous_region_binding_scope)
                            .unwrap();
                        match self.tcx.hir.find(node_id) {
                            Some(hir_map::NodeItem(..)) |
                            Some(hir_map::NodeTraitItem(..)) => {
                                // proceed ahead //
                            }
                            Some(hir_map::NodeImplItem(..)) => {
                                let container_id = self.tcx
                                    .associated_item(anonymous_region_binding_scope)
                                    .container
                                    .id();
                                if self.tcx.impl_trait_ref(container_id).is_some() {
                                    // For now, we do not try to target impls of traits. This is
                                    // because this message is going to suggest that the user
                                    // change the fn signature, but they may not be free to do so,
                                    // since the signature must match the trait.
                                    //
                                    // FIXME(#42706) -- in some cases, we could do better here.
                                    return None;
                                }
                            }
                            _ => return None, // inapplicable
                            // we target only top-level functions
                        }
                        return Some(anonymous_region_binding_scope);
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub fn visit_fn_decl(&self, region: Region<'tcx>, br: &ty::BoundRegion) -> Option<&hir::Ty> {
        // Find the index of the anonymous region that was part of the
        // error. We will then search the function parameters for a bound
        // region at the right depth with the same index.
        let br_index = match *br {
            ty::BrAnon(index) => index,
            _ => return None,
        };

        if self.is_suitable_anonymous_region(region).is_some() {
            let def_id = self.is_suitable_anonymous_region(region).unwrap();
            let node_id = self.tcx.hir.as_local_node_id(def_id).unwrap();
            let ret_ty = self.tcx.type_of(def_id);
            match ret_ty.sty {
                ty::TyFnDef(_, _) => {
                    match self.tcx.hir.get(node_id) {
                        hir_map::NodeItem(it) => {
                            match it.node {
                                hir::ItemFn(ref fndecl, _, _, _, _, _) => {
                                   let mut nested_visitor = FindNestedTypeVisitor {
            infcx: &self,
            hir_map: &self.tcx.hir,

        };
                                    fndecl.inputs.iter().filter_map(|arg| match arg.node {

                  hir::TyRptr(ref lifetime, _) => {
                    
                    match self.tcx.named_region_map.defs.get(&lifetime.id) {
                      Some(&rl::Region::LateBoundAnon(debuijn_index, anon_index)) => {

if debuijn_index.depth ==1 && anon_index == br_index {
            Some(&**arg)
} else{None}
                      
                              }                     
                      Some(&rl::Region::Static)|
                      Some(&rl::Region::EarlyBound(_, _))|
                      Some(&rl::Region::LateBound(_, _))|
                      Some(&rl::Region::Free(_, _))|
                      None => { None }
                    }
                  }
                  
                  _ => None,
                })
                .next()
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        } else {
            None
        }
    }
    pub fn try_report_anon_anon_conflict(&self, error: &RegionResolutionError<'tcx>) -> bool {

        let (span, sub, sup) = match *error {
            ConcreteFailure(ref origin, sub, sup) => (origin.span(), sub, sup),
            _ => return false, // inapplicable
        };

        // Determine whether the sub and sup consist of both anonymous (elided) regions.
        let (ty1, ty2) = if self.is_anonymous_region(sup).is_some() &&
                            self.is_anonymous_region(sub).is_some() {
            let br1 = self.is_anonymous_region(sup).unwrap();
            let br2 = self.is_anonymous_region(sub).unwrap();
            debug!("loop 1 {} {}",
                   self.is_anonymous_region(sup).is_some(),
                   self.is_anonymous_region(sub).is_some());
            if self.visit_fn_decl(sup, &br1).is_some() && self.visit_fn_decl(sub, &br2).is_some() {
                debug!("loop 1 {:?} and {:?}",
                       self.visit_fn_decl(sup, &br1).unwrap(),
                       self.visit_fn_decl(sub, &br2).unwrap());
                (self.visit_fn_decl(sup, &br1).unwrap(), self.visit_fn_decl(sub, &br2).unwrap())
            } else {

                debug!("false - 1");
                return false;
            }

        } else {
            debug!("false - 2");
            return false; // inapplicable
        };

        struct_span_err!(self.tcx.sess, span, E0621, "lifetime mismatch")
            .span_label(ty1.span,
                        format!("these references must have the same lifetime"))
            .span_label(ty2.span, format!(""))
            .emit();

        return true;

    }

    pub fn is_anonymous_region(&self, region: Region<'tcx>) -> Option<ty::BoundRegion> {

        match *region {
            ty::ReFree(ref free_region) => {
                match free_region.bound_region {
                    ty::BrAnon(..) => {
                        let anonymous_region_binding_scope = free_region.scope;
                        let node_id = self.tcx
                            .hir
                            .as_local_node_id(anonymous_region_binding_scope)
                            .unwrap();
                        match self.tcx.hir.find(node_id) {
                            Some(hir_map::NodeItem(..)) |
                            Some(hir_map::NodeTraitItem(..)) => {
                                // proceed ahead //
                            }
                            Some(hir_map::NodeImplItem(..)) => {
                                let container_id = self.tcx
                                    .associated_item(anonymous_region_binding_scope)
                                    .container
                                    .id();
                                if self.tcx.impl_trait_ref(container_id).is_some() {
                                    // For now, we do not try to target impls of traits. This is
                                    // because this message is going to suggest that the user
                                    // change the fn signature, but they may not be free to do so,
                                    // since the signature must match the trait.
                                    //
                                    // FIXME(#42706) -- in some cases, we could do better here.
                                    return None;
                                }
                            }
                            _ => return None, // inapplicable
                            // we target only top-level functions
                        }
                        return Some(free_region.bound_region);
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}
