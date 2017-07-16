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
use hir;
use infer::InferCtxt;
use ty::{self, Region};
use infer::region_inference::RegionResolutionError::*;
use infer::region_inference::RegionResolutionError;
use hir::map as hir_map;
use middle::resolve_lifetime as rl;
use hir::intravisit::{self, Visitor, NestedVisitorMap};

// The visitor captures the corresponding `hir::Ty` of the
// anonymous region.
struct FindNestedTypeVisitor<'a, 'gcx: 'a + 'tcx, 'tcx: 'a> {
    infcx: &'a InferCtxt<'a, 'gcx, 'tcx>,
    hir_map: &'a hir::map::Map<'gcx>,
    bound_region: ty::BoundRegion,
    found_type: Option<&'gcx hir::Ty>,
}

impl<'a, 'gcx, 'tcx> Visitor<'gcx> for FindNestedTypeVisitor<'a, 'gcx, 'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'gcx> {
        NestedVisitorMap::OnlyBodies(&self.hir_map)
    }

    fn visit_ty(&mut self, arg: &'gcx hir::Ty) {
        // Find the index of the anonymous region that was part of the
        // error. We will then search the function parameters for a bound
        // region at the right depth with the same index.
        let br_index = match self.bound_region {
            ty::BrAnon(index) => index,
            _ => return,
        };

        match arg.node {
            hir::TyRptr(ref lifetime, _) => {
                match self.infcx.tcx.named_region_map.defs.get(&lifetime.id) {
                    // the lifetime of the TyRptr!
                    Some(&rl::Region::LateBoundAnon(debuijn_index, anon_index)) => {
                        if debuijn_index.depth == 1 && anon_index == br_index {
                            self.found_type = Some(arg);
                            return; // we can stop visiting now
                        }
                    }
                    Some(&rl::Region::Static) |
                    Some(&rl::Region::EarlyBound(_, _)) |
                    Some(&rl::Region::LateBound(_, _)) |
                    Some(&rl::Region::Free(_, _)) |
                    None => {
                        debug!("no arg found");
                    }
                }
            }
            _ => {}
        }
        // walk the embedded contents: e.g., if we are visiting `Vec<&Foo>`,
        // go on to visit `&Foo`
        intravisit::walk_ty(self, arg);
    }
}

impl<'a, 'gcx, 'tcx> InferCtxt<'a, 'gcx, 'tcx> {
    // This function calls the `visit_ty` method for the parameters
    // corresponding to the anonymous regions. The `nested_visitor.found_type`
    // contains the anonymous type.
    pub fn find_anon_type(&self, region: Region<'tcx>, br: &ty::BoundRegion) -> Option<&hir::Ty> {
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
                                    fndecl
                                        .inputs
                                        .iter()
                                        .filter_map(|arg| {
                                            let mut nested_visitor = FindNestedTypeVisitor {
                                                infcx: &self,
                                                hir_map: &self.tcx.hir,
                                                bound_region: *br,
                                                found_type: None,
                                            };
                                            nested_visitor.visit_ty(&**arg);
                                            if nested_visitor.found_type.is_some() {
                                                return nested_visitor.found_type;
                                            } else {
                                                return None;
                                            }
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

            if self.find_anon_type(sup, &br1).is_some() &&
               self.find_anon_type(sub, &br2).is_some() {
                (self.find_anon_type(sup, &br1).unwrap(), self.find_anon_type(sub, &br2).unwrap())
            } else {
                return false;
            }
        } else {
            return false; // inapplicable
        };

        if let (Some(sup_arg),Some(sub_arg)) = 
(self.find_arg_with_anonymous_region(sup,sup),
self.find_arg_with_anonymous_region(sub,sub)){
        let (anon_arg1, anon_arg2) = match (sup_arg, sub_arg) {
             ((arg1,_,_,_), (arg2,_,_,_)) => (arg1, arg2),
              _ => return false,
        };

        let span_label_var1 = if let Some(simple_name) = anon_arg1.pat.simple_name() {
            format!("from `{}`", simple_name)
        } else {
            format!("data flows here")
        };

        let span_label_var2 = if let Some(simple_name) = anon_arg2.pat.simple_name() {
            format!("into `{}`", simple_name)
        } else {
            format!("")
        };

        struct_span_err!(self.tcx.sess, span, E0622, "lifetime mismatch")
            .span_label(ty1.span,
                        format!("these references must have the same lifetime"))
            .span_label(ty2.span, format!(""))
            .span_label(span, format!("data {} flows {} here",span_label_var1,span_label_var2))
            .emit();
  }
      
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
