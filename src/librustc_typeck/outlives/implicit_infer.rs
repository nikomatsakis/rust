// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(unused)]
#[allow(dead_code)]

use rustc::ty::{self, CratePredicatesMap, TyCtxt};
use rustc::ty::{AdtKind, ToPolyTraitRef, Ty};
use rustc::ty::maps::Providers;
use std::rc::Rc;
use util::nodemap::FxHashMap;
use hir::map as hir_map;
use rustc::hir;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use rustc::hir::def_id::{self, CrateNum, DefId, LOCAL_CRATE};
use std::collections::HashSet;
use rustc::ty::{ToPredicate, ReprOptions};
use syntax_pos::{Span, DUMMY_SP};
use rustc::hir::def::{Def, CtorKind};
use syntax::{abi, ast};

pub fn infer<'tcx>(
    tcx: TyCtxt<'_, 'tcx, 'tcx>,
    crate_num: CrateNum,
    inferred_outlives_map: &FxHashMap<DefId, Rc<Vec<ty::Predicate<'tcx>>>>
) {
    assert_eq!(crate_num, LOCAL_CRATE);
////    let mut predicates = FxHashMap();
//
//    // Now comes the inference part. We iterate over each type and figure out,
//    // for each of its fields, what outlives predicates are needed to make that field's
//    // type well-formed. Those get added to the `inferred_outlives_predicates` set
//    // for that type.
//
//    /*
//        // inferred_outlives_predicate = ['b: 'a] // after round 2
//        struct Foo<'a, 'b> {
//            bar: Bar<'a, 'b> // []
//            // round 2: ['b: 'a] in `required_predicates`
//        }
//
//        // inferred_outlives_predicate = ['b: 'a] // updated after round 1
//        struct Bar<'a, 'b> {
//            field &'a &'b u32 // ['b: 'a] // added to `required_predicates`
//        } // required_predicates = ['b: 'a]
//    */
//
//    let mut changed = true;
//    let mut eval_crate_num = crate_num;
//    {
//        while changed {
//            let mut local_changed = false;
//            {
//                let mut visitor = ImplicitVisitor {
//                    tcx: tcx,
//                    predicates: &mut predicates,
//                    crate_num: &mut eval_crate_num,
//                    changed: &mut local_changed,
//                };
//
//                // iterate over all crates
//                tcx.hir.krate().visit_all_item_likes(&mut visitor);
//            }
//            changed = local_changed;
//        }
//    }

}
//
//pub struct ImplicitVisitor<'a, 'p: 'a, 'cx, 'tcx: 'cx> {
//    tcx: TyCtxt<'cx, 'tcx, 'tcx>,
//    predicates: &'a mut FxHashMap<DefId, Rc<Vec<ty::Predicate<'p>>>>,
//    crate_num: &'a mut CrateNum,
//    changed: &'a mut bool,
//}
//
//impl<'a, 'p, 'cx, 'v, 'tcx> ItemLikeVisitor<'v> for ImplicitVisitor<'a, 'p, 'cx, 'tcx> {
//    fn visit_item(&mut self, item: &hir::Item) {
//
//        use rustc::hir::map::*;
//        use rustc::hir::*;
//
//        *self.changed = false;
//
//        let def_id = DefId {
//            krate: *self.crate_num,
//            index: item.hir_id.owner,
//        };
//
//        let mut required_predicates: HashSet<i32> = HashSet::new();
//        // let adt_def = local_adt_def(self.tcx, def_id);
//
//        let node_id = self.tcx.hir.as_local_node_id(def_id).unwrap();
//        let item = match self.tcx.hir.get(node_id) {
//            NodeItem(item) => item,
//            _ => bug!()
//        };
//
//        match item.node {
//            ItemUnion(ref def, _) => { },
//            ItemEnum(ref def, _) => { },
//            ItemStruct(ref def, _) => {
//
//                // ----------- example
//                for field in def.fields().iter() {
//                    //            for field in variant {
//                    //                // from ty/outlives.rs
//                    //                // outlives_components(Vec<T>) = [T]
//                    //                //    input   Foo<'b, 'c>  ==> ['b, 'c]
//                    //                //    output   Vec<T>: 'a
//                    let outlives = self.tcx.outlives_components(field.ty.unwrap());
//              required_predicates.extend(required_predicates_for_type_to_be_wf(field_ty));
//                    //            }
//                    //        inferred_outlives_predicates.extend(required_predicates);
//                    //        if new predicates were added { changed = true; }
//
//                }
//
//            }
//            _ => {} //bug!()
//        };
//
//
//    }
//
//    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {}
//
//    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {}
//}




//fn local_adt_def<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
//                     def_id: DefId)
//                     -> &'tcx ty::AdtDef {
//    use rustc::hir::map::*;
//    use rustc::hir::*;

//    let node_id = tcx.hir.as_local_node_id(def_id).unwrap();
//    let item = match tcx.hir.get(node_id) {
//        NodeItem(item) => item,
//        _ => bug!()
//    };

//    // let repr = ReprOptions::new(tcx, def_id);
//    let (kind, variants) = match item.node {
//        ItemEnum(ref def, _) => {
//            let mut distance_from_explicit = 0;
//            (AdtKind::Enum, def.variants.iter().map(|v| {
//                let did = tcx.hir.local_def_id(v.node.data.id());
//                let discr = if let Some(e) = v.node.disr_expr {
//                    distance_from_explicit = 0;
//                    ty::VariantDiscr::Explicit(tcx.hir.local_def_id(e.node_id))
//                } else {
//                    ty::VariantDiscr::Relative(distance_from_explicit)
//                };
//                distance_from_explicit += 1;
//
//                convert_struct_variant(tcx, did, v.node.name, discr, &v.node.data)
//            }).collect())
//        }
//        ItemStruct(ref def, _) => {
//   // Use separate constructor id for unit/tuple structs and reuse did for braced structs.
//            let ctor_id = if !def.is_struct() {
//                Some(tcx.hir.local_def_id(def.id()))
//            } else {
//                None
//            };
//            (AdtKind::Struct, vec![
//                convert_struct_variant(tcx, ctor_id.unwrap_or(def_id), item.name,
//                                       ty::VariantDiscr::Relative(0), def)
//            ])
//        }
//        ItemUnion(ref def, _) => {
//            (AdtKind::Union, vec![
//                convert_struct_variant(tcx, def_id, item.name,
//                                       ty::VariantDiscr::Relative(0), def)
//            ])
//        }
//        _ => bug!()
//    };

//    // let def = ty::AdtDef::new(self.tcx, did, kind, variants, repr);
//    // self.tcx.global_arenas.adt_def.alloc(def)
//}

//// pub fn alloc_adt_def(self,
////                      did: DefId,
////                      kind: AdtKind,
////                      variants: Vec<ty::VariantDef>,
////                      repr: ReprOptions)
////                      -> &'gcx ty::AdtDef {
////     let def = ty::AdtDef::new(self, did, kind, variants, repr);
////     self.global_arenas.adt_def.alloc(def)
//// }

//fn convert_struct_variant<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
//                                    did: DefId,
//                                    name: ast::Name,
//                                    discr: ty::VariantDiscr,
//                                    def: &hir::VariantData)
//                                    -> ty::VariantDef {
//    // let mut seen_fields: FxHashMap<ast::Name, Span> = FxHashMap();
//    let node_id = tcx.hir.as_local_node_id(did).unwrap();
//    let fields = def.fields().iter().map(|f| {
//        //let fid = tcx.hir.local_def_id(f.id);
//        ////let dup_span = seen_fields.get(&f.name).cloned();
//        ////if let Some(prev_span) = dup_span {
//        ////    struct_span_err!(tcx.sess, f.span, E0124,
//        ////                     "field `{}` is already declared",
//        ////                     f.name)
//        ////        .span_label(f.span, "field already declared")
//        ////        .span_label(prev_span, format!("`{}` first declared here", f.name))
//        ////        .emit();
//        ////} else {
//        ////    seen_fields.insert(f.name, f.span);
//        ////}

//        ty::FieldDef {
//            // did: fid,
//            did: tcx.hir.local_def_id(f.id),
//            name: f.name,
//            vis: ty::Visibility::from_hir(&f.vis, node_id, tcx)
//        }
//    }).collect();
//    ty::VariantDef {
//        did,
//        name,
//        discr,
//        fields,
//        ctor_kind: CtorKind::from_hir(def),
//    }
//}
