// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


//type DefIdPredicatesMap = <DefId, Vec<OutlivePredicate>>
//pub struct OutlivePredicate {}
//
//pub struct OutlivesCrateVisitor<'tcx> {
//    tcx: TyCtxt<'tcx, 'tcx, 'tcx>,
//    predicates: FxHashMap<_>,
//    empty_predicate: Rc<CratePredicatesMap<'tcx>>,
//}
//
//impl OutlivesCrateVisitor {
//
//    fn add_outlives_for_item(&mut self, id: ast::NodeId, outlive_map: DefIdPredicatesMap) {
//        //we will add things to outlives_map
//
//        let predicates = self.tcx.explicit_predicates_of(def_id);
//        aet filtered: Vec<_> = predicates
//
//            .predicates.iter()
//            .filter(|pred|
//                match *pred {
//                    &ty::Predicate::TypeOutlives(..) | &ty::Predicate::RegionOutlives(..) => true,
//                    _ => false,
//                }
//            )
//            .collect::<Vec<_>>();
//
//        //now infer outlive prediacates from the filtered predicates
//        for p in filtered {
//            the_great_inferring(p)
//        }
//    }
//
//    fn infer_parent_item(&mut self, id: ast::NodeId, outlive_map: DefIdPredicatesMap) {
//        //hopefully we can structure in a way so that child and parent dont need to be separate
//        //functions
//    }
//
//    fn the_great_inferring() {
//        //the solution to all our troubles
//    }
//
//}
//
//impl<'a, 'tcx, 'v> ItemLikeVisitor<'v> for TermsContext<'a, 'tcx> {
//    fn visit_item(&mut self, item: &hir::Item) {
//        //here we want to do the inference for each crate
//        match item.node {
//            hir::ItemStruct(..) => {
//
//                let child_predicates: DefIdPredicatesMap = Map::new()
//                //infer the fields first so that we can then use those rules for the parent
//                for field in struct_def {
//                    match field {
//                        hir::Struct(ref field_def, _) =>
//                        self.add_outlives_for_item(field.id, child_predicates)
//                    }
//                }
//
//                //now infer the main parent struct
//                self.infer_parent_item(item.id, child_predicates);
//            }
//
//            hir::ItemEnum(..) => {
//                //probably need to walk the fields here also.. (later)
//                self.add_inferreds_for_item(item.id);
//            }
//
//        }
//    }
//}
