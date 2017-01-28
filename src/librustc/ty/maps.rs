// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use dep_graph::{DepNode, DepTrackingMapConfig};
use hir::def_id::DefId;
use mir;
use ty::{self, Ty};

use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;
use syntax::attr;

macro_rules! dep_map_ty {
    ($ty_name:ident $([$($lt:tt),*])* : $node_name:ident ($key:ty) -> $value:ty) => {
        pub struct $ty_name $(<$($lt),*>)* {
            data: PhantomData<( $($(& $lt ()),*)* )>
        }

        impl<'tcx> DepTrackingMapConfig for $ty_name $(<$($lt),*>)* {
            type Key = $key;
            type Value = $value;
            fn to_dep_node(key: &$key) -> DepNode<DefId> { DepNode::$node_name(*key) }
        }
    }
}

dep_map_ty! { AssociatedItems['tcx]: AssociatedItems(DefId) -> ty::AssociatedItem }
dep_map_ty! { Types['tcx]: ItemSignature(DefId) -> Ty<'tcx> }
dep_map_ty! { Generics['tcx]: ItemSignature(DefId) -> &'tcx ty::Generics<'tcx> }
dep_map_ty! { Predicates['tcx]: ItemSignature(DefId) -> ty::GenericPredicates<'tcx> }
dep_map_ty! { SuperPredicates['tcx]: ItemSignature(DefId) -> ty::GenericPredicates<'tcx> }
dep_map_ty! { AssociatedItemDefIds['tcx]: AssociatedItemDefIds(DefId) -> Rc<Vec<DefId>> }
dep_map_ty! { ImplTraitRefs['tcx]: ItemSignature(DefId) -> Option<ty::TraitRef<'tcx>> }
dep_map_ty! { TraitDefs['tcx]: ItemSignature(DefId) -> &'tcx ty::TraitDef }
dep_map_ty! { AdtDefs['tcx]: ItemSignature(DefId) -> &'tcx ty::AdtDef }
dep_map_ty! { AdtSizedConstraint['tcx]: SizedConstraint(DefId) -> Ty<'tcx> }
dep_map_ty! { ItemVariances['tcx]: ItemSignature(DefId) -> Rc<Vec<ty::Variance>> }
dep_map_ty! { InherentImpls['tcx]: InherentImpls(DefId) -> Vec<DefId> }
dep_map_ty! { ReprHints['tcx]: ReprHints(DefId) -> Rc<Vec<attr::ReprAttr>> }
dep_map_ty! { Mir['tcx]: Mir(DefId) -> &'tcx RefCell<mir::Mir<'tcx>> }
dep_map_ty! { ClosureKinds['tcx]: ItemSignature(DefId) -> ty::ClosureKind }
dep_map_ty! { ClosureTypes['tcx]: ItemSignature(DefId) -> ty::ClosureTy<'tcx> }
dep_map_ty! { TypeckTables['tcx]: TypeckTables(DefId) -> &'tcx ty::TypeckTables<'tcx> }
dep_map_ty! { UsedTraitImport: UsedTraitImport(DefId) -> () }
