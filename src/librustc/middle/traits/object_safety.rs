// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! "Object safety" refers to the ability for a trait to be converted
//! to an object. In general, traits may only be converted to an
//! object if all of their methods meet certain criteria. In particular,
//! they must:
//!
//!   - have a suitable receiver from which we can extract a vtable;
//!   - not reference the erased type `Self` except for in this receiver;
//!   - not have generic type parameters

use super::supertraits;

use middle::ty;
use std::rc::Rc;
use syntax::ast;

/// Reasons a method might not be object-safe.
#[deriving(Copy,Clone)]
pub enum ObjectSafetyViolationCode {
    /// fn(self),
    ByValueSelf,

    // fn foo()
    StaticMethod,

    // fn foo(&self, x: Self)
    // fn foo(&self) -> Self
    ReferencesSelf,

    // fn foo<A>(),
    Generic,
}

pub struct ObjectSafetyViolation<'tcx> {
    pub method: Rc<ty::Method<'tcx>>,
    pub code: ObjectSafetyViolationCode
}

pub fn is_object_safe<'tcx>(tcx: &ty::ctxt<'tcx>,
                            trait_ref: Rc<ty::PolyTraitRef<'tcx>>)
                            -> bool
{
    // Because we query yes/no results frequently, we keep a cache:
    match tcx.object_safety_cache.borrow().get(&trait_ref.def_id()) {
        Some(&r) => { return r; }
        None => { }
    }

    object_safety_violations(tcx, trait_ref).is_empty()
}

pub fn object_safety_violations<'tcx>(tcx: &ty::ctxt<'tcx>,
                                      sub_trait_ref: Rc<ty::PolyTraitRef<'tcx>>)
                                      -> Vec<ObjectSafetyViolation<'tcx>>
{
    supertraits(tcx, sub_trait_ref)
        .flat_map(|tr| object_safety_violations_for_trait(tcx, tr.def_id()).into_iter())
        .collect()
}

fn object_safety_violations_for_trait<'tcx>(tcx: &ty::ctxt<'tcx>,
                                            trait_def_id: ast::DefId)
                                            -> Vec<ObjectSafetyViolation<'tcx>>
{
    let violations: Vec<_> =
        ty::trait_items(tcx, trait_def_id).iter()
        .flat_map(|item| {
            match *item {
                ty::MethodTraitItem(ref m) => {
                    object_safety_violations_for_method(&**m)
                        .map(|code| {
                            ObjectSafetyViolation {
                                method: m.clone(),
                                code: code,
                            }
                        })
                        .into_iter()
                }
                ty::TypeTraitItem(_) => {
                    None.into_iter()
                }
            }
        })
        .collect();

    // Record just a yes/no result in the cache; this is what is
    // queried most frequently. Note that this may overwrite a
    // previous result, but always with the same thing.
    tcx.object_safety_cache
        .borrow_mut()
        .insert(trait_def_id, violations.is_empty());

    violations
}

fn object_safety_violations_for_method(method: &ty::Method)
                                       -> Option<ObjectSafetyViolationCode>
{
    match method.explicit_self {
        ty::ByValueExplicitSelfCategory => { // reason (a) above
            return Some(ObjectSafetyViolationCode::ByValueSelf);
        }

        ty::StaticExplicitSelfCategory => {
            // Static methods are always object-safe since they
            // can't be called through a trait object
            //
            // TODO(#19949) This is wrong
            return None
        }

        ty::ByReferenceExplicitSelfCategory(..) |
        ty::ByBoxExplicitSelfCategory => {}
    }

    let check_for_self_ty = |ty| {
        if ty::type_has_self(ty) { Some(ObjectSafetyViolationCode::ReferencesSelf) } else { None }
    };

    let ref sig = method.fty.sig;
    for &input_ty in sig.0.inputs[1..].iter() {
        if let Some(code) = check_for_self_ty(input_ty) {
            return Some(code);
        }
    }

    if let ty::FnConverging(result_type) = sig.0.output {
        if let Some(code) = check_for_self_ty(result_type) {
            return Some(code);
        }
    }

    None
}

