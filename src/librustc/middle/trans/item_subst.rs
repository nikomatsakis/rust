// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::subst;
use middle::subst::Subst;
use middle::traits;
use middle::ty;
use middle::ty_fold;
use middle::ty_fold::{TypeFolder, TypeFoldable};

use super::common::{FunctionContext, Block};

pub trait ItemSubst {
    fn item_subst(&self,
                  tcx: &ty::ctxt,
                  item_substs: &subst::ItemSubsts)
                  -> Self;

    fn item_subst_fcx(&self,
                      fcx: &FunctionContext)
                      -> Self
    {
        self.item_subst(&fcx.ccx.tcx, fcx.item_substs)
    }

    fn item_subst_bcx(&self,
                      bcx: &Block)
                      -> Self
    {
        self.item_subst_fcx(bcx.fcx)
    }
}

impl<T:TypeFoldable> ItemSubst for T {
    fn item_subst(&self,
                  tcx: &ty::ctxt,
                  item_substs: &subst::ItemSubsts)
                  -> T
    {
        let mut f = ItemSubstFolder {
            tcx: tcx,
            item_substs: item_substs,
        };
        self.fold_with(&mut f)
    }
}

struct ItemSubstFolder<'a> {
    tcx: &'a ty::ctxt,
    item_substs: &'a subst::ItemSubsts,
}

impl<'a> TypeFolder for ItemSubstFolder<'a> {
    fn tcx<'a>(&'a self) -> &'a ty::ctxt { self.tcx }

    fn fold_region(&mut self, r: ty::Region) -> ty::Region {
        r.subst(self.tcx(), &self.item_substs.substs)
    }

    fn fold_ty(&mut self, t: ty::t) -> ty::t {
        t.subst(self.tcx(), &self.item_substs.substs)
    }

    fn fold_vtable_origin(&mut self,
                          origin: &traits::VtableOrigin)
                          -> traits::VtableOrigin
    {
        match *origin {
            traits::Vtable(..) | traits::Builtin => {
                ty_fold::super_fold_vtable_origin(self, origin)
            }
            traits::VtableParam(ref param, ref r) => {
                assert!(r.is_none()); // errors should have been caught in typeck
                self.item_substs.resolve_vtable_path(self.tcx, &param.path)
            }
        }
    }
}

pub trait ResolveVtablePath {
    fn resolve_vtable_path(&self,
                           tcx: &ty::ctxt,
                           path: &traits::VtablePath)
                           -> traits::VtableOrigin;
}

impl ResolveVtablePath for subst::ItemSubsts {
    fn resolve_vtable_path(&self,
                           tcx: &ty::ctxt,
                           path: &traits::VtablePath)
                           -> traits::VtableOrigin
    {
        let root_origin = self.origins.get(path.space, path.obligation);
        let root_origin = root_origin.item_subst(tcx, self);
        if path.supertraits.len() == 0 {
            root_origin
        } else {
            let root_vtable = assert_vtable(tcx, &root_origin);
            trace_supertraits(tcx, root_vtable, &path.supertraits)
        }
    }
}

fn assert_vtable<'a>(tcx: &ty::ctxt,
                     vtable_origin: &'a traits::VtableOrigin)
                     -> &'a traits::Vtable
{
    /*!
     * Since we are monomorphizing, it often happens that we know
     * `VtableOrigin` must in fact be a vtable.
     */

    match *vtable_origin {
        traits::Vtable(ref vtable, None) => {
            vtable
        }
        traits::Vtable(_, Some(_)) |
        traits::Builtin |
        traits::VtableParam(..) => {
            tcx.sess.bug(
                "trace_supertraits() encountered non-vtable");
        }
    }
}

fn trace_supertraits<'a>(tcx: &ty::ctxt,
                         mut vtable: &'a traits::Vtable,
                         supertraits: &Vec<uint>)
                         -> traits::VtableOrigin
{
    /*!
     * We need to trace through the supertraits to extract out
     * the vtable we want. That is, there was some code like:
     *
     *    trait Foo { fn foo() }
     *    trait Bar : Foo { ... }
     *    trait Baz : Bar { ... }
     *
     *    fn f<T:Baz>(...) { t.foo() }
     *
     * This will be resolved to a path like "Obligation T:Baz,
     * supertrait [0, 0]". We start out with the `vtable` for
     * `T:Baz`. We want to trace through the supertraits to
     * to find the (implied) `T:Foo` obligation.
     *
     * To see how that tracing process works, imagine that `T=uint`
     * and we have the following impls:
     *
     *     impl Baz for uint { ... }   // ID 0
     *     impl Bar for uint { ... }   // ID 1
     *     impl Foo for uint { ... }   // ID 2
     *
     * `vtable` will therefore be the vtable with ID 0. It might look
     * something like:
     *
     *     Vtable
     *       impl_def_id: 0,
     *       substs: ...
     *       origins:
     *         [] // type namespace, empty in this case
     *         [ Vtable
     *             impl_def_id: 1,
     *             substs: ...
     *             origins:
     *               [] // type namespace, again empty
     *               [ Vtable
     *                   impl_def_id: 2,
     *                   substs: ...
     *                   origins: ... ] ]
     */

    for &i in supertraits.iter() {
        let superorigin = vtable.origins.get(subst::SelfSpace, i);
        vtable = assert_vtable(tcx, superorigin);
    }

    traits::Vtable((*vtable).clone(), None)
}
