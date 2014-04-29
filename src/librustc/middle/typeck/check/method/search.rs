// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
 * Search phase for method lookup. See `mod.rs` for documentation
 * on the overall structure.
 */

pub fn inherent_method_search(fcx: &FnCtxt,
                              call_expr: &ast::Expr,
                              self_ty: &ty::t,
                              method_name: ast::Name)
                              -> bool
{
    let inherent_test = InherentTest { fcx: fcx, call_expr: call_expr,
                                       method_name: method_name };
    match autoderef::search(fcx, call_expr.span, self_ty, &inherent_test) {
        NoMatch(_) | Error(_) => {
            false
        }

        FoundMatch(xform_ty, vtable) => {
        }
    }
}

struct InherentTest<'a> {
    fcx: &'a FnCtxt,
    call_expr: &'a ast::Expr,
    method_name: ast::Name,
}

impl<'a> autoderef::Test<Vtable> for InherentTest<'a> {
    fn test(&mut self, ty: ty::t) -> Vtable {
        match ty::get(ty).sty {
            ty_enum(def_id, _) | ty_struct(def_id, _) => {
                let impl_methods = self.tcx().impl_methods.borrow();
                for impl_infos in self.tcx().inherent_impls.borrow().find(&did).iter() {
                    
                    for impl_did in impl_infos.borrow().iter() {
                        self.push_candidates_from_impl(*impl_did, methods.as_slice(), false);
                    }
                }
            }

            ty_trait(ref ty_trait) => {
            }
        }
    }

    fn impl_has_method_with_name(&self, def_id: &ast::DefId, n: ast::Name) {
        let methods = impl_methods.get(impl_did);
        methods.any(|m| self.method_has_name(m, self.method_name))
    }

    fn method_has_name(&self, def_id: &ast::DefId, n: ast::Name) {
        ty::method(self.tcx(), did).ident.name == n
    }
}
