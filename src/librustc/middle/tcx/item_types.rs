// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

pub struct ItemTypes {
    tcache: RefCell<DefIdMap<TypeScheme<'tcx>>>,
}

impl ItemTypes {
    pub fn new() -> ItemTypes {
        ItemTypes { tcache: RefCell::new(DefIdMap()) }
    }

    pub fn get_or_create(&self) -> TypeScheme<'tcx> {
        lookup_locally_or_in_crate_store(
            "tcache", did, &self.tcache,
            || csearch::get_type(self, did))
    }

    pub fn get(&self, did: ast::DefId) -> Option<TypeScheme<'tcx>> {
        self.tcache.borrow().get(did)
    }

    pub fn set(&self, did: ast::DefId, ty: TypeScheme<'tcx>) {
        self.tcache.borrow_mut().insert(did, ty);
    }
}
