// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use hir::def_id::{DefId, LocalDefId, LOCAL_CRATE};
use ty;

use super::resolve_lifetimes;

pub fn provide(providers: &mut ty::maps::Providers) {
    *providers = ty::maps::Providers {
        resolve_lifetimes,

        named_region_map: |tcx, id| {
            let id = LocalDefId::from_def_id(DefId::local(id)); // (*)
            tcx.resolve_lifetimes(LOCAL_CRATE).defs.get(&id).cloned()
        },

        is_late_bound_map: |tcx, id| {
            let id = LocalDefId::from_def_id(DefId::local(id)); // (*)
            tcx.resolve_lifetimes(LOCAL_CRATE)
                .late_bound
                .get(&id)
                .cloned()
        },

        object_lifetime_defaults_map: |tcx, id| {
            let id = LocalDefId::from_def_id(DefId::local(id)); // (*)
            tcx.resolve_lifetimes(LOCAL_CRATE)
                .object_lifetime_defaults
                .get(&id)
                .cloned()
        },

        ..*providers
    };

    // (*) FIXME the query should be defined to take a LocalDefId
}

