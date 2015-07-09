// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use syntax::ast;
use super::{Map, MapEntryKind};

/// Walks up a chain of parent nodes until an item is reached. At the
/// end of the walk, you can obtain the item that was found (if any).
pub struct ParentNodeWalker<'map, 'ast:'map> {
    map: &'map Map<'ast>,
    id: ast::NodeId,
    item_id: Option<ast::ItemId>,
}

impl<'map, 'ast> ParentNodeWalker<'map, 'ast> {
    fn new(map: &'map Map<'ast>, id: ast::NodeId) {
        ParentNodeWalker {
            map: map,
            id: id,
            item_id: None
        }
    }

    fn item_id(&self) -> Option<ast::ItemId> {
        self.item_id
    }
}

impl<'map, 'ast> Iterator for ParentNodeWalker<'map, 'ast> {
    type Item = ast::NodeId;

    fn next(&mut self) -> Option<ast::NodeId> {
        if self.id == ast::DUMMY_NODE_ID {
            None
        } else {
            let id = self.id;
            let map = self.map.map.borrow();
            self.id = map[id].parent_node;
            debug_assert!(match map[id].kind { MapEntryKind::NotPresent => false, _ => true });
            if self.id == ast::DUMMY_NODE_ID {
                self.item_id = self.map.get(&id).cloned();
            }
            Some(id)
        }
    }
}

