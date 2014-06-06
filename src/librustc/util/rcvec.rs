// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(experimental)] // make_unique()

use std::rc::Rc;
use std::slice;

/**
 * A vector for copy-on-write use cases. Only intended for cloneable
 * contents.
 */
#[deriving(PartialEq, Eq, Clone, Hash, Encodable, Decodable)]
pub struct RcVec<T> {
    data: Option<Rc<Vec<T>>>
}

impl<T:Clone> RcVec<T> {
    pub fn new() -> RcVec<T> {
        RcVec { data: None }
    }

    pub fn of(t: T) -> RcVec<T> {
        RcVec::from(vec!(t))
    }

    pub fn from(v: Vec<T>) -> RcVec<T> {
        if v.len() != 0 {
            RcVec { data: Some(Rc::new(v)) }
        } else {
            RcVec::new()
        }
    }

    fn get_mut_vec<'a>(&'a mut self) -> &'a mut Vec<T> {
        if self.data.is_none() {
            self.data = Some(Rc::new(Vec::new()));
        }

        self.data.as_mut().unwrap().make_unique()
    }

    pub fn push(&mut self, value: T) {
        self.get_mut_vec().push(value);
    }

    pub fn push_all(&mut self, value: &[T]) {
        self.get_mut_vec().push_all(value);
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len() == 0 {
            None
        } else if self.len() == 1 {
            let v = self.data.as_ref().unwrap().get(0).clone();
            self.data = None;
            Some(v)
        } else {
            self.get_mut_vec().pop()
        }
    }

    pub fn clear(&mut self) {
        self.data = None;
    }

    pub fn set(&mut self, values: Vec<T>) {
        *self.get_mut_vec() = values;
    }

    pub fn len(&self) -> uint {
        self.data.as_ref().map(|v| v.len()).unwrap_or(0)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get<'a>(&'a self, i: uint) -> Option<&'a T> {
        if i >= self.len() {
            None
        } else {
            Some(self.data.as_ref().unwrap().get(i))
        }
    }

    pub fn get_mut<'a>(&'a mut self, i: uint) -> Option<&'a mut T> {
        if i >= self.len() {
            None
        } else {
            Some(self.get_mut_vec().get_mut(i))
        }
    }

    pub fn iter<'a>(&'a self) -> slice::Items<'a, T> {
        self.as_slice().iter()
    }

    pub fn as_slice<'a>(&'a self) -> &'a [T] {
        match self.data {
            None => &[],
            Some(ref v) => v.as_slice(),
        }
    }

    pub fn last<'a>(&'a self) -> Option<&'a T> {
        self.as_slice().last()
    }

    pub fn to_vec(self) -> Vec<T> {
        // inefficient but so long as there is no easy way to unwrap
        // an Rc, we're going to wind up cloning whatever we do
        self.iter().map(|x| (*x).clone()).collect()
    }
}
