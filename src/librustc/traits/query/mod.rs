// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Experimental types for the trait query interface. The methods
//! defined in this module are all based on **canonicalization**,
//! which makes a canonical query by replacing unbound inference
//! variables and regions, so that results can be reused more broadly.
//! The providers for the queries defined here can be found in
//! `librustc_traits`.

pub mod normalize;
pub mod normalize_erasing_regions;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct NoSolution;

pub type Fallible<T> = Result<T, NoSolution>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Overflow;

pub type CanOverflow<T> = Result<T, Overflow>;

