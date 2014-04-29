// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(non_camel_case_types)]

use syntax::ast;
use syntax::visit;
use syntax::visit::Visitor;

use time;

pub fn time<T, U>(do_it: bool, what: &str, u: U, f: |U| -> T) -> T {
    local_data_key!(depth: uint);
    if !do_it { return f(u); }

    let old = depth.get().map(|d| *d).unwrap_or(0);
    depth.replace(Some(old + 1));

    let start = time::precise_time_s();
    let rv = f(u);
    let end = time::precise_time_s();

    println!("{}time: {:3.3f} s\t{}", "  ".repeat(old), end - start, what);
    depth.replace(Some(old));

    rv
}

pub fn indent<R>(op: || -> R) -> R {
    // Use in conjunction with the log post-processor like `src/etc/indenter`
    // to make debug output more readable.
    debug!(">>");
    let r = op();
    debug!("<< (Result = {:?})", r);
    r
}

pub struct Indenter {
    _cannot_construct_outside_of_this_module: ()
}

impl Drop for Indenter {
    fn drop(&mut self) { debug!("<<"); }
}

pub fn indenter() -> Indenter {
    debug!(">>");
    Indenter { _cannot_construct_outside_of_this_module: () }
}

struct LoopQueryVisitor<'a> {
    p: |&ast::Expr_|: 'a -> bool,
    flag: bool,
}

impl<'a> Visitor<()> for LoopQueryVisitor<'a> {
    fn visit_expr(&mut self, e: &ast::Expr, _: ()) {
        self.flag |= (self.p)(&e.node);
        match e.node {
          // Skip inner loops, since a break in the inner loop isn't a
          // break inside the outer loop
          ast::ExprLoop(..) | ast::ExprWhile(..) => {}
          _ => visit::walk_expr(self, e, ())
        }
    }
}

// Takes a predicate p, returns true iff p is true for any subexpressions
// of b -- skipping any inner loops (loop, while, loop_body)
pub fn loop_query(b: &ast::Block, p: |&ast::Expr_| -> bool) -> bool {
    let mut v = LoopQueryVisitor {
        p: p,
        flag: false,
    };
    visit::walk_block(&mut v, b, ());
    return v.flag;
}

struct BlockQueryVisitor<'a> {
    p: |&ast::Expr|: 'a -> bool,
    flag: bool,
}

impl<'a> Visitor<()> for BlockQueryVisitor<'a> {
    fn visit_expr(&mut self, e: &ast::Expr, _: ()) {
        self.flag |= (self.p)(e);
        visit::walk_expr(self, e, ())
    }
}

// Takes a predicate p, returns true iff p is true for any subexpressions
// of b -- skipping any inner loops (loop, while, loop_body)
pub fn block_query(b: ast::P<ast::Block>, p: |&ast::Expr| -> bool) -> bool {
    let mut v = BlockQueryVisitor {
        p: p,
        flag: false,
    };
    visit::walk_block(&mut v, &*b, ());
    return v.flag;
}


/// Partitions the elements mutable vector in place according to the
/// test `f`. Places elements for which `f` returns `false` first, and
/// then elements for which `f` returns `true`. Returns the number of
/// elements for which `f` returned false (also the index of the first
/// element, if any, for which `f` returned true).
pub fn unstable_partition<T>(elems: &mut [T],
                             f: |&T| -> bool)
                             -> uint
{
    if elems.len() == 0 {
        0
    } else if elems.len() == 1 {
        if !f(&elems[0]) { 1 } else { 0 }
    } else {
        // Divide and conquer.

        let mid = elems.len() / 2;
        let (left_mid, right_mid) = {
            let (left, right) = elems.mut_split_at(mid);
            (unstable_partition(left, |t| f(t)),
             unstable_partition(right, |t| f(t)) + mid)
        };

        // At this point we have:
        //
        // AAAA BBBB CCCC DDDD
        //      ^    ^    ^
        //  left_mid | right_mid
        //          mid
        //
        // and we want:
        //
        // AAAA CCCC BBBB DDDD

        unstable_rotate(elems.mut_slice(left_mid, right_mid),
                        mid - left_mid);

        left_mid + (right_mid - mid)
    }
}

pub fn unstable_rotate<T>(elems: &mut [T],
                          mid: uint) {
    /*!
     * Given a slice like `AABBBBB` (where `mid` is the number of `A`),
     * returns `BBBBBAA`.
     */

    let len = elems.len();
    if mid >= len {
        return;
    }

    for copied in range(0, mid) {
        // At any given point:
        //
        // mid ---------+
        //              |
        //              v
        //        B AAA BBBB A
        //          ^      ^
        //          |      |
        // copied --+      |
        // len-copied-1 ---+
        //
        // becomes
        //
        //        BA AA BBB AA
        elems.swap(copied, len - copied - 1);
    }
}

#[cfg(test)]
fn is_valid_output<T:Eq+Clone+Show>(input: &[T],
                                    test: |&T| -> bool) {
    let mut output = input.to_owned();
    let num_false = unstable_partition(output.as_mut_slice(),
                                       |t| test(t));

    assert!(input.len() == output.len());
    assert!(num_false <= input.len());
    assert!(input.permutations().any(|p| p.as_slice() == output.as_slice()));
    assert!(output.slice_to(num_false).iter().all(|p| !test(p)));
    assert!(output.slice_from(num_false).iter().all(|p| test(p)));
}

#[test]
fn unstable_partition1() {
    is_valid_output::<int>([12, 3, 10, 9, 7, 22], |i| *i > 10);
}

#[test]
fn unstable_partition2() {
    is_valid_output::<int>([12], |i| *i > 10);
}

#[test]
fn unstable_partition3() {
    is_valid_output::<int>([9], |i| *i > 10);
}

#[test]
fn unstable_partition4() {
    is_valid_output::<int>([9, 9, 9, 9], |i| *i > 10);
}

#[test]
fn unstable_partition5() {
    is_valid_output::<int>([12, 15, 22, 23], |i| *i > 10);
}

/**
 * Used in conjunction with `Result` to indicate an error that has
 * been reported to the user. In other words, if the result type of a
 * function is `Result<Foo, ErrorReported>` it means "either success,
 * in which case `Foo`, or an error that was already reported to the
 * user".
 */
pub struct ErrorReported;
