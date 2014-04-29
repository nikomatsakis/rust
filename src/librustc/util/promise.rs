// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// FIXME This should move to standard library I think.

/*!
 * A `Promise` type indicates a value that will be supplied at some
 * later time. A `Promise` begins in an unfulfilled state. At some
 * point, someone may fulfill the promise by setting it to a
 * value. Promises can only be fulfilled at most once; attempting to
 * fulfill a promise more than once results in a dynamic failure.
 *
 * Promises are useful as a replacement for `RefCell` in deferred
 * initialization scenarios where you know the value will only be set
 * exactly once. In those cases, using a `Promise` is preferred
 * because you can borrow the contents of a `Promise` for a longer
 * lifetime than you could borrow the contents of a `RefCell`, since
 * there is no need to track its dynamic state. Using a `Promise`
 * also expresses your intent that the value will be set exactly once.
 *
 * Note that promises are not thread safe and cannot be shared between
 * threads. This makes their implementation simpler, but it implies
 * that the code which fulfills the promise must be running in the
 * current thread. If you are interested in cross-thread or
 * asynchronous promises, you may want to check the `Future` types.
 */

use std::fmt;
use std::kinds::marker;
use std::ty::Unsafe;

/// A mutable memory location that admits only `Copy` data.
pub struct Promise<T> {
    value: Unsafe<Option<T>>,
    noshare: marker::NoShare,
}

impl<T> Promise<T> {
    /// Creates a new, unfulfilled `Promise`.
    pub fn new() -> Promise<T> {
        Promise {
            value: Unsafe::new(None),
            noshare: marker::NoShare,
        }
    }

    /// Creates a new `Promise` that is already fulfilled.
    pub fn fulfilled(value: T) -> Promise<T> {
        Promise {
            value: Unsafe::new(Some(value)),
            noshare: marker::NoShare,
        }
    }

    /// True if this promise has been fulfilled.
    pub fn is_fulfilled(&self) -> bool {
        self.get().is_some()
    }

    /// True if this promise has been fulfilled.
    pub fn is_unfulfilled(&self) -> bool {
        !self.is_fulfilled()
    }

    /// Tries to fulfills a promise. If it succeeds, returns `Ok(())`.
    /// If it fails, returns `Err(value)`.
    pub fn fulfill(&self, value: T) -> Result<(), T> {
        unsafe {
            let p = self.value.get();
            match *p {
                None => {
                    *p = Some(value);
                    Ok(())
                }
                Some(_) => {
                    Err(value)
                }
            }
        }
    }

    /// Reads the value in the promise. Returns `None` if the promise
    /// has not yet been fulfilled.
    pub fn get<'a>(&'a self) -> Option<&'a T> {
        unsafe {
            let p = self.value.get();
            match *p {
                None => { None }
                Some(ref v) => Some(v)
            }
        }
    }

    pub fn map(&self, f: |&T| -> T) -> Promise<T> {
        match self.get() {
            None => Promise::new(),
            Some(t) => Promise::fulfilled(f(t)),
        }
    }
}

impl<T:Clone> Promise<T> {
    pub fn get_clone(&self) -> Option<T> {
        match self.get() {
            None => None,
            Some(p) => Some((*p).clone())
        }
    }
}

impl<T:fmt::Show> fmt::Show for Promise<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.get() {
            None => write!(f, r"Promise()"),
            Some(p) => write!(f, r"{}", *p)
        }
    }
}

impl<T:Clone> Clone for Promise<T> {
    fn clone(&self) -> Promise<T> {
        match self.get() {
            None => Promise::new(),
            Some(p) => Promise::fulfilled(p.clone())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic_get() {
        let p = Promise::new();
        assert_eq!(p.get(), None);

        p.fulfill(22);
        assert_eq!(p.get_clone(), Some(22));
    }

    #[test]
    #[should_fail]
    fn fulfill_twice() {
        let p = Promise::new();
        assert_eq!(p.fulfill(22), Ok(()));
        assert_eq!(p.fulfill(23), Err(23));
    }

    #[test]
    fn promise_has_sensible_show() {
        let p = Promise::new();
        assert_eq!(format!("{}", p), "Promise()");

        p.fulfill(22);
        assert_eq!(format!("{}", p), "Promise(22)");
    }
}
