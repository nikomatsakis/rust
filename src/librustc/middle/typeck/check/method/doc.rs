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

# Method Lookup Documentation

Method lookup in Rust is a surprisingly complicated affair. This is
due to the interaction of autoderef/autoref as well as the support for
methods with custom self-types.

The high-level flowchart of method lookup is as follows:

   Search for inherent methods --[Match]--+
              |                           |
         [No match?]                      |
              |                           |
              v                           |
   Search for trait methods -----[Match]--+
              |                           |
         [No match?]                      |
              |                           |
              v                           |
            Error                         |
                                          v
                                 Reconcile receivers

The *search* phases basically autoderef in a loop until either a match
is found or the receiver type cannot be further autoderef'd. The
result is a stack of autoderef'd pointers and a match result. This
result is fed into the reconciliation phase. The purpose of the
reconciliation phase is to manage the distinction between the various
kinds of self-types, like `Self`, `&Self`, `&mut Self`, `Gc<Self>`,
etc.

For example, imagine this scenario:

    struct Foo { ... }
    impl Foo {
        fn method(self: Box<Foo>, ...) { ... }
    }
    ...
    let v: Box<Foo> = v.method();

The search phase would yield a stack:

    Box<Foo>
    Foo

it would then find the inherent method `method()`.

The patch-up procedure then compares the self-type of the method
(`Box<Foo>`, in this case) and pops autoderefs off the stack until we
find something that matches.

The reconciliation process is also the point where we consider
auto-ref: if we have the type `Foo` on the stack, we first check if
the method's first argument has type `Foo`. If that fails, we check
for `&Foo` or `&mut Foo` -- if either of those is matched, that's an
autoref.

When an autoref 
of `&mut Foo`, however, there is one further complication.

 */
