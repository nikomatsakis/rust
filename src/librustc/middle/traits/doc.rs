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

# TRAIT RESOLUTION

This document describes the general process and points out some non-obvious
things.

## Major concepts

Trait resolution is the process of pairing up an impl with each
reference to a trait. So, for example, if there is a generic function like:

    fn clone_slice<T:Clone>(x: &[T]) -> Vec<T> { ... }

and then a call to that function:

    let v: Vec<int> = clone_slice([1, 2, 3].as_slice())

it is the job of trait resolution to figure out (in which case)
whether there exists an impl of `Clone for int`

Note that in some cases, like generic functions, we may not be able to
find a specific impl, but we can figure out that the caller must
provide an impl. To see what I mean, consider the body of `clone_slice`:

    fn clone_slice<T:Clone>(x: &[T]) -> Vec<T> {
        let mut v = Vec::new();
        for e in x.iter() {
            v.push((*e).clone()); // (*)
        }
    }

The line marked `(*)` is only legal if `T` (the type of `*e`)
implements the `Clone` trait. Naturally, since we don't know what `T`
is, we can't find the specific impl; but based on the bound `T:Clone`,
we can say that there exists an impl which the caller must provide.

## Terminology

We use the term *obligation* to refer to a trait reference in need of
an impl.

## To be written:

- Why must all nested obligations be resolved?

## Generic functions and obligation paths

When we check a generic function, we often will resolve to a bound
that is to be determined by the caller. Consider this simple example:

     trait A1 { ... }
     trait A2 : A1 { ... }

     trait B { ... }

     fn foo<X:A2+B> { ... }

Clearly we can use methods offered by `A1`, `A2`, or `B` within the
body of `foo`. In each case, that will incur an obligation like `<A1
for X>` or `<A2 for X>`.

The algorithm we've described thus far only handled concrete types and
impls. Clearly we must do something differently here: since we don't
know what type `X` is, we can't find the specific impl that implements
`<A2 for X>` (or whatever). (That's the caller's job.)

We handle type parameters by reading information found in the
`ty::ParameterEnvironment`. This environment stores the bounds found
on each type parameter. In this case, it will store `X:A2` and `X:B`,
for example.

When we are asked to resolve an obligation whose self type is a
parameter, we begin by examining this environment to see if the type
in question is found amongst the bounds. (The next step is to search
impls as normal; it's possible there is an impl like `impl<Y:B> C for
Y`, in which case we know that `X` implements the trait `C` even
though it is not directly bounded by `C`.)

Presuming we do find a match, we will then consider the obligation
resolved.  But unlike the normal case, we can't resolve to a specific
impl. After all, we don't know what `X` *is* yet. Instead, we resolve
to an `VtablePath`. The idea here is that the caller, who *does*
know what `X` is, is going to have to prove that `X` implements `A2`
and `B`. So basically the caller will have an obligation for each
bound, indicating the relevant impl. The `VtablePath` tells us how
to navigate through these obligations that the caller produces to find
the one that we need.

Let's do some examples so you can see what I mean. Let's say the
caller of `foo()` instantiates `X` with the type `int`. They will then
assemble a list of obligations (actually a list of lists, one for each
parameter) that looks like `[[<A2 for int>, <B for int>]]`.

Now let's say that `foo` internally has the obligation `<A2 for X>`.
That would be resolved to the path `X:[0]`. Meaning, select the list
corresponding to `X`, then select the 0th obligation from that list.
So the result would be `<A2 for int>`.

There are also more interesting cases. For example, consider the
obligation `<A1 for X>`. There is no bound `X:A1`, but we nonetheless
know that `A1` is implemented for `X` because the trait `A2` implies
`A1`. Therefore, we resolve to the path `X:[0,0]`, which means, select
the 0th obligation for `X` (`<A2 for int>`) and then find the 0th
supertrait (`<A1 for int>`).

These paths are ultimately resolved in trans. The monomorphization
process guarantees that we eventually wind up with an actual impl and
vtable.

*/
