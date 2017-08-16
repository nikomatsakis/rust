# Type inference engine

The engine is based around an extension of HM-type-inference so that
it supports "multiple universes" (that is, the ability to reason about
variables where different sets of names are in scope per variable).
This is very similar to the "Labeled Unification" procedure described
in the paper,
["A Proof Procedure for the Logic of Hereditary Harrop Formulas"][pplhhhf]
by Gopalan Nadathur, with some extensions to accommodate subtyping.

[pplhhhf]: https://pdfs.semanticscholar.org/335f/16ac16b3de99679cb7adf435056000ef811b.pdf

## Universes and skolemization

Universes and skolemization are two complex sound terms, but the
underlying idea is quite simple. Consider a type like this:

    for<'a> fn(&'a u32)
    
Here the `for<'a>` quantifier brings `'a` into scope -- that is,
within the function type, we can refer to `'a`. But outside, we cannot
(in fact, Rust does not allow shadowing in such names, but even if it
did, if we were to use the name `'a`, it would be referring to some
other lifetime, not `'a`).

To describe this idea, we say that, when we enter the function type,
we enter into a **subuniverse** U1 of the original universe U0. In
this subuniverse U1, we can name all the names from U0, but we can
also use refer to `'a`. In this case, when we refer to `'a`, we are
not referring to any 'real' region, but rather an abstract one -- a
kind of ideal representative, meaning "any region that might later be
used for `'a`". This idea, of an abstract representative, is called a
**skolemized** region (named after [Thoraf Skolem], a philosopher and
mathematician who pioneered the technique).

[Thoraf Skolem]: https://en.wikipedia.org/wiki/Thoralf_Skolem

The same ideas (universes and skolemization) apply to types, which
might help make them easier to understand. Consider:

```rust
fn foo<T: Display>(v: Vec<T>) { ... }
```

When we type-check the body of `foo`, we are able to refer to `T` as
if it were a real type. But it's not a real type -- it's a *skolemized
type*, representing the abstract idea of "some type T, where the only
thing we know about `T` is that it is `Sized` and it implements
`Display`".

Universes form a tree. However, in the compiler, we represent them
using only a single integer (`ty::UniverseIndex`). This suffices
because sibling universes never come into contact with one another --
so while names from U1 and U0 may "interact" (i.e., appear in the same
constraint etc), if U0 has *another* subuniverse `U1'`, then names
from `U1` and `U1'` will never interact with one another.

## Basic unification

The basic idea of unification is that, when we encounter a type that
we do not know, we instantiate a type variable `?T` (we will use a
leading question mark to refer to inference variables of this kind;
`?'A` will be used for region variables). Later, when we are doing
type-checking etc, we may encounter a constraint that tells us what
`?T` has to be.  For example, imagine that `Vec<?T>` is the type of
some variable `x`, and we encounter some code which states that the
type of `x` must be equal to `Vec<i32>`. We could write the constraint
that arises from this as:

    Vec<?T> = Vec<i32>
    
Since we know that `Vec<T>` is only equal to `Vec<U>` if `T=U`, we can
further derive from this constraint that `?T = i32`. This general
process is called **unification**. It's a "tried and true" technique
and there are good descriptions of it in many places; you can read a
Rust-oriented description of it in [this blog post][unification1].

[unification1]: http://smallcultfollowing.com/babysteps/blog/2017/03/25/unification-in-chalk-part-1/

## Extending unification with universes

To 

## Handling subtyping

In truth, outside of trait matching, we rarely encounter *equality* constraints in Rust.
