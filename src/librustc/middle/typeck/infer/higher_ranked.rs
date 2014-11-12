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
 * Helper routines for higher-ranked things. See the `doc` module at
 * the end of the file for details.
 */

use middle::ty;
use middle::ty::replace_late_bound_regions;
use middle::typeck::infer::combine;
use middle::typeck::infer::combine::Combine;
use middle::typeck::infer::{cres};
use middle::typeck::infer::InferCtxt;
use middle::typeck::infer::region_inference::{RegionMark};
use middle::ty_fold::{mod, HigherRankedFoldable, TypeFoldable};
use std::collections::HashMap;
use syntax::codemap::Span;
use util::ppaux::{bound_region_to_string, Repr};

pub trait HigherRankedCombineable : HigherRankedFoldable + TypeFoldable + Repr {
    fn super_combine<'tcx,C:Combine<'tcx>>(combiner: &C, a: &Self, b: &Self) -> cres<Self>;
}

pub trait HigherRankedRelations {
    fn higher_ranked_sub<T>(&self, a: &T, b: &T) -> cres<T>
        where T : HigherRankedCombineable;

    fn higher_ranked_lub<T>(&self, a: &T, b: &T) -> cres<T>
        where T : HigherRankedCombineable;

    fn higher_ranked_glb<T>(&self, a: &T, b: &T) -> cres<T>
        where T : HigherRankedCombineable;
}

impl<'tcx,C> HigherRankedRelations for C
    where C : Combine<'tcx>
{
    fn higher_ranked_sub<T>(&self, a: &T, b: &T) -> cres<T>
        where T : HigherRankedCombineable
    {
        debug!("higher_ranked_sub(a={}, b={})",
               a.repr(self.tcx()), b.repr(self.tcx()));

        // Rather than checking the subtype relationship between `a` and `b`
        // as-is, we need to do some extra work here in order to make sure
        // that function subtyping works correctly with respect to regions
        //
        // Note: this is a subtle algorithm.  For a full explanation,
        // please see the large comment at the end of the file in the (inlined) module
        // `doc`.

        // Make a mark so we can examine "all bindings that were
        // created as part of this type comparison".
        let mark = self.infcx().region_vars.mark();

        // First, we instantiate each bound region in the subtype with a fresh
        // region variable.
        let (a_prime, _) =
            self.infcx().replace_late_bound_regions_with_fresh_regions(
                self.trace().origin.span(), a);

        // Second, we instantiate each bound region in the supertype with a
        // fresh concrete region.
        let (b_prime, skol_map) = {
            replace_late_bound_regions(self.tcx(), b, |br| {
                let skol = self.infcx().region_vars.new_skolemized(br);
                debug!("Bound region {} skolemized to {}",
                       bound_region_to_string(self.tcx(), "", false, br),
                       skol);
                skol
            })
        };

        debug!("a_prime={}", a_prime.repr(self.tcx()));
        debug!("b_prime={}", b_prime.repr(self.tcx()));

        // Compare types now that bound regions have been replaced.
        let result = try!(HigherRankedCombineable::super_combine(self, &a_prime, &b_prime));

        // Presuming type comparison succeeds, we need to check
        // that the skolemized regions do not "leak".
        let new_vars =
            self.infcx().region_vars.vars_created_since_mark(mark);
        for (&skol_br, &skol) in skol_map.iter() {
            let tainted = self.infcx().region_vars.tainted(mark, skol);
            for tainted_region in tainted.iter() {
                // Each skolemized should only be relatable to itself
                // or new variables:
                match *tainted_region {
                    ty::ReInfer(ty::ReVar(ref vid)) => {
                        if new_vars.iter().any(|x| x == vid) { continue; }
                    }
                    _ => {
                        if *tainted_region == skol { continue; }
                    }
                };

                // A is not as polymorphic as B:
                if self.a_is_expected() {
                    debug!("Not as polymorphic!");
                    return Err(ty::terr_regions_insufficiently_polymorphic(
                        skol_br, *tainted_region));
                } else {
                    debug!("Overly polymorphic!");
                    return Err(ty::terr_regions_overly_polymorphic(
                        skol_br, *tainted_region));
                }
            }
        }

        debug!("higher_ranked_sub: OK result={}",
               result.repr(self.tcx()));

        return Ok(result);
    }

    fn higher_ranked_lub<T>(&self, a: &T, b: &T) -> cres<T>
        where T : HigherRankedCombineable
    {
        // Make a mark so we can examine "all bindings that were
        // created as part of this type comparison".
        let mark = self.infcx().region_vars.mark();

        // Instantiate each bound region with a fresh region variable.
        let span = self.trace().origin.span();
        let (a_with_fresh, a_map) =
            self.infcx().replace_late_bound_regions_with_fresh_regions(span, a);
        let (b_with_fresh, _) =
            self.infcx().replace_late_bound_regions_with_fresh_regions(span, b);

        // Collect constraints.
        let result0 =
            try!(HigherRankedCombineable::super_combine(self, &a_with_fresh, &b_with_fresh));
        debug!("result0 = {}", result0.repr(self.tcx()));

        // Generalize the regions appearing in result0 if possible
        let new_vars = self.infcx().region_vars.vars_created_since_mark(mark);
        let span = self.trace().origin.span();
        let result1 =
            fold_regions_in(
                self.tcx(),
                &result0,
                |r| generalize_region(self.infcx(), span, mark,
                                      new_vars.as_slice(), &a_map, r));
        return Ok(result1);

        fn generalize_region(infcx: &InferCtxt,
                             span: Span,
                             mark: RegionMark,
                             new_vars: &[ty::RegionVid],
                             a_map: &HashMap<ty::BoundRegion, ty::Region>,
                             r0: ty::Region)
                             -> ty::Region {
            // Regions that pre-dated the LUB computation stay as they are.
            if !is_var_in_set(new_vars, r0) {
                assert!(!r0.is_bound());
                debug!("generalize_region(r0={}): not new variable", r0);
                return r0;
            }

            let tainted = infcx.region_vars.tainted(mark, r0);

            // Variables created during LUB computation which are
            // *related* to regions that pre-date the LUB computation
            // stay as they are.
            if !tainted.iter().all(|r| is_var_in_set(new_vars, *r)) {
                debug!("generalize_region(r0={}): \
                        non-new-variables found in {}",
                       r0, tainted);
                assert!(!r0.is_bound());
                return r0;
            }

            // Otherwise, the variable must be associated with at
            // least one of the variables representing bound regions
            // in both A and B.  Replace the variable with the "first"
            // bound region from A that we find it to be associated
            // with.
            for (a_br, a_r) in a_map.iter() {
                if tainted.iter().any(|x| x == a_r) {
                    debug!("generalize_region(r0={}): \
                            replacing with {}, tainted={}",
                           r0, *a_br, tainted);
                    return ty::ReLateBound(ty::DebruijnIndex::new(1), *a_br);
                }
            }

            infcx.tcx.sess.span_bug(
                span,
                format!("region {} is not associated with \
                         any bound region from A!",
                        r0).as_slice())
        }
    }

    fn higher_ranked_glb<T>(&self, a: &T, b: &T) -> cres<T>
        where T : HigherRankedCombineable
    {
        debug!("{}.higher_ranked_glb({}, {})",
               self.tag(), a.repr(self.tcx()), b.repr(self.tcx()));

        // Make a mark so we can examine "all bindings that were
        // created as part of this type comparison".
        let mark = self.infcx().region_vars.mark();

        // Instantiate each bound region with a fresh region variable.
        let (a_with_fresh, a_map) =
            self.infcx().replace_late_bound_regions_with_fresh_regions(
                self.trace().origin.span(), a);
        let (b_with_fresh, b_map) =
            self.infcx().replace_late_bound_regions_with_fresh_regions(
                self.trace().origin.span(), b);
        let a_vars = var_ids(self, &a_map);
        let b_vars = var_ids(self, &b_map);

        // Collect constraints.
        let result0 =
            try!(HigherRankedCombineable::super_combine(self, &a_with_fresh, &b_with_fresh));
        debug!("result0 = {}", result0.repr(self.tcx()));

        // Generalize the regions appearing in fn_ty0 if possible
        let new_vars = self.infcx().region_vars.vars_created_since_mark(mark);
        let span = self.trace().origin.span();
        let result1 =
            fold_regions_in(
                self.tcx(),
                &result0,
                |r| generalize_region(self.infcx(), span, mark, new_vars.as_slice(),
                                      &a_map, a_vars.as_slice(), b_vars.as_slice(), r));
        debug!("result1 = {}", result1.repr(self.tcx()));
        return Ok(result1);

        fn generalize_region(infcx: &InferCtxt,
                             span: Span,
                             mark: RegionMark,
                             new_vars: &[ty::RegionVid],
                             a_map: &HashMap<ty::BoundRegion, ty::Region>,
                             a_vars: &[ty::RegionVid],
                             b_vars: &[ty::RegionVid],
                             r0: ty::Region) -> ty::Region {
            if !is_var_in_set(new_vars, r0) {
                assert!(!r0.is_bound());
                return r0;
            }

            let tainted = infcx.region_vars.tainted(mark, r0);

            let mut a_r = None;
            let mut b_r = None;
            let mut only_new_vars = true;
            for r in tainted.iter() {
                if is_var_in_set(a_vars, *r) {
                    if a_r.is_some() {
                        return fresh_bound_variable(infcx);
                    } else {
                        a_r = Some(*r);
                    }
                } else if is_var_in_set(b_vars, *r) {
                    if b_r.is_some() {
                        return fresh_bound_variable(infcx);
                    } else {
                        b_r = Some(*r);
                    }
                } else if !is_var_in_set(new_vars, *r) {
                    only_new_vars = false;
                }
            }

            // NB---I do not believe this algorithm computes
            // (necessarily) the GLB.  As written it can
            // spuriously fail. In particular, if there is a case
            // like: |fn(&a)| and fn(fn(&b)), where a and b are
            // free, it will return fn(&c) where c = GLB(a,b).  If
            // however this GLB is not defined, then the result is
            // an error, even though something like
            // "fn<X>(fn(&X))" where X is bound would be a
            // subtype of both of those.
            //
            // The problem is that if we were to return a bound
            // variable, we'd be computing a lower-bound, but not
            // necessarily the *greatest* lower-bound.
            //
            // Unfortunately, this problem is non-trivial to solve,
            // because we do not know at the time of computing the GLB
            // whether a GLB(a,b) exists or not, because we haven't
            // run region inference (or indeed, even fully computed
            // the region hierarchy!). The current algorithm seems to
            // works ok in practice.

            if a_r.is_some() && b_r.is_some() && only_new_vars {
                // Related to exactly one bound variable from each fn:
                return rev_lookup(infcx, span, a_map, a_r.unwrap());
            } else if a_r.is_none() && b_r.is_none() {
                // Not related to bound variables from either fn:
                assert!(!r0.is_bound());
                return r0;
            } else {
                // Other:
                return fresh_bound_variable(infcx);
            }
        }

        fn rev_lookup(infcx: &InferCtxt,
                      span: Span,
                      a_map: &HashMap<ty::BoundRegion, ty::Region>,
                      r: ty::Region) -> ty::Region
        {
            for (a_br, a_r) in a_map.iter() {
                if *a_r == r {
                    return ty::ReLateBound(ty::DebruijnIndex::new(1), *a_br);
                }
            }
            infcx.tcx.sess.span_bug(
                span,
                format!("could not find original bound region for {}", r)[]);
        }

        fn fresh_bound_variable(infcx: &InferCtxt) -> ty::Region {
            infcx.region_vars.new_bound()
        }
    }
}

impl HigherRankedCombineable for ty::FnSig {
    fn super_combine<'tcx,C:Combine<'tcx>>(combiner: &C, a: &ty::FnSig, b: &ty::FnSig)
                                           -> cres<ty::FnSig>
    {
        if a.variadic != b.variadic {
            return Err(ty::terr_variadic_mismatch(
                combine::expected_found(combiner, a.variadic, b.variadic)));
        }

        let inputs = try!(argvecs(combiner,
                                  a.inputs.as_slice(),
                                  b.inputs.as_slice()));

        let output = try!(match (a.output, b.output) {
            (ty::FnConverging(a_ty), ty::FnConverging(b_ty)) =>
                Ok(ty::FnConverging(try!(combiner.tys(a_ty, b_ty)))),
            (ty::FnDiverging, ty::FnDiverging) =>
                Ok(ty::FnDiverging),
            (a, b) =>
                Err(ty::terr_convergence_mismatch(
                    combine::expected_found(combiner, a != ty::FnDiverging, b != ty::FnDiverging))),
        });

        return Ok(ty::FnSig {inputs: inputs,
                             output: output,
                             variadic: a.variadic});


        fn argvecs<'tcx, C: Combine<'tcx>>(combiner: &C,
                                           a_args: &[ty::t],
                                           b_args: &[ty::t])
                                           -> cres<Vec<ty::t>>
        {
            if a_args.len() == b_args.len() {
                a_args.iter().zip(b_args.iter())
                    .map(|(a, b)| combiner.args(*a, *b)).collect()
            } else {
                Err(ty::terr_arg_count)
            }
        }
    }
}

impl HigherRankedCombineable for ty::TraitRef {
    fn super_combine<'tcx,C:Combine<'tcx>>(combiner: &C, a: &ty::TraitRef, b: &ty::TraitRef)
                                           -> cres<ty::TraitRef>
    {
        // Different traits cannot be related
        if a.def_id != b.def_id {
            Err(ty::terr_traits(
                combine::expected_found(combiner, a.def_id, b.def_id)))
        } else {
            let substs = try!(combiner.substs(a.def_id, &a.substs, &b.substs));
            Ok(ty::TraitRef { def_id: a.def_id,
                              substs: substs })
        }
    }
}

fn var_ids<'tcx, T: Combine<'tcx>>(combiner: &T,
                                   map: &HashMap<ty::BoundRegion, ty::Region>)
                                   -> Vec<ty::RegionVid> {
    map.iter().map(|(_, r)| match *r {
            ty::ReInfer(ty::ReVar(r)) => { r }
            r => {
                combiner.infcx().tcx.sess.span_bug(
                    combiner.trace().origin.span(),
                    format!("found non-region-vid: {}", r).as_slice());
            }
        }).collect()
}

fn is_var_in_set(new_vars: &[ty::RegionVid], r: ty::Region) -> bool {
    match r {
        ty::ReInfer(ty::ReVar(ref v)) => new_vars.iter().any(|x| x == v),
        _ => false
    }
}

fn fold_regions_in<T:TypeFoldable>(tcx: &ty::ctxt,
                                   value: &T,
                                   fldr: |r: ty::Region| -> ty::Region)
                                   -> T
{
    value.fold_with(&mut ty_fold::RegionFolder::new(tcx, |region, current_depth| {
        // we should only be encountering "escaping" late-bound regions here,
        // because the ones at the current level should have been replaced
        // with fresh variables
        assert!(match region {
            ty::ReLateBound(debruijn, _) => debruijn.depth > current_depth,
            _ => true
        });

        fldr(region)
    }))
}

mod doc {
    /*!

# Skolemization and functions

One of the trickiest and most subtle aspects of regions is dealing
with higher-ranked things which include bound region variables, such
as function types. I strongly suggest that if you want to understand
the situation, you read this paper (which is, admittedly, very long,
but you don't have to read the whole thing):

http://research.microsoft.com/en-us/um/people/simonpj/papers/higher-rank/

Although my explanation will never compete with SPJ's (for one thing,
his is approximately 100 pages), I will attempt to explain the basic
problem and also how we solve it. Note that the paper only discusses
subtyping, not the computation of LUB/GLB.

The problem we are addressing is that there is a kind of subtyping
between functions with bound region parameters. Consider, for
example, whether the following relation holds:

    fn(&'a int) <: |&'b int|? (Yes, a => b)

The answer is that of course it does. These two types are basically
the same, except that in one we used the name `a` and one we used
the name `b`.

In the examples that follow, it becomes very important to know whether
a lifetime is bound in a function type (that is, is a lifetime
parameter) or appears free (is defined in some outer scope).
Therefore, from now on I will write the bindings explicitly, using a
notation like `fn<a>(&'a int)` to indicate that `a` is a lifetime
parameter.

Now let's consider two more function types. Here, we assume that the
`self` lifetime is defined somewhere outside and hence is not a
lifetime parameter bound by the function type (it "appears free"):

    fn<a>(&'a int) <: |&'a int|? (Yes, a => self)

This subtyping relation does in fact hold. To see why, you have to
consider what subtyping means. One way to look at `T1 <: T2` is to
say that it means that it is always ok to treat an instance of `T1` as
if it had the type `T2`. So, with our functions, it is always ok to
treat a function that can take pointers with any lifetime as if it
were a function that can only take a pointer with the specific
lifetime `&self`. After all, `&self` is a lifetime, after all, and
the function can take values of any lifetime.

You can also look at subtyping as the *is a* relationship. This amounts
to the same thing: a function that accepts pointers with any lifetime
*is a* function that accepts pointers with some specific lifetime.

So, what if we reverse the order of the two function types, like this:

    fn(&'a int) <: <a>|&'a int|? (No)

Does the subtyping relationship still hold?  The answer of course is
no. In this case, the function accepts *only the lifetime `&self`*,
so it is not reasonable to treat it as if it were a function that
accepted any lifetime.

What about these two examples:

    fn<a,b>(&'a int, &'b int) <: <a>|&'a int, &'a int|? (Yes)
    fn<a>(&'a int, &'a int) <: <a,b>|&'a int, &'b int|? (No)

Here, it is true that functions which take two pointers with any two
lifetimes can be treated as if they only accepted two pointers with
the same lifetime, but not the reverse.

## The algorithm

Here is the algorithm we use to perform the subtyping check:

1. Replace all bound regions in the subtype with new variables
2. Replace all bound regions in the supertype with skolemized
   equivalents. A "skolemized" region is just a new fresh region
   name.
3. Check that the parameter and return types match as normal
4. Ensure that no skolemized regions 'leak' into region variables
   visible from "the outside"

Let's walk through some examples and see how this algorithm plays out.

#### First example

We'll start with the first example, which was:

    1. fn<a>(&'a T) <: <b>|&'b T|?        Yes: a -> b

After steps 1 and 2 of the algorithm we will have replaced the types
like so:

    1. fn(&'A T) <: |&'x T|?

Here the upper case `&A` indicates a *region variable*, that is, a
region whose value is being inferred by the system. I also replaced
`&b` with `&x`---I'll use letters late in the alphabet (`x`, `y`, `z`)
to indicate skolemized region names. We can assume they don't appear
elsewhere. Note that neither the sub- nor the supertype bind any
region names anymore (as indicated by the absence of `<` and `>`).

The next step is to check that the parameter types match. Because
parameters are contravariant, this means that we check whether:

    &'x T <: &'A T

Region pointers are contravariant so this implies that

    &A <= &x

must hold, where `<=` is the subregion relationship. Processing
*this* constrain simply adds a constraint into our graph that `&A <=
&x` and is considered successful (it can, for example, be satisfied by
choosing the value `&x` for `&A`).

So far we have encountered no error, so the subtype check succeeds.

#### The third example

Now let's look first at the third example, which was:

    3. fn(&'a T)    <: <b>|&'b T|?        No!

After steps 1 and 2 of the algorithm we will have replaced the types
like so:

    3. fn(&'a T) <: |&'x T|?

This looks pretty much the same as before, except that on the LHS
`&self` was not bound, and hence was left as-is and not replaced with
a variable. The next step is again to check that the parameter types
match. This will ultimately require (as before) that `&self` <= `&x`
must hold: but this does not hold. `self` and `x` are both distinct
free regions. So the subtype check fails.

#### Checking for skolemization leaks

You may be wondering about that mysterious last step in the algorithm.
So far it has not been relevant. The purpose of that last step is to
catch something like *this*:

    fn<a>() -> fn(&'a T) <: || -> fn<b>(&'b T)?   No.

Here the function types are the same but for where the binding occurs.
The subtype returns a function that expects a value in precisely one
region. The supertype returns a function that expects a value in any
region. If we allow an instance of the subtype to be used where the
supertype is expected, then, someone could call the fn and think that
the return value has type `fn<b>(&'b T)` when it really has type
`fn(&'a T)` (this is case #3, above). Bad.

So let's step through what happens when we perform this subtype check.
We first replace the bound regions in the subtype (the supertype has
no bound regions). This gives us:

    fn() -> fn(&'A T) <: || -> fn<b>(&'b T)?

Now we compare the return types, which are covariant, and hence we have:

    fn(&'A T) <: <b>|&'b T|?

Here we skolemize the bound region in the supertype to yield:

    fn(&'A T) <: |&'x T|?

And then proceed to compare the argument types:

    &'x T <: &'A T
    &A <= &x

Finally, this is where it gets interesting!  This is where an error
*should* be reported. But in fact this will not happen. The reason why
is that `A` is a variable: we will infer that its value is the fresh
region `x` and think that everything is happy. In fact, this behavior
is *necessary*, it was key to the first example we walked through.

The difference between this example and the first one is that the variable
`A` already existed at the point where the skolemization occurred. In
the first example, you had two functions:

    fn<a>(&'a T) <: <b>|&'b T|

and hence `&A` and `&x` were created "together". In general, the
intention of the skolemized names is that they are supposed to be
fresh names that could never be equal to anything from the outside.
But when inference comes into play, we might not be respecting this
rule.

So the way we solve this is to add a fourth step that examines the
constraints that refer to skolemized names. Basically, consider a
non-directed verison of the constraint graph. Let `Tainted(x)` be the
set of all things reachable from a skolemized variable `x`.
`Tainted(x)` should not contain any regions that existed before the
step at which the skolemization was performed. So this case here
would fail because `&x` was created alone, but is relatable to `&A`.

## Computing the LUB and GLB

The paper I pointed you at is written for Haskell. It does not
therefore considering subtyping and in particular does not consider
LUB or GLB computation. We have to consider this. Here is the
algorithm I implemented.

First though, let's discuss what we are trying to compute in more
detail. The LUB is basically the "common supertype" and the GLB is
"common subtype"; one catch is that the LUB should be the
*most-specific* common supertype and the GLB should be *most general*
common subtype (as opposed to any common supertype or any common
subtype).

Anyway, to help clarify, here is a table containing some
function pairs and their LUB/GLB:

```
Type 1              Type 2              LUB               GLB
fn<a>(&a)           fn(&X)              fn(&X)            fn<a>(&a)
fn(&A)              fn(&X)              --                fn<a>(&a)
fn<a,b>(&a, &b)     fn<x>(&x, &x)       fn<a>(&a, &a)     fn<a,b>(&a, &b)
fn<a,b>(&a, &b, &a) fn<x,y>(&x, &y, &y) fn<a>(&a, &a, &a) fn<a,b,c>(&a,&b,&c)
```

### Conventions

I use lower-case letters (e.g., `&a`) for bound regions and upper-case
letters for free regions (`&A`).  Region variables written with a
dollar-sign (e.g., `$a`).  I will try to remember to enumerate the
bound-regions on the fn type as well (e.g., `fn<a>(&a)`).

### High-level summary

Both the LUB and the GLB algorithms work in a similar fashion.  They
begin by replacing all bound regions (on both sides) with fresh region
inference variables.  Therefore, both functions are converted to types
that contain only free regions.  We can then compute the LUB/GLB in a
straightforward way, as described in `combine.rs`.  This results in an
interim type T.  The algorithms then examine the regions that appear
in T and try to, in some cases, replace them with bound regions to
yield the final result.

To decide whether to replace a region `R` that appears in `T` with a
bound region, the algorithms make use of two bits of information.
First is a set `V` that contains all region variables created as part
of the LUB/GLB computation. `V` will contain the region variables
created to replace the bound regions in the input types, but it also
contains 'intermediate' variables created to represent the LUB/GLB of
individual regions.  Basically, when asked to compute the LUB/GLB of a
region variable with another region, the inferencer cannot oblige
immediately since the values of that variables are not known.
Therefore, it creates a new variable that is related to the two
regions.  For example, the LUB of two variables `$x` and `$y` is a
fresh variable `$z` that is constrained such that `$x <= $z` and `$y
<= $z`.  So `V` will contain these intermediate variables as well.

The other important factor in deciding how to replace a region in T is
the function `Tainted($r)` which, for a region variable, identifies
all regions that the region variable is related to in some way
(`Tainted()` made an appearance in the subtype computation as well).

### LUB

The LUB algorithm proceeds in three steps:

1. Replace all bound regions (on both sides) with fresh region
   inference variables.
2. Compute the LUB "as normal", meaning compute the GLB of each
   pair of argument types and the LUB of the return types and
   so forth.  Combine those to a new function type `F`.
3. Replace each region `R` that appears in `F` as follows:
   - Let `V` be the set of variables created during the LUB
     computational steps 1 and 2, as described in the previous section.
   - If `R` is not in `V`, replace `R` with itself.
   - If `Tainted(R)` contains a region that is not in `V`,
     replace `R` with itself.
   - Otherwise, select the earliest variable in `Tainted(R)` that originates
     from the left-hand side and replace `R` with the bound region that
     this variable was a replacement for.

So, let's work through the simplest example: `fn(&A)` and `fn<a>(&a)`.
In this case, `&a` will be replaced with `$a` and the interim LUB type
`fn($b)` will be computed, where `$b=GLB(&A,$a)`.  Therefore, `V =
{$a, $b}` and `Tainted($b) = { $b, $a, &A }`.  When we go to replace
`$b`, we find that since `&A \in Tainted($b)` is not a member of `V`,
we leave `$b` as is.  When region inference happens, `$b` will be
resolved to `&A`, as we wanted.

Let's look at a more complex one: `fn(&a, &b)` and `fn(&x, &x)`.  In
this case, we'll end up with a (pre-replacement) LUB type of `fn(&g,
&h)` and a graph that looks like:

```
     $a        $b     *--$x
       \        \    /  /
        \        $h-*  /
         $g-----------*
```

Here `$g` and `$h` are fresh variables that are created to represent
the LUB/GLB of things requiring inference.  This means that `V` and
`Tainted` will look like:

```
V = {$a, $b, $g, $h, $x}
Tainted($g) = Tainted($h) = { $a, $b, $h, $g, $x }
```

Therefore we replace both `$g` and `$h` with `$a`, and end up
with the type `fn(&a, &a)`.

### GLB

The procedure for computing the GLB is similar.  The difference lies
in computing the replacements for the various variables. For each
region `R` that appears in the type `F`, we again compute `Tainted(R)`
and examine the results:

1. If `R` is not in `V`, it is not replaced.
2. Else, if `Tainted(R)` contains only variables in `V`, and it
   contains exactly one variable from the LHS and one variable from
   the RHS, then `R` can be mapped to the bound version of the
   variable from the LHS.
3. Else, if `Tainted(R)` contains no variable from the LHS and no
   variable from the RHS, then `R` can be mapped to itself.
4. Else, `R` is mapped to a fresh bound variable.

These rules are pretty complex.  Let's look at some examples to see
how they play out.

Out first example was `fn(&a)` and `fn(&X)`.  In this case, `&a` will
be replaced with `$a` and we will ultimately compute a
(pre-replacement) GLB type of `fn($g)` where `$g=LUB($a,&X)`.
Therefore, `V={$a,$g}` and `Tainted($g)={$g,$a,&X}.  To find the
replacement for `$g` we consult the rules above:
- Rule (1) does not apply because `$g \in V`
- Rule (2) does not apply because `&X \in Tainted($g)`
- Rule (3) does not apply because `$a \in Tainted($g)`
- Hence, by rule (4), we replace `$g` with a fresh bound variable `&z`.
So our final result is `fn(&z)`, which is correct.

The next example is `fn(&A)` and `fn(&Z)`. In this case, we will again
have a (pre-replacement) GLB of `fn(&g)`, where `$g = LUB(&A,&Z)`.
Therefore, `V={$g}` and `Tainted($g) = {$g, &A, &Z}`.  In this case,
by rule (3), `$g` is mapped to itself, and hence the result is
`fn($g)`.  This result is correct (in this case, at least), but it is
indicative of a case that *can* lead us into concluding that there is
no GLB when in fact a GLB does exist.  See the section "Questionable
Results" below for more details.

The next example is `fn(&a, &b)` and `fn(&c, &c)`. In this case, as
before, we'll end up with `F=fn($g, $h)` where `Tainted($g) =
Tainted($h) = {$g, $h, $a, $b, $c}`.  Only rule (4) applies and hence
we'll select fresh bound variables `y` and `z` and wind up with
`fn(&y, &z)`.

For the last example, let's consider what may seem trivial, but is
not: `fn(&a, &a)` and `fn(&b, &b)`.  In this case, we'll get `F=fn($g,
$h)` where `Tainted($g) = {$g, $a, $x}` and `Tainted($h) = {$h, $a,
$x}`.  Both of these sets contain exactly one bound variable from each
side, so we'll map them both to `&a`, resulting in `fn(&a, &a)`, which
is the desired result.

### Shortcomings and correctness

You may be wondering whether this algorithm is correct.  The answer is
"sort of".  There are definitely cases where they fail to compute a
result even though a correct result exists.  I believe, though, that
if they succeed, then the result is valid, and I will attempt to
convince you.  The basic argument is that the "pre-replacement" step
computes a set of constraints.  The replacements, then, attempt to
satisfy those constraints, using bound identifiers where needed.

For now I will briefly go over the cases for LUB/GLB and identify
their intent:

- LUB:
  - The region variables that are substituted in place of bound regions
    are intended to collect constraints on those bound regions.
  - If Tainted(R) contains only values in V, then this region is unconstrained
    and can therefore be generalized, otherwise it cannot.
- GLB:
  - The region variables that are substituted in place of bound regions
    are intended to collect constraints on those bound regions.
  - If Tainted(R) contains exactly one variable from each side, and
    only variables in V, that indicates that those two bound regions
    must be equated.
  - Otherwise, if Tainted(R) references any variables from left or right
    side, then it is trying to combine a bound region with a free one or
    multiple bound regions, so we need to select fresh bound regions.

Sorry this is more of a shorthand to myself.  I will try to write up something
more convincing in the future.

#### Where are the algorithms wrong?

- The pre-replacement computation can fail even though using a
  bound-region would have succeeded.
- We will compute GLB(fn(fn($a)), fn(fn($b))) as fn($c) where $c is the
  GLB of $a and $b.  But if inference finds that $a and $b must be mapped
  to regions without a GLB, then this is effectively a failure to compute
  the GLB.  However, the result `fn<$c>(fn($c))` is a valid GLB.

     */
}
