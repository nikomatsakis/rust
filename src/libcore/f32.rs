/*
Module: f32

Floating point operations and constants for `f32`
*/

// PORT

import cmath::c_float::*;
import cmath::c_float_targ_consts::*;

type t = f32;

// These are not defined inside consts:: for consistency with
// the integer types

/* Const: NaN */
const NaN: f32 = 0.0_f32/0.0_f32;

/* Const: infinity */
const infinity: f32 = 1.0_f32/0.0_f32;

/* Const: neg_infinity */
const neg_infinity: f32 = -1.0_f32/0.0_f32;

/* Predicate: isNaN */
pure fn is_NaN(f: f32) -> bool { f != f }

/* Function: add */
pure fn add(x: f32, y: f32) -> f32 { ret x + y; }

/* Function: sub */
pure fn sub(x: f32, y: f32) -> f32 { ret x - y; }

/* Function: mul */
pure fn mul(x: f32, y: f32) -> f32 { ret x * y; }

/* Function: div */
pure fn div(x: f32, y: f32) -> f32 { ret x / y; }

/* Function: rem */
pure fn rem(x: f32, y: f32) -> f32 { ret x % y; }

/* Predicate: lt */
pure fn lt(x: f32, y: f32) -> bool { ret x < y; }

/* Predicate: le */
pure fn le(x: f32, y: f32) -> bool { ret x <= y; }

/* Predicate: eq */
pure fn eq(x: f32, y: f32) -> bool { ret x == y; }

/* Predicate: ne */
pure fn ne(x: f32, y: f32) -> bool { ret x != y; }

/* Predicate: ge */
pure fn ge(x: f32, y: f32) -> bool { ret x >= y; }

/* Predicate: gt */
pure fn gt(x: f32, y: f32) -> bool { ret x > y; }

// FIXME replace the predicates below with llvm intrinsics or calls
// to the libmath macros in the rust runtime for performance

/*
Predicate: is_positive

Returns true if `x` is a positive number, including +0.0f320 and +Infinity.
 */
pure fn is_positive(x: f32) -> bool
    { ret x > 0.0f32 || (1.0f32/x) == infinity; }

/*
Predicate: is_negative

Returns true if `x` is a negative number, including -0.0f320 and -Infinity.
 */
pure fn is_negative(x: f32) -> bool
    { ret x < 0.0f32 || (1.0f32/x) == neg_infinity; }

/*
Predicate: is_nonpositive

Returns true if `x` is a negative number, including -0.0f320 and -Infinity.
(This is the same as `f32::negative`.)
*/
pure fn is_nonpositive(x: f32) -> bool {
  ret x < 0.0f32 || (1.0f32/x) == neg_infinity;
}

/*
Predicate: nonnegative

Returns true if `x` is a positive number, including +0.0f320 and +Infinity.
(This is the same as `f32::positive`.)
*/
pure fn is_nonnegative(x: f32) -> bool {
  ret x > 0.0f32 || (1.0f32/x) == infinity;
}

/*
Predicate: is_zero

Returns true if `x` is a zero number (positive or negative zero)
*/
pure fn is_zero(x: f32) -> bool {
    ret x == 0.0f32 || x == -0.0f32;
}

/*
Predicate: is_infinite

Returns true if `x`is an infinite numer
*/
pure fn is_infinite(x: f32) -> bool {
    ret x == infinity || x == neg_infinity;
}

/*
Predicate: is_finite

Returns true if `x`is a finite numer
*/
pure fn is_finite(x: f32) -> bool {
    ret !(is_NaN(x) || is_infinite(x));
}

// FIXME add is_normal, is_subnormal, and fpclassify

/* Module: consts */
mod consts {

    // FIXME replace with mathematical constants from cmath

    /*
    Const: pi

    Archimedes' constant
    */
    const pi: f32 = 3.14159265358979323846264338327950288_f32;

    /*
    Const: frac_pi_2

    pi/2.0
    */
    const frac_pi_2: f32 = 1.57079632679489661923132169163975144_f32;

    /*
    Const: frac_pi_4

    pi/4.0
    */
    const frac_pi_4: f32 = 0.785398163397448309615660845819875721_f32;

    /*
    Const: frac_1_pi

    1.0/pi
    */
    const frac_1_pi: f32 = 0.318309886183790671537767526745028724_f32;

    /*
    Const: frac_2_pi

    2.0/pi
    */
    const frac_2_pi: f32 = 0.636619772367581343075535053490057448_f32;

    /*
    Const: frac_2_sqrtpi

    2.0/sqrt(pi)
    */
    const frac_2_sqrtpi: f32 = 1.12837916709551257389615890312154517_f32;

    /*
    Const: sqrt2

    sqrt(2.0)
    */
    const sqrt2: f32 = 1.41421356237309504880168872420969808_f32;

    /*
    Const: frac_1_sqrt2

    1.0/sqrt(2.0)
    */
    const frac_1_sqrt2: f32 = 0.707106781186547524400844362104849039_f32;

    /*
    Const: e

    Euler's number
    */
    const e: f32 = 2.71828182845904523536028747135266250_f32;

    /*
    Const: log2_e

    log2(e)
    */
    const log2_e: f32 = 1.44269504088896340735992468100189214_f32;

    /*
    Const: log10_e

    log10(e)
    */
    const log10_e: f32 = 0.434294481903251827651128918916605082_f32;

    /*
    Const: ln_2

    ln(2.0)
    */
    const ln_2: f32 = 0.693147180559945309417232121458176568_f32;

    /*
    Const: ln_10

    ln(10.0)
    */
    const ln_10: f32 = 2.30258509299404568401799145468436421_f32;
}

pure fn signbit(x: f32) -> int {
    if is_negative(x) { ret 1; } else { ret 0; }
}

#[cfg(target_os="linux")]
#[cfg(target_os="macos")]
#[cfg(target_os="win32")]
pure fn logarithm(n: f32, b: f32) -> f32 {
    // FIXME check if it is good to use log2 instead of ln here;
    // in theory should be faster since the radix is 2
    ret log2(n) / log2(b);
}

#[cfg(target_os="freebsd")]
pure fn logarithm(n: f32, b: f32) -> f32 {
    ret ln(n) / ln(b);
}

#[cfg(target_os="freebsd")]
pure fn log2(n: f32) -> f32 {
    ret ln(n) / consts::ln_2;
}

//
// Local Variables:
// mode: rust
// fill-column: 78;
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// End:
//
