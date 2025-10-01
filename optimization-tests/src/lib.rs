//! Checking compilation with optimizations for the `assert_unchecked` range tests in `unsafe_api`.
//!
//! ```rust,compile_fail
//! const LOWER_BOUND: usize = 15;
//!
//! let bounded = bounded_integer::BoundedUsize::<LOWER_BOUND, 20>::new_saturating(15);
//! let bounded = core::hint::black_box(bounded);
//!
//! optimization_tests::assert_optimized_out!(
//!     bounded.get() <= LOWER_BOUND
//! )
//! optimization_tests::assert_optimized_out!(
//!     *bounded.get_ref() <= LOWER_BOUND
//! )
//! optimization_tests::assert_optimized_out!(
//!     *unsafe { bounded.get_mut() } <= LOWER_BOUND
//! )
//! ```

// We should not export anything when not running tests
#![cfg(test)]

use bounded_integer::BoundedUsize;

unsafe extern "C" {
    /// This function should fail to link if range checks are not optimized out as expected.
    safe fn should_be_optimized_out() -> !;
}

/// Ensure that LLVM has enough information at compile-time to statically ensure that the
/// condition is true. If LLVM cannot statically ensure that the condition is true and
/// emits a run-time branch, the binary will contain a call to a non-existent `extern`
/// function and fail to link.
#[macro_export]
macro_rules! optimizer_assert_guaranteed {
    ($cond:expr) => {
        if !$cond {
            $crate::should_be_optimized_out();
        }
    };
}

/// Assert that the inner value is statically enforced to be between the bounds `LO` and
/// `HI` inclusive.
fn range_check_optimized_out_usize<const LO: usize, const HI: usize>(expected: usize) {
    let i = core::hint::black_box(BoundedUsize::<LO, HI>::new(expected).unwrap());
    optimizer_assert_guaranteed!(i.get() >= LO && i.get() <= HI);
    let i = core::hint::black_box(i);
    optimizer_assert_guaranteed!(*i.get_ref() >= LO && *i.get_ref() <= HI);
    let mut i = core::hint::black_box(i);
    optimizer_assert_guaranteed!(*unsafe { i.get_mut() } >= LO && *unsafe { i.get_mut() } <= HI);

    assert_eq!(
        core::hint::black_box(i.get()),
        core::hint::black_box(expected)
    );
}

#[test]
fn range_check_optimized_out() {
    range_check_optimized_out_usize::<10, 20>(15);
    range_check_optimized_out_usize::<20, 20>(20);
    range_check_optimized_out_usize::<1, { usize::MAX - 1 }>(usize::MAX - 1);
}
