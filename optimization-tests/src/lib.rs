//! Checking compilation with optimizations for the `assert_unchecked` range tests in `unsafe_api`.
//!
//! > *TODO*: Rust seems to ignore optimization for doctests even if they are specified in the profile,
//! > and even if running `cargo test --doc --release`. The `compile_fail` test _does_ correctly fail
//! > to compile, but that is probably true even for out-of-range comparisons.
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

unsafe extern "C" {
    // This function should fail to link if range checks are not optimized out as expected.
    pub safe fn should_be_optimized_out() -> !;
}

#[macro_export]
macro_rules! assert_optimized_out {
    ($cond:expr) => {
        if $cond {
            $crate::should_be_optimized_out();
        }
    }
}

#[cfg(test)]
mod tests {
    use bounded_integer::BoundedUsize;
    use crate::assert_optimized_out;

    fn range_check_optimized_out_usize<const LO: usize, const HI: usize>(expected: usize) {
        let i = core::hint::black_box(BoundedUsize::<LO, HI>::new(expected).unwrap());
        assert_optimized_out!(i.get() < LO || i.get() > HI);
        let i = core::hint::black_box(i);
        assert_optimized_out!(*i.get_ref() < LO || i.get() > HI);
        let mut i = core::hint::black_box(i);
        assert_optimized_out!(*unsafe { i.get_mut() } < LO || *unsafe { i.get_mut() } > HI);

        assert_eq!(core::hint::black_box(i.get()), core::hint::black_box(expected));
    }

    #[test]
    fn range_check_optimized_out() {
        range_check_optimized_out_usize::<10, 20>(15);
        range_check_optimized_out_usize::<20, 20>(20);
        range_check_optimized_out_usize::<1, { usize::MAX - 1 }>(usize::MAX - 1);
    }
}
