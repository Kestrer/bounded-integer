#![expect(clippy::must_use_candidate)]

use core::fmt::{self, Display, Formatter};
use core::num::NonZero;

/// An error returned when a checked conversion into a bounded integer fails.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct TryFromError;

impl Display for TryFromError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str("out of range conversion to bounded integer attempted")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryFromError {}

#[must_use]
pub fn try_from_error() -> TryFromError {
    TryFromError
}

pub trait PrimInt {
    type Signed;
    type Unsigned;
}

pub type Signed<T> = <T as PrimInt>::Signed;
pub type Unsigned<T> = <T as PrimInt>::Unsigned;

generate! {
    u8 i8,
    u16 i16,
    u32 i32,
    u64 i64,
    u128 i128,
    usize isize,
}

macro_rules! generate {
    ($($unsigned:ident $signed:ident,)*) => { $(
        impl PrimInt for $unsigned {
            type Signed = $signed;
            type Unsigned = $unsigned;
        }
        impl PrimInt for $signed {
            type Signed = $signed;
            type Unsigned = $unsigned;
        }

        impl crate::__private::Dispatch<$unsigned> {
            pub const fn checked_add_unsigned(lhs: $unsigned, rhs: $unsigned) -> Option<$unsigned> {
                lhs.checked_add(rhs)
            }
            pub const fn checked_sub_unsigned(lhs: $unsigned, rhs: $unsigned) -> Option<$unsigned> {
                lhs.checked_sub(rhs)
            }
            pub const fn rem_euclid_unsigned(lhs: $unsigned, rhs: NonZero<$unsigned>) -> $unsigned {
                lhs.rem_euclid(rhs.get())
            }
        }
        impl crate::__private::Dispatch<$signed> {
            pub const fn checked_add_unsigned(lhs: $signed, rhs: $unsigned) -> Option<$signed> {
                lhs.checked_add_unsigned(rhs)
            }
            pub const fn checked_sub_unsigned(lhs: $signed, rhs: $unsigned) -> Option<$signed> {
                lhs.checked_sub_unsigned(rhs)
            }
            pub const fn rem_euclid_unsigned(lhs: $signed, rhs: NonZero<$unsigned>) -> $unsigned {
                // In my benchmarks, this is faster than methods involving widening.
                #[expect(clippy::cast_possible_wrap)]
                #[expect(clippy::cast_sign_loss)]
                if 0 <= lhs {
                    // If `lhs` is nonnegative, just use regular unsigned remainder.
                    (lhs as $unsigned).rem_euclid(rhs.get())
                } else if 0 <= rhs.get() as $signed {
                    // If `rhs` is small enough to fit in a signed type, use regular `rem_euclid`.
                    // We know the result is nonnegative, so we can cast to the unsigned type.
                    lhs.rem_euclid(rhs.get() as $signed) as $unsigned
                } else {
                    // Otherwise, `lhs` is negative and `rhs` is larger than all signed values. We
                    // can therefore add `rhs` to `lhs` and get an unsigned value without overflow,
                    // which won’t affect the result.
                    rhs.get().checked_add_signed(lhs).unwrap().rem_euclid(rhs.get())
                }
            }
        }
    )* };
}
use generate;

// We don’t implement for `usize` because we don’t get `(wide usize): From<usize>` impls which
// makes things difficult trait-wise.
pub trait HasWide {
    type Wide;
}

pub type Wide<T> = <T as HasWide>::Wide;

impl HasWide for u8 {
    type Wide = u16;
}
impl HasWide for u16 {
    type Wide = u32;
}
impl HasWide for u32 {
    type Wide = u64;
}
impl HasWide for u64 {
    type Wide = u128;
}
impl HasWide for i8 {
    type Wide = i16;
}
impl HasWide for i16 {
    type Wide = i32;
}
impl HasWide for i32 {
    type Wide = i64;
}
impl HasWide for i64 {
    type Wide = i128;
}
