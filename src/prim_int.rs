use core::mem::transmute_copy;
use core::num::NonZero;

/// Marker trait for primitive integers.
pub trait PrimInt: sealed::Sealed {}

mod sealed {
    use super::PrimInt;

    // Not public API.
    pub trait Sealed: 'static + Sized + Copy {
        type NonZero: Into<Self>;
        type Unsigned: Sealed;
        fn checked_add_unsigned(self, rhs: Self::Unsigned) -> Option<Self>;
        fn checked_sub_unsigned(self, rhs: Self::Unsigned) -> Option<Self>;
        fn rem_euclid_unsigned(self, rhs: <Self::Unsigned as Sealed>::NonZero) -> Self::Unsigned;
        fn truncate<T: PrimInt + Into<Self>>(self) -> T;
        fn nonzero_from<T: PrimInt + Into<Self>>(val: T::NonZero) -> Self::NonZero;
    }
}
pub(crate) use sealed::Sealed;

gen! {
    u8 i8,
    u16 i16,
    u32 i32,
    u64 i64,
    u128 i128,
    usize isize,
}

macro_rules! gen {
    ($($unsigned:ident $signed:ident,)*) => { $(
        pub(crate) mod $unsigned {
            use core::num::NonZero;

            pub(crate) type Unsigned = $unsigned;
            #[allow(unused)] // only needed for non-u8
            pub(crate) type Signed = $signed;
            #[allow(unused)] // only needed for non-u8
            pub(crate) use super::$signed as signed;

            pub(crate) const fn checked_add_unsigned(lhs: Unsigned, rhs: Unsigned) -> Option<Unsigned> {
                lhs.checked_add(rhs)
            }
            pub(crate) const fn checked_sub_unsigned(lhs: Unsigned, rhs: Unsigned) -> Option<Unsigned> {
                lhs.checked_sub(rhs)
            }
            pub(crate) const fn rem_euclid_unsigned(lhs: Unsigned, rhs: NonZero<Unsigned>) -> Unsigned {
                lhs.rem_euclid(rhs.get())
            }
        }
        pub(crate) mod $signed {
            use core::num::NonZero;

            pub(crate) type Unsigned = $unsigned;
            #[allow(unused)] // only needed for non-u8
            pub(crate) type Signed = $signed;
            #[allow(unused)] // only needed for non-u8
            pub(crate) use super::$signed as signed;

            pub(crate) const fn checked_add_unsigned(lhs: Signed, rhs: Unsigned) -> Option<Signed> {
                lhs.checked_add_unsigned(rhs)
            }
            pub(crate) const fn checked_sub_unsigned(lhs: Signed, rhs: Unsigned) -> Option<Signed> {
                lhs.checked_sub_unsigned(rhs)
            }
            pub(crate) const fn rem_euclid_unsigned(lhs: Signed, rhs: NonZero<Unsigned>) -> Unsigned {
                // In my benchmarks, this is faster than methods involving widening.
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
    )* gen_impl!($($unsigned $signed)*); };
}
use gen;

macro_rules! gen_impl {
    ($($ty:ident)*) => { $(
        impl PrimInt for $ty {}

        impl Sealed for $ty {
            type NonZero = NonZero<$ty>;
            type Unsigned = $ty::Unsigned;
            fn checked_add_unsigned(self, rhs: Self::Unsigned) -> Option<Self> {
                $ty::checked_add_unsigned(self, rhs)
            }
            fn checked_sub_unsigned(self, rhs: Self::Unsigned) -> Option<Self> {
                $ty::checked_sub_unsigned(self, rhs)
            }
            fn rem_euclid_unsigned(self, rhs: NonZero<Self::Unsigned>) -> Self::Unsigned {
                $ty::rem_euclid_unsigned(self, rhs)
            }
            fn truncate<T: PrimInt + Into<Self>>(self) -> T {
                match size_of::<T>() {
                    1 => unsafe { transmute_copy(&(self as u8)) },
                    2 => unsafe { transmute_copy(&(self as u16)) },
                    4 => unsafe { transmute_copy(&(self as u32)) },
                    8 => unsafe { transmute_copy(&(self as u64)) },
                    16 => unsafe { transmute_copy(&(self as u128)) },
                    _ => unreachable!(),
                }
            }
            fn nonzero_from<T: PrimInt + Into<Self>>(val: T::NonZero) -> Self::NonZero {
                let val: T = val.into();
                let val: Self = val.into();
                unsafe { NonZero::new_unchecked(val) }
            }
        }
    )* };
}
use gen_impl;
