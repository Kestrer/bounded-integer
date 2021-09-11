macro_rules! bin_op_variations {
    ([$($generics:tt)*] $lhs:ty, $rhs:ty, $op:ident::$method:ident/$op_assign:ident::$method_assign:ident) => {
        impl<$($generics)*> $op<$rhs> for &$lhs {
            type Output = $lhs;
            #[inline]
            fn $method(self, rhs: $rhs) -> Self::Output {
                <$lhs as $op<$rhs>>::$method(*self, rhs)
            }
        }
        impl<$($generics)*> $op<&$rhs> for $lhs {
            type Output = $lhs;
            #[inline]
            fn $method(self, rhs: &$rhs) -> Self::Output {
                <$lhs as $op<$rhs>>::$method(self, *rhs)
            }
        }
        impl<$($generics)*> $op<&$rhs> for &$lhs {
            type Output = $lhs;
            #[inline]
            fn $method(self, rhs: &$rhs) -> Self::Output {
                <$lhs as $op<$rhs>>::$method(*self, *rhs)
            }
        }

        impl<$($generics)*> $op_assign<$rhs> for $lhs {
            #[inline]
            fn $method_assign(&mut self, rhs: $rhs) {
                *self = <Self as $op<$rhs>>::$method(*self, rhs);
            }
        }
        impl<$($generics)*> $op_assign<&$rhs> for $lhs {
            #[inline]
            fn $method_assign(&mut self, rhs: &$rhs) {
                *self = <Self as $op<$rhs>>::$method(*self, *rhs);
            }
        }
    }
}

macro_rules! impl_bin_op {
    ($op:ident::$method:ident/$op_assign:ident::$method_assign:ident, $desc:literal) => {
        use core::ops::{$op, $op_assign};

        impl<const MIN: Inner, const MAX: Inner> $op<Inner> for Bounded<MIN, MAX> {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: Inner) -> Self::Output {
                Self::new(self.get().$method(rhs))
                    .expect(concat!("Attempted to ", $desc, " out of range"))
            }
        }
        bin_op_variations!(
            [const MIN: Inner, const MAX: Inner]
            Bounded<MIN, MAX>, Inner, $op::$method/$op_assign::$method_assign
        );

        impl<const MIN: Inner, const MAX: Inner> $op<Bounded<MIN, MAX>> for Inner {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: Bounded<MIN, MAX>) -> Self::Output {
                self.$method(rhs.get())
            }
        }
        bin_op_variations! {
            [const MIN: Inner, const MAX: Inner]
            Inner, Bounded<MIN, MAX>, $op::$method/$op_assign::$method_assign
        }

        impl<const L_MIN: Inner, const L_MAX: Inner, const R_MIN: Inner, const R_MAX: Inner>
            $op<Bounded<R_MIN, R_MAX>> for Bounded<L_MIN, L_MAX>
        {
            type Output = Self;
             #[inline]
            fn $method(self, rhs: Bounded<R_MIN, R_MAX>) -> Self::Output {
                Self::new(self.get().$method(rhs))
                    .expect(concat!("Attempted to ", $desc, " out of range"))
            }
        }
        bin_op_variations! {
            [const L_MIN: Inner, const L_MAX: Inner, const R_MIN: Inner, const R_MAX: Inner]
            Bounded<L_MIN, L_MAX>, Bounded<R_MIN, R_MAX>, $op::$method/$op_assign::$method_assign
        }
    };
}

#[cfg(test)]
macro_rules! test_arithmetic {
    (ops($($op:tt $op_assign:tt)*) infallibles($($infallible:ident)*) fallibles($($fallible:ident)*)) => {
        $( #[allow(const_item_mutation)] {
            let _: Bounded = Bounded::MIN $op 0;
            let _: Bounded = &Bounded::MIN $op 0;
            let _: Bounded = Bounded::MIN $op &0;
            let _: Bounded = &Bounded::MIN $op &0;
            let _: Inner = 0 $op Bounded::MIN;
            let _: Inner = 0 $op &Bounded::MIN;
            let _: Inner = &0 $op Bounded::MIN;
            let _: Inner = &0 $op &Bounded::MIN;
            let _: Bounded = Bounded::MIN $op Bounded::MIN;
            let _: Bounded = &Bounded::MIN $op Bounded::MIN;
            let _: Bounded = Bounded::MIN $op &Bounded::MIN;
            let _: Bounded = &Bounded::MIN $op &Bounded::MIN;
            *&mut Bounded::MIN $op_assign 0;
            *&mut Bounded::MIN $op_assign &0;
            *&mut Bounded::MIN $op_assign Bounded::MIN;
            *&mut Bounded::MIN $op_assign &Bounded::MIN;
            *&mut 0 $op_assign Bounded::MIN;
            *&mut 0 $op_assign &Bounded::MIN;
        } )*
        $(let _: Bounded = Bounded::MIN.$infallible(0);)*
        $(let _: Option<Bounded> = Bounded::MIN.$fallible(0);)*
        let _: Option<Bounded> = Bounded::MIN.checked_neg();
    };
    (signed $($tt:tt)*) => {
        test_arithmetic!($($tt)*);

        let _: Bounded = Bounded::MIN.abs();
        let _: Option<Bounded> = Bounded::MIN.checked_abs();

        let _: Bounded = -Bounded::MIN;
        let _: Bounded = -&Bounded::MIN;
        let _: Bounded = Bounded::MIN.saturating_neg();
    };
}

macro_rules! impl_fmt_traits {
    ($($trait:ident),*) => { $(
        impl<const MIN: Inner, const MAX: Inner> fmt::$trait for Bounded<MIN, MAX> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                fmt::$trait::fmt(&self.get(), f)
            }
        }
    )* }
}

macro_rules! define_bounded_integers {
    ($(
        $name:ident $inner:ident $(signed $([$signed:ident])?)? -> $($into:ident)*,
    )*) => { $( mod $inner {
        use core::borrow::Borrow;
        use core::cmp;
        use core::fmt;
        use core::iter;
        use core::str::FromStr;

        use crate::parse::{ParseError, FromStrRadix};

        type Inner = core::primitive::$inner;

        /// An
        #[doc = concat!("[`", stringify!($inner), "`]")]
        /// constrained to be in the range `MIN..=MAX`.
        #[cfg_attr(doc_cfg, doc(cfg(feature = "types")))]
        #[repr(transparent)]
        #[derive(Debug, Hash, Clone, Copy, Eq, Ord)]
        pub struct Bounded<const MIN: Inner, const MAX: Inner>(Inner);

        impl<const MIN: Inner, const MAX: Inner> Bounded<MIN, MAX> {
            /// The smallest value this bounded integer can contain.
            pub const MIN_VALUE: Inner = MIN;
            /// The largest value that this bounded integer can contain.
            pub const MAX_VALUE: Inner = MAX;

            /// The smallest value of the bounded integer.
            pub const MIN: Self = Self(MIN);
            /// The largest value of the bounded integer.
            pub const MAX: Self = Self(MAX);

            /// Creates a bounded integer without checking the value.
            ///
            /// # Safety
            ///
            /// The value must not be outside the valid range of values; it must not be less than
            /// [`MIN_VALUE`](Self::MIN_VALUE) or greater than [`MAX_VALUE`](Self::MAX_VALUE).
            #[must_use]
            pub const unsafe fn new_unchecked(n: Inner) -> Self {
                // Doesn't work in `const fn`:
                // debug_assert!(Self::in_range(n));
                Self(n)
            }

            /// Creates a shared reference to a bounded integer from a shared reference to a
            /// primitive.
            ///
            /// # Safety
            ///
            /// The value must not be outside the valid range of values; it must not be less than
            /// [`MIN_VALUE`](Self::MIN_VALUE) or greater than [`MAX_VALUE`](Self::MAX_VALUE).
            #[must_use]
            pub unsafe fn new_ref_unchecked(n: &Inner) -> &Self {
                debug_assert!(Self::in_range(*n));
                &*<*const _>::cast(n)
            }

            /// Creates a mutable reference to a bounded integer from a mutable reference to a
            /// primitive.
            ///
            /// # Safety
            ///
            /// The value must not be outside the valid range of values; it must not be less than
            /// [`MIN_VALUE`](Self::MIN_VALUE) or greater than [`MAX_VALUE`](Self::MAX_VALUE).
            #[must_use]
            pub unsafe fn new_mut_unchecked(n: &mut Inner) -> &mut Self {
                debug_assert!(Self::in_range(*n));
                &mut *<*mut _>::cast(n)
            }

            /// Checks whether the given value is in the range of the bounded integer.
            #[must_use]
            #[inline]
            pub const fn in_range(n: Inner) -> bool {
                n >= Self::MIN_VALUE && n <= Self::MAX_VALUE
            }

            /// Creates a bounded integer if the given value is within the range
            /// [[`MIN`](Self::MIN), [`MAX`](Self::MAX)].
            #[must_use]
            #[inline]
            pub const fn new(n: Inner) -> Option<Self> {
                if Self::in_range(n) {
                    Some(Self(n))
                } else {
                    None
                }
            }

            /// Creates a reference to a bounded integer from a reference to a primitive if the
            /// given value is within the range [[`MIN`](Self::MIN), [`MAX`](Self::MAX)].
            #[must_use]
            #[inline]
            pub fn new_ref(n: &Inner) -> Option<&Self> {
                Self::in_range(*n).then(|| {
                    // SAFETY: We just asserted that the value is in range.
                    unsafe { Self::new_ref_unchecked(n) }
                })
            }

            /// Creates a mutable reference to a bounded integer from a mutable reference to a
            /// primitive if the given value is within the range
            /// [[`MIN`](Self::MIN), [`MAX`](Self::MAX)].
            #[must_use]
            #[inline]
            pub fn new_mut(n: &mut Inner) -> Option<&mut Self> {
                Self::in_range(*n).then(move || {
                    // SAFETY: We just asserted that the value is in range.
                    unsafe { Self::new_mut_unchecked(n) }
                })
            }

            /// Creates a bounded integer by setting the value to [`MIN`](Self::MIN) or
            /// [`MAX`](Self::MAX) if it is too low or too high respectively.
            #[must_use]
            #[inline]
            pub const fn new_saturating(n: Inner) -> Self {
                if n < Self::MIN_VALUE {
                    Self::MIN
                } else if n > Self::MAX_VALUE {
                    Self::MAX
                } else {
                    Self(n)
                }
            }

            /// Converts a string slice in a given base to the bounded integer.
            ///
            /// # Panics
            ///
            /// Panics if `radix` is below 2 or above 36.
            pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseError> {
                let value = <Inner as FromStrRadix>::from_str_radix(src, radix)?;
                if value < Self::MIN_VALUE {
                    Err(crate::parse::error_below_min())
                } else if value > Self::MAX_VALUE {
                    Err(crate::parse::error_above_max())
                } else {
                    Ok(unsafe { Self::new_unchecked(value) })
                }
            }

            /// Returns the value of the bounded integer as a primitive type.
            #[must_use]
            #[inline]
            pub const fn get(self) -> Inner {
                self.0
            }

            /// Returns a shared reference to the value of the bounded integer.
            #[must_use]
            #[inline]
            pub const fn get_ref(&self) -> &Inner {
                &self.0
            }

            /// Returns a mutable reference to the value of the bounded integer.
            ///
            /// # Safety
            ///
            /// This value must never be set to a value beyond the range of the bounded integer.
            #[must_use]
            #[inline]
            pub unsafe fn get_mut(&mut self) -> &mut Inner {
                &mut *<*mut _>::cast(self)
            }

            $($(if $signed)?
                /// Computes the absolute value of `self`, panicking if it is out of range.
                #[must_use]
                #[inline]
                pub fn abs(self) -> Self {
                    Self::new(self.get().abs()).expect("Absolute value out of range")
                }
            )*

            /// Raises `self` to the power of `exp`, using exponentiation by squaring. Panics if it
            /// is out of range.
            #[must_use]
            #[inline]
            pub fn pow(self, exp: u32) -> Self {
                Self::new(self.get().pow(exp)).expect("Value raised to power out of range")
            }

            /// Calculates the quotient of Euclidean division of `self` by `rhs`. Panics if `rhs`
            /// is 0 or the result is out of range.
            #[must_use]
            #[inline]
            pub fn div_euclid(self, rhs: Inner) -> Self {
                Self::new(self.get().div_euclid(rhs)).expect("Attempted to divide out of range")
            }

            /// Calculates the least nonnegative remainder of `self (mod rhs)`. Panics if `rhs` is 0
            /// or the result is out of range.
            #[must_use]
            #[inline]
            pub fn rem_euclid(self, rhs: Inner) -> Self {
                Self::new(self.get().rem_euclid(rhs))
                    .expect("Attempted to divide with remainder out of range")
            }

            /// Checked integer addition.
            #[must_use]
            #[inline]
            pub const fn checked_add(self, rhs: Inner) -> Option<Self> {
                match self.get().checked_add(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Saturating integer addition.
            #[must_use]
            #[inline]
            pub const fn saturating_add(self, rhs: Inner) -> Self {
                Self::new_saturating(self.get().saturating_add(rhs))
            }

            /// Checked integer subtraction.
            #[must_use]
            #[inline]
            pub const fn checked_sub(self, rhs: Inner) -> Option<Self> {
                match self.get().checked_sub(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Saturating integer subtraction.
            #[must_use]
            #[inline]
            pub const fn saturating_sub(self, rhs: Inner) -> Self {
                Self::new_saturating(self.get().saturating_sub(rhs))
            }

            /// Checked integer multiplication.
            #[must_use]
            #[inline]
            pub const fn checked_mul(self, rhs: Inner) -> Option<Self> {
                match self.get().checked_mul(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Saturating integer multiplication.
            #[must_use]
            #[inline]
            pub const fn saturating_mul(self, rhs: Inner) -> Self {
                Self::new_saturating(self.get().saturating_mul(rhs))
            }

            /// Checked integer division.
            #[must_use]
            #[inline]
            pub const fn checked_div(self, rhs: Inner) -> Option<Self> {
                match self.get().checked_div(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Checked Euclidean division.
            #[must_use]
            #[inline]
            pub const fn checked_div_euclid(self, rhs: Inner) -> Option<Self> {
                match self.get().checked_div_euclid(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Checked integer remainder.
            #[must_use]
            #[inline]
            pub const fn checked_rem(self, rhs: Inner) -> Option<Self> {
                match self.get().checked_rem(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Checked Euclidean remainder.
            #[must_use]
            #[inline]
            pub const fn checked_rem_euclid(self, rhs: Inner) -> Option<Self> {
                match self.get().checked_rem_euclid(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Checked negation.
            #[must_use]
            #[inline]
            pub const fn checked_neg(self) -> Option<Self> {
                match self.get().checked_neg() {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            $($(if $signed)?
                /// Saturating negation.
                #[must_use]
                #[inline]
                pub const fn saturating_neg(self) -> Self {
                    Self::new_saturating(self.get().saturating_neg())
                }

                /// Checked absolute value.
                #[must_use]
                #[inline]
                pub const fn checked_abs(self) -> Option<Self> {
                    match self.get().checked_abs() {
                        Some(val) => Self::new(val),
                        None => None,
                    }
                }

                /// Saturating absolute value.
                #[must_use]
                #[inline]
                pub const fn saturating_abs(self) -> Self {
                    Self::new_saturating(self.get().saturating_abs())
                }
            )*

            /// Checked exponentiation.
            #[must_use]
            #[inline]
            pub const fn checked_pow(self, rhs: u32) -> Option<Self> {
                match self.get().checked_pow(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Saturating exponentiation.
            #[must_use]
            #[inline]
            pub const fn saturating_pow(self, rhs: u32) -> Self {
                Self::new_saturating(self.get().saturating_pow(rhs))
            }
        }

        // === Operators ===

        impl_bin_op!(Add::add/AddAssign::add_assign, "add");
        impl_bin_op!(Sub::sub/SubAssign::sub_assign, "subtract");
        impl_bin_op!(Mul::mul/MulAssign::mul_assign, "multiply");
        impl_bin_op!(Div::div/DivAssign::div_assign, "divide");
        impl_bin_op!(Rem::rem/RemAssign::rem_assign, "take remainder");

        $($(if $signed)?
            use core::ops::Neg;

            impl<const MIN: Inner, const MAX: Inner> Neg for Bounded<MIN, MAX> {
                type Output = Self;
                #[inline]
                fn neg(self) -> Self::Output {
                    Self::new(-self.get())
                        .expect("Attempted to negate out of range")
                }
            }
            impl<const MIN: Inner, const MAX: Inner> Neg for &Bounded<MIN, MAX> {
                type Output = Bounded<MIN, MAX>;
                #[inline]
                fn neg(self) -> Self::Output {
                    -*self
                }
            }
        )?

        // === Comparisons ===

        impl<const MIN: Inner, const MAX: Inner> PartialEq<Inner> for Bounded<MIN, MAX> {
            #[inline]
            fn eq(&self, other: &Inner) -> bool {
                self.get() == *other
            }
        }
        impl<const MIN: Inner, const MAX: Inner> PartialEq<Bounded<MIN, MAX>> for Inner {
            #[inline]
            fn eq(&self, other: &Bounded<MIN, MAX>) -> bool {
                *self == other.get()
            }
        }
        impl<const A_MIN: Inner, const A_MAX: Inner, const B_MIN: Inner, const B_MAX: Inner>
            PartialEq<Bounded<B_MIN, B_MAX>> for Bounded<A_MIN, A_MAX>
        {
            #[inline]
            fn eq(&self, other: &Bounded<B_MIN, B_MAX>) -> bool {
                self.get() == other.get()
            }
        }

        impl<const MIN: Inner, const MAX: Inner> PartialOrd<Inner> for Bounded<MIN, MAX> {
            #[inline]
            fn partial_cmp(&self, other: &Inner) -> Option<cmp::Ordering> {
                self.get().partial_cmp(other)
            }
        }
        impl<const MIN: Inner, const MAX: Inner> PartialOrd<Bounded<MIN, MAX>> for Inner {
            #[inline]
            fn partial_cmp(&self, other: &Bounded<MIN, MAX>) -> Option<cmp::Ordering> {
                self.partial_cmp(&other.get())
            }
        }
        impl<const A_MIN: Inner, const A_MAX: Inner, const B_MIN: Inner, const B_MAX: Inner>
            PartialOrd<Bounded<B_MIN, B_MAX>> for Bounded<A_MIN, A_MAX>
        {
            #[inline]
            fn partial_cmp(&self, other: &Bounded<B_MIN, B_MAX>) -> Option<cmp::Ordering> {
                self.get().partial_cmp(&other.get())
            }
        }

        // === AsRef, Borrow ===

        impl<const MIN: Inner, const MAX: Inner> AsRef<Inner> for Bounded<MIN, MAX> {
            #[inline]
            fn as_ref(&self) -> &Inner {
                self.get_ref()
            }
        }
        impl<const MIN: Inner, const MAX: Inner> Borrow<Inner> for Bounded<MIN, MAX> {
            #[inline]
            fn borrow(&self) -> &Inner {
                self.get_ref()
            }
        }

        // === Iterator traits ===

        // Sum bounded to bounded
        impl<const MIN: Inner, const MAX: Inner> iter::Sum for Bounded<MIN, MAX> {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.reduce(Add::add)
                    .unwrap_or_else(|| Self::new(0).expect("Attempted to sum to zero"))
            }
        }
        impl<'a, const MIN: Inner, const MAX: Inner> iter::Sum<&'a Self> for Bounded<MIN, MAX> {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.copied().sum()
            }
        }

        // Sum bounded to primitive
        impl<const MIN: Inner, const MAX: Inner> iter::Sum<Bounded<MIN, MAX>> for Inner {
            fn sum<I: Iterator<Item = Bounded<MIN, MAX>>>(iter: I) -> Self {
                iter.map(Bounded::get).sum()
            }
        }
        impl<'a, const MIN: Inner, const MAX: Inner> iter::Sum<&'a Bounded<MIN, MAX>> for Inner {
            fn sum<I: Iterator<Item = &'a Bounded<MIN, MAX>>>(iter: I) -> Self {
                iter.copied().sum()
            }
        }

        // Take product of bounded to bounded
        impl<const MIN: Inner, const MAX: Inner> iter::Product for Bounded<MIN, MAX> {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.reduce(Mul::mul)
                    .unwrap_or_else(|| Self::new(1).expect("Attempted to take product to one"))
            }
        }
        impl<'a, const MIN: Inner, const MAX: Inner> iter::Product<&'a Self> for Bounded<MIN, MAX> {
            fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.copied().product()
            }
        }

        // Take product of bounded to primitive
        impl<const MIN: Inner, const MAX: Inner> iter::Product<Bounded<MIN, MAX>> for Inner {
            fn product<I: Iterator<Item = Bounded<MIN, MAX>>>(iter: I) -> Self {
                iter.map(Bounded::get).product()
            }
        }
        impl<'a, const MIN: Inner, const MAX: Inner> iter::Product<&'a Bounded<MIN, MAX>> for Inner {
            fn product<I: Iterator<Item = &'a Bounded<MIN, MAX>>>(iter: I) -> Self {
                iter.copied().product()
            }
        }

        #[cfg(feature = "step_trait")]
        impl<const MIN: Inner, const MAX: Inner> iter::Step for Bounded<MIN, MAX> {
            #[inline]
            fn steps_between(start: &Self, end: &Self) -> Option<usize> {
                iter::Step::steps_between(&start.get(), &end.get())
            }
            #[inline]
            fn forward_checked(start: Self, count: usize) -> Option<Self> {
                iter::Step::forward_checked(start.get(), count).and_then(Self::new)
            }
            #[inline]
            fn backward_checked(start: Self, count: usize) -> Option<Self> {
                iter::Step::backward_checked(start.get(), count).and_then(Self::new)
            }
        }

        // === Parsing ===

        impl<const MIN: Inner, const MAX: Inner> FromStr for Bounded<MIN, MAX> {
            type Err = ParseError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                Self::from_str_radix(s, 10)
            }
        }

        // === Formatting ===

        impl_fmt_traits!(Binary, Display, LowerExp, LowerHex, Octal, UpperExp, UpperHex);

        // === Arbitrary ===

        #[cfg(feature = "arbitrary")]
        use arbitrary::{Arbitrary, Unstructured};

        #[cfg(feature = "arbitrary")]
        impl<'a, const MIN: Inner, const MAX: Inner> Arbitrary<'a> for Bounded<MIN, MAX> {
            fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
                Self::new(u.arbitrary()?).ok_or(arbitrary::Error::IncorrectFormat)
            }

            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
                <Inner as Arbitrary<'a>>::size_hint(depth)
            }
        }

        // === Serde ===

        #[cfg(feature = "serde")]
        use serde::{de::Error as _, Deserialize, Deserializer, Serialize, Serializer};

        #[cfg(feature = "serde")]
        impl<const MIN: Inner, const MAX: Inner> Serialize for Bounded<MIN, MAX> {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.get().serialize(serializer)
            }
        }

        #[cfg(feature = "serde")]
        impl<'de, const MIN: Inner, const MAX: Inner> Deserialize<'de> for Bounded<MIN, MAX> {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                Self::new(Inner::deserialize(deserializer)?)
                    .ok_or_else(|| {
                        D::Error::custom(format_args!(
                            "integer out of range, expected it to be between {} and {}",
                            Self::MIN_VALUE,
                            Self::MAX_VALUE,
                        ))
                    })
            }
        }

        // === Conversions ===

        $(impl<const MIN: Inner, const MAX: Inner> From<Bounded<MIN, MAX>> for $into {
            fn from(bounded: Bounded<MIN, MAX>) -> Self {
                Self::from(bounded.get())
            }
        })*

        // === Tests ===

        #[cfg(test)]
        mod tests {
            use super::Inner;

            #[cfg(feature = "std")]
            use std::format;

            #[test]
            fn range() {
                type Bounded = super::Bounded<3, 10>;
                assert_eq!(Bounded::MIN_VALUE, 3);
                assert_eq!(Bounded::MAX_VALUE, 10);
                assert_eq!(Bounded::MIN.get(), Bounded::MIN_VALUE);
                assert_eq!(Bounded::MAX.get(), Bounded::MAX_VALUE);

                assert!(Bounded::in_range(3));
                assert!(!Bounded::in_range(2));
                assert!(Bounded::in_range(10));
                assert!(!Bounded::in_range(11));
            }

            #[test]
            fn saturating() {
                type Bounded = super::Bounded<3, 10>;
                assert_eq!(Bounded::new_saturating(Inner::MIN), Bounded::MIN);
                assert_eq!(Bounded::new_saturating(Inner::MAX), Bounded::MAX);
                assert_eq!(Bounded::new_saturating(11).get(), 10);
                assert_eq!(Bounded::new_saturating(10).get(), 10);
                assert_eq!(Bounded::new_saturating(3).get(), 3);
                assert_eq!(Bounded::new_saturating(2).get(), 3);
            }

            #[test]
            fn arithmetic() {
                if false {
                    type Bounded = super::Bounded<0, 15>;
                    test_arithmetic! {
                        $($(if $signed)? signed)?
                        ops(+ += - -= * *= / /= % %=)
                        infallibles(
                            pow
                            div_euclid
                            rem_euclid
                            saturating_add
                            saturating_sub
                            saturating_mul
                            saturating_pow
                        )
                        fallibles(
                            checked_add
                            checked_sub
                            checked_mul
                            checked_div
                            checked_div_euclid
                            checked_rem
                            checked_rem_euclid
                            checked_pow
                        )
                    }
                }
            }

            #[test]
            fn iter() {
                type Bounded = super::Bounded<{ 0 $($(if $signed)? - 8)? }, 8>;

                fn b(&n: &Inner) -> Bounded {
                    Bounded::new(n).unwrap()
                }

                assert_eq!([3, 2, 1].iter().map(b).sum::<Bounded>().get(), 6);
                $($(if $signed)? assert_eq!([-8, 3, 7, 5, -2].iter().map(b).sum::<Bounded>().get(), 5);)?
                assert_eq!([7, 6, 4].iter().map(b).sum::<Inner>(), 17);
                $($(if $signed)? assert_eq!([-8, 3, 7, 5, -2].iter().map(b).sum::<Inner>(), 5);)?

                assert_eq!([1, 3, 2, 1].iter().map(b).product::<Bounded>().get(), 6);
                assert_eq!([1, 3, 2, 1, 0].iter().map(b).product::<Bounded>().get(), 0);
                $($(if $signed)? assert_eq!([-2, -3, -1].iter().map(b).product::<Bounded>().get(), -6);)?
                assert_eq!([3, 3].iter().map(b).product::<Inner>(), 9);
            }

            #[test]
            fn parse() {
                use crate::ParseErrorKind::*;

                type Bounded = super::Bounded<3, 11>;

                assert_eq!("3".parse::<Bounded>().unwrap().get(), 3);
                assert_eq!("10".parse::<Bounded>().unwrap().get(), 10);
                assert_eq!("+11".parse::<Bounded>().unwrap().get(), 11);
                assert_eq!(Bounded::from_str_radix("1010", 2).unwrap().get(), 10);
                assert_eq!(Bounded::from_str_radix("B", 0xC).unwrap().get(), 11);
                assert_eq!(Bounded::from_str_radix("11", 7).unwrap().get(), 8);
                assert_eq!(Bounded::from_str_radix("7", 36).unwrap().get(), 7);

                assert_eq!("".parse::<Bounded>().unwrap_err().kind(), NoDigits);
                assert_eq!("+".parse::<Bounded>().unwrap_err().kind(), NoDigits);
                assert_eq!("-".parse::<Bounded>().unwrap_err().kind(), NoDigits);
                assert_eq!("2".parse::<Bounded>().unwrap_err().kind(), BelowMin);
                assert_eq!("12".parse::<Bounded>().unwrap_err().kind(), AboveMax);
                assert_eq!("-5".parse::<Bounded>().unwrap_err().kind(), BelowMin);
                #[cfg(feature = "std")]
                assert_eq!(
                    format!("{}00", Inner::MAX).parse::<Bounded>().unwrap_err().kind(),
                    AboveMax
                );
                #[cfg(feature = "std")]
                assert_eq!(
                    format!("{}00", Inner::MIN).parse::<Bounded>().unwrap_err().kind(),
                    BelowMin
                );

                assert_eq!("++0".parse::<Bounded>().unwrap_err().kind(), InvalidDigit);
                assert_eq!("--0".parse::<Bounded>().unwrap_err().kind(), InvalidDigit);
                assert_eq!("O".parse::<Bounded>().unwrap_err().kind(), InvalidDigit);
                assert_eq!("C".parse::<Bounded>().unwrap_err().kind(), InvalidDigit);
                assert_eq!(Bounded::from_str_radix("3", 2).unwrap_err().kind(), InvalidDigit);
            }
        }
    } pub use self::$inner::Bounded as $name; )* }
}

define_bounded_integers! {
    BoundedU8 u8 -> u8 u16 u32 u64 u128 usize i16 i32 i64 i128 isize,
    BoundedU16 u16 -> u16 u32 u64 u128 usize i32 i64 i128,
    BoundedU32 u32 -> u32 u64 u128 i64 i128,
    BoundedU64 u64 -> u64 u128 i128,
    BoundedU128 u128 -> u128,
    BoundedUsize usize -> usize,
    BoundedI8 i8 signed -> i8 i16 i32 i64 i128 isize,
    BoundedI16 i16 signed -> i16 i32 i64 i128 isize,
    BoundedI32 i32 signed -> i32 i64 i128,
    BoundedI64 i64 signed -> i64 i128,
    BoundedI128 i128 signed -> i128,
    BoundedIsize isize signed -> isize,
}
