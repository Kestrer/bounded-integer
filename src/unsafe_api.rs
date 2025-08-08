/// Unsafely provide the bounded integer API for a custom type.
///
/// This is used by the higher-level const generic types and by
/// [the `bounded_integer!` macro](crate::bounded_integer). It is preferable to use those APIs when
/// possible.
///
/// Takes in a `ty` and a `repr`. `ty` must be a type whose layout is identical to `repr`.
///
/// `min` and `max` are const expressions giving the bounds of the type (inclusive).
/// If `zero` is provided, various traits like [`Default`] will be implemented;
/// if `one` is provided, `num_traits::One` will be implemented.
///
/// # Safety
///
/// The given type must be `repr(transparent)` over its claimed `repr`.
///
/// # Examples
///
/// ```
#[cfg_attr(feature = "step_trait", doc = "# #![feature(step_trait)]")]
/// #[repr(transparent)]
/// struct MyInteger(u8);
///
/// bounded_integer::unsafe_api! {
///     for MyInteger,
///     unsafe repr: u8,
///     min: 0,
///     max: 37,
///     zero,
///     one,
/// }
///
/// assert_eq!(MyInteger::new(0).unwrap(), 0);
/// assert_eq!(MyInteger::new(38), None);
/// ```
///
/// # Reprs
///
/// `repr` may either be a primitive integer type, or a descriptor:
///
/// ```text
/// unsafe repr: {
///     type: u32, // a primitive integer type, or something that resolves to one (e.g. c_int)
///     signed: false,
///     supersets: [u32, u64, u128, i64, i128], // Types implementing `From<u32>`
///     non_supersets: [u8, u16, usize, i8, i16, i32, isize], // All the other integer types
///     has_wide, // Include for all except `u128` and `i128`.
/// }
/// ```
#[macro_export]
macro_rules! unsafe_api {
    (
        $([$($generics:tt)*])? for $ty:ty $(where { $($where:tt)* })?,
        unsafe repr: $repr:tt,
        min: $min:expr,
        max: $max:expr,
        $(zero $([$($_:tt)* $zero:tt])?,)?
        $(one $([$($__:tt)* $one:tt])?,)?
    ) => {
        $crate::__unsafe_api_internal! {
            @repr $repr,
            [$($($generics)*)?] for $ty where { $($($where)*)? },
            ([$($($generics)*)?] where $($($where)*)?),
            min: $min,
            max: $max,
            $(zero, $($zero)?)?
            $(one, $($one)?)?
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! __unsafe_api_internal {
    (
        @repr {
            type: $inner:ty,
            signed: $(true $([$($_:tt)* $signed:tt])?)? $(false)?,
            supersets: [$($super:ty),* $(,)?],
            non_supersets: [$($non_super:ty),* $(,)?],
            $(has_wide $([$($__:tt)* $has_wide:tt])?,)?
        },
        [$($generics:tt)*] for $ty:ty where { $($where:tt)* },
        $generics_single_token:tt,
        min: $min:expr,
        max: $max:expr,
        $(zero $([$zero:tt])?,)?
        $(one $([$one:tt])?,)?
    ) => { const _: () = {
        // The presence of these imports is somewhat unhygienic: it means users cannot name their
        // type any of these things. This can always be changed if the need arises.
        use ::core::assert;
        use ::core::hash::Hash;
        use ::core::hash::Hasher;
        use ::core::fmt;
        use ::core::borrow::Borrow;
        use ::core::cmp;
        use ::core::debug_assert;
        use ::core::iter;
        use ::core::num::NonZero;
        use ::core::prelude::rust_2024::*;
        use ::core::primitive::*;
        use ::core::str::FromStr;

        use $crate::ParseError;
        #[cfg(any($($(if $has_wide)? true)?))]
        use $crate::__private::Wide;
        #[cfg(any($($(if $has_wide)? true)?))]
        use $crate::__private::Signed;
        use $crate::__private::Unsigned;
        use $crate::__private::Dispatch;

        #[allow(dead_code)]
        #[allow(clippy::double_must_use)]
        impl<$($generics)*> $ty where $($where)* {
            /// The smallest value this bounded integer can contain.
            pub const MIN_VALUE: $inner = $min;
            /// The largest value that this bounded integer can contain.
            pub const MAX_VALUE: $inner = $max;

            /// The smallest value of the bounded integer.
            pub const MIN: Self = Self::new(Self::MIN_VALUE)
                .expect("range minimum should be less than maximum");
            /// The largest value of the bounded integer.
            pub const MAX: Self = Self::new(Self::MAX_VALUE)
                .expect("range minimum should be less than maximum");

            /// Creates a bounded integer if the given value is within the range
            /// [[`MIN`](Self::MIN), [`MAX`](Self::MAX)].
            #[must_use]
            #[inline]
            pub const fn new(n: $inner) -> Option<Self> {
                if Self::in_range(n) {
                    Some(unsafe { Self::new_unchecked(n) })
                } else {
                    None
                }
            }

            /// Creates a bounded integer whose value is known at compile time.
            ///
            /// Causes a compile-time error if `N` is not in the valid range.
            #[must_use]
            #[inline]
            pub const fn const_new<const N: $inner>() -> Self {
                const { Self::new(N).expect("value passed to `const_new` is out of range") }
            }

            /// Creates a reference to a bounded integer from a reference to a primitive if the
            /// given value is within the range [[`MIN`](Self::MIN), [`MAX`](Self::MAX)].
            #[must_use]
            #[inline]
            pub const fn new_ref(n: &$inner) -> Option<&Self> {
                if Self::in_range(*n) {
                    // SAFETY: We just asserted that the value is in range.
                    Some(unsafe { Self::new_ref_unchecked(n) })
                } else {
                    None
                }
            }

            /// Creates a mutable reference to a bounded integer from a mutable reference to a
            /// primitive if the given value is within the range
            /// [[`MIN`](Self::MIN), [`MAX`](Self::MAX)].
            #[must_use]
            #[inline]
            pub const fn new_mut(n: &mut $inner) -> Option<&mut Self> {
                if Self::in_range(*n) {
                    // SAFETY: We just asserted that the value is in range.
                    Some(unsafe { Self::new_mut_unchecked(n) })
                } else {
                    None
                }
            }

            /// Creates a bounded integer without checking the value.
            ///
            /// # Safety
            ///
            /// The value must not be outside the valid range of values; it must not be less than
            /// [`MIN_VALUE`](Self::MIN_VALUE) or greater than [`MAX_VALUE`](Self::MAX_VALUE).
            #[must_use]
            pub const unsafe fn new_unchecked(n: $inner) -> Self {
                debug_assert!(Self::in_range(n));
                unsafe { ::core::mem::transmute(n) }
            }

            /// Creates a shared reference to a bounded integer from a shared reference to a
            /// primitive.
            ///
            /// # Safety
            ///
            /// The value must not be outside the valid range of values; it must not be less than
            /// [`MIN_VALUE`](Self::MIN_VALUE) or greater than [`MAX_VALUE`](Self::MAX_VALUE).
            #[must_use]
            pub const unsafe fn new_ref_unchecked(n: &$inner) -> &Self {
                debug_assert!(Self::in_range(*n));
                unsafe { &*<*const _>::cast(n) }
            }

            /// Creates a mutable reference to a bounded integer from a mutable reference to a
            /// primitive.
            ///
            /// # Safety
            ///
            /// The value must not be outside the valid range of values; it must not be less than
            /// [`MIN_VALUE`](Self::MIN_VALUE) or greater than [`MAX_VALUE`](Self::MAX_VALUE).
            #[must_use]
            pub const unsafe fn new_mut_unchecked(n: &mut $inner) -> &mut Self {
                debug_assert!(Self::in_range(*n));
                unsafe { &mut *<*mut _>::cast(n) }
            }

            /// Checks whether the given value is in the range of the bounded integer.
            #[must_use]
            #[inline]
            pub const fn in_range(n: $inner) -> bool {
                n >= Self::MIN_VALUE && n <= Self::MAX_VALUE
            }

            /// Creates a bounded integer by setting the value to [`MIN`](Self::MIN) or
            /// [`MAX`](Self::MAX) if it is too low or too high respectively.
            #[must_use]
            #[inline]
            pub const fn new_saturating(n: $inner) -> Self {
                if n < Self::MIN_VALUE {
                    Self::MIN
                } else if n > Self::MAX_VALUE {
                    Self::MAX
                } else {
                    unsafe { Self::new_unchecked(n) }
                }
            }

            /// Creates a bounded integer by wrapping using modular arithmetic.
            ///
            /// For `n` in range, this is an identity function, and it wraps for `n` out of range.
            ///
            /// The type parameter `Z` must be any integer type that is a superset of this one.
            #[must_use]
            #[inline]
            pub const fn new_wrapping<__Z: LargerInt>(n: __Z) -> Self {
                const { assert!(Self::MIN_VALUE < Self::MAX_VALUE) };
                let range_sub_one: Unsigned<$inner> = Self::MAX_VALUE.abs_diff(Self::MIN_VALUE);
                let offsets = match range_sub_one.checked_add(1) {
                    Some(range) => {
                        let range = NonZero::new(range).unwrap();

                        // The smallest nonnegative value satisfying `left ≡ MIN [MOD range]`.
                        let left = <Dispatch<$inner>>::rem_euclid_unsigned(Self::MIN_VALUE, range);

                        // The smallest nonnegative value satisfying `−right ≡ MIN [MOD range]`.
                        let right = match left.checked_sub(1) {
                            None => 0,
                            Some(left_sub_one) => range_sub_one - left_sub_one,
                        };

                        Some((range, left, right))
                    },
                    None => None,
                };

                const {
                    let mut n: u32 = 0;
                    $(n += str_eq(__Z::KIND, stringify!($super)) as u32;)*
                    assert!(n == 1);
                }

                $(if str_eq(__Z::KIND, stringify!($super)) {
                    let n = unsafe { ::core::mem::transmute_copy::<__Z, $super>(&n) };

                    let Some((range, left, right)) = offsets else {
                        // In the case where the range spans this entire type, truncating is
                        // equivalent to taking modulo.
                        #[allow(clippy::cast_possible_truncation)]
                        #[allow(clippy::cast_sign_loss)]
                        return unsafe { Self::new_unchecked(n as _) };
                    };

                    // At least one of `n − left` and `n + right` fits in a `__Z`. We calculate
                    // this value.
                    let shifted = match <Dispatch<$super>>::checked_add_unsigned(n, right as _) {
                        Some(n) => n,
                        None => <Dispatch<$super>>::checked_sub_unsigned(n, left as _).unwrap(),
                    };

                    let range_t = NonZero::new(range.get() as _).unwrap();

                    // Calculate `shifted mod range`. Since `range` fits in an `Unsigned`, we
                    // know the result will too.
                    #[allow(clippy::cast_possible_truncation)]
                    let rem = <Dispatch<$super>>::rem_euclid_unsigned(shifted, range_t) as _;

                    let inner = <Dispatch<$inner>>::checked_add_unsigned(Self::MIN_VALUE, rem).unwrap();

                    return unsafe { Self::new_unchecked(inner) };
                })*

                const fn str_eq(a: &str, b: &str) -> bool {
                    if a.len() != b.len() {
                        return false;
                    }
                    let mut i = 0;
                    while i < a.len() {
                        if a.as_bytes()[i] != b.as_bytes()[i] {
                            return false;
                        }
                        i += 1;
                    }
                    true
                }

                ::core::unreachable!()
            }

            /// Converts a string slice in a given base to the bounded integer.
            ///
            /// # Panics
            ///
            /// Panics if `radix` is below 2 or above 36.
            pub const fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseError> {
                let value = match <Dispatch<$inner>>::from_ascii_radix(src.as_bytes(), radix) {
                    Ok(value) => value,
                    Err(e) => return Err(e),
                };
                if value < Self::MIN_VALUE {
                    Err($crate::__private::error_below_min())
                } else if value > Self::MAX_VALUE {
                    Err($crate::__private::error_above_max())
                } else {
                    Ok(unsafe { Self::new_unchecked(value) })
                }
            }

            /// Returns the value of the bounded integer as a primitive type.
            #[must_use]
            #[inline]
            pub const fn get(self) -> $inner {
                unsafe { ::core::mem::transmute(self) }
            }

            /// Returns a shared reference to the value of the bounded integer.
            #[must_use]
            #[inline]
            pub const fn get_ref(&self) -> &$inner {
                unsafe { &*<*const _>::cast(self) }
            }

            /// Returns a mutable reference to the value of the bounded integer.
            ///
            /// # Safety
            ///
            /// This value must never be set to a value beyond the range of the bounded integer.
            #[must_use]
            #[inline]
            pub const unsafe fn get_mut(&mut self) -> &mut $inner {
                unsafe { &mut *<*mut _>::cast(self) }
            }

            $($(if $signed)?
                /// Computes the absolute value of `self`, panicking if it is out of range.
                #[must_use]
                #[inline]
                pub const fn abs(self) -> Self {
                    Self::new(self.get().abs()).expect("Absolute value out of range")
                }
            )*

            /// Raises `self` to the power of `exp`, using exponentiation by squaring. Panics if it
            /// is out of range.
            #[must_use]
            #[inline]
            pub const fn pow(self, exp: u32) -> Self {
                Self::new(self.get().pow(exp)).expect("Value raised to power out of range")
            }

            /// Calculates the quotient of Euclidean division of `self` by `rhs`. Panics if `rhs`
            /// is 0 or the result is out of range.
            #[must_use]
            #[inline]
            pub const fn div_euclid(self, rhs: $inner) -> Self {
                Self::new(self.get().div_euclid(rhs)).expect("Attempted to divide out of range")
            }

            /// Calculates the least nonnegative remainder of `self (mod rhs)`. Panics if `rhs` is 0
            /// or the result is out of range.
            #[must_use]
            #[inline]
            pub const fn rem_euclid(self, rhs: $inner) -> Self {
                Self::new(self.get().rem_euclid(rhs))
                    .expect("Attempted to divide with remainder out of range")
            }

            /// Checked integer addition.
            ///
            /// Returns `None` if the result would be out of range.
            #[must_use]
            #[inline]
            pub const fn checked_add(self, rhs: $inner) -> Option<Self> {
                match self.get().checked_add(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Saturating integer addition.
            #[must_use]
            #[inline]
            pub const fn saturating_add(self, rhs: $inner) -> Self {
                Self::new_saturating(self.get().saturating_add(rhs))
            }

            /// Wrapping (modular) integer addition.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_add(self, rhs: $inner) -> Self {
                Self::new_wrapping((self.get() as Wide<$inner>) + (rhs as Wide<$inner>))
            }

            /// Checked integer subtraction.
            ///
            /// Returns `None` if the result would be out of range.
            #[must_use]
            #[inline]
            pub const fn checked_sub(self, rhs: $inner) -> Option<Self> {
                match self.get().checked_sub(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Saturating integer subtraction.
            #[must_use]
            #[inline]
            pub const fn saturating_sub(self, rhs: $inner) -> Self {
                Self::new_saturating(self.get().saturating_sub(rhs))
            }

            /// Wrapping (modular) integer subtraction.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_sub(self, rhs: $inner) -> Self {
                Self::new_wrapping(
                    (self.get() as Signed<Wide<$inner>>) - (rhs as Signed<Wide<$inner>>)
                )
            }

            /// Checked integer multiplication.
            ///
            /// Returns `None` if the result would be out of range.
            #[must_use]
            #[inline]
            pub const fn checked_mul(self, rhs: $inner) -> Option<Self> {
                match self.get().checked_mul(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Saturating integer multiplication.
            #[must_use]
            #[inline]
            pub const fn saturating_mul(self, rhs: $inner) -> Self {
                Self::new_saturating(self.get().saturating_mul(rhs))
            }

            /// Wrapping (modular) integer multiplication.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_mul(self, rhs: $inner) -> Self {
                Self::new_wrapping((self.get() as Wide<$inner>) * (rhs as Wide<$inner>))
            }

            /// Checked integer division.
            ///
            /// Returns `None` if the result would be out of range, or if `rhs` is zero.
            #[must_use]
            #[inline]
            pub const fn checked_div(self, rhs: $inner) -> Option<Self> {
                match self.get().checked_div(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Wrapping (modular) integer division.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_div(self, rhs: $inner) -> Self {
                // We need to widen for the case of `$inner::MIN / −1`.
                Self::new_wrapping((self.get() as Wide<$inner>) / (rhs as Wide<$inner>))
            }

            /// Checked Euclidean division.
            ///
            /// Returns `None` if the result would be out of range, or if `rhs` is zero.
            #[must_use]
            #[inline]
            pub const fn checked_div_euclid(self, rhs: $inner) -> Option<Self> {
                match self.get().checked_div_euclid(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Wrapping (modular) Euclidean division.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_div_euclid(self, rhs: $inner) -> Self {
                // We need to widen for the case of `$inner::MIN / −1`.
                Self::new_wrapping((self.get() as Wide<$inner>).div_euclid(rhs as Wide<$inner>))
            }

            /// Checked integer remainder.
            ///
            /// Returns `None` if the result would be out of range, or if `rhs` is zero.
            #[must_use]
            #[inline]
            pub const fn checked_rem(self, rhs: $inner) -> Option<Self> {
                match self.get().checked_rem(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Wrapping (modular) integer remainder.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_rem(self, rhs: $inner) -> Self {
                // We need to widen for the case of `$inner::MIN % −1`.
                Self::new_wrapping((self.get() as Wide<$inner>) % (rhs as Wide<$inner>))
            }

            /// Checked Euclidean remainder.
            ///
            /// Returns `None` if the result would be out of range, or if `rhs` is zero.
            #[must_use]
            #[inline]
            pub const fn checked_rem_euclid(self, rhs: $inner) -> Option<Self> {
                match self.get().checked_rem_euclid(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Wrapping (modular) Euclidean remainder.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_rem_euclid(self, rhs: $inner) -> Self {
                // We need to widen for the case of `$inner::MIN % −1`.
                Self::new_wrapping((self.get() as Wide<$inner>).rem_euclid(rhs as Wide<$inner>))
            }

            /// Checked negation.
            ///
            /// Returns `None` if the result would be out of range.
            #[must_use]
            #[inline]
            pub const fn checked_neg(self) -> Option<Self> {
                match self.get().checked_neg() {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Saturating negation.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $signed)? false)?)))]
            pub const fn saturating_neg(self) -> Self {
                Self::new_saturating(self.get().saturating_neg())
            }

            /// Wrapping (modular) negation.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $signed)? false)?)))]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_neg(self) -> Self {
                Self::new_wrapping(-(self.get() as Wide<$inner>))
            }

            /// Checked absolute value.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $signed)? false)?)))]
            pub const fn checked_abs(self) -> Option<Self> {
                match self.get().checked_abs() {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Saturating absolute value.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $signed)? false)?)))]
            pub const fn saturating_abs(self) -> Self {
                Self::new_saturating(self.get().saturating_abs())
            }

            /// Wrapping (modular) absolute value.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $signed)? false)?)))]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_abs(self) -> Self {
                Self::new_wrapping((self.get() as Wide<$inner>).abs())
            }

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

            /// Wrapping (modular) exponentiation.
            #[must_use]
            #[inline]
            #[cfg(not(all($($(if $has_wide)? false)?)))]
            pub const fn wrapping_pow(self, mut exp: u32) -> Self {
                let range_sub_one = Self::MAX_VALUE.abs_diff(Self::MIN_VALUE);
                let Some(range) = range_sub_one.checked_add(1) else {
                    return unsafe { Self::new_unchecked(self.get().wrapping_pow(exp)) };
                };

                // Exponentiation by squaring (same algorithm as used in std), but taking modulo
                // each time. We keep our values in the range [0, MAX − MIN].
                if exp == 0 {
                    return Self::new_wrapping::<$inner>(1);
                }
                let mut base = self.get() as Wide<$inner>;
                let mut acc: Wide<$inner> = 1;
                let range = range as Wide<$inner>;
                loop {
                    if (exp & 1) == 1 {
                        acc = (acc * base).rem_euclid(range);
                        if exp == 1 {
                            return Self::new_wrapping(acc);
                        }
                    }
                    exp /= 2;
                    base = (base * base).rem_euclid(range);
                }
            }

            /// Checked shift left.
            #[must_use]
            #[inline]
            pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
                match self.get().checked_shl(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }

            /// Checked shift right.
            #[must_use]
            #[inline]
            pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
                match self.get().checked_shr(rhs) {
                    Some(val) => Self::new(val),
                    None => None,
                }
            }
        }

        pub trait LargerInt: Copy {
            const KIND: &'static str;
        }

        $(#[automatically_derived]
        impl LargerInt for $super { const KIND: &'static str = stringify!($super); })*

        $crate::__unsafe_api_internal!(@with_super($ty, $inner)
            $({ super: $super, generics: $generics_single_token })*
        );

        // === Clone / Copy ===

        #[automatically_derived]
        impl<$($generics)*> Clone for $ty where $($where)* {
            fn clone(&self) -> Self { *self }
        }
        #[automatically_derived]
        impl<$($generics)*> Copy for $ty where $($where)* {}

        // === Default ===

        #[cfg(not(all($($($zero)? false)?)))]
        #[automatically_derived]
        impl<$($generics)*> Default for $ty where $($where)* {
            fn default() -> Self {
                const {
                    Self::new(0).expect("used `zero` on a type whose range does not include zero")
                }
            }
        }

        // Use a function to force post-mono errors even if `num-traits02` is disabled.
        #[cfg(not(all($($($one)? false)?)))]
        impl<$($generics)*> $ty where $($where)* {
            #[allow(unused)]
            fn one() -> Self {
                const {
                    Self::new(1).expect("used `one` on a type whose range does not include one")
                }
            }
        }

        // === Operators ===

        $crate::__unsafe_api_internal!(@bin_ops($ty, $inner)
            ($generics_single_token, Add::add/AddAssign::add_assign, "add"),
            ($generics_single_token, Sub::sub/SubAssign::sub_assign, "subtract"),
            ($generics_single_token, Mul::mul/MulAssign::mul_assign, "multiply"),
            ($generics_single_token, Div::div/DivAssign::div_assign, "divide"),
            ($generics_single_token, Rem::rem/RemAssign::rem_assign, "take remainder"),
            ($generics_single_token, BitAnd::bitand/BitAndAssign::bitand_assign, "binary and"),
            ($generics_single_token, BitOr::bitor/BitOrAssign::bitor_assign, "binary or"),
            ($generics_single_token, BitXor::bitxor/BitXorAssign::bitxor_assign, "binary xor"),
        );
        use ::core::ops::{Shl, Shr, ShlAssign, ShrAssign};
        #[automatically_derived]
        impl<$($generics)*> Shl<u32> for $ty where $($where)* {
            type Output = Self;
            #[inline]
            fn shl(self, rhs: u32) -> Self::Output {
                Self::new(self.get().shl(rhs))
                    .expect("Attempted to shift left out of range")
            }
        }
        $crate::__unsafe_api_internal!(@bin_op_variations
            $generics_single_token,
            $ty, u32, Shl::shl/ShlAssign::shl_assign
        );
        #[automatically_derived]
        impl<$($generics)*> Shr<u32> for $ty where $($where)* {
            type Output = Self;
            #[inline]
            fn shr(self, rhs: u32) -> Self::Output {
                Self::new(self.get().shr(rhs))
                    .expect("Attempted to shift right out of range")
            }
        }
        $crate::__unsafe_api_internal!(@bin_op_variations
            $generics_single_token,
            $ty, u32, Shr::shr/ShrAssign::shr_assign
        );

        #[cfg(not(all($($(if $signed)? false)?)))]
        use ::core::ops::Neg;

        #[cfg(not(all($($(if $signed)? false)?)))]
        #[automatically_derived]
        impl<$($generics)*> Neg for $ty where $($where)* {
            type Output = Self;
            #[inline]
            fn neg(self) -> Self::Output {
                Self::new(-self.get())
                    .expect("Attempted to negate out of range")
            }
        }
        #[cfg(not(all($($(if $signed)? false)?)))]
        #[automatically_derived]
        impl<$($generics)*> Neg for &$ty where $($where)* {
            type Output = $ty;
            #[inline]
            fn neg(self) -> Self::Output {
                -*self
            }
        }

        use ::core::ops::Not;

        #[automatically_derived]
        impl<$($generics)*> Not for $ty where $($where)* {
            type Output = Self;
            #[inline]
            fn not(self) -> Self::Output {
                Self::new(!self.get())
                    .expect("Attempted to invert bits out of range")
            }
        }
        #[automatically_derived]
        impl<$($generics)*> Not for &$ty where $($where)* {
            type Output = $ty;
            #[inline]
            fn not(self) -> Self::Output {
                !*self
            }
        }

        // === Comparisons and Hash ===

        #[automatically_derived]
        impl<$($generics)*> PartialEq<$inner> for $ty where $($where)* {
            #[inline]
            fn eq(&self, other: &$inner) -> bool {
                self.get() == *other
            }
        }
        #[automatically_derived]
        impl<$($generics)*> PartialEq<$ty> for $inner where $($where)* {
            #[inline]
            fn eq(&self, other: &$ty) -> bool {
                *self == other.get()
            }
        }
        #[automatically_derived]
        impl<$($generics)*> PartialEq for $ty where $($where)* {
            #[inline]
            fn eq(&self, other: &$ty) -> bool {
                self.get() == other.get()
            }
        }
        #[automatically_derived]
        impl<$($generics)*> Eq for $ty where $($where)* {}

        #[automatically_derived]
        impl<$($generics)*> PartialOrd<$inner> for $ty where $($where)* {
            #[inline]
            fn partial_cmp(&self, other: &$inner) -> Option<cmp::Ordering> {
                self.get().partial_cmp(other)
            }
        }
        #[automatically_derived]
        impl<$($generics)*> PartialOrd<$ty> for $inner where $($where)* {
            #[inline]
            fn partial_cmp(&self, other: &$ty) -> Option<cmp::Ordering> {
                self.partial_cmp(&other.get())
            }
        }
        #[automatically_derived]
        impl<$($generics)*> PartialOrd for $ty where $($where)* {
            #[inline]
            fn partial_cmp(&self, other: &$ty) -> Option<cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
        #[automatically_derived]
        impl<$($generics)*> Ord for $ty where $($where)* {
            #[inline]
            fn cmp(&self, other: &$ty) -> cmp::Ordering {
                self.get().cmp(&other.get())
            }
        }

        #[automatically_derived]
        impl<$($generics)*> Hash for $ty where $($where)* {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.get().hash(state);
            }
        }

        // === AsRef, Borrow ===

        #[automatically_derived]
        impl<$($generics)*> AsRef<$inner> for $ty where $($where)* {
            #[inline]
            fn as_ref(&self) -> &$inner {
                self.get_ref()
            }
        }
        #[automatically_derived]
        impl<$($generics)*> Borrow<$inner> for $ty where $($where)* {
            #[inline]
            fn borrow(&self) -> &$inner {
                self.get_ref()
            }
        }

        // === Iterator traits ===

        // Sum bounded to bounded
        #[automatically_derived]
        impl<$($generics)*> iter::Sum for $ty where $($where)* {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.reduce(Add::add)
                    .unwrap_or_else(|| Self::new(0).expect("Attempted to sum to zero"))
            }
        }
        #[automatically_derived]
        impl<'__a, $($generics)*> iter::Sum<&'__a Self> for $ty where $($where)* {
            fn sum<I: Iterator<Item = &'__a Self>>(iter: I) -> Self {
                iter.copied().sum()
            }
        }

        // Sum bounded to primitive
        #[automatically_derived]
        impl<$($generics)*> iter::Sum<$ty> for $inner where $($where)* {
            fn sum<I: Iterator<Item = $ty>>(iter: I) -> Self {
                iter.map(<$ty>::get).sum()
            }
        }
        #[automatically_derived]
        impl<'__a, $($generics)*> iter::Sum<&'__a $ty> for $inner where $($where)* {
            fn sum<I: Iterator<Item = &'__a $ty>>(iter: I) -> Self {
                iter.copied().sum()
            }
        }

        // Take product of bounded to bounded
        #[automatically_derived]
        impl<$($generics)*> iter::Product for $ty where $($where)* {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.reduce(Mul::mul)
                    .unwrap_or_else(|| Self::new(1).expect("Attempted to take product to one"))
            }
        }
        #[automatically_derived]
        impl<'__a, $($generics)*> iter::Product<&'__a Self> for $ty where $($where)* {
            fn product<I: Iterator<Item = &'__a Self>>(iter: I) -> Self {
                iter.copied().product()
            }
        }

        // Take product of bounded to primitive
        #[automatically_derived]
        impl<$($generics)*> iter::Product<$ty> for $inner where $($where)* {
            fn product<I: Iterator<Item = $ty>>(iter: I) -> Self {
                iter.map(<$ty>::get).product()
            }
        }
        #[automatically_derived]
        impl<'__a, $($generics)*> iter::Product<&'__a $ty> for $inner where $($where)* {
            fn product<I: Iterator<Item = &'__a $ty>>(iter: I) -> Self {
                iter.copied().product()
            }
        }

        $crate::__private::__cfg_step_trait! {
            #[automatically_derived]
            impl<$($generics)*> iter::Step for $ty where $($where)* {
                #[inline]
                fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
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
        }

        // === Parsing ===

        #[automatically_derived]
        impl<$($generics)*> FromStr for $ty where $($where)* {
            type Err = ParseError;
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                Self::from_str_radix(s, 10)
            }
        }

        // === Formatting ===

        #[automatically_derived]
        impl<$($generics)*> fmt::Debug for $ty where $($where)* {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple("Bounded").field(&self.get()).finish()
            }
        }

        $crate::__unsafe_api_internal!(@fmt_traits($ty, $inner)
            $generics_single_token Binary,
            $generics_single_token Display,
            $generics_single_token LowerExp,
            $generics_single_token LowerHex,
            $generics_single_token Octal,
            $generics_single_token UpperExp,
            $generics_single_token UpperHex,
        );

        // === Arbitrary ===

        $crate::__private::__cfg_arbitrary1! {
            use $crate::__private::arbitrary1::{self, Arbitrary, Unstructured};

            #[automatically_derived]
            impl<'__a, $($generics)*> Arbitrary<'__a> for $ty where $($where)* {
                fn arbitrary(u: &mut Unstructured<'__a>) -> arbitrary1::Result<Self> {
                    Self::new(u.arbitrary()?).ok_or(arbitrary1::Error::IncorrectFormat)
                }

                #[inline]
                fn size_hint(depth: usize) -> (usize, Option<usize>) {
                    <$inner as Arbitrary<'__a>>::size_hint(depth)
                }
            }
        }

        // === Bytemuck ===

        $crate::__private::__cfg_bytemuck1! {
            use $crate::__private::bytemuck1;

            #[automatically_derived]
            unsafe impl<$($generics)*> bytemuck1::Contiguous for $ty
            where
                Self: 'static,
                $($where)*
            {
                type Int = $inner;
                const MAX_VALUE: $inner = Self::MAX_VALUE;
                const MIN_VALUE: $inner = Self::MIN_VALUE;
            }

            #[automatically_derived]
            unsafe impl<$($generics)*> bytemuck1::NoUninit for $ty
            where
                Self: 'static,
                $($where)*
            {}

            #[cfg(not(all($($(if $zero)? false)?)))]
            #[automatically_derived]
            unsafe impl<$($generics)*> bytemuck1::Zeroable for $ty where $($where)* {}
        }

        // === Num ===

        $crate::__private::__cfg_num_traits02! {
            use $crate::__private::num_traits02;

            #[automatically_derived]
            impl<$($generics)*> num_traits02::Bounded for $ty where $($where)* {
                fn min_value() -> Self {
                    Self::MIN
                }
                fn max_value() -> Self {
                    Self::MAX
                }
            }

            #[automatically_derived]
            impl<__T, $($generics)*> num_traits02::AsPrimitive<__T> for $ty
            where
                $inner: num_traits02::AsPrimitive<__T>,
                __T: 'static + Copy,
                Self: 'static,
                $($where)*
            {
                fn as_(self) -> __T {
                    self.get().as_()
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::FromPrimitive for $ty
            where
                $inner: num_traits02::FromPrimitive,
                $($where)*
            {
                fn from_i64(n: i64) -> Option<Self> {
                    <$inner>::from_i64(n).and_then(Self::new)
                }
                fn from_u64(n: u64) -> Option<Self> {
                    <$inner>::from_u64(n).and_then(Self::new)
                }
                fn from_isize(n: isize) -> Option<Self> {
                    <$inner>::from_isize(n).and_then(Self::new)
                }
                fn from_i8(n: i8) -> Option<Self> {
                    <$inner>::from_i8(n).and_then(Self::new)
                }
                fn from_i16(n: i16) -> Option<Self> {
                    <$inner>::from_i16(n).and_then(Self::new)
                }
                fn from_i32(n: i32) -> Option<Self> {
                    <$inner>::from_i32(n).and_then(Self::new)
                }
                fn from_i128(n: i128) -> Option<Self> {
                    <$inner>::from_i128(n).and_then(Self::new)
                }
                fn from_usize(n: usize) -> Option<Self> {
                    <$inner>::from_usize(n).and_then(Self::new)
                }
                fn from_u8(n: u8) -> Option<Self> {
                    <$inner>::from_u8(n).and_then(Self::new)
                }
                fn from_u16(n: u16) -> Option<Self> {
                    <$inner>::from_u16(n).and_then(Self::new)
                }
                fn from_u32(n: u32) -> Option<Self> {
                    <$inner>::from_u32(n).and_then(Self::new)
                }
                fn from_u128(n: u128) -> Option<Self> {
                    <$inner>::from_u128(n).and_then(Self::new)
                }
                fn from_f32(n: f32) -> Option<Self> {
                    <$inner>::from_f32(n).and_then(Self::new)
                }
                fn from_f64(n: f64) -> Option<Self> {
                    <$inner>::from_f64(n).and_then(Self::new)
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::NumCast for $ty
            where
                $inner: num_traits02::NumCast,
                $($where)*
            {
                fn from<__T: num_traits02::ToPrimitive>(n: __T) -> Option<Self> {
                    <$inner as num_traits02::NumCast>::from(n).map(Self::new).flatten()
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::ToPrimitive for $ty
            where
                $inner: num_traits02::ToPrimitive,
                $($where)*
            {
                fn to_i64(&self) -> Option<i64> {
                    self.get().to_i64()
                }
                fn to_u64(&self) -> Option<u64> {
                    self.get().to_u64()
                }
                fn to_isize(&self) -> Option<isize> {
                    self.get().to_isize()
                }
                fn to_i8(&self) -> Option<i8> {
                    self.get().to_i8()
                }
                fn to_i16(&self) -> Option<i16> {
                    self.get().to_i16()
                }
                fn to_i32(&self) -> Option<i32> {
                    self.get().to_i32()
                }
                fn to_i128(&self) -> Option<i128> {
                    self.get().to_i128()
                }
                fn to_usize(&self) -> Option<usize> {
                    self.get().to_usize()
                }
                fn to_u8(&self) -> Option<u8> {
                    self.get().to_u8()
                }
                fn to_u16(&self) -> Option<u16> {
                    self.get().to_u16()
                }
                fn to_u32(&self) -> Option<u32> {
                    self.get().to_u32()
                }
                fn to_u128(&self) -> Option<u128> {
                    self.get().to_u128()
                }
                fn to_f32(&self) -> Option<f32> {
                    self.get().to_f32()
                }
                fn to_f64(&self) -> Option<f64> {
                    self.get().to_f64()
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::CheckedAdd for $ty where $($where)* {
                fn checked_add(&self, v: &Self) -> Option<Self> {
                    Self::checked_add(*self, v.get())
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::CheckedDiv for $ty where $($where)* {
                fn checked_div(&self, v: &Self) -> Option<Self> {
                    Self::checked_div(*self, v.get())
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::CheckedMul for $ty where $($where)* {
                fn checked_mul(&self, v: &Self) -> Option<Self> {
                    Self::checked_mul(*self, v.get())
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::CheckedNeg for $ty where $($where)* {
                fn checked_neg(&self) -> Option<Self> {
                    Self::checked_neg(*self)
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::CheckedRem for $ty where $($where)* {
                fn checked_rem(&self, v: &Self) -> Option<Self> {
                    Self::checked_rem(*self, v.get())
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::CheckedShl for $ty where $($where)* {
                fn checked_shl(&self, v: u32) -> Option<Self> {
                    Self::checked_shl(*self, v)
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::CheckedShr for $ty where $($where)* {
                fn checked_shr(&self, v: u32) -> Option<Self> {
                    Self::checked_shr(*self, v)
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::CheckedSub for $ty where $($where)* {
                fn checked_sub(&self, v: &Self) -> Option<Self> {
                    Self::checked_sub(*self, v.get())
                }
            }

            #[automatically_derived]
            impl<__A, __B, $($generics)*> num_traits02::MulAdd<__A, __B> for $ty
            where
                $inner: num_traits02::MulAdd<__A, __B, Output = $inner>,
                $($where)*
            {
                type Output = $inner;

                fn mul_add(self, a: __A, b: __B) -> Self::Output {
                    self.get().mul_add(a, b)
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::SaturatingAdd for $ty where $($where)* {
                fn saturating_add(&self, v: &Self) -> Self {
                    Self::saturating_add(*self, v.get())
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::SaturatingMul for $ty where $($where)* {
                fn saturating_mul(&self, v: &Self) -> Self {
                    Self::saturating_mul(*self, v.get())
                }
            }

            #[automatically_derived]
            impl<$($generics)*> num_traits02::SaturatingSub for $ty where $($where)* {
                fn saturating_sub(&self, v: &Self) -> Self {
                    Self::saturating_sub(*self, v.get())
                }
            }

            #[cfg(not(all($($($zero)? false)?)))]
            #[automatically_derived]
            impl<$($generics)*> num_traits02::Zero for $ty where $($where)* {
                fn zero() -> Self {
                    Self::default()
                }
                fn is_zero(&self) -> bool {
                    self.get() == 0
                }
            }

            #[cfg(not(all($($($one)? false)?)))]
            #[automatically_derived]
            impl<$($generics)*> num_traits02::One for $ty where $($where)* {
                fn one() -> Self {
                    Self::one()
                }
            }
        }

        // === Serde ===

        $crate::__private::__cfg_serde1! {
            use $crate::__private::serde1::{self, Deserialize, Deserializer, Serialize, Serializer};

            #[automatically_derived]
            impl<$($generics)*> Serialize for $ty where $($where)* {
                fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                    self.get().serialize(serializer)
                }
            }

            // Disable this to prevent triggering `clippy::unsafe_derive_deserialize`. I couldn’t
            // figure out how to `#[allow]` it.
            // #[automatically_derived]
            impl<'__de, $($generics)*> Deserialize<'__de> for $ty where $($where)* {
                fn deserialize<D: Deserializer<'__de>>(deserializer: D) -> Result<Self, D::Error> {
                    Self::new(<$inner>::deserialize(deserializer)?)
                        .ok_or_else(|| {
                            <D::Error as serde1::de::Error>::custom(format_args!(
                                "integer out of range, expected it to be between {} and {}",
                                Self::MIN_VALUE,
                                Self::MAX_VALUE,
                            ))
                        })
                }
            }
        }
    }; };

    (@repr u8, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: u8,
            signed: false,
            supersets: [u8, u16, u32, u64, u128, usize, i16, i32, i64, i128, isize],
            non_supersets: [i8],
            has_wide,
        },
        $($rest)*
    } };
    (@repr u16, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: u16,
            signed: false,
            supersets: [u16, u32, u64, u128, usize, i32, i64, i128],
            non_supersets: [u8, i8, i16, isize],
            has_wide,
        },
        $($rest)*
    } };
    (@repr u32, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: u32,
            signed: false,
            supersets: [u32, u64, u128, i64, i128],
            non_supersets: [u8, u16, usize, i8, i16, i32, isize],
            has_wide,
        },
        $($rest)*
    } };
    (@repr u64, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: u64,
            signed: false,
            supersets: [u64, u128, i128],
            non_supersets: [u8, u16, u32, usize, i8, i16, i32, i64, isize],
            has_wide,
        },
        $($rest)*
    } };
    (@repr u128, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: u128,
            signed: false,
            supersets: [u128],
            non_supersets: [u8, u16, u32, u64, usize, i8, i16, i32, i64, i128, isize],
        },
        $($rest)*
    } };
    (@repr usize, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: usize,
            signed: false,
            supersets: [usize],
            non_supersets: [u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, isize],
        },
        $($rest)*
    } };
    (@repr i8, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: i8,
            signed: true,
            supersets: [i8, i16, i32, i64, i128, isize],
            non_supersets: [u8, u16, u32, u64, u128, usize],
            has_wide,
        },
        $($rest)*
    } };
    (@repr i16, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: i16,
            signed: true,
            supersets: [i16, i32, i64, i128, isize],
            non_supersets: [u8, u16, u32, u64, u128, usize, i8],
            has_wide,
        },
        $($rest)*
    } };
    (@repr i32, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: i32,
            signed: true,
            supersets: [i32, i64, i128],
            non_supersets: [u8, u16, u32, u64, u128, usize, i8, i16, isize],
            has_wide,
        },
        $($rest)*
    } };
    (@repr i64, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: i64,
            signed: true,
            supersets: [i64, i128],
            non_supersets: [u8, u16, u32, u64, u128, usize, i8, i16, i32, isize],
            has_wide,
        },
        $($rest)*
    } };
    (@repr i128, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: i128,
            signed: true,
            supersets: [i128],
            non_supersets: [u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, isize],
        },
        $($rest)*
    } };
    (@repr isize, $($rest:tt)*) => { $crate::__unsafe_api_internal! {
        @repr {
            type: isize,
            signed: true,
            supersets: [isize],
            non_supersets: [u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128],
        },
        $($rest)*
    } };

    (@with_super($ty:ty, $inner:ty)
        $({ super: $super:ty, generics: ([$($generics:tt)*] where $($where:tt)*) })*
    ) => { $(
        #[automatically_derived]
        impl<$($generics)*> From<$ty> for $super where $($where)* {
            fn from(bounded: $ty) -> Self {
                Self::from(bounded.get())
            }
        }
    )* };

    (@bin_ops($ty:ty, $inner:ty)
        $((
            ([$($generics:tt)*] where $($where:tt)*),
            $op:ident::$method:ident/$op_assign:ident::$method_assign:ident, $desc:literal
        ),)*
    ) => { $(
        use ::core::ops::{$op, $op_assign};

        #[automatically_derived]
        impl<$($generics)*> $op<$inner> for $ty where $($where)* {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: $inner) -> Self::Output {
                Self::new(self.get().$method(rhs))
                    .expect(concat!("Attempted to ", $desc, " out of range"))
            }
        }
        $crate::__unsafe_api_internal!(@bin_op_variations
            ([$($generics)*] where $($where)*),
            $ty, $inner, $op::$method/$op_assign::$method_assign
        );

        #[automatically_derived]
        impl<$($generics)*> $op<$ty> for $inner where $($where)* {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: $ty) -> Self::Output {
                self.$method(rhs.get())
            }
        }
        $crate::__unsafe_api_internal!(@bin_op_variations
            ([$($generics)*] where $($where)*),
            $inner, $ty, $op::$method/$op_assign::$method_assign
        );

        #[automatically_derived]
        impl<$($generics)*> $op<$ty> for $ty where $($where)* {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: $ty) -> Self::Output {
                self.$method(rhs.get())
            }
        }
        $crate::__unsafe_api_internal!(@bin_op_variations
            ([$($generics)*] where $($where)*),
            $ty, $ty, $op::$method/$op_assign::$method_assign
        );
    )* };

    (@bin_op_variations
        ([$($generics:tt)*] where $($where:tt)*),
        $lhs:ty, $rhs:ty, $op:ident::$method:ident/$op_assign:ident::$method_assign:ident
    ) => {
        #[automatically_derived]
        impl<$($generics)*> $op<$rhs> for &$lhs where $($where)* {
            type Output = $lhs;
            #[inline]
            fn $method(self, rhs: $rhs) -> Self::Output {
                <$lhs as $op<$rhs>>::$method(*self, rhs)
            }
        }
        #[automatically_derived]
        impl<$($generics)*> $op<&$rhs> for $lhs where $($where)* {
            type Output = $lhs;
            #[inline]
            fn $method(self, rhs: &$rhs) -> Self::Output {
                <$lhs as $op<$rhs>>::$method(self, *rhs)
            }
        }
        #[automatically_derived]
        impl<$($generics)*> $op<&$rhs> for &$lhs where $($where)* {
            type Output = $lhs;
            #[inline]
            fn $method(self, rhs: &$rhs) -> Self::Output {
                <$lhs as $op<$rhs>>::$method(*self, *rhs)
            }
        }

        #[automatically_derived]
        impl<$($generics)*> $op_assign<$rhs> for $lhs where $($where)* {
            #[inline]
            fn $method_assign(&mut self, rhs: $rhs) {
                *self = <Self as $op<$rhs>>::$method(*self, rhs);
            }
        }
        #[automatically_derived]
        impl<$($generics)*> $op_assign<&$rhs> for $lhs where $($where)* {
            #[inline]
            fn $method_assign(&mut self, rhs: &$rhs) {
                *self = <Self as $op<$rhs>>::$method(*self, *rhs);
            }
        }
    };

    (@fmt_traits($ty:ty, $inner:ty)
        $(([$($generics:tt)*] where $($where:tt)*) $trait:ident,)*
    ) => { $(
        #[automatically_derived]
        impl<$($generics)*> fmt::$trait for $ty where $($where)* {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::$trait::fmt(&self.get(), f)
            }
        }
    )* }
}

// Most functionality is tested in `types.rs`. But there are some things that API cannot do.
#[cfg(test)]
mod tests {
    use crate::unsafe_api;
    use core::ffi::c_int;
    use core::marker::PhantomData;

    #[test]
    fn c_int() {
        #[repr(transparent)]
        struct S(c_int);

        unsafe_api! {
            for S,
            unsafe repr: {
                type: c_int,
                signed: true,
                supersets: [i32, i64, i128],
                non_supersets: [],
                has_wide,
            },
            min: -5,
            max: 5,
            zero,
        }
    }

    #[test]
    fn where_clause() {
        #[repr(transparent)]
        struct S<T: Copy>(i32, PhantomData<T>);

        unsafe_api! {
            [T] for S<T> where { T: Copy },
            unsafe repr: i32,
            min: -1,
            max: i32::MAX,
            zero,
            one,
        }
    }
}
