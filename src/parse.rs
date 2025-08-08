use core::fmt::{self, Display, Formatter};
#[cfg(feature = "std")]
use std::error::Error;

macro_rules! from_str_radix_impl {
    ($($ty:ident)*) => { $(
        impl $crate::__private::Dispatch<$ty> {
            // Implement it ourselves (copying the implementation from std) because `IntErrorKind`
            // is non-exhaustive.
            pub const fn from_ascii_radix(src: &[u8], radix: u32) -> Result<$ty, ParseError> {
                assert!(
                    2 <= radix && radix <= 36,
                    "from_str_radix: radix must lie in the range `[2, 36]`",
                );

                macro_rules! yeet {
                    ($e:expr) => { return Err(ParseError { kind: $e }) };
                }

                let (positive, digits) = match *src {
                    [b'+', ref digits @ ..] => (true, digits),
                    [b'-', ref digits @ ..] => (false, digits),
                    ref digits => (true, digits),
                };

                if digits.is_empty() {
                    yeet!(ParseErrorKind::NoDigits);
                }

                let overflow_kind = if positive {
                    ParseErrorKind::AboveMax
                } else {
                    ParseErrorKind::BelowMin
                };

                let mut result: $ty = 0;

                let mut i = 0;
                while i < digits.len() {
                    let digit = digits[i];

                    let Some(digit_value) = (digit as char).to_digit(radix) else {
                        yeet!(ParseErrorKind::InvalidDigit);
                    };

                    #[allow(clippy::cast_possible_wrap)]
                    #[allow(clippy::cast_possible_truncation)]
                    let Some(new_result) = result.checked_mul(radix as $ty) else {
                        yeet!(overflow_kind);
                    };

                    #[allow(clippy::cast_possible_wrap)]
                    #[allow(clippy::cast_possible_truncation)]
                    let Some(new_result) = (if positive {
                        new_result.checked_add(digit_value as $ty)
                    } else {
                        new_result.checked_sub(digit_value as $ty)
                    }) else {
                        yeet!(overflow_kind);
                    };

                    result = new_result;

                    i += 1;
                }

                Ok(result)
            }
        }
    )* }
}
from_str_radix_impl! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

/// An error which can be returned when parsing a bounded integer.
///
/// This is the error type of all bounded integers' `from_str_radix()` functions (such as
/// [`BoundedI8::from_str_radix`](crate::BoundedI8::from_str_radix)) as well as their
/// [`FromStr`](std::str::FromStr) implementations.
#[derive(Debug, Clone)]
pub struct ParseError {
    kind: ParseErrorKind,
}

impl ParseError {
    /// Gives the cause of the error.
    #[must_use]
    pub fn kind(&self) -> ParseErrorKind {
        self.kind
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.kind() {
            ParseErrorKind::NoDigits => f.write_str("no digits found"),
            ParseErrorKind::InvalidDigit => f.write_str("invalid digit found in string"),
            ParseErrorKind::AboveMax => f.write_str("number too high to fit in target range"),
            ParseErrorKind::BelowMin => f.write_str("number too low to fit in target range"),
        }
    }
}

#[cfg(feature = "std")]
impl Error for ParseError {}

/// The cause of the failure to parse the integer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseErrorKind {
    /// No digits were found in the input string.
    ///
    /// This happens when the input is an empty string, or when it only contains a `+` or `-`.
    #[non_exhaustive]
    NoDigits,
    /// An invalid digit was found in the input.
    #[non_exhaustive]
    InvalidDigit,
    /// The integer is too high to fit in the bounded integer's range.
    #[non_exhaustive]
    AboveMax,
    /// The integer is too low to fit in the bounded integer's range.
    #[non_exhaustive]
    BelowMin,
}

#[must_use]
pub const fn error_below_min() -> ParseError {
    ParseError {
        kind: ParseErrorKind::BelowMin,
    }
}
#[must_use]
pub const fn error_above_max() -> ParseError {
    ParseError {
        kind: ParseErrorKind::AboveMax,
    }
}
