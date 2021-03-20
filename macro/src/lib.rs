//! A macro for generating bounded integer structs and enums.
#![warn(
    clippy::pedantic,
    rust_2018_idioms,
    missing_docs,
    unused_qualifications
)]

use std::borrow::Borrow;
use std::cmp;
use std::convert::TryInto;
use std::fmt::{self, Display, Formatter};
use std::ops::RangeInclusive;

use proc_macro2::{Ident, Literal, Span, TokenStream};
use quote::{quote, ToTokens, TokenStreamExt as _};
use syn::parse::{self, Parse, ParseStream, Parser};
use syn::{braced, parse_macro_input, token::Brace, Token};
use syn::{Attribute, Error, Expr, Path, PathArguments, PathSegment, Visibility};
use syn::{BinOp, ExprBinary, ExprRange, ExprUnary, RangeLimits, UnOp};
use syn::{ExprGroup, ExprParen};
use syn::{ExprLit, Lit};

use num_bigint::{BigInt, TryFromBigIntError};

mod generate;

/// Generate a bounded integer type.
///
/// It takes in single struct or enum, with the content being a bounded range expression, whose
/// upper bound can be inclusive (`x..=y`) or exclusive (`x..y`). The attributes and visibility
/// (e.g. `pub`) of the type are forwarded directly to the output type.
///
/// # Examples
///
/// With a struct:
/// ```
/// # mod force_item_scope {
/// # use bounded_integer_macro::bounded_integer;
/// # #[cfg(not(feature = "serde"))]
/// bounded_integer! {
///     pub struct S { -3..2 }
/// }
/// # }
/// ```
/// The generated item should look like this (i8 is chosen as it is the smallest repr):
/// ```
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// #[repr(transparent)]
/// pub struct S(i8);
/// ```
/// And the methods will ensure that `-3 <= S.0 < 2`.
///
/// With an enum:
/// ```
/// # mod force_item_scope {
/// # use bounded_integer_macro::bounded_integer;
/// # #[cfg(not(feature = "serde"))]
/// bounded_integer! {
///     pub enum S { 5..=7 }
/// }
/// # }
/// ```
/// The generated item should look like this (u8 is chosen as it is the smallest repr):
/// ```
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// #[repr(u8)]
/// pub enum S {
///     P5 = 5, P6, P7
/// }
/// ```
///
/// # Custom repr
///
/// The item can have a `repr` attribute to specify how it will be represented in memory, which can
/// be a `u*` or `i*` type. In this example we override the `repr` to be a `u16`, when it would
/// have normally been a `u8`.
///
/// ```
/// # mod force_item_scope {
/// # use bounded_integer_macro::bounded_integer;
/// # #[cfg(not(feature = "serde"))]
/// bounded_integer! {
///     #[repr(u16)]
///     pub struct S { 2..5 }
/// }
/// # }
/// ```
/// The generated item should look like this:
/// ```
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// #[repr(transparent)]
/// pub struct S(u16);
/// ```
///
/// # Custom path to bounded integer
///
/// `bounded-integer` will assume that it is located at `::bounded_integer` by default. You can
/// override this by adding a `bounded_integer` attribute to your item. For example if
/// `bounded_integer` is instead located at `path::to::bounded_integer`:
///
/// ```ignore
/// # mod force_item_scope {
/// # use bounded_integer_macro::bounded_integer;
/// bounded_integer! {
///     #[repr(i8)]
///     #[bounded_integer = path::to::bounded_integer]
///     pub struct S { 5..7 }
/// }
/// # }
/// ```
///
/// # Limitations
///
/// - Both bounds of ranges must be closed and a simple const expression involving only literals and
/// the following operators:
///     - Negation (`-x`)
///     - Addition (`x+y`), subtraction (`x-y`), multiplication (`x*y`), division (`x/y`) and
///     remainder (`x%y`).
///     - Bitwise not (`!x`), XOR (`x^y`), AND (`x&y`) and OR (`x|y`).
#[proc_macro]
pub fn bounded_integer(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let mut item = parse_macro_input!(input as BoundedInteger);

    // Hide in a module to prevent access to private parts.
    let module_name = Ident::new(
        &format!("__bounded_integer_private_{}", item.ident),
        item.ident.span(),
    );
    let ident = &item.ident;
    let original_visibility = item.vis;

    let import = quote!(#original_visibility use #module_name::#ident);

    item.vis = raise_one_level(original_visibility);
    let mut result = TokenStream::new();
    generate::generate(&item, &mut result);

    quote!(
        #[allow(non_snake_case)]
        mod #module_name {
            #result
        }
        #import;
    )
    .into()
}

macro_rules! signed {
    (unsigned) => {
        false
    };
    (signed) => {
        true
    };
}

struct BoundedInteger {
    attrs: Vec<Attribute>,
    crate_path: TokenStream,
    repr: Repr,
    vis: Visibility,
    kind: Kind,
    ident: Ident,
    brace_token: Brace,
    range: RangeInclusive<BigInt>,
}

impl Parse for BoundedInteger {
    fn parse(input: ParseStream<'_>) -> parse::Result<Self> {
        let mut attrs = input.call(Attribute::parse_outer)?;

        let repr_pos = attrs.iter().position(|attr| attr.path.is_ident("repr"));
        let repr = repr_pos
            .map(|pos| attrs.remove(pos).parse_args::<Repr>())
            .transpose()?;

        let crate_path = attrs
            .iter()
            .position(|attr| attr.path.is_ident("bounded_integer"))
            .map(|pos| {
                (|input: ParseStream<'_>| {
                    input.parse::<Token![=]>()?;
                    input.parse::<Path>()
                })
                .parse2(attrs.remove(pos).tokens)
            })
            .transpose()?
            .map_or_else(|| quote!(::bounded_integer), Path::into_token_stream);

        let vis: Visibility = input.parse()?;

        let kind: Kind = input.parse()?;

        let ident: Ident = input.parse()?;

        let range_tokens;
        let brace_token = braced!(range_tokens in input);
        let range: ExprRange = range_tokens.parse()?;

        let (from_expr, to_expr) = match range.from.as_deref().zip(range.to.as_deref()) {
            Some(t) => t,
            None => return Err(Error::new_spanned(range, "Range must be closed")),
        };
        let from = eval_expr(from_expr)?;
        let to = eval_expr(to_expr)?;
        let to = if let RangeLimits::HalfOpen(_) = range.limits {
            to - 1
        } else {
            to
        };
        if from >= to {
            return Err(Error::new_spanned(
                range,
                "The start of the range must be before the end",
            ));
        }

        let repr = match repr {
            Some(explicit_repr) => {
                if !explicit_repr.signed && from.sign() == num_bigint::Sign::Minus {
                    return Err(Error::new_spanned(
                        from_expr,
                        "An unsigned integer cannot hold a negative value",
                    ));
                }

                if explicit_repr.minimum().map_or(false, |min| from < min) {
                    return Err(Error::new_spanned(
                        from_expr,
                        format_args!(
                            "Bound {} is below the minimum value for the underlying type",
                            from
                        ),
                    ));
                }
                if explicit_repr.maximum().map_or(false, |max| to > max) {
                    return Err(Error::new_spanned(
                        to_expr,
                        format_args!(
                            "Bound {} is above the maximum value for the underlying type",
                            to
                        ),
                    ));
                }

                explicit_repr
            }
            None => Repr::smallest_repr(&from, &to).ok_or_else(|| {
                Error::new_spanned(range, "Range is too wide to fit in any integer primitive")
            })?,
        };

        Ok(Self {
            attrs,
            crate_path,
            repr,
            vis,
            kind,
            ident,
            brace_token,
            range: from..=to,
        })
    }
}

enum Kind {
    Struct(Token![struct]),
    Enum(Token![enum]),
}

impl Parse for Kind {
    fn parse(input: ParseStream<'_>) -> parse::Result<Self> {
        Ok(if input.peek(Token![struct]) {
            Self::Struct(input.parse()?)
        } else {
            Self::Enum(input.parse()?)
        })
    }
}

struct Repr {
    signed: bool,
    size: ReprSize,
    name: Ident,
}

impl Repr {
    fn new(signed: bool, size: ReprSize) -> Self {
        Self {
            signed,
            size,
            name: Ident::new(
                &format!("{}{}", if signed { 'i' } else { 'u' }, size),
                Span::call_site(),
            ),
        }
    }

    fn smallest_repr(min: &BigInt, max: &BigInt) -> Option<Self> {
        Some(if min.sign() == num_bigint::Sign::Minus {
            Self::new(
                true,
                ReprSize::Fixed(cmp::max(
                    ReprSizeFixed::from_bits((min + 1_u8).bits() + 1)?,
                    ReprSizeFixed::from_bits(max.bits() + 1)?,
                )),
            )
        } else {
            Self::new(
                false,
                ReprSize::Fixed(ReprSizeFixed::from_bits(max.bits())?),
            )
        })
    }

    fn minimum(&self) -> Option<BigInt> {
        Some(match (self.signed, self.size) {
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed8)) => BigInt::from(u8::MIN),
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed16)) => BigInt::from(u16::MIN),
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed32)) => BigInt::from(u32::MIN),
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed64)) => BigInt::from(u64::MIN),
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed128)) => BigInt::from(u128::MIN),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed8)) => BigInt::from(i8::MIN),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed16)) => BigInt::from(i16::MIN),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed32)) => BigInt::from(i32::MIN),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed64)) => BigInt::from(i64::MIN),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed128)) => BigInt::from(i128::MIN),
            (_, ReprSize::Pointer) => return None,
        })
    }

    fn maximum(&self) -> Option<BigInt> {
        Some(match (self.signed, self.size) {
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed8)) => BigInt::from(u8::MAX),
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed16)) => BigInt::from(u16::MAX),
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed32)) => BigInt::from(u32::MAX),
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed64)) => BigInt::from(u64::MAX),
            (false, ReprSize::Fixed(ReprSizeFixed::Fixed128)) => BigInt::from(u128::MAX),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed8)) => BigInt::from(i8::MAX),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed16)) => BigInt::from(i16::MAX),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed32)) => BigInt::from(i32::MAX),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed64)) => BigInt::from(i64::MAX),
            (true, ReprSize::Fixed(ReprSizeFixed::Fixed128)) => BigInt::from(i128::MAX),
            (_, ReprSize::Pointer) => return None,
        })
    }

    fn try_number_literal(
        &self,
        value: impl Borrow<BigInt>,
    ) -> Result<Literal, TryFromBigIntError<()>> {
        macro_rules! match_repr {
            ($($sign:ident $size:ident $(($fixed:ident))? => $f:ident,)*) => {
                match (self.signed, self.size) {
                    $((signed!($sign), ReprSize::$size $((ReprSizeFixed::$fixed))?) => {
                        Ok(Literal::$f(value.borrow().try_into()?))
                    })*
                }
            }
        }

        match_repr! {
            unsigned Fixed(Fixed8) => u8_suffixed,
            unsigned Fixed(Fixed16) => u16_suffixed,
            unsigned Fixed(Fixed32) => u32_suffixed,
            unsigned Fixed(Fixed64) => u64_suffixed,
            unsigned Fixed(Fixed128) => u128_suffixed,
            unsigned Pointer => usize_suffixed,
            signed Fixed(Fixed8) => i8_suffixed,
            signed Fixed(Fixed16) => i16_suffixed,
            signed Fixed(Fixed32) => i32_suffixed,
            signed Fixed(Fixed64) => i64_suffixed,
            signed Fixed(Fixed128) => i128_suffixed,
            signed Pointer => isize_suffixed,
        }
    }

    fn number_literal(&self, value: impl Borrow<BigInt>) -> Literal {
        self.try_number_literal(value).unwrap()
    }

    fn larger_reprs(&self) -> impl Iterator<Item = Self> {
        if self.signed {
            Either::A(self.size.larger_reprs().map(|size| Self::new(true, size)))
        } else {
            Either::B(
                self.size
                    .larger_reprs()
                    .map(|size| Self::new(false, size))
                    .chain(
                        self.size
                            .larger_reprs()
                            .skip(1)
                            .map(|size| Self::new(true, size)),
                    ),
            )
        }
    }
}

impl Parse for Repr {
    fn parse(input: ParseStream<'_>) -> parse::Result<Self> {
        let name = input.parse::<Ident>()?;
        let span = name.span();
        let s = name.to_string();

        let (size, signed) = if let Some(size) = s.strip_prefix("i") {
            (size, true)
        } else if let Some(size) = s.strip_prefix("u") {
            (size, false)
        } else {
            return Err(Error::new(span, "Repr must a primitive integer type"));
        };

        let size = match size {
            "8" => ReprSize::Fixed(ReprSizeFixed::Fixed8),
            "16" => ReprSize::Fixed(ReprSizeFixed::Fixed16),
            "32" => ReprSize::Fixed(ReprSizeFixed::Fixed32),
            "64" => ReprSize::Fixed(ReprSizeFixed::Fixed64),
            "128" => ReprSize::Fixed(ReprSizeFixed::Fixed128),
            "size" => ReprSize::Pointer,
            unknown => {
                return Err(Error::new(
                    span,
                    format_args!(
                        "Unknown integer size {}, must be one of 8, 16, 32, 64, 128 or size",
                        unknown
                    ),
                ));
            }
        };

        Ok(Self { signed, size, name })
    }
}

impl ToTokens for Repr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append(self.name.clone());
    }
}

#[derive(Clone, Copy)]
enum ReprSize {
    Fixed(ReprSizeFixed),
    /// `usize`/`isize`
    Pointer,
}

impl ReprSize {
    fn larger_reprs(self) -> impl Iterator<Item = Self> {
        match self {
            Self::Fixed(fixed) => Either::A(fixed.larger_reprs().map(Self::Fixed)),
            Self::Pointer => Either::B(std::iter::once(Self::Pointer)),
        }
    }
}

impl Display for ReprSize {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fixed(fixed) => fixed.fmt(f),
            Self::Pointer => f.write_str("size"),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
enum ReprSizeFixed {
    Fixed8,
    Fixed16,
    Fixed32,
    Fixed64,
    Fixed128,
}

impl ReprSizeFixed {
    fn from_bits(bits: u64) -> Option<Self> {
        Some(match bits {
            0..=8 => Self::Fixed8,
            9..=16 => Self::Fixed16,
            17..=32 => Self::Fixed32,
            33..=64 => Self::Fixed64,
            65..=128 => Self::Fixed128,
            129..=u64::MAX => return None,
        })
    }

    fn larger_reprs(self) -> impl Iterator<Item = Self> {
        const REPRS: [ReprSizeFixed; 5] = [
            ReprSizeFixed::Fixed8,
            ReprSizeFixed::Fixed16,
            ReprSizeFixed::Fixed32,
            ReprSizeFixed::Fixed64,
            ReprSizeFixed::Fixed128,
        ];
        let index = match self {
            Self::Fixed8 => 0,
            Self::Fixed16 => 1,
            Self::Fixed32 => 2,
            Self::Fixed64 => 3,
            Self::Fixed128 => 4,
        };
        REPRS[index..].iter().copied()
    }
}

impl Display for ReprSizeFixed {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Fixed8 => "8",
            Self::Fixed16 => "16",
            Self::Fixed32 => "32",
            Self::Fixed64 => "64",
            Self::Fixed128 => "128",
        })
    }
}

fn eval_expr(expr: &Expr) -> syn::Result<BigInt> {
    Ok(match expr {
        Expr::Lit(ExprLit { lit, .. }) => match lit {
            Lit::Int(int) => int.base10_parse()?,
            _ => {
                return Err(Error::new_spanned(lit, "literal must be integer"));
            }
        },
        Expr::Unary(ExprUnary { op, expr, .. }) => {
            let expr = eval_expr(&expr)?;
            match op {
                UnOp::Not(_) => !expr,
                UnOp::Neg(_) => -expr,
                _ => {
                    return Err(Error::new_spanned(op, "unary operator must be ! or -"));
                }
            }
        }
        Expr::Binary(ExprBinary {
            left, op, right, ..
        }) => {
            let left = eval_expr(&left)?;
            let right = eval_expr(&right)?;
            match op {
                BinOp::Add(_) => left + right,
                BinOp::Sub(_) => left - right,
                BinOp::Mul(_) => left * right,
                BinOp::Div(_) => left
                    .checked_div(&right)
                    .ok_or_else(|| Error::new_spanned(op, "Attempted to divide by zero"))?,
                BinOp::Rem(_) => left % right,
                BinOp::BitXor(_) => left ^ right,
                BinOp::BitAnd(_) => left & right,
                BinOp::BitOr(_) => left | right,
                _ => {
                    return Err(Error::new_spanned(
                        op,
                        "operator not supported in this context",
                    ));
                }
            }
        }
        Expr::Group(ExprGroup { expr, .. }) | Expr::Paren(ExprParen { expr, .. }) => {
            eval_expr(expr)?
        }
        _ => return Err(Error::new_spanned(expr, "expected simple expression")),
    })
}

/// Raise a visibility one level.
///
/// ```text
/// no visibility -> pub(super)
/// pub(self) -> pub(super)
/// pub(in self) -> pub(in super)
/// pub(in self::some::path) -> pub(in super::some::path)
/// pub(super) -> pub(in super::super)
/// pub(in super) -> pub(in super::super)
/// pub(in super::some::path) -> pub(in super::super::some::path)
/// ```
fn raise_one_level(vis: Visibility) -> Visibility {
    match vis {
        Visibility::Inherited => syn::parse2(quote!(pub(super))).unwrap(),
        Visibility::Restricted(mut restricted)
            if restricted.path.segments.first().unwrap().ident == "self" =>
        {
            let first = &mut restricted.path.segments.first_mut().unwrap().ident;
            *first = Ident::new("super", first.span());
            Visibility::Restricted(restricted)
        }
        Visibility::Restricted(mut restricted)
            if restricted.path.segments.first().unwrap().ident == "super" =>
        {
            restricted
                .in_token
                .get_or_insert_with(<Token![in]>::default);
            let first = PathSegment {
                ident: restricted.path.segments.first().unwrap().ident.clone(),
                arguments: PathArguments::None,
            };
            restricted.path.segments.insert(0, first);
            Visibility::Restricted(restricted)
        }
        absolute_visibility => absolute_visibility,
    }
}

#[test]
fn test_raise_one_level() {
    fn assert_output(input: TokenStream, output: TokenStream) {
        let tokens = raise_one_level(syn::parse2(input).unwrap()).into_token_stream();
        assert_eq!(tokens.to_string(), output.to_string());
        drop(output);
    }

    assert_output(TokenStream::new(), quote!(pub(super)));
    assert_output(quote!(pub(self)), quote!(pub(super)));
    assert_output(quote!(pub(in self)), quote!(pub(in super)));
    assert_output(
        quote!(pub(in self::some::path)),
        quote!(pub(in super::some::path)),
    );
    assert_output(quote!(pub(super)), quote!(pub(in super::super)));
    assert_output(quote!(pub(in super)), quote!(pub(in super::super)));
    assert_output(
        quote!(pub(in super::some::path)),
        quote!(pub(in super::super::some::path)),
    );

    assert_output(quote!(pub), quote!(pub));
    assert_output(quote!(pub(crate)), quote!(pub(crate)));
    assert_output(quote!(crate), quote!(crate));
    assert_output(quote!(pub(in crate)), quote!(pub(in crate)));
    assert_output(
        quote!(pub(in crate::some::path)),
        quote!(pub(in crate::some::path)),
    );
}

enum Either<A, B> {
    A(A),
    B(B),
}
impl<T, A: Iterator<Item = T>, B: Iterator<Item = T>> Iterator for Either<A, B> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::A(a) => a.next(),
            Self::B(b) => b.next(),
        }
    }
}
