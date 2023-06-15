//! A macro for generating bounded integer structs and enums.
//!
//! This crate is unstable and must not be used directly.
#![warn(clippy::pedantic, rust_2018_idioms, unused_qualifications)]

use std::borrow::Borrow;
use std::cmp;
use std::convert::TryInto;
use std::fmt::{self, Display, Formatter};
use std::ops::RangeInclusive;

use proc_macro2::{Group, Ident, Literal, Span, TokenStream};
use quote::{quote, ToTokens, TokenStreamExt as _};
use syn::parse::{self, Parse, ParseStream};
use syn::{braced, parse_macro_input, token::Brace, Token};
use syn::{Attribute, Error, Expr, PathArguments, PathSegment, Visibility};
use syn::{BinOp, ExprBinary, ExprRange, ExprUnary, RangeLimits, UnOp};
use syn::{ExprGroup, ExprParen};
use syn::{ExprLit, Lit, LitBool};

use num_bigint::{BigInt, Sign, TryFromBigIntError};

mod generate;

#[proc_macro]
#[doc(hidden)]
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

#[allow(clippy::struct_excessive_bools)]
struct BoundedInteger {
    // $crate
    crate_path: TokenStream,

    // Optional features
    alloc: bool,
    arbitrary1: bool,
    bytemuck1: bool,
    serde1: bool,
    std: bool,
    zerocopy06: bool,
    step_trait: bool,

    // The item itself
    attrs: Vec<Attribute>,
    repr: Repr,
    vis: Visibility,
    kind: Kind,
    ident: Ident,
    brace_token: Brace,
    range: RangeInclusive<BigInt>,
}

impl Parse for BoundedInteger {
    fn parse(input: ParseStream<'_>) -> parse::Result<Self> {
        let crate_path = input.parse::<Group>()?.stream();

        let alloc = input.parse::<LitBool>()?.value;
        let arbitrary1 = input.parse::<LitBool>()?.value;
        let bytemuck1 = input.parse::<LitBool>()?.value;
        let serde1 = input.parse::<LitBool>()?.value;
        let std = input.parse::<LitBool>()?.value;
        let zerocopy06 = input.parse::<LitBool>()?.value;
        let step_trait = input.parse::<LitBool>()?.value;

        let mut attrs = input.call(Attribute::parse_outer)?;

        let repr_pos = attrs.iter().position(|attr| attr.path().is_ident("repr"));
        let repr = repr_pos
            .map(|pos| attrs.remove(pos).parse_args::<Repr>())
            .transpose()?;

        let vis: Visibility = input.parse()?;

        let kind: Kind = input.parse()?;

        let ident: Ident = input.parse()?;

        let range_tokens;
        let brace_token = braced!(range_tokens in input);
        let range: ExprRange = range_tokens.parse()?;

        let Some((start_expr, end_expr)) = range.start.as_deref().zip(range.end.as_deref()) else {
            return Err(Error::new_spanned(range, "Range must be closed"))
        };
        let start = eval_expr(start_expr)?;
        let end = eval_expr(end_expr)?;
        let end = if let RangeLimits::HalfOpen(_) = range.limits {
            end - 1
        } else {
            end
        };
        if start >= end {
            return Err(Error::new_spanned(
                range,
                "The start of the range must be before the end",
            ));
        }

        let repr = match repr {
            Some(explicit_repr) => {
                if explicit_repr.sign == Unsigned && start.sign() == Sign::Minus {
                    return Err(Error::new_spanned(
                        start_expr,
                        "An unsigned integer cannot hold a negative value",
                    ));
                }

                if explicit_repr.minimum().map_or(false, |min| start < min) {
                    return Err(Error::new_spanned(
                        start_expr,
                        format_args!(
                            "Bound {start} is below the minimum value for the underlying type",
                        ),
                    ));
                }
                if explicit_repr.maximum().map_or(false, |max| end > max) {
                    return Err(Error::new_spanned(
                        end_expr,
                        format_args!(
                            "Bound {end} is above the maximum value for the underlying type",
                        ),
                    ));
                }

                explicit_repr
            }
            None => Repr::smallest_repr(&start, &end).ok_or_else(|| {
                Error::new_spanned(range, "Range is too wide to fit in any integer primitive")
            })?,
        };

        Ok(Self {
            crate_path,
            alloc,
            arbitrary1,
            bytemuck1,
            serde1,
            std,
            zerocopy06,
            step_trait,
            attrs,
            repr,
            vis,
            kind,
            ident,
            brace_token,
            range: start..=end,
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum ReprSign {
    Signed,
    Unsigned,
}
use ReprSign::{Signed, Unsigned};

struct Repr {
    sign: ReprSign,
    size: ReprSize,
    name: Ident,
}

impl Repr {
    fn new(sign: ReprSign, size: ReprSize) -> Self {
        let prefix = match sign {
            Signed => 'i',
            Unsigned => 'u',
        };
        Self {
            sign,
            size,
            name: Ident::new(&format!("{prefix}{size}"), Span::call_site()),
        }
    }

    fn smallest_repr(min: &BigInt, max: &BigInt) -> Option<Self> {
        // NOTE: Never infer nonzero types, even if we can.
        Some(if min.sign() == Sign::Minus {
            Self::new(
                Signed,
                ReprSize::Fixed(cmp::max(
                    ReprSizeFixed::from_bits((min + 1_u8).bits() + 1)?,
                    ReprSizeFixed::from_bits(max.bits() + 1)?,
                )),
            )
        } else {
            Self::new(
                Unsigned,
                ReprSize::Fixed(ReprSizeFixed::from_bits(max.bits())?),
            )
        })
    }

    fn minimum(&self) -> Option<BigInt> {
        Some(match (self.sign, self.size) {
            (Unsigned, ReprSize::Fixed(_)) => BigInt::from(0u8),
            (Signed, ReprSize::Fixed(size)) => -(BigInt::from(1u8) << (size.to_bits() - 1)),
            (_, ReprSize::Pointer) => return None,
        })
    }

    fn maximum(&self) -> Option<BigInt> {
        Some(match (self.sign, self.size) {
            (Unsigned, ReprSize::Fixed(size)) => (BigInt::from(1u8) << size.to_bits()) - 1,
            (Signed, ReprSize::Fixed(size)) => (BigInt::from(1u8) << (size.to_bits() - 1)) - 1,
            (_, ReprSize::Pointer) => return None,
        })
    }

    fn try_number_literal(
        &self,
        value: impl Borrow<BigInt>,
    ) -> Result<Literal, TryFromBigIntError<()>> {
        macro_rules! match_repr {
            ($($sign:ident $size:ident $(($fixed:ident))? => $f:ident,)*) => {
                match (self.sign, self.size) {
                    $(($sign, ReprSize::$size $((ReprSizeFixed::$fixed))?) => {
                        Ok(Literal::$f(value.borrow().try_into()?))
                    })*
                }
            }
        }

        match_repr! {
            Unsigned Fixed(Fixed8) => u8_suffixed,
            Unsigned Fixed(Fixed16) => u16_suffixed,
            Unsigned Fixed(Fixed32) => u32_suffixed,
            Unsigned Fixed(Fixed64) => u64_suffixed,
            Unsigned Fixed(Fixed128) => u128_suffixed,
            Unsigned Pointer => usize_suffixed,
            Signed Fixed(Fixed8) => i8_suffixed,
            Signed Fixed(Fixed16) => i16_suffixed,
            Signed Fixed(Fixed32) => i32_suffixed,
            Signed Fixed(Fixed64) => i64_suffixed,
            Signed Fixed(Fixed128) => i128_suffixed,
            Signed Pointer => isize_suffixed,
        }
    }

    fn number_literal(&self, value: impl Borrow<BigInt>) -> Literal {
        self.try_number_literal(value).unwrap()
    }

    fn larger_reprs(&self) -> impl Iterator<Item = Self> {
        match self.sign {
            Signed => Either::A(self.size.larger_reprs().map(|size| Self::new(Signed, size))),
            Unsigned => Either::B(
                self.size
                    .larger_reprs()
                    .map(|size| Self::new(Unsigned, size))
                    .chain(
                        self.size
                            .larger_reprs()
                            .skip(1)
                            .map(|size| Self::new(Signed, size)),
                    ),
            ),
        }
    }

    fn is_usize(&self) -> bool {
        matches!((self.sign, self.size), (Unsigned, ReprSize::Pointer))
    }
}

impl Parse for Repr {
    fn parse(input: ParseStream<'_>) -> parse::Result<Self> {
        let name = input.parse::<Ident>()?;
        let span = name.span();
        let s = name.to_string();

        let (size, sign) = if let Some(size) = s.strip_prefix('i') {
            (size, Signed)
        } else if let Some(size) = s.strip_prefix('u') {
            (size, Unsigned)
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
                        "Unknown integer size {unknown}, must be one of 8, 16, 32, 64, 128 or size",
                    ),
                ));
            }
        };

        Ok(Self { sign, size, name })
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
    fn to_bits(self) -> u64 {
        match self {
            ReprSizeFixed::Fixed8 => 8,
            ReprSizeFixed::Fixed16 => 16,
            ReprSizeFixed::Fixed32 => 32,
            ReprSizeFixed::Fixed64 => 64,
            ReprSizeFixed::Fixed128 => 128,
        }
    }

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
            Lit::Byte(byte) => byte.value().into(),
            Lit::Int(int) => int.base10_parse()?,
            _ => {
                return Err(Error::new_spanned(lit, "literal must be integer"));
            }
        },
        Expr::Unary(ExprUnary { op, expr, .. }) => {
            let expr = eval_expr(expr)?;
            match op {
                UnOp::Not(_) => !expr,
                UnOp::Neg(_) => -expr,
                _ => return Err(Error::new_spanned(op, "unary operator must be ! or -")),
            }
        }
        Expr::Binary(ExprBinary {
            left, op, right, ..
        }) => {
            let left = eval_expr(left)?;
            let right = eval_expr(right)?;
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
    #[track_caller]
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
