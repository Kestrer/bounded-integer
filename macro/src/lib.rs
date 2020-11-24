//! A macro for generating bounded integer structs and enums.

use std::cmp::Ordering;
use std::iter;
use std::ops::RangeInclusive;

use proc_macro2::{Ident, Literal, Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens, TokenStreamExt as _};
use syn::parse::{self, Parse, ParseStream};
use syn::{braced, parse_macro_input, token::Brace, Token};
use syn::{Attribute, Error, Expr, Path, PathSegment, Visibility};
use syn::{BinOp, ExprBinary, ExprRange, ExprUnary, RangeLimits, UnOp};
use syn::{ExprGroup, ExprParen};
use syn::{ExprLit, Lit};

/// Generate a bounded integer type.
///
/// It takes in single struct or enum, with the content being any range expression, which can be
/// inclusive or not. The attributes and visibility (e.g. `pub`) of the type are forwarded directly
/// to the output type. It also implements:
/// * `Debug`, `Display`, `Binary`, `LowerExp`, `LowerHex`, `Octal`, `UpperExp` and `UpperHex`
/// * `Hash`
/// * `Clone` and `Copy`
/// * `PartialEq` and `Eq`
/// * `PartialOrd` and `Ord`
/// * If the `serde` feature is enabled, `Serialize` and `Deserialize`
///
/// The item must have a `repr` attribute to specify how it will be represented in memory, and it
/// must be a `u*` or `i*` type.
///
/// # Examples
/// With a struct:
/// ```rust
/// # mod force_item_scope {
/// # use bounded_integer_macro::bounded_integer;
/// # #[cfg(not(feature = "serde"))]
/// bounded_integer! {
///     #[repr(i8)]
///     pub struct S { -3..2 }
/// }
/// # }
/// ```
/// The generated item should look like this:
/// ```rust
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// pub struct S(i8);
/// ```
/// And the methods will ensure that `-3 <= S.0 < 2`.
///
/// With an enum:
/// ```rust
/// # mod force_item_scope {
/// # use bounded_integer_macro::bounded_integer;
/// # #[cfg(not(feature = "serde"))]
/// bounded_integer! {
///     #[repr(u8)]
///     pub enum S { 5..=7 }
/// }
/// # }
/// ```
/// The generated item should look like this:
/// ```rust
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// #[repr(u8)]
/// pub enum S {
///     P5 = 5, P6, P7
/// }
/// ```
///
/// # Custom path to bounded integer
///
/// If your are using the `serde` feature and have `bounded_integer` at a path other than
/// `::bounded_integer`, then you will need to tell `bounded_integer` the correct path. For example
/// if `bounded_integer` is instead located at `path::to::bounded_integer`:
///
/// ```rust
/// # mod force_item_scope {
/// # use bounded_integer_macro::bounded_integer;
/// # #[cfg(not(feature = "serde"))]
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
/// - Both bounds of enum ranges must be closed and be a simple const expression involving only
/// literals and the following operators:
///     - Negation (`-x`)
///     - Addition (`x+y`), subtraction (`x-y`), multiplication (`x*y`), division (`x/y`) and
///     remainder (`x%y`).
///     - Bitwise not (`!x`), XOR (`x^y`), AND (`x&y`) and OR (`x|y`).
/// - The above limitations do not apply to struct ranges.

#[proc_macro]
pub fn bounded_integer(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let bounded_integer = parse_macro_input!(input as BoundedInteger);

    let mut result = TokenStream::new();
    bounded_integer.generate_item(&mut result);
    bounded_integer.generate_impl(&mut result);
    result.into()
}

struct BoundedInteger {
    attrs: Vec<Attribute>,
    crate_location: Path,
    repr: Repr,
    vis: Visibility,
    ident: Ident,
    brace_token: Brace,
    kind: Kind,
}

struct Repr {
    span: Span,
    signed: bool,
    size: ReprSize,
    origin: Ident,
}

impl Parse for Repr {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        let ident = input.parse::<Ident>()?;
        let span = ident.span();
        let s = ident.to_string();

        let (size, signed) = if let Some(size) = s.strip_prefix("i") {
            (size, true)
        } else if let Some(size) = s.strip_prefix("u") {
            (size, false)
        } else {
            return Err(Error::new(span, "Repr must a primitive integer type"));
        };

        let size = match size {
            "8" => ReprSize::Fixed8,
            "16" => ReprSize::Fixed16,
            "32" => ReprSize::Fixed32,
            "64" => ReprSize::Fixed64,
            "128" => ReprSize::Fixed128,
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

        Ok(Self { span, signed, size, origin: ident })
    }
}

impl ToTokens for Repr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append(self.origin.clone());
    }
}

enum ReprSize {
    Fixed8,
    Fixed16,
    Fixed32,
    Fixed64,
    Fixed128,
    /// `usize`/`isize`
    Pointer,
}

enum Kind {
    Struct {
        struct_token: Token![struct],
        range: Box<(Option<Expr>, Option<Expr>)>,
    },
    Enum {
        enum_token: Token![enum],
        range: RangeInclusive<isize>,
        semi_token: Option<Token![;]>,
    },
}

impl BoundedInteger {
    fn generate_item(&self, tokens: &mut TokenStream) {
        let repr = &self.repr;

        for attr in &self.attrs {
            attr.to_tokens(tokens);
        }
        tokens.extend(quote! {
            #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        });

        if let Kind::Enum { .. } = &self.kind {
            tokens.extend(quote!(#[repr(#repr)]));
        }

        self.vis.to_tokens(tokens);

        match &self.kind {
            Kind::Enum { enum_token, .. } => enum_token.to_tokens(tokens),
            Kind::Struct { struct_token, .. } => struct_token.to_tokens(tokens),
        }

        self.ident.to_tokens(tokens);

        match &self.kind {
            Kind::Struct { .. } => {
                tokens.extend(quote_spanned!(self.brace_token.span=> (::core::primitive::#repr);));
            }
            Kind::Enum {
                range, semi_token, ..
            } => {
                let mut inner_tokens = TokenStream::new();

                let mut variants = range.clone().map(enum_variant);

                if let Some(first_variant) = variants.next() {
                    let start = Literal::isize_unsuffixed(*range.start());
                    inner_tokens.extend(quote!(#first_variant = #start));
                }
                for variant in variants {
                    inner_tokens.extend(quote!(, #variant));
                }

                tokens.extend(quote_spanned!(self.brace_token.span=> { #inner_tokens }));
                semi_token.to_tokens(tokens);
            }
        }
    }

    fn generate_consts(&self, tokens: &mut TokenStream) {
        let repr = &self.repr;

        let (min_value, min, max_value, max);
        match &self.kind {
            Kind::Struct { range, .. } => {
                min_value = range
                    .0
                    .as_ref()
                    .map_or_else(|| quote!(::core::primitive::#repr::MIN), ToTokens::into_token_stream);
                min = quote!(Self(Self::MIN_VALUE));
                max_value = range
                    .1
                    .as_ref()
                    .map_or_else(|| quote!(::core::primitive::#repr::MAX), ToTokens::into_token_stream);
                max = quote!(Self(Self::MAX_VALUE));
            }
            Kind::Enum { range, .. } => {
                min_value = Literal::isize_unsuffixed(*range.start()).into_token_stream();
                max_value = Literal::isize_unsuffixed(*range.end()).into_token_stream();
                let min_variant = enum_variant(*range.start());
                let max_variant = enum_variant(*range.end());
                min = quote!(Self::#min_variant);
                max = quote!(Self::#max_variant);
            }
        }

        let vis = &self.vis;

        tokens.extend(quote! {
            /// The smallest value that this bounded integer can contain.
            #vis const MIN_VALUE: ::core::primitive::#repr = #min_value;
            /// The largest value that this bounded integer can contain.
            #vis const MAX_VALUE: ::core::primitive::#repr = #max_value;

            /// The smallest value of the bounded integer.
            #vis const MIN: Self = #min;
            /// The largest value of the bounded integer.
            #vis const MAX: Self = #max;

            /// The number of values the bounded integer can contain.
            #vis const RANGE: ::core::primitive::#repr = Self::MAX_VALUE - Self::MIN_VALUE + 1;
        });
    }

    fn generate_base(&self, tokens: &mut TokenStream) {
        let repr = &self.repr;

        let (get_body, new_body, low_bounded, high_bounded) = match &self.kind {
            Kind::Struct { range, .. } => (
                quote!(self.0),
                quote!(Self(n)),
                range.0.is_some(),
                range.1.is_some(),
            ),
            Kind::Enum { .. } => (
                quote!(self as ::core::primitive::#repr),
                quote!(::core::mem::transmute::<::core::primitive::#repr, Self>(n)),
                true,
                true,
            ),
        };

        let low_check = if low_bounded {
            quote!(n >= Self::MIN_VALUE)
        } else {
            quote!(true)
        };
        let high_check = if high_bounded {
            quote!(n <= Self::MAX_VALUE)
        } else {
            quote!(true)
        };

        let vis = &self.vis;

        tokens.extend(quote! {
            /// Creates a bounded integer without checking the value.
            ///
            /// # Safety
            ///
            /// The value must not be outside the valid range of values; it must not be less than
            /// `MIN` or greater than `MAX`.
            #[must_use]
            #vis unsafe fn new_unchecked(n: ::core::primitive::#repr) -> Self {
                #new_body
            }

            /// Checks whether the given value is in the range of the bounded integer.
            #[must_use]
            #vis fn in_range(n: ::core::primitive::#repr) -> ::core::primitive::bool {
                #low_check && #high_check
            }

            /// Creates a bounded integer if the given value is within the range [`MIN`, `MAX`].
            #[must_use]
            #vis fn new(n: ::core::primitive::#repr) -> ::core::option::Option<Self> {
                if Self::in_range(n) {
                    // SAFETY: We just asserted that the value is in range.
                    ::core::option::Option::Some(unsafe { Self::new_unchecked(n) })
                } else {
                    ::core::option::Option::None
                }
            }

            /// Creates a bounded integer by setting the value to `MIN` or `MAX` if it is too low
            /// or too high respectively.
            #[must_use]
            #vis fn new_saturating(n: ::core::primitive::#repr) -> Self {
                if !(#low_check) {
                    Self::MIN
                } else if !(#high_check) {
                    Self::MAX
                } else {
                    // SAFETY: This branch can only happen if n is in range.
                    unsafe { Self::new_unchecked(n) }
                }
            }

            /// Creates a bounded integer by using modulo arithmetic. Values in the range won't be
            /// changed but values outside will be wrapped around.
            #[must_use]
            #vis fn new_wrapping(n: ::core::primitive::#repr) -> Self {
                unsafe {
                    Self::new_unchecked(
                        (n + (Self::RANGE - (Self::MIN_VALUE.rem_euclid(Self::RANGE)))).rem_euclid(Self::RANGE)
                            + Self::MIN_VALUE
                    )
                }
            }

            /// Gets the value of the bounded integer as a primitive type.
            #[must_use]
            #vis fn get(self) -> ::core::primitive::#repr {
                #get_body
            }
        });
    }

    fn generate_operators(&self, tokens: &mut TokenStream) {
        let vis = &self.vis;
        let repr = &self.repr;

        if self.repr.signed {
            tokens.extend(quote! {
                /// Computes the absolute value of `self`, panicking if it is out of range.
                #[must_use]
                #vis fn abs(self) -> Self {
                    Self::new(self.get().abs()).expect("Absolute value out of range")
                }
            });
        }

        tokens.extend(quote! {
            /// Raises self to the power of `exp`, using exponentiation by squaring. Panics if it
            /// is out of range.
            #[must_use]
            #vis fn pow(self, exp: ::core::primitive::u32) -> Self {
                Self::new(self.get().pow(exp)).expect("Value raised to power out of range")
            }
            /// Calculates the quotient of Euclidean division of `self` by `rhs`. Panics if `rhs`
            /// is 0 or the result is out of range.
            #[must_use]
            #vis fn div_euclid(self, rhs: ::core::primitive::#repr) -> Self {
                Self::new(self.get().div_euclid(rhs)).expect("Attempted to divide out of range")
            }
            /// Calculates the least nonnegative remainder of `self (mod rhs)`. Panics if `rhs` is 0
            /// or the result is out of range.
            #[must_use]
            #vis fn rem_euclid(self, rhs: ::core::primitive::#repr) -> Self {
                Self::new(self.get().rem_euclid(rhs))
                    .expect("Attempted to divide with remainder out of range")
            }
        });
    }

    fn generate_ops_traits(&self, tokens: &mut TokenStream) {
        let repr = &self.repr;
        let full_repr = quote!(::core::primitive::#repr);

        for op in OPERATORS {
            if !self.repr.signed && !op.on_unsigned {
                continue;
            }

            let description = op.description;

            if op.bin {
                binop_trait_variations(
                    op.trait_name,
                    op.method,
                    &self.ident,
                    &full_repr,
                    |trait_name, method| {
                        quote! {
                            Self::new(<::core::primitive::#repr as ::core::ops::#trait_name>::#method(self.get(), rhs))
                                .expect(::core::concat!("Attempted to ", #description, " out of range"))
                        }
                    },
                    tokens,
                );

                binop_trait_variations(
                    op.trait_name,
                    op.method,
                    &self.ident,
                    &self.ident,
                    |trait_name, method| {
                        quote! {
                            <Self as ::core::ops::#trait_name<::core::primitive::#repr>>::#method(self, rhs.get())
                        }
                    },
                    tokens,
                );
            } else {
                let trait_name = Ident::new(op.trait_name, Span::call_site());
                let method = Ident::new(op.method, Span::call_site());

                unop_trait_variations(
                    &trait_name,
                    &method,
                    &self.ident,
                    &quote! {
                        Self::new(<::core::primitive::#repr as ::core::ops::#trait_name>::#method(self.get()))
                            .expect(::core::concat!("Attempted to ", #description, " out of range"))
                    },
                    tokens,
                );
            }
        }
    }

    fn generate_checked_operators(&self, tokens: &mut TokenStream) {
        let vis = &self.vis;

        for op in CHECKED_OPERATORS {
            let variants = if self.repr.signed {
                op.signed_variants
            } else {
                op.unsigned_variants
            };

            if variants == NoOps {
                continue;
            }

            let rhs = match op.rhs {
                Some("Self") => Some({
                    let repr = &self.repr;
                    quote!(::core::primitive::#repr)
                }),
                Some(name) => Some({
                    let ident = Ident::new(name, Span::call_site());
                    quote!(::core::primitive::#ident)
                }),
                None => None,
            };
            let rhs_type = rhs.as_ref().map(|ty| quote!(rhs: #ty,));
            let rhs_value = rhs.map(|_| quote!(rhs,));

            let checked_name = Ident::new(&format!("checked_{}", op.name), Span::call_site());
            let checked_comment = format!("Checked {}.", op.description);

            tokens.extend(quote! {
                #[doc = #checked_comment]
                #[must_use]
                #vis fn #checked_name(self, #rhs_type) -> ::core::option::Option<Self> {
                    self.get().#checked_name(#rhs_value).and_then(Self::new)
                }
            });

            if variants != All {
                continue;
            }

            let saturating_name = Ident::new(&format!("saturating_{}", op.name), Span::call_site());
            let saturating_comment = format!("Saturing {}.", op.description);

            tokens.extend(quote! {
                #[doc = #saturating_comment]
                #[must_use]
                #vis fn #saturating_name(self, #rhs_type) -> Self {
                    Self::new_saturating(self.get().#saturating_name(#rhs_value))
                }
            });
        }
    }

    fn generate_fmt_traits(&self, tokens: &mut TokenStream) {
        let ident = &self.ident;
        let repr = &self.repr;

        for &fmt_trait in &[
            "Binary", "Display", "LowerExp", "LowerHex", "Octal", "UpperExp", "UpperHex",
        ] {
            let fmt_trait = Ident::new(fmt_trait, Span::call_site());

            tokens.extend(quote! {
                impl ::core::fmt::#fmt_trait for #ident {
                    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                        <::core::primitive::#repr as ::core::fmt::#fmt_trait>::fmt(&self.get(), f)
                    }
                }
            });
        }
    }

    #[cfg(feature = "serde")]
    fn generate_serde(&self, tokens: &mut TokenStream) {
        let ident = &self.ident;
        let repr = &self.repr;
        let crate_location = &self.crate_location;
        let serde = quote!(#crate_location::serde);

        tokens.extend(quote! {
            impl #serde::Serialize for #ident {
                fn serialize<S>(&self, serializer: S) -> ::core::result::Result<
                    <S as #serde::Serializer>::Ok,
                    <S as #serde::Serializer>::Error,
                >
                where
                    S: #serde::Serializer,
                {
                    <#repr as #serde::Serialize>::serialize(&self.get(), serializer)
                }
            }
        });

        tokens.extend(quote! {
            impl<'de> #serde::Deserialize<'de> for #ident {
                fn deserialize<D>(deserializer: D) -> ::core::result::Result<
                    Self,
                    <D as #serde::Deserializer<'de>>::Error,
                >
                where
                    D: #serde::Deserializer<'de>,
                {
                    let value = <#repr as #serde::Deserialize<'de>>::deserialize(deserializer)?;
                    Self::new(value)
                        .ok_or_else(|| {
                            <<D as #serde::Deserializer<'de>>::Error as #serde::de::Error>::custom(
                                ::core::format_args!(
                                    "integer out of range, expected it to be between {} and {}",
                                    Self::MIN_VALUE,
                                    Self::MAX_VALUE
                                )
                            )
                        })
                }
            }
        });
    }

    fn generate_impl(&self, tokens: &mut TokenStream) {
        let mut inner_tokens = TokenStream::new();

        self.generate_consts(&mut inner_tokens);
        self.generate_base(&mut inner_tokens);
        self.generate_operators(&mut inner_tokens);
        self.generate_checked_operators(&mut inner_tokens);

        let ident = &self.ident;
        tokens.extend(quote!(impl #ident { #inner_tokens }));

        self.generate_ops_traits(tokens);
        self.generate_fmt_traits(tokens);
        #[cfg(feature = "serde")]
        self.generate_serde(tokens);
    }
}

impl Parse for BoundedInteger {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        let mut attrs = input.call(Attribute::parse_outer)?;

        let repr_pos = attrs
            .iter()
            .position(|attr| attr.path.is_ident("repr"))
            .ok_or_else(|| input.error("no repr attribute on bounded integer"))?;
        let repr: Repr = attrs.remove(repr_pos).parse_args()?;

        let crate_location_pos = attrs
            .iter()
            .position(|attr| attr.path.is_ident("bounded_integer"));
        let crate_location = crate_location_pos
            .map(|crate_location_pos| -> parse::Result<_> {
                let location: CrateLocation = syn::parse2(attrs.remove(crate_location_pos).tokens)?;
                Ok(location.0)
            })
            .transpose()?
            .unwrap_or_else(|| Path {
                leading_colon: Some(Token![::](Span::call_site())),
                segments: iter::once(PathSegment::from(Ident::new(
                    "bounded_integer",
                    Span::call_site(),
                )))
                .collect(),
            });

        let vis: Visibility = input.parse()?;

        Ok(if input.peek(Token![struct]) {
            let struct_token: Token![struct] = input.parse()?;

            let range;
            #[allow(clippy::eval_order_dependence)]
            let this = Self {
                attrs,
                crate_location,
                repr,
                vis,
                ident: input.parse()?,
                brace_token: braced!(range in input),
                kind: Kind::Struct {
                    struct_token,
                    range: {
                        let range: ExprRange = range.parse()?;
                        let limits = range.limits;
                        Box::new((
                            range.from.map(|from| *from),
                            range.to.map(|to| match limits {
                                RangeLimits::HalfOpen(_) => Expr::Verbatim(quote!(#to - 1)),
                                RangeLimits::Closed(_) => *to,
                            }),
                        ))
                    },
                },
            };
            input.parse::<Option<Token![;]>>()?;
            this
        } else {
            let enum_token: Token![enum] = input.parse()?;

            let range_tokens;
            #[allow(clippy::eval_order_dependence)]
            Self {
                attrs,
                crate_location,
                repr,
                vis,
                ident: input.parse()?,
                brace_token: braced!(range_tokens in input),
                kind: Kind::Enum {
                    enum_token,
                    range: {
                        let range: ExprRange = range_tokens.parse()?;
                        let (from, to) = range
                            .from
                            .as_deref()
                            .zip(range.to.as_deref())
                            .ok_or_else(|| {
                                Error::new_spanned(
                                    &range,
                                    "the bounds of an enum range must be closed",
                                )
                            })?;
                        let (from, to) = (eval_expr(from)?, eval_expr(to)?);
                        from..=if let RangeLimits::HalfOpen(_) = range.limits {
                            to - 1
                        } else {
                            to
                        }
                    },
                    semi_token: input.parse()?,
                },
            }
        })
    }
}

struct CrateLocation(Path);
impl Parse for CrateLocation {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        input.parse::<Token![=]>()?;
        Ok(Self(input.parse::<Path>()?))
    }
}

fn eval_expr(expr: &Expr) -> syn::Result<isize> {
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
                BinOp::Div(_) => left / right,
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

fn enum_variant(i: isize) -> Ident {
    Ident::new(
        &*match i.cmp(&0) {
            Ordering::Less => format!("N{}", i.abs()),
            Ordering::Equal => "Z0".to_owned(),
            Ordering::Greater => format!("P{}", i),
        },
        Span::call_site(),
    )
}

#[rustfmt::skip]
const CHECKED_OPERATORS: &[CheckedOperator] = &[
    CheckedOperator::new("add"       , "integer addition"      , Some("Self"), All         , All         ),
    CheckedOperator::new("sub"       , "integer subtraction"   , Some("Self"), All         , All         ),
    CheckedOperator::new("mul"       , "integer multiplication", Some("Self"), All         , All         ),
    CheckedOperator::new("div"       , "integer division"      , Some("Self"), NoSaturating, NoSaturating),
    CheckedOperator::new("div_euclid", "Euclidean division"    , Some("Self"), NoSaturating, NoSaturating),
    CheckedOperator::new("rem"       , "integer remainder"     , Some("Self"), NoSaturating, NoSaturating),
    CheckedOperator::new("rem_euclid", "Euclidean remainder"   , Some("Self"), NoSaturating, NoSaturating),
    CheckedOperator::new("neg"       , "negation"              , None        , All         , NoSaturating),
    CheckedOperator::new("abs"       , "absolute value"        , None        , All         , NoOps       ),
    CheckedOperator::new("pow"       , "exponentiation"        , Some("u32") , All         , All         ),
];

#[derive(Eq, PartialEq, Clone, Copy)]
enum Variants {
    NoOps,
    NoSaturating,
    All,
}

use Variants::*;

struct CheckedOperator {
    name: &'static str,
    description: &'static str,
    rhs: Option<&'static str>,
    signed_variants: Variants,
    unsigned_variants: Variants,
}

impl CheckedOperator {
    const fn new(
        name: &'static str,
        description: &'static str,
        rhs: Option<&'static str>,
        signed_variants: Variants,
        unsigned_variants: Variants,
    ) -> Self {
        Self {
            name,
            description,
            rhs,
            signed_variants,
            unsigned_variants,
        }
    }
}

#[rustfmt::skip]
const OPERATORS: &[Operator] = &[
    Operator { trait_name: "Add", method: "add", description: "add"           , bin: true , on_unsigned: true  },
    Operator { trait_name: "Sub", method: "sub", description: "subtract"      , bin: true , on_unsigned: true  },
    Operator { trait_name: "Mul", method: "mul", description: "multiply"      , bin: true , on_unsigned: true  },
    Operator { trait_name: "Div", method: "div", description: "divide"        , bin: true , on_unsigned: true  },
    Operator { trait_name: "Rem", method: "rem", description: "take remainder", bin: true , on_unsigned: true  },
    Operator { trait_name: "Neg", method: "neg", description: "negate"        , bin: false, on_unsigned: false },
];

struct Operator {
    trait_name: &'static str,
    method: &'static str,
    description: &'static str,
    bin: bool,
    on_unsigned: bool,
}

fn binop_trait_variations<B: ToTokens>(
    trait_name_root: &str,
    method_root: &str,
    lhs: &impl ToTokens,
    rhs: &impl ToTokens,
    body: impl FnOnce(&Ident, &Ident) -> B,
    tokens: &mut TokenStream,
) {
    let trait_name = Ident::new(trait_name_root, Span::call_site());
    let trait_name_assign = Ident::new(&format!("{}Assign", trait_name_root), Span::call_site());
    let method = Ident::new(method_root, Span::call_site());
    let method_assign = Ident::new(&format!("{}_assign", method_root), Span::call_site());
    let body = body(&trait_name, &method);

    tokens.extend(quote! {
        impl ::core::ops::#trait_name<#rhs> for #lhs {
            type Output = #lhs;
            fn #method(self, rhs: #rhs) -> Self::Output {
                #body
            }
        }
        impl<'a> ::core::ops::#trait_name<#rhs> for &'a #lhs {
            type Output = #lhs;
            fn #method(self, rhs: #rhs) -> Self::Output {
                <#lhs as ::core::ops::#trait_name<#rhs>>::#method(*self, rhs)
            }
        }
        impl<'b> ::core::ops::#trait_name<&'b #rhs> for #lhs {
            type Output = #lhs;
            fn #method(self, rhs: &'b #rhs) -> Self::Output {
                <#lhs as ::core::ops::#trait_name<#rhs>>::#method(self, *rhs)
            }
        }
        impl<'b, 'a> ::core::ops::#trait_name<&'b #rhs> for &'a #lhs {
            type Output = #lhs;
            fn #method(self, rhs: &'b #rhs) -> Self::Output {
                <#lhs as ::core::ops::#trait_name<#rhs>>::#method(*self, *rhs)
            }
        }

        impl ::core::ops::#trait_name_assign<#rhs> for #lhs {
            fn #method_assign(&mut self, rhs: #rhs) {
                *self = <Self as ::core::ops::#trait_name<#rhs>>::#method(*self, rhs);
            }
        }
        impl<'a> ::core::ops::#trait_name_assign<&'a #rhs> for #lhs {
            fn #method_assign(&mut self, rhs: &'a #rhs) {
                *self = <Self as ::core::ops::#trait_name<#rhs>>::#method(*self, *rhs);
            }
        }
    });
}

fn unop_trait_variations(
    trait_name: &impl ToTokens,
    method: &impl ToTokens,
    lhs: &impl ToTokens,
    body: &impl ToTokens,
    tokens: &mut TokenStream,
) {
    tokens.extend(quote! {
        impl ::core::ops::#trait_name for #lhs {
            type Output = #lhs;
            fn #method(self) -> Self::Output {
                #body
            }
        }
        impl<'a> ::core::ops::#trait_name for &'a #lhs {
            type Output = #lhs;
            fn #method(self) -> Self::Output {
                <#lhs as ::core::ops::#trait_name>::#method(*self)
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse2;

    fn assert_result(
        f: impl FnOnce(&BoundedInteger, &mut TokenStream),
        input: TokenStream,
        expected: TokenStream,
    ) {
        let mut result = TokenStream::new();
        f(&parse2::<BoundedInteger>(input).unwrap(), &mut result);
        assert_eq!(result.to_string(), expected.to_string());
    }

    #[cfg(test)]
    #[test]
    fn test_tokens() {
        assert_result(
            BoundedInteger::generate_item,
            quote! {
                #[repr(isize)]
                pub(crate) enum Nibble { -8..6+2 }
            },
            quote! {
                #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
                #[repr(isize)]
                pub(crate) enum Nibble {
                    N8 = -8, N7, N6, N5, N4, N3, N2, N1, Z0, P1, P2, P3, P4, P5, P6, P7
                }
            },
        );

        assert_result(
            BoundedInteger::generate_item,
            quote! {
                #[repr(u16)]
                enum Nibble { 3..=7 };
            },
            quote! {
                #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
                #[repr(u16)]
                enum Nibble {
                    P3 = 3, P4, P5, P6, P7
                };
            },
        );

        assert_result(
            BoundedInteger::generate_item,
            quote! {
                #[repr(i8)]
                pub struct S { -3..2 }
            },
            quote! {
                #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
                pub struct S(i8);
            },
        );
    }
}
