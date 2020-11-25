//! A macro for generating bounded integer structs and enums.
#![warn(
    clippy::pedantic,
    rust_2018_idioms,
    missing_docs,
    unused_qualifications,
)]

use std::ops::RangeInclusive;

use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens, TokenStreamExt as _};
use syn::parse::{self, Parse, ParseStream};
use syn::{braced, parse_macro_input, token::Brace, Token};
use syn::{Attribute, Error, Expr, Path, Visibility};
use syn::{BinOp, ExprBinary, ExprRange, ExprUnary, RangeLimits, UnOp};
use syn::{ExprGroup, ExprParen};
use syn::{ExprLit, Lit};

mod generate;

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
/// ```
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
/// ```
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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
///     #[repr(u8)]
///     pub enum S { 5..=7 }
/// }
/// # }
/// ```
/// The generated item should look like this:
/// ```
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// #[repr(u8)]
/// pub enum S {
///     P5 = 5, P6, P7
/// }
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
    let item = parse_macro_input!(input as BoundedInteger);

    let mut result = TokenStream::new();
    generate::generate(&item, &mut result);
    result.into()
}

struct BoundedInteger {
    attrs: Vec<Attribute>,
    #[cfg(feature = "serde")]
    serde: TokenStream,
    repr: Repr,
    vis: Visibility,
    ident: Ident,
    brace_token: Brace,
    kind: Kind,
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

impl Parse for BoundedInteger {
    fn parse(input: ParseStream<'_>) -> parse::Result<Self> {
        let mut attrs = input.call(Attribute::parse_outer)?;

        let repr_pos = attrs
            .iter()
            .position(|attr| attr.path.is_ident("repr"))
            .ok_or_else(|| input.error("no repr attribute on bounded integer"))?;
        let repr: Repr = attrs.remove(repr_pos).parse_args()?;

        let crate_location_pos = attrs
            .iter()
            .position(|attr| attr.path.is_ident("bounded_integer"));
        #[cfg_attr(not(feature = "serde"), allow(unused_variables))]
        let crate_location = crate_location_pos
            .map(|crate_location_pos| -> parse::Result<_> {
                struct CrateLocation(Path);
                impl Parse for CrateLocation {
                    fn parse(input: ParseStream<'_>) -> parse::Result<Self> {
                        input.parse::<Token![=]>()?;
                        Ok(Self(input.parse::<Path>()?))
                    }
                }

                let location: CrateLocation = syn::parse2(attrs.remove(crate_location_pos).tokens)?;
                Ok(location.0.into_token_stream())
            })
            .transpose()?
            .unwrap_or_else(|| quote!(::bounded_integer));
        #[cfg(feature = "serde")]
        let serde = quote!(#crate_location::__serde);

        let vis: Visibility = input.parse()?;

        Ok(if input.peek(Token![struct]) {
            let struct_token: Token![struct] = input.parse()?;

            let range;
            #[allow(clippy::eval_order_dependence)]
            let this = Self {
                attrs,
                #[cfg(feature = "serde")]
                serde,
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
                #[cfg(feature = "serde")]
                serde,
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

struct Repr {
    // We might use this later
    #[allow(dead_code)]
    span: Span,
    signed: bool,
    // We might use this later
    #[allow(dead_code)]
    size: ReprSize,
    origin: Ident,
}

impl Parse for Repr {
    fn parse(input: ParseStream<'_>) -> parse::Result<Self> {
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
