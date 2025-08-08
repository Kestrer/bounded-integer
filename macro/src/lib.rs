//! A macro for generating bounded integer structs and enums.
//!
//! This crate is unstable and must not be used directly.
#![warn(clippy::pedantic, rust_2018_idioms, unused_qualifications)]
#![allow(clippy::single_match_else, clippy::match_bool)]

use std::array;
use std::fmt::Debug;

use proc_macro2::{Delimiter, Ident, Literal, Span, TokenStream, TokenTree};
use quote::{ToTokens, quote, quote_spanned};

#[proc_macro]
#[doc(hidden)]
#[expect(clippy::too_many_lines)]
pub fn bounded_integer(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = TokenStream::from(input).into_iter().map(|t| {
        let TokenTree::Group(group) = t else {
            panic!("non-group in input")
        };
        assert_eq!(group.delimiter(), Delimiter::Bracket);
        group.stream()
    });
    let [
        zerocopy,
        mut attrs,
        vis,
        super_vis,
        is_named,
        item_kind,
        name,
        min_or_variants,
        max_or_none,
        crate_path,
    ] = to_array(input);

    let zerocopy = match to_array(zerocopy) {
        [TokenTree::Punct(p)] if p.as_char() == '-' => false,
        [TokenTree::Punct(p)] if p.as_char() == '+' => true,
        [t] => panic!("zerocopy ({t})"),
    };

    let [TokenTree::Ident(item_kind)] = to_array(item_kind) else {
        panic!("item kind")
    };
    let is_enum = match &*item_kind.to_string() {
        "struct" => false,
        "enum" => true,
        s => panic!("unknown item kind {s}"),
    };
    let [TokenTree::Ident(name)] = to_array(name) else {
        panic!("name")
    };

    let mut new_attrs = TokenStream::new();
    let mut maybe_repr = None;
    for attr in attrs {
        let TokenTree::Group(group) = &attr else {
            panic!("attr ({attr})")
        };
        let mut iter = group.stream().into_iter();
        if let [Some(TokenTree::Ident(i)), Some(TokenTree::Group(g)), None] =
            [iter.next(), iter.next(), iter.next()]
            && i == "repr"
            && g.delimiter() == Delimiter::Parenthesis
        {
            if maybe_repr.is_some() {
                return error!(i.span(), "duplicate `repr` attribute");
            }
            maybe_repr = Some(g.stream());
            continue;
        }
        new_attrs.extend(quote!(# #attr));
    }
    attrs = new_attrs;

    let (variants, min, max, min_val, max_val);
    match to_array(is_named) {
        // Unnamed
        [TokenTree::Punct(p)] if p.as_char() == '-' => {
            [min, max] = [min_or_variants, max_or_none].map(ungroup_none);
            [min_val, max_val] = [&min, &max].map(|lit| {
                parse_literal(lit.clone()).map(|(lit, repr)| {
                    // if there is an existing repr, Rust will cause an error anyway later on
                    if let Some(repr) = repr
                        && maybe_repr.is_none()
                    {
                        maybe_repr = Some(quote!(#repr));
                    }
                    lit
                })
            });

            variants = match is_enum {
                false => None,
                true => {
                    let Some(min_val) = min_val else {
                        return error!(min, "`enum` requires bound to be statically known");
                    };
                    let Some(max_val) = max_val else {
                        return error!(max, "`enum` requires bound to be statically known");
                    };
                    let Some(range) = range(min_val, max_val) else {
                        return error!(min, "refusing to generate this many `enum` variants");
                    };
                    let mut variants = TokenStream::new();
                    let min_span = stream_span(min.clone());
                    for int in range {
                        let enum_variant_name = int.enum_variant_name(min_span);
                        if int == min_val {
                            variants.extend(quote!(#[allow(dead_code)] #enum_variant_name = #min,));
                        } else {
                            variants.extend(quote!(#[allow(dead_code)] #enum_variant_name,));
                        }
                    }
                    Some(variants)
                }
            };
        }
        // Named
        [TokenTree::Punct(p)] if p.as_char() == '+' => {
            assert!(is_enum);
            assert!(max_or_none.into_iter().next().is_none());

            // ((min_val, min), current_val, current_span)
            let mut min_current = None::<((Int, TokenStream), Int, Span)>;
            let mut variant_list = TokenStream::new();
            for variant in min_or_variants {
                let TokenTree::Group(variant) = variant else {
                    panic!("variant")
                };
                let [
                    TokenTree::Group(attrs),
                    TokenTree::Ident(variant_name),
                    TokenTree::Group(variant_val),
                ] = to_array(variant.stream())
                else {
                    panic!("variant inner")
                };
                let attrs = attrs.stream();
                let variant_val = variant_val.stream();
                min_current = Some(if variant_val.is_empty() {
                    variant_list.extend(quote!(#attrs #variant_name,));
                    match min_current {
                        Some((min, current, current_span)) => match current.succ() {
                            Some(current) => (min, current, current_span),
                            None => {
                                return error!(
                                    variant_name.span(),
                                    "too many variants (overflows a u128)"
                                );
                            }
                        },
                        None => (
                            (Int::new(true, 0), quote_spanned!(variant_name.span()=> 0)),
                            Int::new(true, 0),
                            variant_name.span(),
                        ),
                    }
                } else {
                    variant_list.extend(quote!(#attrs #variant_name = #variant_val,));
                    let variant_val = ungroup_none(variant_val);
                    let Some((int, _)) = parse_literal(variant_val.clone()) else {
                        return error!(variant_val, "could not parse variant value");
                    };
                    match min_current {
                        Some((min, current, _)) if current.succ() == Some(int) => {
                            (min, int, stream_span(variant_val))
                        }
                        Some(_) => return error!(variant_val, "enum not contiguous"),
                        None => ((int, variant_val.clone()), int, stream_span(variant_val)),
                    }
                });
            }
            variants = Some(variant_list);
            [(min_val, min), (max_val, max)] = match min_current {
                Some(((min_val, min), current, current_span)) => [
                    (Some(min_val), min),
                    (Some(current), current.literal(current_span)),
                ],
                None => [
                    (Some(Int::new(true, 1)), quote!(1)),
                    (Some(Int::new(true, 0)), quote!(0)),
                ],
            };
        }
        [t] => panic!("named ({t})"),
    }

    let zeroable = min_val
        .zip(max_val)
        .map(|(min, max)| (min..=max).contains(&Int::new(true, 0)));
    if zeroable == Some(true) && zerocopy {
        attrs.extend(quote!(#[derive(#crate_path::__private::zerocopy::FromZeros)]));
    }
    let zeroable_token = match zeroable {
        Some(true) => quote!(zeroable,),
        Some(false) | None => quote!(),
    };

    let repr = match (maybe_repr, min_val, max_val) {
        (Some(repr), _, _) => repr,
        (None, Some(min_val), Some(max_val)) => match infer_repr(min_val, max_val) {
            Some(repr) => {
                let repr = Ident::new(&repr, stream_span(min.clone()));
                quote!(#repr)
            }
            None => return error!(min, "range too large for any integer type"),
        },
        (None, _, _) => {
            let msg = "no #[repr] attribute found, and could not infer";
            return error!(min, "{msg}");
        }
    };

    match is_enum {
        false => attrs.extend(quote!(#[repr(transparent)])),
        true => attrs.extend(quote!(#[repr(#repr)])),
    }

    if matches!(repr.to_string().trim(), "u8" | "i8") && zerocopy {
        attrs.extend(quote!(#[derive(#crate_path::__private::zerocopy::Unaligned)]));
    }

    let item = match variants {
        Some(variants) => quote!({ #variants }),
        None if zeroable == Some(false) => quote!((::core::num::NonZero<#repr>);),
        None => quote!((#repr);),
    };

    // Hide in a module to prevent access to private parts.
    let module_name = Ident::new(&format!("__bounded_integer_private_{name}"), name.span());

    let res = quote!(
        #[allow(non_snake_case)]
        mod #module_name {
            #attrs
            #super_vis #item_kind #name #item

            #crate_path::unsafe_api! {
                for #name,
                unsafe repr: #repr,
                min: #min,
                max: #max,
                #zeroable_token
            }
        }
        #vis use #module_name::#name;
    );

    res.into()
}

fn to_array<I: IntoIterator<Item: Debug>, const N: usize>(iter: I) -> [I::Item; N] {
    let mut iter = iter.into_iter();
    let array = array::from_fn(|_| iter.next().expect("iterator too short"));
    if let Some(item) = iter.next() {
        panic!("iterator too long: found {item:?}");
    }
    array
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Int {
    nonnegative: bool,
    magnitude: u128,
}

impl Int {
    fn new(nonnegative: bool, magnitude: u128) -> Self {
        Self {
            nonnegative,
            magnitude,
        }
    }
    fn succ(self) -> Option<Self> {
        Some(match self.nonnegative {
            true => Self::new(true, self.magnitude.checked_add(1)?),
            false if self.magnitude == 1 => Self::new(true, 0),
            false => Self::new(false, self.magnitude - 1),
        })
    }
    fn enum_variant_name(self, span: Span) -> Ident {
        if self.magnitude == 0 {
            Ident::new("Z", span)
        } else if self.nonnegative {
            Ident::new(&format!("P{}", self.magnitude), span)
        } else {
            Ident::new(&format!("N{}", self.magnitude), span)
        }
    }
    fn literal(self, span: Span) -> TokenStream {
        let mut magnitude = Literal::u128_unsuffixed(self.magnitude);
        magnitude.set_span(span);
        match self.nonnegative {
            true => quote!(#magnitude),
            false => quote!(-#magnitude),
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.nonnegative, other.nonnegative) {
            (true, true) => self.magnitude.cmp(&other.magnitude),
            (true, false) => std::cmp::Ordering::Greater,
            (false, true) => std::cmp::Ordering::Less,
            (false, false) => other.magnitude.cmp(&self.magnitude),
        }
    }
}

fn parse_literal(e: TokenStream) -> Option<(Int, Option<Ident>)> {
    let mut tokens = e.into_iter().peekable();
    let minus = tokens
        .next_if(|t| matches!(t, TokenTree::Punct(p) if p.as_char() == '-'))
        .is_some();
    let Some(TokenTree::Literal(lit)) = tokens.next() else {
        return None;
    };
    if tokens.next().is_some() {
        return None;
    }

    // Algorithm reference:
    // https://docs.rs/syn/2.0.104/src/syn/lit.rs.html#1679-1767

    let mut lit_chars = &*lit.to_string();

    let (base, base_len) = match lit_chars.get(..2) {
        Some("0x") => (16, 2),
        Some("0o") => (8, 2),
        Some("0b") => (2, 2),
        _ => (10, 0),
    };
    lit_chars = &lit_chars[base_len..];

    let mut magnitude = 0_u128;
    let mut has_digit = None;

    let suffix = loop {
        lit_chars = lit_chars.trim_start_matches('_');
        let Some(c) = lit_chars.chars().next() else {
            has_digit?;
            break None;
        };
        if let 'i' | 'u' = c {
            let ("8" | "16" | "32" | "64" | "128" | "size") = &lit_chars[1..] else {
                return None;
            };
            break Some(Ident::new(lit_chars, lit.span()));
        }
        let digit = c.to_digit(base)?;
        lit_chars = &lit_chars[1..];
        magnitude = magnitude
            .checked_mul(base.into())?
            .checked_add(digit.into())?;
        has_digit = Some(());
    };

    let lit = Int::new(!minus || magnitude == 0, magnitude);
    Some((lit, suffix))
}

fn range(min: Int, max: Int) -> Option<impl Iterator<Item = Int>> {
    let range_minus_one = match (max.nonnegative, min.nonnegative) {
        (true, true) => max.magnitude.saturating_sub(min.magnitude),
        (true, false) => max.magnitude.saturating_add(min.magnitude),
        (false, true) => 0,
        (false, false) => min.magnitude.saturating_sub(max.magnitude),
    };
    if 100_000 <= range_minus_one {
        return None;
    }
    #[expect(clippy::reversed_empty_ranges)]
    let (negative_part, nonnegative_part) = match (min.nonnegative, max.nonnegative) {
        (true, true) => (1..=0, min.magnitude..=max.magnitude),
        (false, true) => (1..=min.magnitude, 0..=max.magnitude),
        (true, false) => (1..=0, 1..=0),
        (false, false) => (max.magnitude..=min.magnitude, 1..=0),
    };
    let negative_part = negative_part.map(|i| Int::new(false, i));
    let nonnegative_part = nonnegative_part.map(|i| Int::new(true, i));
    Some(negative_part.rev().chain(nonnegative_part))
}

fn infer_repr(min: Int, max: Int) -> Option<String> {
    for bits in [8, 16, 32, 64, 128] {
        let fits_unsigned =
            |lit: Int| lit.nonnegative && lit.magnitude <= (u128::MAX >> (128 - bits));
        let fits_signed = |lit: Int| {
            (lit.nonnegative && lit.magnitude < (1 << (bits - 1)))
                || (!lit.nonnegative && lit.magnitude <= (1 << (bits - 1)))
        };
        if fits_unsigned(min) && fits_unsigned(max) {
            return Some(format!("u{bits}"));
        } else if fits_signed(min) && fits_signed(max) {
            return Some(format!("i{bits}"));
        }
    }
    None
}

fn ungroup_none(tokens: TokenStream) -> TokenStream {
    let mut tokens = tokens.into_iter().peekable();
    if let Some(TokenTree::Group(g)) =
        tokens.next_if(|t| matches!(t, TokenTree::Group(g) if g.delimiter() == Delimiter::None))
    {
        return g.stream();
    }
    // Sigh… make it opportunistic to get it to work on rust-analyzer
    // https://github.com/rust-lang/rust-analyzer/issues/18211
    tokens.collect()
}

macro_rules! error {
    ($span:expr, $($fmt:tt)*) => {{
        let span = SpanHelper($span).span_helper();
        let msg = format!($($fmt)*);
        proc_macro::TokenStream::from(quote_spanned!(span=> compile_error!(#msg);))
    }};
}
use error;

struct SpanHelper<T>(T);
impl SpanHelper<TokenStream> {
    fn span_helper(self) -> Span {
        stream_span(self.0.into_token_stream())
    }
}
trait SpanHelperTrait {
    fn span_helper(self) -> Span;
}
impl SpanHelperTrait for SpanHelper<Span> {
    fn span_helper(self) -> Span {
        self.0
    }
}

fn stream_span(stream: TokenStream) -> Span {
    stream
        .into_iter()
        .next()
        .map_or_else(Span::call_site, |token| token.span())
}
