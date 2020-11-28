use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};

use num_bigint::BigInt;

use crate::{BoundedInteger, Kind};

pub(crate) fn generate(item: &BoundedInteger, tokens: &mut TokenStream) {
    generate_item(item, tokens);

    generate_consts(item, tokens);
    generate_base(item, tokens);
    generate_operators(item, tokens);
    generate_checked_operators(item, tokens);

    generate_cmp_traits(item, tokens);
    generate_ops_traits(item, tokens);
    generate_iter_traits(item, tokens);
    generate_fmt_traits(item, tokens);
    #[cfg(feature = "serde")]
    generate_serde(item, tokens);
}

fn generate_item(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;

    for attr in &item.attrs {
        attr.to_tokens(tokens);
    }
    tokens.extend(quote! {
        #[derive(
            ::core::fmt::Debug,
            ::core::hash::Hash,
            ::core::clone::Clone,
            ::core::marker::Copy,
            ::core::cmp::PartialEq,
            ::core::cmp::Eq,
            ::core::cmp::PartialOrd,
            ::core::cmp::Ord
        )]
    });

    if let Kind::Enum(_) = &item.kind {
        tokens.extend(quote!(#[repr(#repr)]));
    }

    item.vis.to_tokens(tokens);

    match &item.kind {
        Kind::Enum(token) => token.to_tokens(tokens),
        Kind::Struct(token) => token.to_tokens(tokens),
    }

    item.ident.to_tokens(tokens);

    match &item.kind {
        Kind::Struct(_) => {
            tokens.extend(quote_spanned!(item.brace_token.span=> (::core::primitive::#repr);));
        }
        Kind::Enum(_) => {
            let mut inner_tokens = TokenStream::new();

            let first_variant = enum_variant(item.range.start());
            let start_literal = item.repr.number_literal(item.range.start());
            inner_tokens.extend(quote!(#first_variant = #start_literal));

            let mut variant = item.range.start() + 1;
            while variant <= *item.range.end() {
                let name = enum_variant(&variant);
                inner_tokens.extend(quote!(, #name));
                variant += 1;
            }

            tokens.extend(quote_spanned!(item.brace_token.span=> { #inner_tokens }));
        }
    }
}

fn generate_consts(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;

    let min_value = repr.number_literal(item.range.start()).into_token_stream();
    let max_value = repr.number_literal(item.range.end()).into_token_stream();

    let (min, max) = match &item.kind {
        Kind::Struct(_) => (quote!(Self(Self::MIN_VALUE)), quote!(Self(Self::MAX_VALUE))),
        Kind::Enum(_) => {
            let (min, max) = (
                enum_variant(item.range.start()),
                enum_variant(item.range.end()),
            );

            (quote!(Self::#min), quote!(Self::#max))
        }
    };

    let ident = &item.ident;
    let vis = &item.vis;

    let min_value_doc = format!(
        "The smallest value that this bounded integer can contain; {}.",
        item.range.start()
    );
    let max_value_doc = format!(
        "The largest value that this bounded integer can contain; {}.",
        item.range.end()
    );
    let min_doc = format!(
        "The smallest value of the bounded integer; {}.",
        item.range.start()
    );
    let max_doc = format!(
        "The largest value of the bounded integer; {}.",
        item.range.end()
    );
    let range_doc = format!(
        "The number of values the bounded integer contains; {}.",
        item.range.end() - item.range.start() + 1
    );

    tokens.extend(quote! {
        impl #ident {
            #[doc = #min_value_doc]
            #vis const MIN_VALUE: ::core::primitive::#repr = #min_value;
            #[doc = #max_value_doc]
            #vis const MAX_VALUE: ::core::primitive::#repr = #max_value;

            #[doc = #min_doc]
            #vis const MIN: Self = #min;
            #[doc = #max_doc]
            #vis const MAX: Self = #max;

            #[doc = #range_doc]
            #vis const RANGE: ::core::primitive::#repr = Self::MAX_VALUE - Self::MIN_VALUE + 1;
        }
    });
}

fn generate_base(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;

    let (get_body, new_body) = match &item.kind {
        Kind::Struct(_) => (quote!(self.0), quote!(Self(n))),
        Kind::Enum(_) => (
            quote!(self as ::core::primitive::#repr),
            quote!(::core::mem::transmute::<::core::primitive::#repr, Self>(n)),
        ),
    };

    let ident = &item.ident;
    let vis = &item.vis;

    tokens.extend(quote! {
        impl #ident {
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
                n >= Self::MIN_VALUE && n <= Self::MAX_VALUE
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
                if n < Self::MIN_VALUE {
                    Self::MIN
                } else if n > Self::MAX_VALUE {
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
        }
    });
}

fn generate_operators(item: &BoundedInteger, tokens: &mut TokenStream) {
    let vis = &item.vis;
    let repr = &item.repr;

    let abs_if_signed = if item.repr.signed {
        quote! {
            /// Computes the absolute value of `self`, panicking if it is out of range.
            #[must_use]
            #vis fn abs(self) -> Self {
                Self::new(self.get().abs()).expect("Absolute value out of range")
            }
        }
    } else {
        TokenStream::new()
    };

    let ident = &item.ident;

    tokens.extend(quote! {
        impl #ident {
            #abs_if_signed

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
        }
    });
}

fn generate_cmp_traits(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;

    // These are only impls that can't be derived
    tokens.extend(quote! {
        impl ::core::cmp::PartialEq<::core::primitive::#repr> for #ident {
            fn eq(&self, other: &::core::primitive::#repr) -> bool {
                self.get() == *other
            }
        }
        impl ::core::cmp::PartialEq<#ident> for ::core::primitive::#repr {
            fn eq(&self, other: &#ident) -> bool {
                *self == other.get()
            }
        }
        impl ::core::cmp::PartialOrd<::core::primitive::#repr> for #ident {
            fn partial_cmp(
                &self,
                other: &::core::primitive::#repr
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                ::core::cmp::PartialOrd::partial_cmp(&self.get(), other)
            }
        }
        impl ::core::cmp::PartialOrd<#ident> for ::core::primitive::#repr {
            fn partial_cmp(
                &self,
                other: &#ident
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                ::core::cmp::PartialOrd::partial_cmp(self, &other.get())
            }
        }
    });
}

fn generate_ops_traits(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;
    let full_repr = quote!(::core::primitive::#repr);

    for op in OPERATORS {
        if !item.repr.signed && !op.on_unsigned {
            continue;
        }

        let description = op.description;

        if op.bin {
            // bounded + repr
            binop_trait_variations(
                op.trait_name,
                op.method,
                &item.ident,
                &full_repr,
                |trait_name, method| {
                    quote! {
                        Self::new(<#full_repr as ::core::ops::#trait_name>::#method(self.get(), rhs))
                            .expect(::core::concat!("Attempted to ", #description, " out of range"))
                    }
                },
                tokens,
            );

            // repr + bounded
            binop_trait_variations(
                op.trait_name,
                op.method,
                &full_repr,
                &item.ident,
                |trait_name, method| {
                    quote! {
                        <Self as ::core::ops::#trait_name<#full_repr>>::#method(self, rhs.get())
                    }
                },
                tokens,
            );

            // bounded + bounded
            binop_trait_variations(
                op.trait_name,
                op.method,
                &item.ident,
                &item.ident,
                |trait_name, method| {
                    quote! {
                        <Self as ::core::ops::#trait_name<#full_repr>>::#method(self, rhs.get())
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
                &item.ident,
                &quote! {
                    Self::new(<#full_repr as ::core::ops::#trait_name>::#method(self.get()))
                        .expect(::core::concat!("Attempted to ", #description, " out of range"))
                },
                tokens,
            );
        }
    }
}

fn generate_checked_operators(item: &BoundedInteger, tokens: &mut TokenStream) {
    let mut block_tokens = TokenStream::new();
    let vis = &item.vis;

    for op in CHECKED_OPERATORS {
        let variants = if item.repr.signed {
            op.signed_variants
        } else {
            op.unsigned_variants
        };

        if variants == NoOps {
            continue;
        }

        let rhs = match op.rhs {
            Some("Self") => Some({
                let repr = &item.repr;
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

        block_tokens.extend(quote! {
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
        let saturating_comment = format!("Saturating {}.", op.description);

        block_tokens.extend(quote! {
            #[doc = #saturating_comment]
            #[must_use]
            #vis fn #saturating_name(self, #rhs_type) -> Self {
                Self::new_saturating(self.get().#saturating_name(#rhs_value))
            }
        });
    }

    let ident = &item.ident;
    tokens.extend(quote! {
        impl #ident { #block_tokens }
    });
}

fn generate_iter_traits(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;

    if item.range.contains(&BigInt::from(0)) {
        tokens.extend(quote! {
            impl ::core::iter::Sum for #ident {
                fn sum<I: ::core::iter::Iterator<Item = Self>>(iter: I) -> Self {
                    ::core::iter::Iterator::fold(
                        iter,
                        unsafe { Self::new_unchecked(0) },
                        ::core::ops::Add::add,
                    )
                }
            }
            impl<'a> ::core::iter::Sum<&'a Self> for #ident {
                fn sum<I: ::core::iter::Iterator<Item = &'a Self>>(iter: I) -> Self {
                    ::core::iter::Iterator::sum(::core::iter::Iterator::copied(iter))
                }
            }

            impl ::core::iter::Sum<#ident> for ::core::primitive::#repr {
                fn sum<I: ::core::iter::Iterator<Item = #ident>>(iter: I) -> Self {
                    ::core::iter::Iterator::sum(::core::iter::Iterator::map(iter, #ident::get))
                }
            }
            impl<'a> ::core::iter::Sum<&'a #ident> for ::core::primitive::#repr {
                fn sum<I: ::core::iter::Iterator<Item = &'a #ident>>(iter: I) -> Self {
                    ::core::iter::Iterator::sum(::core::iter::Iterator::copied(iter))
                }
            }
        });
    }
    if item.range.contains(&BigInt::from(1)) {
        tokens.extend(quote! {
            impl ::core::iter::Product for #ident {
                fn product<I: ::core::iter::Iterator<Item = Self>>(iter: I) -> Self {
                    ::core::iter::Iterator::fold(
                        iter,
                        unsafe { Self::new_unchecked(1) },
                        ::core::ops::Mul::mul,
                    )
                }
            }
            impl<'a> ::core::iter::Product<&'a Self> for #ident {
                fn product<I: ::core::iter::Iterator<Item = &'a Self>>(iter: I) -> Self {
                    ::core::iter::Iterator::product(::core::iter::Iterator::copied(iter))
                }
            }

            impl ::core::iter::Product<#ident> for ::core::primitive::#repr {
                fn product<I: ::core::iter::Iterator<Item = #ident>>(iter: I) -> Self {
                    ::core::iter::Iterator::product(::core::iter::Iterator::map(iter, #ident::get))
                }
            }
            impl<'a> ::core::iter::Product<&'a #ident> for ::core::primitive::#repr {
                fn product<I: ::core::iter::Iterator<Item = &'a #ident>>(iter: I) -> Self {
                    ::core::iter::Iterator::product(::core::iter::Iterator::copied(iter))
                }
            }
        });
    }
    #[cfg(feature = "step_trait")]
    {
        tokens.extend(quote! {
            unsafe impl ::core::iter::Step for #ident {
                fn steps_between(start: &Self, end: &Self) -> ::core::option::Option<::core::primitive::usize> {
                    ::core::iter::Step::steps_between(&start.get(), &end.get())
                }
                fn forward_checked(start: Self, count: ::core::primitive::usize) -> ::core::option::Option<Self> {
                    ::core::iter::Step::forward_checked(start.get(), count).and_then(Self::new)
                }
                fn backward_checked(start: Self, count: ::core::primitive::usize) -> ::core::option::Option<Self> {
                    ::core::iter::Step::backward_checked(start.get(), count).and_then(Self::new)
                }
            }
        });
    }
}

fn generate_fmt_traits(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;

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
fn generate_serde(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;
    let serde = &item.serde;

    tokens.extend(quote! {
        impl #serde::Serialize for #ident {
            fn serialize<S>(&self, serializer: S) -> ::core::result::Result<
                <S as #serde::Serializer>::Ok,
                <S as #serde::Serializer>::Error,
            >
            where
                S: #serde::Serializer,
            {
                <::core::primitive::#repr as #serde::Serialize>::serialize(&self.get(), serializer)
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
                let value = <::core::primitive::#repr as #serde::Deserialize<'de>>::deserialize(deserializer)?;
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

fn enum_variant(i: &BigInt) -> Ident {
    Ident::new(
        &*match i.sign() {
            num_bigint::Sign::Minus => format!("N{}", i.magnitude()),
            num_bigint::Sign::NoSign => "Z".to_owned(),
            num_bigint::Sign::Plus => format!("P{}", i),
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

use Variants::{All, NoOps, NoSaturating};

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
        let item = match parse2::<BoundedInteger>(input.clone()) {
            Ok(item) => item,
            Err(e) => panic!("Failed to parse '{}': {}", input.to_string(), e),
        };
        let mut result = TokenStream::new();
        f(&item, &mut result);
        assert_eq!(result.to_string(), expected.to_string());
        drop((input, expected));
    }

    #[test]
    fn test_tokens() {
        let derives = quote! {
            #[derive(
                ::core::fmt::Debug,
                ::core::hash::Hash,
                ::core::clone::Clone,
                ::core::marker::Copy,
                ::core::cmp::PartialEq,
                ::core::cmp::Eq,
                ::core::cmp::PartialOrd,
                ::core::cmp::Ord
            )]
        };

        assert_result(
            generate_item,
            quote! {
                #[repr(isize)]
                pub(crate) enum Nibble { -8..6+2 }
            },
            quote! {
                #derives
                #[repr(isize)]
                pub(crate) enum Nibble {
                    N8 = -8isize, N7, N6, N5, N4, N3, N2, N1, Z, P1, P2, P3, P4, P5, P6, P7
                }
            },
        );

        assert_result(
            generate_item,
            quote! {
                #[repr(u16)]
                enum Nibble { 3..=7 }
            },
            quote! {
                #derives
                #[repr(u16)]
                enum Nibble {
                    P3 = 3u16, P4, P5, P6, P7
                }
            },
        );

        assert_result(
            generate_item,
            quote! {
                #[repr(i8)]
                pub struct S { -3..2 }
            },
            quote! {
                #derives
                pub struct S(::core::primitive::i8);
            },
        );
    }
}
