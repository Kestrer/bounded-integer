use proc_macro2::{Ident, Punct, Spacing, Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::Token;

use num_bigint::BigInt;

use crate::{BoundedInteger, Kind, ReprSize, ReprSizeFixed};

pub(crate) fn generate(item: &BoundedInteger, tokens: &mut TokenStream) {
    generate_item(item, tokens);
    generate_impl(item, tokens);

    // TODO: Implement TryFrom and TryInto. This will require adding an error type to the main crate.
    generate_ops_traits(item, tokens);
    generate_cmp_traits(item, tokens);
    generate_as_ref_borrow(item, tokens);
    generate_default(item, tokens);
    generate_iter_traits(item, tokens);
    generate_from_str(item, tokens);
    generate_fmt_traits(item, tokens);
    generate_to_primitive_traits(item, tokens);
    if item.arbitrary1 {
        generate_arbitrary1(item, tokens);
    }
    if item.bytemuck1 {
        generate_bytemuck1(item, tokens);
    }
    if item.serde1 {
        generate_serde1(item, tokens);
    }

    if cfg!(feature = "generate_tests") {
        generate_tests(item, tokens);
    }
}

fn generate_item(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;
    let crate_path = &item.crate_path;

    if item.zerocopy06 {
        let zerocopy = quote!(#crate_path::__private::zerocopy06);

        // Zerocopy is not hygienic: https://bugs.fuchsia.dev/p/fuchsia/issues/detail?id=84476
        tokens.extend(quote! {
            use ::core::marker::Sized;
            use #zerocopy as zerocopy;
        });

        tokens.extend(quote!(#[derive(#zerocopy::AsBytes)]));
        if let ReprSize::Fixed(ReprSizeFixed::Fixed8) = item.repr.size {
            tokens.extend(quote!(#[derive(#zerocopy::Unaligned)]));
        }
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

    for attr in &item.attrs {
        attr.to_tokens(tokens);
    }

    tokens.extend(match &item.kind {
        Kind::Enum(_) => quote!(#[repr(#repr)]),
        Kind::Struct(_) => quote!(#[repr(transparent)]),
    });

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

fn generate_impl(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;

    let mut content = TokenStream::new();
    generate_min_max_value(item, &mut content);
    generate_min_max(item, &mut content);
    generate_unchecked_constructors(item, &mut content);
    generate_checked_constructors(item, &mut content);
    generate_from_str_radix(item, &mut content);
    generate_getters(item, &mut content);
    generate_inherent_operators(item, &mut content);
    generate_checked_operators(item, &mut content);

    tokens.extend(quote! {
        impl #ident {
            #content
        }
    });
}

fn generate_min_max_value(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;
    let vis = &item.vis;

    let min_value_doc = format!(
        "The smallest value that this bounded integer can contain; {}.",
        item.range.start()
    );
    let max_value_doc = format!(
        "The largest value that this bounded integer can contain; {}.",
        item.range.end()
    );

    let min_value = repr.number_literal(item.range.start()).into_token_stream();
    let max_value = repr.number_literal(item.range.end()).into_token_stream();

    tokens.extend(quote! {
        #[doc = #min_value_doc]
        #vis const MIN_VALUE: ::core::primitive::#repr = #min_value;
        #[doc = #max_value_doc]
        #vis const MAX_VALUE: ::core::primitive::#repr = #max_value;
    });
}

fn generate_min_max(item: &BoundedInteger, tokens: &mut TokenStream) {
    let vis = &item.vis;

    let min_doc = format!(
        "The smallest value of the bounded integer; {}.",
        item.range.start()
    );
    let max_doc = format!(
        "The largest value of the bounded integer; {}.",
        item.range.end()
    );

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

    tokens.extend(quote! {
        #[doc = #min_doc]
        #vis const MIN: Self = #min;
        #[doc = #max_doc]
        #vis const MAX: Self = #max;
    });
}

fn generate_unchecked_constructors(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;
    let vis = &item.vis;

    let (new_unchecked_const, new_unchecked_body) = match item.kind {
        Kind::Struct(_) => (Some(Token![const](Span::call_site())), quote!(Self(n))),
        Kind::Enum(_) => (
            None,
            quote!(::core::mem::transmute::<::core::primitive::#repr, Self>(n)),
        ),
    };

    let safety_doc = "
# Safety

The value must not be outside the valid range of values; it must not be less than
[`MIN_VALUE`](Self::MIN_VALUE) or greater than [`MAX_VALUE`](Self::MAX_VALUE).\
    ";

    tokens.extend(quote! {
        /// Creates a bounded integer without checking the value.
        #[doc = #safety_doc]
        #[must_use]
        #vis #new_unchecked_const unsafe fn new_unchecked(n: ::core::primitive::#repr) -> Self {
            #new_unchecked_body
        }

        /// Creates a shared reference to a bounded integer from a shared reference to a primitive.
        #[doc = #safety_doc]
        #[must_use]
        #vis unsafe fn new_ref_unchecked(n: &::core::primitive::#repr) -> &Self {
            ::core::debug_assert!(Self::in_range(*n));
            &*(n as *const ::core::primitive::#repr as *const Self)
        }

        /// Creates a mutable reference to a bounded integer from a mutable reference to a
        /// primitive.
        #[doc = #safety_doc]
        #[must_use]
        #vis unsafe fn new_mut_unchecked(n: &mut ::core::primitive::#repr) -> &mut Self {
            ::core::debug_assert!(Self::in_range(*n));
            &mut *(n as *mut ::core::primitive::#repr as *mut Self)
        }
    });
}

fn generate_checked_constructors(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;
    let vis = &item.vis;

    let (new_body, new_saturating_body) = match item.kind {
        Kind::Struct(_) => (
            quote! {
                if Self::in_range(n) {
                    ::core::option::Option::Some(Self(n))
                } else {
                    ::core::option::Option::None
                }
            },
            quote! {
                if n < Self::MIN_VALUE {
                    Self::MIN
                } else if n > Self::MAX_VALUE {
                    Self::MAX
                } else {
                    Self(n)
                }
            },
        ),
        Kind::Enum(_) => {
            let mut new_arms = TokenStream::new();
            let mut new_saturating_arms = quote! {
                ::core::primitive::#repr::MIN..=Self::MIN_VALUE => Self::MIN,
                Self::MAX_VALUE..=::core::primitive::#repr::MAX => Self::MAX,
            };

            let mut variant = item.range.start().clone();
            while variant <= *item.range.end() {
                let variant_value = item.repr.number_literal(&variant);
                let variant_name = enum_variant(&variant);

                new_arms.extend(quote! {
                    #variant_value => ::core::option::Option::Some(Self::#variant_name),
                });
                new_saturating_arms.extend(quote! {
                    #variant_value => Self::#variant_name,
                });

                variant += 1;
            }

            new_arms.extend(quote! {
                _ => ::core::option::Option::None,
            });

            (
                quote! { match n { #new_arms } },
                quote! { match n { #new_saturating_arms } },
            )
        }
    };

    tokens.extend(quote! {
        /// Checks whether the given value is in the range of the bounded integer.
        #[must_use]
        #[inline]
        #vis const fn in_range(n: ::core::primitive::#repr) -> ::core::primitive::bool {
            n >= Self::MIN_VALUE && n <= Self::MAX_VALUE
        }

        /// Creates a bounded integer if the given value is within the range
        /// [[`MIN`](Self::MIN), [`MAX`](Self::MAX)].
        #[must_use]
        #[inline]
        #vis const fn new(n: ::core::primitive::#repr) -> ::core::option::Option<Self> {
            #new_body
        }

        /// Creates a reference to a bounded integer from a reference to a primitive if the
        /// given value is within the range [[`MIN`](Self::MIN), [`MAX`](Self::MAX)].
        #[must_use]
        #[inline]
        #vis fn new_ref(n: &::core::primitive::#repr) -> ::core::option::Option<&Self> {
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
        #vis fn new_mut(n: &mut ::core::primitive::#repr) -> ::core::option::Option<&mut Self> {
            Self::in_range(*n).then(move || {
                // SAFETY: We just asserted that the value is in range.
                unsafe { Self::new_mut_unchecked(n) }
            })
        }

        /// Creates a bounded integer by setting the value to [`MIN`](Self::MIN) or
        /// [`MAX`](Self::MAX) if it is too low or too high respectively.
        #[must_use]
        #[inline]
        #vis const fn new_saturating(n: ::core::primitive::#repr) -> Self {
            #new_saturating_body
        }
    });
}

fn generate_from_str_radix(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;
    let vis = &item.vis;
    let crate_path = &item.crate_path;

    tokens.extend(quote! {
        /// Converts a string slice in a given base to the bounded integer.
        ///
        /// # Panics
        ///
        /// Panics if `radix` is below 2 or above 36.
        #vis fn from_str_radix(
            src: &::core::primitive::str,
            radix: ::core::primitive::u32
        ) -> ::core::result::Result<Self, #crate_path::ParseError> {
            let value: ::core::primitive::#repr = #crate_path::__private::FromStrRadix::from_str_radix(
                src,
                radix
            )?;
            if value < Self::MIN_VALUE {
                ::core::result::Result::Err(#crate_path::__private::error_below_min())
            } else if value > Self::MAX_VALUE {
                ::core::result::Result::Err(#crate_path::__private::error_above_max())
            } else {
                ::core::result::Result::Ok(unsafe { Self::new_unchecked(value) })
            }
        }
    });
}

fn generate_getters(item: &BoundedInteger, tokens: &mut TokenStream) {
    let repr = &item.repr;
    let vis = &item.vis;

    let get_body = match item.kind {
        Kind::Struct(_) => quote!(self.0),
        Kind::Enum(_) => quote!(self as _),
    };

    tokens.extend(quote! {
        /// Returns the value of the bounded integer as a primitive type.
        #[must_use]
        #[inline]
        #vis const fn get(self) -> ::core::primitive::#repr {
            #get_body
        }
    });

    let (get_ref_const, get_ref_body) = match item.kind {
        Kind::Struct(_) => (Some(Token![const](Span::call_site())), quote!(&self.0)),
        Kind::Enum(_) => (
            None,
            quote!(unsafe { &*(self as *const Self as *const ::core::primitive::#repr) }),
        ),
    };

    tokens.extend(quote! {
        /// Returns a shared reference to the value of the bounded integer.
        #[must_use]
        #[inline]
        #vis #get_ref_const fn get_ref(&self) -> &::core::primitive::#repr {
            #get_ref_body
        }

        /// Returns a mutable reference to the value of the bounded integer.
        ///
        /// # Safety
        ///
        /// This value must never be set to a value beyond the range of the bounded integer.
        #[must_use]
        #[inline]
        #vis unsafe fn get_mut(&mut self) -> &mut ::core::primitive::#repr {
            &mut *(self as *mut Self as *mut ::core::primitive::#repr)
        }
    });
}

fn generate_inherent_operators(item: &BoundedInteger, tokens: &mut TokenStream) {
    let vis = &item.vis;
    let repr = &item.repr;

    if item.repr.signed {
        tokens.extend(quote! {
            /// Computes the absolute value of `self`, panicking if it is out of range.
            #[must_use]
            #[inline]
            #vis fn abs(self) -> Self {
                Self::new(self.get().abs()).expect("Absolute value out of range")
            }
        });
    }

    tokens.extend(quote! {
        /// Raises `self` to the power of `exp`, using exponentiation by squaring. Panics if it
        /// is out of range.
        #[must_use]
        #[inline]
        #vis fn pow(self, exp: ::core::primitive::u32) -> Self {
            Self::new(self.get().pow(exp)).expect("Value raised to power out of range")
        }
        /// Calculates the quotient of Euclidean division of `self` by `rhs`. Panics if `rhs`
        /// is 0 or the result is out of range.
        #[must_use]
        #[inline]
        #vis fn div_euclid(self, rhs: ::core::primitive::#repr) -> Self {
            Self::new(self.get().div_euclid(rhs)).expect("Attempted to divide out of range")
        }
        /// Calculates the least nonnegative remainder of `self (mod rhs)`. Panics if `rhs` is 0
        /// or the result is out of range.
        #[must_use]
        #[inline]
        #vis fn rem_euclid(self, rhs: ::core::primitive::#repr) -> Self {
            Self::new(self.get().rem_euclid(rhs))
                .expect("Attempted to divide with remainder out of range")
        }
    });
}

fn generate_checked_operators(item: &BoundedInteger, tokens: &mut TokenStream) {
    let vis = &item.vis;

    for op in CHECKED_OPERATORS {
        if !item.repr.signed && op.variants == OpVariants::Signed {
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
        let checked_comment = format!("Checked {}.", op.description.trim());

        tokens.extend(quote! {
            #[doc = #checked_comment]
            #[must_use]
            #[inline]
            #vis const fn #checked_name(self, #rhs_type) -> ::core::option::Option<Self> {
                match self.get().#checked_name(#rhs_value) {
                    ::core::option::Option::Some(val) => Self::new(val),
                    ::core::option::Option::None => ::core::option::Option::None,
                }
            }
        });

        if op.variants == OpVariants::NoSaturating
            || !item.repr.signed && op.variants == OpVariants::SignedSaturating
        {
            continue;
        }

        let saturating_name = Ident::new(&format!("saturating_{}", op.name), Span::call_site());
        let saturating_comment = format!("Saturating {}.", op.description.trim());

        tokens.extend(quote! {
            #[doc = #saturating_comment]
            #[must_use]
            #[inline]
            #vis const fn #saturating_name(self, #rhs_type) -> Self {
                Self::new_saturating(self.get().#saturating_name(#rhs_value))
            }
        });
    }
}

struct CheckedOperator {
    name: &'static str,
    description: &'static str,
    rhs: Option<&'static str>,
    variants: OpVariants,
}

#[derive(Eq, PartialEq, Clone, Copy)]
enum OpVariants {
    /// Checked and saturating ops on all integers.
    All,
    /// Checked operators on unsigned integers, checked and saturating ops on signed integers.
    SignedSaturating,
    /// Checked operators on all integers.
    NoSaturating,
    /// Checked and saturating operations on signed integers.
    Signed,
}

macro_rules! tokens_or {
    (() ($($else:tt)*)) => { $($else)* };
    (($($tokens:tt)*) ($($else:tt)*)) => { $($tokens)* };
}
macro_rules! checked_operators {
    ($(
        #[doc = $description:literal]
        fn $name:ident($($rhs:ty)?)
        $variants:ident
    ,)*) => {
        [$(
            CheckedOperator {
                name: stringify!($name),
                description: $description,
                rhs: tokens_or!(($(Some(stringify!($rhs)))?) (None)),
                variants: OpVariants::$variants,
            }
        ,)*]
    }
}

const CHECKED_OPERATORS: &[CheckedOperator] = &checked_operators! {
    /** integer addition       */ fn add        (Self) All             ,
    /** integer subtraction    */ fn sub        (Self) All             ,
    /** integer multiplication */ fn mul        (Self) All             ,
    /** integer division       */ fn div        (Self) NoSaturating    ,
    /** Euclidean division     */ fn div_euclid (Self) NoSaturating    ,
    /** integer remainder      */ fn rem        (Self) NoSaturating    ,
    /** Euclidean remainder    */ fn rem_euclid (Self) NoSaturating    ,
    /** negation               */ fn neg        (    ) SignedSaturating,
    /** absolute value         */ fn abs        (    ) Signed          ,
    /** exponentiation         */ fn pow        (u32 ) All             ,
};

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
            #[inline]
            fn #method(self, rhs: #rhs) -> Self::Output {
                #body
            }
        }
        impl ::core::ops::#trait_name<#rhs> for &#lhs {
            type Output = #lhs;
            #[inline]
            fn #method(self, rhs: #rhs) -> Self::Output {
                <#lhs as ::core::ops::#trait_name<#rhs>>::#method(*self, rhs)
            }
        }
        impl<'b> ::core::ops::#trait_name<&'b #rhs> for #lhs {
            type Output = #lhs;
            #[inline]
            fn #method(self, rhs: &'b #rhs) -> Self::Output {
                <#lhs as ::core::ops::#trait_name<#rhs>>::#method(self, *rhs)
            }
        }
        impl<'a> ::core::ops::#trait_name<&'a #rhs> for &#lhs {
            type Output = #lhs;
            #[inline]
            fn #method(self, rhs: &'a #rhs) -> Self::Output {
                <#lhs as ::core::ops::#trait_name<#rhs>>::#method(*self, *rhs)
            }
        }

        impl ::core::ops::#trait_name_assign<#rhs> for #lhs {
            #[inline]
            fn #method_assign(&mut self, rhs: #rhs) {
                *self = <Self as ::core::ops::#trait_name<#rhs>>::#method(*self, rhs);
            }
        }
        impl<'a> ::core::ops::#trait_name_assign<&'a #rhs> for #lhs {
            #[inline]
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
            #[inline]
            fn #method(self) -> Self::Output {
                #body
            }
        }
        impl ::core::ops::#trait_name for &#lhs {
            type Output = #lhs;
            #[inline]
            fn #method(self) -> Self::Output {
                <#lhs as ::core::ops::#trait_name>::#method(*self)
            }
        }
    });
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

fn generate_cmp_traits(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;

    // These are only impls that can't be derived
    tokens.extend(quote! {
        impl ::core::cmp::PartialEq<::core::primitive::#repr> for #ident {
            #[inline]
            fn eq(&self, other: &::core::primitive::#repr) -> bool {
                self.get() == *other
            }
        }
        impl ::core::cmp::PartialEq<#ident> for ::core::primitive::#repr {
            #[inline]
            fn eq(&self, other: &#ident) -> bool {
                *self == other.get()
            }
        }
        impl ::core::cmp::PartialOrd<::core::primitive::#repr> for #ident {
            #[inline]
            fn partial_cmp(
                &self,
                other: &::core::primitive::#repr
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                ::core::cmp::PartialOrd::partial_cmp(&self.get(), other)
            }
        }
        impl ::core::cmp::PartialOrd<#ident> for ::core::primitive::#repr {
            #[inline]
            fn partial_cmp(
                &self,
                other: &#ident
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                ::core::cmp::PartialOrd::partial_cmp(self, &other.get())
            }
        }
    });
}

fn generate_as_ref_borrow(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;

    tokens.extend(quote! {
        impl ::core::convert::AsRef<::core::primitive::#repr> for #ident {
            #[inline]
            fn as_ref(&self) -> &::core::primitive::#repr {
                self.get_ref()
            }
        }
        impl ::core::borrow::Borrow<::core::primitive::#repr> for #ident {
            #[inline]
            fn borrow(&self) -> &::core::primitive::#repr {
                self.get_ref()
            }
        }
    });
}

fn generate_default(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;

    if item.range.contains(&BigInt::from(0)) {
        tokens.extend(quote! {
            impl ::core::default::Default for #ident {
                fn default() -> Self {
                    unsafe { Self::new_unchecked(0) }
                }
            }
        });
    }
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
                        <Self as ::core::default::Default>::default(),
                        ::core::ops::Add::add,
                    )
                }
            }
            impl<'a> ::core::iter::Sum<&'a Self> for #ident {
                fn sum<I: ::core::iter::Iterator<Item = &'a Self>>(iter: I) -> Self {
                    ::core::iter::Iterator::sum(::core::iter::Iterator::copied(iter))
                }
            }
        });
    }

    tokens.extend(quote! {
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
        });
    }

    tokens.extend(quote! {
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

    if item.step_trait {
        tokens.extend(quote! {
            impl ::core::iter::Step for #ident {
                #[inline]
                fn steps_between(start: &Self, end: &Self) -> ::core::option::Option<::core::primitive::usize> {
                    ::core::iter::Step::steps_between(&start.get(), &end.get())
                }
                #[inline]
                fn forward_checked(start: Self, count: ::core::primitive::usize) -> ::core::option::Option<Self> {
                    ::core::iter::Step::forward_checked(start.get(), count).and_then(Self::new)
                }
                #[inline]
                fn backward_checked(start: Self, count: ::core::primitive::usize) -> ::core::option::Option<Self> {
                    ::core::iter::Step::backward_checked(start.get(), count).and_then(Self::new)
                }
            }
        });
    }
}

fn generate_from_str(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let crate_path = &item.crate_path;

    tokens.extend(quote! {
        impl ::core::str::FromStr for #ident {
            type Err = #crate_path::ParseError;
            fn from_str(s: &::core::primitive::str) -> ::core::result::Result<Self, Self::Err> {
                Self::from_str_radix(s, 10)
            }
        }
    });
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

fn generate_to_primitive_traits(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;

    for repr in item.repr.larger_reprs() {
        tokens.extend(quote! {
            impl ::core::convert::From<#ident> for ::core::primitive::#repr {
                #[inline]
                fn from(bounded: #ident) -> Self {
                    ::core::convert::From::from(bounded.get())
                }
            }
        });
    }
}

fn generate_arbitrary1(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;
    let crate_path = &item.crate_path;
    let arbitrary = quote!(#crate_path::__private::arbitrary1);

    tokens.extend(quote! {
        impl<'a> #arbitrary::Arbitrary<'a> for #ident {
            fn arbitrary(u: &mut #arbitrary::Unstructured<'a>) -> #arbitrary::Result<Self> {
                Self::new(u.arbitrary()?).ok_or(#arbitrary::Error::IncorrectFormat)
            }

            #[inline]
            fn size_hint(
                depth: ::core::primitive::usize,
            ) -> (::core::primitive::usize, ::core::option::Option<::core::primitive::usize>) {
                <#repr as #arbitrary::Arbitrary<'a>>::size_hint(depth)
            }
        }
    });
}

fn generate_bytemuck1(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;
    let crate_path = &item.crate_path;
    let bytemuck = quote!(#crate_path::__private::bytemuck1);

    tokens.extend(quote! {
        unsafe impl #bytemuck::Contiguous for #ident {
            type Int = ::core::primitive::#repr;
            const MAX_VALUE: ::core::primitive::#repr = Self::MAX_VALUE;
            const MIN_VALUE: ::core::primitive::#repr = Self::MIN_VALUE;
        }
    });

    if item.range.contains(&BigInt::from(0)) {
        tokens.extend(quote! {
            unsafe impl #bytemuck::Zeroable for #ident {}
        });
    }
}

fn generate_serde1(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;
    let crate_path = &item.crate_path;
    let serde = quote!(#crate_path::__private::serde1);

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
                                Self::MAX_VALUE,
                            )
                        )
                    })
            }
        }
    });
}

fn generate_tests(item: &BoundedInteger, tokens: &mut TokenStream) {
    let mut tests = TokenStream::new();

    generate_test_range(item, &mut tests);
    generate_test_arithmetic(item, &mut tests);

    tokens.extend(quote! {
        mod tests {
            use super::*;
            use ::core::{assert, assert_eq};
            use ::core::primitive::*;
            use ::core::option::Option::{self, Some, None};
            #tests
        }
    });
}

fn generate_test_range(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;

    let min = item.repr.number_literal(item.range.start());
    let max = item.repr.number_literal(item.range.end());

    let above_min = item.repr.number_literal(item.range.start() + 1);
    let below_max = item.repr.number_literal(item.range.end() - 1);

    let opt_literal = |num| {
        if let Ok(lit) = item.repr.try_number_literal(num) {
            quote!(Some(#lit))
        } else {
            quote!(None)
        }
    };
    let below_range = opt_literal(item.range.start() - 1);
    let above_range = opt_literal(item.range.end() + 1);

    tokens.extend(quote! {
        #[test]
        fn range() {
            assert_eq!(#ident::MIN_VALUE, #min);
            assert_eq!(#ident::MAX_VALUE, #max);
            assert_eq!(#ident::MIN.get(), #min);
            assert_eq!(#ident::MAX.get(), #max);

            if let Some(below_range) = #below_range {
                assert!(!#ident::in_range(below_range));
            } else {
                assert_eq!(#ident::MIN_VALUE, #repr::MIN);
            }
            assert!(#ident::in_range(#min));
            assert!(#ident::in_range(#above_min));
            assert!(#ident::in_range(#below_max));
            assert!(#ident::in_range(#max));
            if let Some(above_range) = #above_range {
               assert!(!#ident::in_range(above_range));
            } else {
                assert_eq!(#ident::MAX_VALUE, #repr::MAX);
            }
        }

        #[test]
        fn saturating() {
            assert_eq!(#ident::new_saturating(#repr::MIN), #ident::MIN_VALUE);
            if let Some(below_range) = #below_range {
                assert_eq!(#ident::new_saturating(below_range), #ident::MIN_VALUE);
            }
            assert_eq!(#ident::new_saturating(#min), #ident::MIN_VALUE);

            assert_eq!(#ident::new_saturating(#above_min).get(), #above_min);
            assert_eq!(#ident::new_saturating(#below_max).get(), #below_max);

            assert_eq!(#ident::new_saturating(#max), #ident::MAX_VALUE);
            if let Some(above_range) = #above_range {
                assert_eq!(#ident::new_saturating(above_range), #ident::MAX_VALUE);
            }
            assert_eq!(#ident::new_saturating(#repr::MAX), #ident::MAX_VALUE);
        }
    });
}

fn generate_test_arithmetic(item: &BoundedInteger, tokens: &mut TokenStream) {
    let ident = &item.ident;
    let repr = &item.repr;

    let mut body = TokenStream::new();

    for &op in &['+', '-', '*', '/', '%'] {
        let op = Punct::new(op, Spacing::Joint);
        body.extend(quote! {
            let _: #ident = #ident::MIN #op 0;
            let _: #ident = &#ident::MIN #op 0;
            let _: #ident = #ident::MIN #op &0;
            let _: #ident = &#ident::MIN #op &0;
            let _: #repr = 0 #op #ident::MIN;
            let _: #repr = 0 #op &#ident::MIN;
            let _: #repr = &0 #op #ident::MIN;
            let _: #repr = &0 #op &#ident::MIN;
            let _: #ident = #ident::MIN #op #ident::MIN;
            let _: #ident = &#ident::MIN #op #ident::MIN;
            let _: #ident = #ident::MIN #op &#ident::MIN;
            let _: #ident = &#ident::MIN #op &#ident::MIN;
            *&mut #ident::MIN #op= 0;
            *&mut #ident::MIN #op= &0;
            *&mut #ident::MIN #op= #ident::MIN;
            *&mut #ident::MIN #op= &#ident::MIN;
            *&mut 0 #op= #ident::MIN;
            *&mut 0 #op= &#ident::MIN;
        });
    }

    if item.repr.signed {
        body.extend(quote! {
            let _: #ident = #ident::MIN.abs();
            let _: Option<#ident> = #ident::MIN.checked_abs();

            let _: #ident = -#ident::MIN;
            let _: #ident = -&#ident::MIN;
            let _: #ident = #ident::MIN.saturating_neg();
        });
    }
    body.extend(quote! {
        let _: Option<#ident> = #ident::MIN.checked_neg();
    });

    let infallibles = [
        "pow",
        "div_euclid",
        "rem_euclid",
        "saturating_add",
        "saturating_sub",
        "saturating_mul",
        "saturating_pow",
    ];
    let fallibles = [
        "add",
        "sub",
        "mul",
        "div",
        "div_euclid",
        "rem",
        "rem_euclid",
        "pow",
    ];
    for method in &infallibles {
        let method = Ident::new(method, Span::call_site());
        body.extend(quote! {
            let _: #ident = #ident::MIN.#method(0);
        });
    }
    for method in &fallibles {
        let method = Ident::new(&format!("checked_{}", method), Span::call_site());
        body.extend(quote! {
            let _: Option<#ident> = #ident::MIN.#method(0);
        });
    }

    tokens.extend(quote! {
        #[test]
        fn arithmetic() {
            // Don't run the tests, as they might panic. We just need to make sure these methods
            // exist.
            if false { #body }
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

#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse2;

    #[allow(clippy::needless_pass_by_value)]
    fn assert_result(
        f: impl FnOnce(&BoundedInteger, &mut TokenStream),
        input: TokenStream,
        expected: TokenStream,
    ) {
        let input = quote!([::path] false false false false false #input);
        let item = match parse2::<BoundedInteger>(input.clone()) {
            Ok(item) => item,
            Err(e) => panic!("Failed to parse '{}': {}", input, e),
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
                #[repr(transparent)]
                pub struct S(::core::primitive::i8);
            },
        );
    }
}
