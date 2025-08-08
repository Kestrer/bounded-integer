/// Generate a bounded integer type.
///
/// It takes in single struct or enum, with the content being a bounded range expression, whose
/// upper bound can be inclusive (`x, y`) or exclusive (`x, y`). The attributes and visibility
/// (e.g. `pub`) of the type are forwarded directly to the output type.
///
/// If the type is a struct and the bounded integer's range does not include zero,
/// the struct will have a niche at zero,
/// allowing for `Option<BoundedInteger>` to be the same size as `BoundedInteger` itself.
///
/// See the [`examples`](crate::examples) module for examples of what this macro generates.
///
/// # Examples
///
/// With a struct:
/// ```
#[cfg_attr(feature = "step_trait", doc = "# #![feature(step_trait)]")]
/// # mod force_item_scope {
/// # use bounded_integer::bounded_integer;
/// bounded_integer! {
///     pub struct S(2, 5);
/// }
/// # }
/// ```
/// The generated item should look like this (u8 is chosen as it is the smallest repr):
/// ```
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// #[repr(transparent)]
/// pub struct S(u8);
/// ```
/// And the methods will ensure that `2 ≤ S.0 ≤ 5`.
///
/// With an enum:
/// ```
#[cfg_attr(feature = "step_trait", doc = "# #![feature(step_trait)]")]
/// # mod force_item_scope {
/// # use bounded_integer::bounded_integer;
/// bounded_integer! {
///     pub enum S(-1, 1);
/// }
/// # }
/// ```
/// The generated item should look like this (i8 is chosen as it is the smallest repr):
/// ```
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// #[repr(i8)]
/// pub enum S {
///     N1 = -1, Z, P1
/// }
/// ```
///
/// You can also ascribe dedicated names to the enum variants:
/// ```
#[cfg_attr(feature = "step_trait", doc = "# #![feature(step_trait)]")]
/// # use bounded_integer::bounded_integer;
/// bounded_integer! {
///     pub enum Sign {
///         Negative = -1,
///         Zero,
///         Positive,
///     }
/// }
/// assert_eq!(Sign::Negative.get(), -1);
/// assert_eq!(Sign::new(1).unwrap(), Sign::Positive);
/// ```
///
/// # Custom repr
///
/// The item can have a `repr` attribute to specify how it will be represented in memory, which can
/// be a `u*` or `i*` type. In this example we override the `repr` to be a `u16`, when it would
/// have normally been a `u8`.
///
/// ```
#[cfg_attr(feature = "step_trait", doc = "# #![feature(step_trait)]")]
/// # mod force_item_scope {
/// # use bounded_integer::bounded_integer;
/// bounded_integer! {
///     #[repr(u16)]
///     pub struct S(2, 4);
/// }
/// # }
/// ```
/// The generated item should look like this:
/// ```
/// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// #[repr(transparent)]
/// pub struct S(u16);
/// ```
#[macro_export]
macro_rules! bounded_integer {
    (
        $(#[$($attr:tt)*])*
        $(pub $(($($vis:tt)*))?)? struct $name:ident($min:expr, $max:expr);
    ) => {
        $crate::__helper! { validate_attrs
            [$([$($attr)*])*]
            [$(pub $(($($vis)*))?)?]
            [-] [struct] [$name] [$min] [$max]
            [$crate]
        }
    };
    (
        $(#[$($attr:tt)*])*
        $(pub $(($($vis:tt)*))?)? enum $name:ident($min:expr, $max:expr);
    ) => {
        $crate::__helper! { validate_attrs
            [$([$($attr)*])*]
            [$(pub $(($($vis)*))?)?]
            [-] [enum] [$name] [$min] [$max]
            [$crate]
        }
    };
    (
        $(#[$($attr:tt)*])*
        $(pub $(($($vis:tt)*))?)? enum $name:ident {
            $($(#[$($var_attr:tt)*])* $variant:ident $(= $val:literal)?),* $(,)?
        }
    ) => {
        $crate::__helper! { validate_attrs
            [$([$($attr)*])*]
            [$(pub $(($($vis)*))?)?]
            [+] [enum] [$name] [$([[$(#[$($var_attr)*])*] $variant [$($val)?]])*] []
            [$crate]
        }
    };
    // Migration
    ($(#[$($attr:tt)*])* $vis:vis struct $name:ident { $($_:tt)* }) => {
        compile_error!(concat!(
            "syntax has changed; use `struct ",
            stringify!($name),
            "(MIN, MAX);` instead.",
        ));
    };
    ($(#[$($attr:tt)*])* $vis:vis enum $name:ident { $($_:tt)* }) => {
        compile_error!(concat!(
            "syntax has changed; use `enum ",
            stringify!($name),
            "(MIN, MAX);` instead.",
        ));
    };
}

#[macro_export]
#[cfg(feature = "zerocopy")]
#[doc(hidden)]
macro_rules! __dispatch_zerocopy {
    ([$($attr:tt)*] $($t:tt)*) => {
        $crate::__helper! { vis
            [+]
            [
                $($attr)*
                [derive($crate::__private::zerocopy::IntoBytes)]
                [derive($crate::__private::zerocopy::Immutable)]
            ]
            $($t)*
        }
    };
}
#[macro_export]
#[cfg(not(feature = "zerocopy"))]
#[doc(hidden)]
macro_rules! __dispatch_zerocopy {
    ($($t:tt)*) => {
        $crate::__helper! { vis [-] $($t)* }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! __helper {
    (validate_attrs [$($attr:tt)*] $($t:tt)*) => {
        $crate::__dispatch_zerocopy! { [$($attr)*] $($t)* }
        $($crate::__helper! { validate_attr $attr })*
    };
    (validate_attr [doc = $($_:tt)*]) => {};
    (validate_attr [repr($($_:tt)*)]) => {};
    (validate_attr [allow($($_:tt)*)]) => {};
    (validate_attr [expect($($_:tt)*)]) => {};
    (validate_attr [warn($($_:tt)*)]) => {};
    (validate_attr [deny($($_:tt)*)]) => {};
    (validate_attr [forbid($($_:tt)*)]) => {};
    (validate_attr [deprecated$(($($_:tt)*))?]) => {};
    (validate_attr [must_use]) => {};
    (validate_attr [cfg_attr($cfg:meta, $($attr:tt)*)]) => { $crate::__helper! { validate_attr [$($attr)*] } };
    (validate_attr [$($attr:tt)*]) => {
        ::core::compile_error!("for soundness reasons, custom attributes are not allowed");
    };
    (vis $zerocopy:tt $attr:tt [$(pub($(in)? self))?] $($t:tt)*) => {
        $crate::__private::proc_macro! { $zerocopy $attr [] [pub(super)] $($t)* }
    };
    (vis $zerocopy:tt $attr:tt [pub] $($t:tt)*) => {
        $crate::__private::proc_macro! { $zerocopy $attr [pub] [pub] $($t)* }
    };
    (vis $zerocopy:tt $attr:tt [pub($(in)? crate$(::$($path:ident)::+)?)] $($t:tt)*) => {
        $crate::__private::proc_macro! { $zerocopy $attr [pub(in crate$(::$($path)::+)?)] [pub(in crate$(::$($path)::+)?)] $($t)* }
    };
    (vis $zerocopy:tt $attr:tt [pub(super)] $($t:tt)*) => {
        $crate::__private::proc_macro! { $zerocopy $attr [pub(super)] [pub(in super::super)] $($t)* }
    };
    (vis $zerocopy:tt $attr:tt [pub(in $($path:ident)::+)] $($t:tt)*) => {
        $crate::__private::proc_macro! { $zerocopy $attr [pub(in $($path)::+)] [pub(in super::$($path)::+)] $($t)* }
    };
}

#[cfg(test)]
mod tests {
    use crate::bounded_integer;

    #[test]
    fn all_below_zero() {
        #![expect(unused)]
        bounded_integer!(struct Struct(-400, -203););
        bounded_integer!(enum Enum(-500, -483););
    }

    #[test]
    fn publicity() {
        mod a {
            #![expect(unused)]
            bounded_integer!(struct A(0, 0););
            bounded_integer!(pub(self) struct B(0, 0););
            bounded_integer!(pub(in self) struct C(0, 0););
            mod c {
                bounded_integer!(pub(in super) struct D(0, 0););
            }
            pub(super) use c::*;
        }
        #[expect(unused)]
        use a::*;
        mod b {
            bounded_integer!(pub(super) struct A(0, 0););
            bounded_integer!(pub(crate) struct B(0, 0););
            bounded_integer!(pub(in crate::r#macro) struct C(0, 0););
            mod c {
                bounded_integer!(pub(in super::super) struct D(0, 0););
            }
            pub(super) use c::*;
        }
        use b::*;
        // would cause an ambiguity error if the number of reachable items above is >1
        A::default();
        B::default();
        C::default();
        D::default();
    }

    #[test]
    fn inferred_reprs() {
        bounded_integer!(struct ByteStruct(0, 255););
        const _: u8 = ByteStruct::MIN_VALUE;
        bounded_integer!(enum ByteEnum(0, 255););
        const _: u8 = ByteEnum::MIN_VALUE;

        bounded_integer!(struct U16Struct(0, 256););
        const _: u16 = U16Struct::MIN_VALUE;
        bounded_integer!(enum U16Enum(0, 256););
        const _: u16 = U16Enum::MIN_VALUE;

        bounded_integer!(struct I16Struct(-1, 255););
        const _: i16 = I16Struct::MIN_VALUE;
        bounded_integer!(enum I16Enum(-1, 255););
        const _: i16 = I16Enum::MIN_VALUE;

        bounded_integer!(struct SignedByteStruct(-128, 127););
        const _: i8 = SignedByteStruct::MIN_VALUE;
        bounded_integer!(struct SignedByteEnum(-128, 127););
        const _: i8 = SignedByteEnum::MIN_VALUE;
    }

    #[test]
    fn simple_enum() {
        bounded_integer!(enum M(-3, 2););
        assert_eq!(M::MIN_VALUE, -3);
        assert_eq!(M::MAX_VALUE, 2);
        assert_eq!(M::N3.get(), -3);
        assert_eq!(M::N2.get(), -2);
        assert_eq!(M::N1.get(), -1);
        assert_eq!(M::Z.get(), 0);
        assert_eq!(M::P1.get(), 1);
        assert_eq!(M::P2.get(), 2);
        assert_eq!(M::N3 as i8, -3);
        assert_eq!(M::N2 as i8, -2);
        assert_eq!(M::N1 as i8, -1);
        assert_eq!(M::Z as i8, 0);
        assert_eq!(M::P1 as i8, 1);
        assert_eq!(M::P2 as i8, 2);

        bounded_integer!(
            enum X {
                A = -1,
                B,
                C = 1,
                D,
            }
        );
        assert_eq!(X::A.get(), -1);
        assert_eq!(X::B.get(), 0);
        assert_eq!(X::C.get(), 1);
        assert_eq!(X::D.get(), 2_i8);

        bounded_integer!(
            enum Y {
                A = 4_294_967_295,
            }
        );
        assert_eq!(Y::A.get(), 4_294_967_295_u32);

        bounded_integer!(
            enum Z {
                A = 4_294_967_295,
                B,
            }
        );
        assert_eq!(Z::A.get(), 4_294_967_295_u64);
        assert_eq!(Z::B.get(), 4_294_967_296_u64);
    }

    #[test]
    fn zeroable() {
        #[cfg(all(feature = "bytemuck1", feature = "zerocopy"))]
        fn assert_zeroable<T: Default + bytemuck1::Zeroable + zerocopy::FromZeros>() {}
        #[cfg(not(all(feature = "bytemuck1", feature = "zerocopy")))]
        fn assert_zeroable<T: Default>() {}
        #[expect(unused)]
        trait NotZeroable<const N: usize> {}
        impl<T: Default> NotZeroable<0> for T {}
        #[cfg(feature = "bytemuck1")]
        impl<T: bytemuck1::Zeroable> NotZeroable<1> for T {}
        #[cfg(feature = "zerocopy")]
        impl<T: zerocopy::FromZeros> NotZeroable<2> for T {}
        macro_rules! not_zeroable {
            ($t:ty) => {
                impl NotZeroable<0> for $t {}
                #[cfg(feature = "bytemuck1")]
                impl NotZeroable<1> for $t {}
                #[cfg(feature = "zerocopy")]
                impl NotZeroable<2> for $t {}
            };
        }

        bounded_integer!(struct A(0, 0););
        assert_zeroable::<A>();

        bounded_integer!(struct B(-459, 3););
        assert_zeroable::<B>();

        bounded_integer!(struct C(1, 5););
        not_zeroable!(C);
        assert_eq!(size_of::<Option<C>>(), size_of::<C>());

        bounded_integer!(struct D(-5, -1););
        not_zeroable!(D);
        assert_eq!(size_of::<Option<D>>(), size_of::<D>());

        bounded_integer!(struct E(-(5), 0_i8););
        not_zeroable!(E);
        assert_ne!(size_of::<Option<E>>(), size_of::<E>());
    }

    #[test]
    #[cfg(feature = "zerocopy")]
    fn unaligned() {
        fn assert_unaligned<T: zerocopy::Unaligned>() {}
        bounded_integer!(struct A(0, 255););
        assert_unaligned::<A>();
        bounded_integer!(struct B(-128, 127););
        assert_unaligned::<B>();

        #[expect(unused)]
        trait NotUnaligned {}
        impl<T: zerocopy::Unaligned> NotUnaligned for T {}

        bounded_integer!(struct C(255, 256););
        bounded_integer!(struct D(-129, -128););
        impl NotUnaligned for C {}
        impl NotUnaligned for D {}
    }

    #[test]
    fn lit_radix() {
        #![expect(clippy::mixed_case_hex_literals)]

        bounded_integer!(struct Hex(0x5, 0xf_F););
        assert_eq!(Hex::MIN_VALUE, 5);
        assert_eq!(Hex::MAX_VALUE, 255);

        bounded_integer!(struct Oct(0o35, 0o40););
        assert_eq!(Oct::MIN_VALUE, 29);
        assert_eq!(Oct::MAX_VALUE, 32);

        bounded_integer!(struct Bin(0b1101, 0b11101););
        assert_eq!(Bin::MIN_VALUE, 0b1101);
        assert_eq!(Bin::MAX_VALUE, 0b11101);
    }

    #[test]
    fn repr_without_repr() {
        #![expect(unused)]
        bounded_integer!(struct Owo(0_u8, 2 + 2););
        bounded_integer!(struct Uwu(-57 * 37, 8_i64););
    }

    #[test]
    fn allowed_attrs() {
        #![expect(deprecated)]
        use crate::bounded_integer;

        bounded_integer! {
            #[cfg_attr(all(), doc = "")]
            #[deprecated]
            #[must_use]
            struct S(0, 255);
        }

        #[expect(deprecated, unused_must_use)]
        S::new(0).unwrap();
    }

    #[test]
    fn complex_expr() {
        bounded_integer!(#[repr(u8)] struct S(0, 10 + 10););
        assert_eq!(S::MIN_VALUE, 0);
        assert_eq!(S::MAX_VALUE, 20);
    }
}
