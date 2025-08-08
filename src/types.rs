define_bounded_integers! {
    BoundedU8(u8, unaligned, unsigned),
    BoundedU16(u16, unsigned),
    BoundedU32(u32, unsigned),
    BoundedU64(u64, unsigned),
    BoundedU128(u128, unsigned),
    BoundedUsize(usize, unsigned),
    BoundedI8(i8, unaligned, unsigned),
    BoundedI16(i16),
    BoundedI32(i32),
    BoundedI64(i64),
    BoundedI128(i128),
    BoundedIsize(isize),
}

macro_rules! define_bounded_integers {
    ($($name:ident(
        $inner:ident
        $(, unaligned $([$unaligned:ident])?)?
        $(, unsigned $([$unsigned:ident])?)?
    ),)*) => { $(
        #[doc = "An"]
        #[doc = concat!("[`", stringify!($inner), "`]")]
        #[doc = "constrained to be in the range `MIN..=MAX`."]
        #[repr(transparent)]
        #[cfg_attr(feature = "zerocopy", derive(zerocopy::IntoBytes, zerocopy::Immutable))]
        #[cfg_attr(
            all(feature = "zerocopy", any($($(if $unaligned)? true)?)),
            derive(zerocopy::Unaligned),
        )]
        pub struct $name<const MIN: $inner, const MAX: $inner>($inner);

        $crate::unsafe_api! {
            [const MIN: $inner, const MAX: $inner] for $name<MIN, MAX>,
            unsafe repr: $inner,
            min: MIN,
            max: MAX,
        }

        #[cfg(any($($(if $unsigned)? true)?))]
        impl<const MAX: $inner> Default for $name<0, MAX> {
            fn default() -> Self {
                Self::const_new::<0>()
            }
        }

        #[cfg(feature = "bytemuck1")]
        #[cfg(any($($($unsigned)? true)?))]
        unsafe impl<const MAX: $inner> bytemuck1::Zeroable for $name<0, MAX> {}
    )* }
}
use define_bounded_integers;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range() {
        type Bounded = BoundedI8<3, 10>;
        assert_eq!(Bounded::MIN_VALUE, 3);
        assert_eq!(Bounded::MAX_VALUE, 10);
        assert_eq!(Bounded::MIN.get(), Bounded::MIN_VALUE);
        assert_eq!(Bounded::MAX.get(), Bounded::MAX_VALUE);

        assert!(Bounded::in_range(3));
        assert!(!Bounded::in_range(2));
        assert!(Bounded::in_range(10));
        assert!(!Bounded::in_range(11));
    }

    #[test]
    fn new_saturating() {
        type Bounded = BoundedI8<3, 10>;
        assert_eq!(Bounded::new_saturating(i8::MIN), Bounded::MIN);
        assert_eq!(Bounded::new_saturating(i8::MAX), Bounded::MAX);
        assert_eq!(Bounded::new_saturating(11).get(), 10);
        assert_eq!(Bounded::new_saturating(10).get(), 10);
        assert_eq!(Bounded::new_saturating(3).get(), 3);
        assert_eq!(Bounded::new_saturating(2).get(), 3);
    }

    #[test]
    fn wrapping_unwiden() {
        type Bounded = BoundedU8<2, 20>;

        assert_eq!(Bounded::new_wrapping(0_u8), 19);
        assert_eq!(Bounded::new_wrapping(2_u8), 2);
        assert_eq!(Bounded::new_wrapping(20_u8), 20);
        assert_eq!(Bounded::new_wrapping(21_u8), 2);
        assert_eq!(Bounded::new_wrapping(255_u8), 8);

        assert_eq!(Bounded::new_wrapping(12_u16), 12);
        assert_eq!(Bounded::new_wrapping(21_u16), 2);
        assert_eq!(Bounded::new_wrapping(12_i16), 12);
        assert_eq!(Bounded::new_wrapping(21_i16), 2);

        assert_eq!(Bounded::new_wrapping(0_u16), 19);
        assert_eq!(Bounded::new_wrapping(65535_u16), 4);
        assert_eq!(Bounded::new_wrapping(65533_u16), 2);
        assert_eq!(Bounded::new_wrapping(65532_u16), 20);

        assert_eq!(Bounded::new_wrapping(-32768_i16), 7);
        assert_eq!(Bounded::new_wrapping(-32755_i16), 20);
        assert_eq!(Bounded::new_wrapping(-32754_i16), 2);
        assert_eq!(Bounded::new_wrapping(32767_i16), 11);
    }

    #[test]
    fn wrapping_full() {
        type Bounded = BoundedI8<{ i8::MIN }, { i8::MAX }>;
        assert_eq!(Bounded::new_wrapping(37_i8), 37);
        assert_eq!(Bounded::new_wrapping(-128_i8), -128);
        assert_eq!(Bounded::new_wrapping(127_i8), 127);
        assert_eq!(Bounded::new_wrapping(128_i16), -128);
        assert_eq!(Bounded::new_wrapping(-200_i16), 56);
        assert_eq!(Bounded::new(25).unwrap().wrapping_pow(20), 97);
    }

    #[test]
    fn wrapping_signed() {
        type Bounded = BoundedI8<-5, 2>;
        assert_eq!(Bounded::new_wrapping(0_i8).get(), 0);
        assert_eq!(Bounded::new_wrapping(-5_i8).get(), -5);
        assert_eq!(Bounded::new_wrapping(2_i8).get(), 2);
        assert_eq!(Bounded::new_wrapping(-128_i8).get(), 0);
    }

    #[test]
    fn arithmetic() {
        #![expect(clippy::modulo_one)]
        type Bounded = BoundedI8<-5, 20>;
        assert_eq!(Bounded::new(2).unwrap() + 3, 5);
        assert_eq!(Bounded::new(2).unwrap() - 5, -3);
        assert_eq!(Bounded::new(3).unwrap() * 5, 15);
        assert_eq!(Bounded::new(11).unwrap() / 3, 3);
        assert_eq!(Bounded::new(11).unwrap() % 3, 2);
        assert_eq!(Bounded::new(-3).unwrap() / 2, -1);
        assert_eq!(Bounded::new(-3).unwrap() % 2, -1);
        assert_eq!(-Bounded::new(-3).unwrap(), 3);
        assert_eq!(!Bounded::new(-3).unwrap(), 2);
        assert_eq!(-&Bounded::new(-3).unwrap(), 3);
        assert_eq!(!&Bounded::new(-3).unwrap(), 2);
        assert_eq!(Bounded::new(3).unwrap() << 1, 6);
        assert_eq!(Bounded::new(3).unwrap() >> 1, 1);
        variations!(Bounded, i8, + += - -= * *= / /= % %=);

        assert_eq!(Bounded::new(2).unwrap().pow(3).get(), 8);
        assert_eq!(Bounded::new(-3).unwrap().div_euclid(2).get(), -2);
        assert_eq!(Bounded::new(-3).unwrap().rem_euclid(2).get(), 1);
        assert_eq!(Bounded::new(-3).unwrap().abs().get(), 3);
        assert_eq!(Bounded::new(4).unwrap().abs().get(), 4);

        macro_rules! variations {
            ($ty:ty, $inner:ty, $($op:tt $op_assign:tt)*) => {
                $(
                    let _: $ty = <$ty>::new(0).unwrap() $op 1;
                    let _: $ty = &<$ty>::new(0).unwrap() $op 1;
                    let _: $ty = <$ty>::new(0).unwrap() $op &1;
                    let _: $ty = &<$ty>::new(0).unwrap() $op &1;
                    let _: $inner = 0 $op <$ty>::new(1).unwrap();
                    let _: $inner = 0 $op &<$ty>::new(1).unwrap();
                    let _: $inner = &0 $op <$ty>::new(1).unwrap();
                    let _: $inner = &0 $op &<$ty>::new(1).unwrap();
                    let _: $ty = <$ty>::new(0).unwrap() $op <$ty>::new(1).unwrap();
                    let _: $ty = &<$ty>::new(0).unwrap() $op <$ty>::new(1).unwrap();
                    let _: $ty = <$ty>::new(0).unwrap() $op &<$ty>::new(1).unwrap();
                    let _: $ty = &<$ty>::new(0).unwrap() $op &<$ty>::new(1).unwrap();
                    *&mut <$ty>::new(0).unwrap() $op_assign 1;
                    *&mut <$ty>::new(0).unwrap() $op_assign &1;
                    *&mut <$ty>::new(0).unwrap() $op_assign <$ty>::new(1).unwrap();
                    *&mut <$ty>::new(0).unwrap() $op_assign &<$ty>::new(1).unwrap();
                    *&mut 0 $op_assign <$ty>::new(1).unwrap();
                    *&mut 0 $op_assign &<$ty>::new(1).unwrap();
                )*
            };
        }
        use variations;
    }

    #[test]
    fn saturating() {
        type Bounded = BoundedI8<-5, 20>;
        assert_eq!(Bounded::new(13).unwrap().saturating_add(1).get(), 14);
        assert_eq!(Bounded::new(14).unwrap().saturating_add(7).get(), 20);
        assert_eq!(Bounded::new(-2).unwrap().saturating_sub(-1).get(), -1);
        assert_eq!(Bounded::new(-2).unwrap().saturating_sub(127).get(), -5);
        assert_eq!(Bounded::new(2).unwrap().saturating_mul(3).get(), 6);
        assert_eq!(Bounded::new(15).unwrap().saturating_mul(-1).get(), -5);
        assert_eq!(Bounded::new(3).unwrap().saturating_pow(2).get(), 9);
        assert_eq!(Bounded::new(3).unwrap().saturating_pow(3).get(), 20);
        assert_eq!(Bounded::new(-4).unwrap().saturating_neg().get(), 4);
        assert_eq!(Bounded::new(8).unwrap().saturating_neg().get(), -5);
        assert_eq!(Bounded::new(8).unwrap().saturating_abs().get(), 8);
        assert_eq!(<BoundedI8<-20, 5>>::new(-6).unwrap().saturating_abs(), 5);
    }

    #[test]
    fn checked() {
        type Bounded = BoundedI8<-5, 20>;
        assert_eq!(Bounded::new(13).unwrap().checked_add(2).unwrap().get(), 15);
        assert_eq!(Bounded::new(14).unwrap().checked_add(7), None);
        assert_eq!(Bounded::new(-2).unwrap().checked_sub(-1).unwrap().get(), -1);
        assert_eq!(Bounded::new(-2).unwrap().checked_sub(127), None);
        assert_eq!(Bounded::new(2).unwrap().checked_mul(3).unwrap().get(), 6);
        assert_eq!(Bounded::new(15).unwrap().checked_mul(-1), None);
        assert_eq!(Bounded::new(3).unwrap().checked_pow(2).unwrap().get(), 9);
        assert_eq!(Bounded::new(3).unwrap().checked_pow(3), None);
        assert_eq!(Bounded::new(2).unwrap().checked_shl(3).unwrap().get(), 16);
        assert_eq!(Bounded::new(3).unwrap().checked_shl(3), None);
        assert_eq!(Bounded::new(9).unwrap().checked_shr(2).unwrap().get(), 2);
        assert_eq!(<BoundedI8<4, 8>>::new(8).unwrap().checked_shr(2), None);
        assert_eq!(Bounded::new(11).unwrap().checked_div(3).unwrap().get(), 3);
        assert_eq!(Bounded::new(11).unwrap().checked_rem(3).unwrap().get(), 2);
        assert_eq!(<BoundedI8<4, 11>>::new(11).unwrap().checked_div(3), None);
        assert_eq!(<BoundedI8<4, 11>>::new(11).unwrap().checked_rem(3), None);
        assert_eq!(Bounded::new(11).unwrap().checked_div_euclid(3).unwrap(), 3);
        assert_eq!(Bounded::new(11).unwrap().checked_rem_euclid(3).unwrap(), 2);
        assert_eq!(
            <BoundedI8<4, 11>>::new(11).unwrap().checked_div_euclid(3),
            None
        );
        assert_eq!(
            <BoundedI8<4, 11>>::new(11).unwrap().checked_rem_euclid(3),
            None
        );
        assert_eq!(Bounded::new(-3).unwrap().checked_neg().unwrap().get(), 3);
        assert_eq!(Bounded::new(6).unwrap().checked_neg(), None);
        assert_eq!(Bounded::new(-3).unwrap().checked_abs().unwrap().get(), 3);
        assert_eq!(Bounded::new(6).unwrap().checked_abs().unwrap().get(), 6);
        assert_eq!(<BoundedI8<-20, 5>>::new(-6).unwrap().checked_abs(), None);
    }

    #[test]
    fn wrapping() {
        type Bounded = BoundedI8<-5, 20>;
        assert_eq!(Bounded::new(0).unwrap().wrapping_add(0).get(), 0);
        assert_eq!(Bounded::new(-5).unwrap().wrapping_add(-128), -3);
        assert_eq!(Bounded::new(-5).unwrap().wrapping_sub(127), -2);
        assert_eq!(Bounded::new(20).unwrap().wrapping_add(127), 17);
        assert_eq!(Bounded::new(15).unwrap().wrapping_mul(17), -5);
        assert_eq!(Bounded::new(-5).unwrap().wrapping_div(2), -2);
        assert_eq!(Bounded::new(-5).unwrap().wrapping_rem(2), -1);
        assert_eq!(Bounded::new(-5).unwrap().wrapping_div_euclid(2), -3);
        assert_eq!(Bounded::new(-5).unwrap().wrapping_rem_euclid(2), 1);
        assert_eq!(Bounded::new(-5).unwrap().wrapping_neg(), 5);
        assert_eq!(Bounded::new(6).unwrap().wrapping_neg(), 20);
        assert_eq!(Bounded::new(-5).unwrap().wrapping_abs(), 5);
        assert_eq!(Bounded::new(6).unwrap().wrapping_abs(), 6);
        assert_eq!(<BoundedI8<-20, 5>>::new(-6).unwrap().wrapping_abs(), -20);
        assert_eq!(Bounded::new(5).unwrap().wrapping_pow(607), -5);
    }

    #[test]
    fn wrapping_div() {
        type Bounded = BoundedI32<{ i32::MIN }, -1>;
        assert_eq!(Bounded::new(i32::MIN).unwrap().wrapping_div(-1), i32::MIN);
    }

    #[test]
    fn iter() {
        type Bounded = BoundedI8<-8, 8>;
        #[expect(clippy::trivially_copy_pass_by_ref)]
        fn b(&n: &i8) -> Bounded {
            Bounded::new(n).unwrap()
        }
        assert_eq!([3, 2, 1].iter().map(b).sum::<Bounded>().get(), 6);
        assert_eq!([-8, 3, 7, 5, -2].iter().map(b).sum::<Bounded>().get(), 5);
        assert_eq!([7, 6, 4].iter().map(b).sum::<i8>(), 17);
        assert_eq!([-8, 3, 7, 5, -2].iter().map(b).sum::<i8>(), 5);

        assert_eq!([1, 3, 2, 1].iter().map(b).product::<Bounded>().get(), 6);
        assert_eq!([1, 3, 2, 1, 0].iter().map(b).product::<Bounded>().get(), 0);
        assert_eq!([-2, -3, -1].iter().map(b).product::<Bounded>().get(), -6);
        assert_eq!([3, 3].iter().map(b).product::<i8>(), 9);
    }

    #[test]
    fn parse() {
        use crate::ParseErrorKind::*;

        type Bounded = BoundedI8<3, 11>;

        assert_eq!("3".parse::<Bounded>().unwrap().get(), 3);
        assert_eq!("10".parse::<Bounded>().unwrap().get(), 10);
        assert_eq!("+11".parse::<Bounded>().unwrap().get(), 11);
        assert_eq!(Bounded::from_str_radix("1010", 2).unwrap().get(), 10);
        assert_eq!(Bounded::from_str_radix("B", 0xC).unwrap().get(), 11);
        assert_eq!(Bounded::from_str_radix("11", 7).unwrap().get(), 8);
        assert_eq!(Bounded::from_str_radix("7", 36).unwrap().get(), 7);

        assert_eq!("".parse::<Bounded>().unwrap_err().kind(), NoDigits);
        assert_eq!("+".parse::<Bounded>().unwrap_err().kind(), NoDigits);
        assert_eq!("-".parse::<Bounded>().unwrap_err().kind(), NoDigits);
        assert_eq!("2".parse::<Bounded>().unwrap_err().kind(), BelowMin);
        assert_eq!("12".parse::<Bounded>().unwrap_err().kind(), AboveMax);
        assert_eq!("-5".parse::<Bounded>().unwrap_err().kind(), BelowMin);
        assert_eq!("128".parse::<Bounded>().unwrap_err().kind(), AboveMax);
        assert_eq!("-129".parse::<Bounded>().unwrap_err().kind(), BelowMin);

        assert_eq!("++0".parse::<Bounded>().unwrap_err().kind(), InvalidDigit);
        assert_eq!("--0".parse::<Bounded>().unwrap_err().kind(), InvalidDigit);
        assert_eq!("O".parse::<Bounded>().unwrap_err().kind(), InvalidDigit);
        assert_eq!("C".parse::<Bounded>().unwrap_err().kind(), InvalidDigit);
        assert_eq!(
            Bounded::from_str_radix("3", 2).unwrap_err().kind(),
            InvalidDigit
        );
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn fmt() {
        use alloc::format;
        use alloc::string::ToString;
        type Bounded = BoundedU8<3, 210>;
        assert_eq!(Bounded::new(3).unwrap().to_string(), "3");
        assert_eq!(format!("{:b}", Bounded::new(5).unwrap()), "101");
        assert_eq!(format!("{:x}", Bounded::new(200).unwrap()), "c8");
        assert_eq!(format!("{:X}", Bounded::new(200).unwrap()), "C8");
        assert_eq!(format!("{:o}", Bounded::new(200).unwrap()), "310");
    }

    #[test]
    fn default() {
        assert_eq!(<BoundedU8<0, 5>>::default().get(), 0);
    }

    #[test]
    fn conversions() {
        assert_eq!(i8::from(<BoundedI8<1, 5>>::new(3).unwrap()), 3);
        assert_eq!(i16::from(<BoundedI8<1, 5>>::new(3).unwrap()), 3);
        assert_eq!(i32::from(<BoundedI8<1, 5>>::new(3).unwrap()), 3);
        assert_eq!(u32::from(<BoundedU32<1, 5>>::new(3).unwrap()), 3);
        assert_eq!(i64::from(<BoundedU32<1, 5>>::new(3).unwrap()), 3);
        assert_eq!(usize::from(<BoundedU16<1, 5>>::new(3).unwrap()), 3);
    }

    #[test]
    #[cfg(feature = "num-traits02")]
    #[expect(clippy::too_many_lines)]
    fn num() {
        use num_traits02::{
            AsPrimitive, Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedRem,
            CheckedShl, CheckedShr, CheckedSub, FromPrimitive, NumCast, ToPrimitive,
        };

        type B = BoundedI8<2, 8>;
        type BNeg = BoundedI8<-4, 8>;

        fn b(n: i8) -> B {
            B::new(n).unwrap()
        }

        fn bneg(n: i8) -> BNeg {
            BNeg::new(n).unwrap()
        }

        assert_eq!(B::min_value(), 2);
        assert_eq!(B::max_value(), 8);

        assert_eq!(BNeg::min_value(), -4);
        assert_eq!(BNeg::max_value(), 8);

        assert_eq!(<B as AsPrimitive<u8>>::as_(b(4)), 4u8);
        assert_eq!(<B as AsPrimitive<u16>>::as_(b(4)), 4u16);
        assert_eq!(<B as AsPrimitive<u32>>::as_(b(4)), 4u32);
        assert_eq!(<B as AsPrimitive<u64>>::as_(b(4)), 4u64);
        assert_eq!(<B as AsPrimitive<u128>>::as_(b(4)), 4u128);
        assert_eq!(<B as AsPrimitive<usize>>::as_(b(4)), 4usize);
        assert_eq!(<B as AsPrimitive<i8>>::as_(b(4)), 4i8);
        assert_eq!(<B as AsPrimitive<i16>>::as_(b(4)), 4i16);
        assert_eq!(<B as AsPrimitive<i32>>::as_(b(4)), 4i32);
        assert_eq!(<B as AsPrimitive<i64>>::as_(b(4)), 4i64);
        assert_eq!(<B as AsPrimitive<i128>>::as_(b(4)), 4i128);
        assert_eq!(<B as AsPrimitive<isize>>::as_(b(4)), 4isize);
        #[expect(clippy::float_cmp)]
        let () = assert_eq!(<B as AsPrimitive<f32>>::as_(b(4)), 4f32);
        #[expect(clippy::float_cmp)]
        let () = assert_eq!(<B as AsPrimitive<f64>>::as_(b(4)), 4f64);

        assert_eq!(B::from_u8(4u8), Some(b(4)));
        assert_eq!(B::from_u16(4u16), Some(b(4)));
        assert_eq!(B::from_u32(4u32), Some(b(4)));
        assert_eq!(B::from_u64(4u64), Some(b(4)));
        assert_eq!(B::from_u128(4u128), Some(b(4)));
        assert_eq!(B::from_usize(4usize), Some(b(4)));
        assert_eq!(B::from_i8(4i8), Some(b(4)));
        assert_eq!(B::from_i16(4i16), Some(b(4)));
        assert_eq!(B::from_i32(4i32), Some(b(4)));
        assert_eq!(B::from_i64(4i64), Some(b(4)));
        assert_eq!(B::from_i128(4i128), Some(b(4)));
        assert_eq!(B::from_isize(4isize), Some(b(4)));
        assert_eq!(B::from_f32(4f32), Some(b(4)));
        assert_eq!(B::from_f64(4f64), Some(b(4)));

        assert_eq!(B::from_u8(16u8), None);
        assert_eq!(B::from_u16(16u16), None);
        assert_eq!(B::from_u32(16u32), None);
        assert_eq!(B::from_u64(16u64), None);
        assert_eq!(B::from_u128(16u128), None);
        assert_eq!(B::from_usize(16usize), None);
        assert_eq!(B::from_i8(16i8), None);
        assert_eq!(B::from_i16(16i16), None);
        assert_eq!(B::from_i32(16i32), None);
        assert_eq!(B::from_i64(16i64), None);
        assert_eq!(B::from_i128(16i128), None);
        assert_eq!(B::from_isize(16isize), None);
        assert_eq!(B::from_f32(16f32), None);
        assert_eq!(B::from_f64(16f64), None);

        assert_eq!(<B as NumCast>::from(4u8), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4u16), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4u32), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4u64), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4u128), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4usize), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4i8), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4i16), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4i32), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4i64), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4i128), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4isize), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4f32), Some(b(4)));
        assert_eq!(<B as NumCast>::from(4f64), Some(b(4)));

        assert_eq!(<B as NumCast>::from(16u8), None);
        assert_eq!(<B as NumCast>::from(16u16), None);
        assert_eq!(<B as NumCast>::from(16u32), None);
        assert_eq!(<B as NumCast>::from(16u64), None);
        assert_eq!(<B as NumCast>::from(16u128), None);
        assert_eq!(<B as NumCast>::from(16usize), None);
        assert_eq!(<B as NumCast>::from(16i8), None);
        assert_eq!(<B as NumCast>::from(16i16), None);
        assert_eq!(<B as NumCast>::from(16i32), None);
        assert_eq!(<B as NumCast>::from(16i64), None);
        assert_eq!(<B as NumCast>::from(16i128), None);
        assert_eq!(<B as NumCast>::from(16isize), None);
        assert_eq!(<B as NumCast>::from(16f32), None);
        assert_eq!(<B as NumCast>::from(16f64), None);

        assert_eq!(b(4).to_u8(), Some(4u8));
        assert_eq!(b(4).to_u16(), Some(4u16));
        assert_eq!(b(4).to_u32(), Some(4u32));
        assert_eq!(b(4).to_u64(), Some(4u64));
        assert_eq!(b(4).to_u128(), Some(4u128));
        assert_eq!(b(4).to_usize(), Some(4usize));
        assert_eq!(b(4).to_i8(), Some(4i8));
        assert_eq!(b(4).to_i16(), Some(4i16));
        assert_eq!(b(4).to_i32(), Some(4i32));
        assert_eq!(b(4).to_i64(), Some(4i64));
        assert_eq!(b(4).to_i128(), Some(4i128));
        assert_eq!(b(4).to_isize(), Some(4isize));
        assert_eq!(b(4).to_f32(), Some(4f32));
        assert_eq!(b(4).to_f64(), Some(4f64));

        assert_eq!(<B as CheckedAdd>::checked_add(&b(4), &b(4)), Some(b(8)));
        assert_eq!(<B as CheckedAdd>::checked_add(&b(4), &b(8)), None);

        assert_eq!(<B as CheckedDiv>::checked_div(&b(8), &b(2)), Some(b(4)));
        assert_eq!(<B as CheckedDiv>::checked_div(&b(4), &b(4)), None);

        assert_eq!(<B as CheckedMul>::checked_mul(&b(2), &b(2)), Some(b(4)));
        assert_eq!(<B as CheckedMul>::checked_mul(&b(2), &b(8)), None);

        assert_eq!(<BNeg as CheckedNeg>::checked_neg(&bneg(2)), Some(bneg(-2)));

        assert_eq!(<BNeg as CheckedNeg>::checked_neg(&bneg(8)), None);

        assert_eq!(<B as CheckedRem>::checked_rem(&b(8), &b(6)), Some(b(2)));
        assert_eq!(<B as CheckedRem>::checked_rem(&b(8), &b(7)), None);

        assert_eq!(<B as CheckedSub>::checked_sub(&b(4), &b(2)), Some(b(2)));
        assert_eq!(<B as CheckedSub>::checked_sub(&b(4), &b(4)), None);

        assert_eq!(<B as CheckedShl>::checked_shl(&b(4), 1u32), Some(b(8)));
        assert_eq!(<B as CheckedShl>::checked_shl(&b(4), 2u32), None);

        assert_eq!(<B as CheckedShr>::checked_shr(&b(4), 1u32), Some(b(2)));
        assert_eq!(<B as CheckedShr>::checked_shr(&b(4), 2u32), None);
    }
}
