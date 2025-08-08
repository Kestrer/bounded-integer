#![no_implicit_prelude]
#![no_std]
#![cfg_attr(feature = "step_trait", feature(step_trait))]
#![cfg(feature = "macro")]
#![deny(clippy::pedantic)]

#[expect(dead_code, non_camel_case_types)]
struct u8 {}
#[expect(dead_code, non_camel_case_types)]
struct u16 {}
#[expect(dead_code, non_camel_case_types)]
struct u32 {}
#[expect(dead_code, non_camel_case_types)]
struct u64 {}
#[expect(dead_code, non_camel_case_types)]
struct u128 {}
#[expect(dead_code, non_camel_case_types)]
struct usize {}
#[expect(dead_code, non_camel_case_types)]
struct i8 {}
#[expect(dead_code, non_camel_case_types)]
struct i16 {}
#[expect(dead_code, non_camel_case_types)]
struct i32 {}
#[expect(dead_code, non_camel_case_types)]
struct i64 {}
#[expect(dead_code, non_camel_case_types)]
struct i128 {}
#[expect(dead_code, non_camel_case_types)]
struct isize {}

::bounded_integer::bounded_integer! {
    #[repr(isize)]
    pub struct StructSigned(-3, 1);
}
::bounded_integer::bounded_integer! {
    #[repr(u16)]
    pub struct StructUnsigned(36, 65535);
}
::bounded_integer::bounded_integer! {
    #[repr(i64)]
    pub enum EnumSigned(-4, 5);
}
::bounded_integer::bounded_integer! {
    #[repr(u8)]
    pub enum EnumUnsigned(253, 255);
}
// generic parameters are not hygienic :(
::bounded_integer::bounded_integer!(pub struct A(0, 0););
::bounded_integer::bounded_integer!(pub struct B(0, 0););
::bounded_integer::bounded_integer!(pub enum C(0, 0););
::bounded_integer::bounded_integer!(
    pub enum T {
        X = 0,
    }
);
