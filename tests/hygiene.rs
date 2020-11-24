#![no_implicit_prelude]

::bounded_integer::bounded_integer! {
    #[repr(isize)]
    pub struct StructSigned { -3..2 }
}
::bounded_integer::bounded_integer! {
    #[repr(u16)]
    pub struct StructUnsigned { 36..65535 }
}
::bounded_integer::bounded_integer! {
    #[repr(i64)]
    pub enum EnumSigned { -4..6 }
}
::bounded_integer::bounded_integer! {
    #[repr(u8)]
    pub enum EnumUnsigned { 253..255 }
}
