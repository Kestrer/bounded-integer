use bounded_integer::bounded_integer;

bounded_integer! {
    #[repr(u8)]
    #[repr(u8)]
    struct DoubleRepr(0, 0);
}

bounded_integer! {
    enum EnumUnknownMin((0), 0);
}

bounded_integer! {
    enum EnumUnknownMax(0, (0));
}

bounded_integer! {
    enum EnumTooBig(0, 100_000);
}

bounded_integer! {
    enum EnumTooHigh {
        A = 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
        B,
    }
}

bounded_integer! {
    enum EnumUnparseable {
        A = "",
    }
}

bounded_integer! {
    enum EnumTooLarge {
        A = 0x1_0000_0000_0000_0000_0000_0000_0000_0000,
    }
}

bounded_integer! {
    enum EnumNotContiguous {
        A,
        B = 2,
    }
}

bounded_integer! {
    struct RangeTooLargeStruct(-0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF, 0);
}

bounded_integer! {
    enum RangeTooLargeEnum {
        A = -0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
    }
}

bounded_integer! {
    struct CouldNotInferRepr((0), 0);
}

bounded_integer! {
    #[derive(Default)]
    #[cfg_attr(all(), another_disallowed)]
    pub struct DisallowedAttr(1_u8, (1));
}

bounded_integer! {
    #[repr(u8)]
    pub struct ReprTooSmall(256, 257);
}

bounded_integer! {
    #[repr(u8)]
    pub struct ReprWrong(0, 1_u16);
}

fn main() {}
