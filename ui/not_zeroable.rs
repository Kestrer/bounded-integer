#![cfg_attr(feature = "step_trait", feature(step_trait))]

#[repr(transparent)]
struct S(u8);

bounded_integer::unsafe_api! {
    for S,
    unsafe repr: u8,
    min: 1,
    max: 1,
    zeroable,
}

fn main() {}
