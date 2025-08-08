#[repr(transparent)]
struct A(u8);

bounded_integer::unsafe_api! {
    for A,
    unsafe repr: u8,
    min: 1,
    max: 1,
    zero,
}

#[repr(transparent)]
struct B(u8);

bounded_integer::unsafe_api! {
    for B,
    unsafe repr: u8,
    min: 0,
    max: 0,
    one,
}

fn main() {}
