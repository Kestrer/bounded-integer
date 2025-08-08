#![cfg_attr(feature = "step_trait", feature(step_trait))]
fn main() {
    #![expect(unused)]
    let _ = <bounded_integer::BoundedUsize<5, 4>>::MIN;
    bounded_integer::bounded_integer!(struct X(5, 4););
}
