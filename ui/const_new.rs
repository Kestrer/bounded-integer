#![cfg_attr(feature = "step_trait", feature(step_trait))]
fn main() {
    let _ = <bounded_integer::BoundedUsize<0, 5>>::const_new::<6>();
}
