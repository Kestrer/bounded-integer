fn main() {
    let _ = <bounded_integer::BoundedUsize<5, 4>>::MIN;
    bounded_integer::bounded_integer!(#[expect(unused)] struct X(5, 4););
}
