fn main() {
    let ac = autocfg::new();
    ac.emit_has_type("i128");
    ac.emit_has_type("u128");
}
