# Bounded Integer

[![Crate version][crate-badge]][crate]
[![docs.rs][docsrs-badge]][docsrs]
[![checks][checks-badge]][checks]

[crate]: https://crates.io/crates/bounded-integer
[crate-badge]: https://img.shields.io/crates/v/bounded-integer.svg
[docsrs]: https://docs.rs/bounded-integer
[docsrs-badge]: https://img.shields.io/badge/docs.rs-bounded--integer-informational
[checks]: https://github.com/Kestrer/bounded-integer/actions?query=workflow%3ACI+branch%3Amaster
[checks-badge]: https://github.com/Kestrer/bounded-integer/workflows/CI/badge.svg

This crate provides two types of bounded integer for use in Rust.

## Macro-generated bounded integers

The [`bounded_integer!`] macro allows you to define your own bounded integer type, given a
specific range it inhabits. For example:

```rust
bounded_integer! {
    struct MyInteger { 0..8 }
}
let num = MyInteger::new(5).unwrap();
assert_eq!(num, 5);
```

This macro supports both `struct`s and `enum`s. See the [`examples`] module for the
documentation of generated types.

## Const generics-based bounded integers

You can also create ad-hoc bounded integers via types in this library that use const generics,
for example:

```rust
let num = <BoundedU8<0, 7>>::new(5).unwrap();
assert_eq!(num, 5);
```

These integers are shorter to use as they don't require a type declaration or explicit name,
and they interoperate better with other integers that have different ranges. However due to the
limits of const generics, they do not implement some traits like `Default`.

## `no_std`

All the integers in this crate depend only on libcore and so work in `#![no_std]` environments.

## Crate Features

By default, no crate features are enabled.
- `std`: Implement traits from `std`, such as [`Error`] on [`ParseError`].
- `macro`: Enable the [`bounded_integer!`] macro.
- `types`: Enable the bounded integer types that use const generics.
- `arbitrary`: Implement [`Arbitrary`] for the bounded integers. This is useful when using
bounded integers as fuzzing inputs.
- `bytemuck`: Implement [`Contiguous`] for all bounded integers, and [`Zeroable`] for
macro-generated bounded integers that support it.
- `serde`: Implement [`Serialize`] and [`Deserialize`] for the bounded integers, making sure all
values will never be out of bounds.
- `step_trait`: Implement the [`Step`] trait which allows the bounded integers to be easily used
in ranges. This will require you to use nightly and place `#![feature(step_trait)]` in your
crate root if you use the macro.

[`bounded_integer!`]: https://docs.rs/bounded-integer/*/bounded_integer/macro.bounded_integer.html
[`examples`]: https://docs.rs/bounded-integer/*/bounded_integer/examples/
[`Arbitrary`]: https://docs.rs/arbitrary/1/arbitrary/trait.Arbitrary.html
[`Contiguous`]: https://docs.rs/bytemuck/1/bytemuck/trait.Contiguous.html
[`Zeroable`]: https://docs.rs/bytemuck/1/bytemuck/trait.Zeroable.html
[`Serialize`]: https://docs.rs/serde/1/serde/trait.Serialize.html
[`Deserialize`]: https://docs.rs/serde/1/serde/trait.Deserialize.html
[`Step`]: https://doc.rust-lang.org/nightly/core/iter/trait.Step.html
[`Error`]: https://doc.rust-lang.org/stable/std/error/trait.Error.html
[`ParseError`]: https://docs.rs/bounded-integer/*/bounded_integer/struct.ParseError.html

## License

Copyright © 2016, Curtis McEnroe <curtis@cmcenroe.me>

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
