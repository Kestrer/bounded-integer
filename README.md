<!-- cargo-rdme start -->

This crate provides two types of bounded integer.

# Macro-generated bounded integers

The [`bounded_integer!`] macro allows you to define your own bounded integer type, given a
specific (inclusive) range it inhabits. For example:

```rust
bounded_integer! {
    struct MyInteger(0, 7);
}
let num = MyInteger::new(5).unwrap();
assert_eq!(num, 5);
```

This macro supports both `struct`s and `enum`s. See the [`examples`] module for the
documentation of generated types.

# Const generics-based bounded integers

You can also create ad-hoc bounded integers via types in this library that use const generics,
for example:

```rust
let num = <BoundedU8<0, 7>>::new(5).unwrap();
assert_eq!(num, 5);
```

These integers are shorter to use as they don't require a type declaration or explicit name.
However due to the limits of const generics, they may not implement some traits –
namely [`Default`], bytemuck’s [`Zeroable`] and zerocopy’s [`FromZeros`].
Also, unlike their macro counterparts they will not be subject to niche layout optimizations.

# `no_std`

All the integers in this crate depend only on libcore and so work in `#![no_std]` environments.

# Crate Features

By default, no crate features are enabled.
- `std`: Interopate with `std` — implies `alloc`. Enables the following things:
    - An implementation of [`Error`] for [`ParseError`].
- `alloc`: Interopate with `alloc`. Has no effect currently.
- `macro`: Enable the [`bounded_integer!`] macro.
- `arbitrary1`: Implement [`Arbitrary`] for the bounded integers. This is useful when using
  bounded integers as fuzzing inputs.
- `bytemuck1`: Implement [`Contiguous`] and [`NoUninit`] for all bounded integers,
  and [`Zeroable`] for macro-generated bounded integers that support it.
- `num-traits02`: Implement [`Bounded`], [`AsPrimitive`], [`FromPrimitive`], [`NumCast`],
  [`ToPrimitive`], [`CheckedAdd`], [`CheckedDiv`], [`CheckedMul`], [`CheckedNeg`],
  [`CheckedRem`], [`CheckedSub`], [`MulAdd`], [`SaturatingAdd`], [`SaturatingMul`] and
  [`SaturatingSub`] for all bounded integers.
- `serde1`: Implement [`Serialize`] and [`Deserialize`] for the bounded integers, making sure all
  values will never be out of bounds.
- `zerocopy`: Implement [`IntoBytes`] and [`Immutable`] for all bounded integers,
  [`Unaligned`] for ones backed by `u8` or `i8`,
  and [`FromZeros`] for suitable macro-generated ones.
- `step_trait`: Implement the [`Step`] trait which allows the bounded integers to be easily used
  in ranges. This will require you to use nightly and place `#![feature(step_trait)]` in your
  crate root if you use the macro.

[`bounded_integer!`]: https://docs.rs/bounded-integer/*/bounded_integer/macro.bounded_integer.html
[`examples`]: https://docs.rs/bounded-integer/*/bounded_integer/examples/
[`Arbitrary`]: https://docs.rs/arbitrary/1/arbitrary/trait.Arbitrary.html
[`Contiguous`]: https://docs.rs/bytemuck/1/bytemuck/trait.Contiguous.html
[`NoUninit`]: https://docs.rs/bytemuck/1/bytemuck/trait.NoUninit.html
[`Zeroable`]: https://docs.rs/bytemuck/1/bytemuck/trait.Zeroable.html
[`Bounded`]: https://docs.rs/num-traits/0.2/num_traits/bounds/trait.Bounded.html
[`AsPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.AsPrimitive.html
[`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
[`NumCast`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.NumCast.html
[`ToPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.ToPrimitive.html
[`CheckedAdd`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedAdd.html
[`CheckedDiv`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedDiv.html
[`CheckedMul`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedMul.html
[`CheckedNeg`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedNeg.html
[`CheckedRem`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedRem.html
[`CheckedSub`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedSub.html
[`MulAdd`]: https://docs.rs/num-traits/0.2/num_traits/ops/mul_add/trait.MulAdd.html
[`SaturatingAdd`]: https://docs.rs/num-traits/0.2/num_traits/ops/saturating/trait.SaturatingAdd.html
[`SaturatingMul`]: https://docs.rs/num-traits/0.2/num_traits/ops/saturating/trait.SaturatingMul.html
[`SaturatingSub`]: https://docs.rs/num-traits/0.2/num_traits/ops/saturating/trait.SaturatingSub.html
[`Serialize`]: https://docs.rs/serde/1/serde/trait.Serialize.html
[`Deserialize`]: https://docs.rs/serde/1/serde/trait.Deserialize.html
[`IntoBytes`]: https://docs.rs/zerocopy/0.8/zerocopy/trait.IntoBytes.html
[`FromZeros`]: https://docs.rs/zerocopy/0.8/zerocopy/trait.FromZeros.html
[`Immutable`]: https://docs.rs/zerocopy/0.8/zerocopy/trait.Immutable.html
[`Unaligned`]: https://docs.rs/zerocopy/0.8/zerocopy/trait.Unaligned.html
[`Step`]: https://doc.rust-lang.org/nightly/core/iter/trait.Step.html
[`Error`]: https://doc.rust-lang.org/stable/std/error/trait.Error.html
[`ParseError`]: https://docs.rs/bounded-integer/*/bounded_integer/struct.ParseError.html

<!-- cargo-rdme end -->
