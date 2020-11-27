//! Provides a macro to generate bounded integers, integers which are restricted to a range of
//! values.
//!
//! This crate provides the `bounded_integer` macro to generate bounded integers, as well as
//! [examples](examples) (behind the `example` feature which isn't activated by default).
//!
//! The integers generated from bounded-integer depend only on libcore and so work in `#![no_std]`
//! environments.
//!
//! # Features
//!
//! - `serde`: Implement `Serialize` and `Deserialize` for the bounded integers, making sure all
//! values will never be out of bounds.
//! - `step_trait`: Implement the unstable [`core::iter::Step`] trait which allows the bounded
//! integers to be easily used in ranges. This will require you to use nightly and place
//! `#![feature(step_trait, step_trait_ext)]` in your crate root.
#![cfg_attr(
    all(feature = "examples", feature = "step_trait"),
    feature(step_trait, step_trait_ext)
)]

#[cfg(feature = "serde")]
#[doc(hidden)]
pub use serde_crate as __serde;

#[cfg(feature = "examples")]
pub mod examples;

pub use bounded_integer_macro::bounded_integer;
