//! Provides a macro to generate bounded integers, integers which are restricted to a range of
//! values.
//!
//! This crate provides the `bounded_integer` macro to generate bounded integers, as well as
//! examples (behind the `example` feature which isn't activated by default).
//!
//! The integers generated from bounded-integer depend only on libcore and so work in `#![no_std]`
//! environments.

#[cfg(feature = "examples")]
pub mod examples;

pub use bounded_integer_macro::bounded_integer;
