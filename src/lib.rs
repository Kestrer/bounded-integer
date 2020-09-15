//! Provides a macro to generate bounded integers, integers which are restricted to a range of
//! values.
//!
//! This crate provides the `bounded_integer` macro to generate bounded integers, as well as
//! examples (behind the `example` feature which isn't activated by default).
//!
//! The integers generated from bounded-integer depend only on libcore and so work in `#![no_std]`
//! environments.
//!
//! # Serde
//!
//! If you enable the `serde` feature of this crate then all bounded integers will implement
//! `Serialize` and `Deserialize`, making sure that the internal invariants are never violated.

#[cfg(feature = "serde")]
#[doc(hidden)]
pub use serde_crate as serde;

#[cfg(feature = "examples")]
pub mod examples;

pub use bounded_integer_macro::bounded_integer;
