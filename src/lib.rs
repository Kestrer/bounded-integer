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
//! - `macro`: Enable the [`bounded_integer!`] macro.
//! - `types`: Enable the bounded integer types that use const generics.
//! - `serde`: Implement `Serialize` and `Deserialize` for the bounded integers, making sure all
//! values will never be out of bounds.
//! - `step_trait`: Implement the [`core::iter::Step`] trait which allows the bounded
//! integers to be easily used in ranges. This will require you to use nightly and place
//! `#![feature(step_trait)]` in your crate root.
#![cfg_attr(feature = "step_trait", feature(step_trait))]
#![cfg_attr(doc_cfg, feature(doc_cfg))]
#![no_std]

#[cfg(feature = "serde")]
extern crate serde_crate as serde;

#[cfg(feature = "types")]
mod types;
#[cfg(feature = "types")]
pub use types::*;

#[doc(hidden)]
pub mod __private {
    #[cfg(feature = "serde")]
    pub use serde_crate as serde;

    pub const HAS_ACCESS_TO_CRATE: () = ();
}

#[cfg(feature = "examples")]
pub mod examples;

#[cfg(feature = "macro")]
macro_rules! import_macro {
    ($name:ident) => {
        /// Generate a bounded integer type.
        ///
        /// It takes in single struct or enum, with the content being a bounded range expression, whose
        /// upper bound can be inclusive (`x..=y`) or exclusive (`x..y`). The attributes and visibility
        /// (e.g. `pub`) of the type are forwarded directly to the output type.
        ///
        /// # Examples
        ///
        /// With a struct:
        /// ```
        #[cfg_attr(feature = "step_trait", doc = "# #![feature(step_trait)]")]
        /// # mod force_item_scope {
        /// # use bounded_integer::bounded_integer;
        /// bounded_integer! {
        ///     pub struct S { -3..2 }
        /// }
        /// # }
        /// ```
        /// The generated item should look like this (i8 is chosen as it is the smallest repr):
        /// ```
        /// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        /// #[repr(transparent)]
        /// pub struct S(i8);
        /// ```
        /// And the methods will ensure that `-3 <= S.0 < 2`.
        ///
        /// With an enum:
        /// ```
        #[cfg_attr(feature = "step_trait", doc = "# #![feature(step_trait)]")]
        /// # mod force_item_scope {
        /// # use bounded_integer::bounded_integer;
        /// bounded_integer! {
        ///     pub enum S { 5..=7 }
        /// }
        /// # }
        /// ```
        /// The generated item should look like this (u8 is chosen as it is the smallest repr):
        /// ```
        /// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        /// #[repr(u8)]
        /// pub enum S {
        ///     P5 = 5, P6, P7
        /// }
        /// ```
        ///
        /// # Custom repr
        ///
        /// The item can have a `repr` attribute to specify how it will be represented in memory, which can
        /// be a `u*` or `i*` type. In this example we override the `repr` to be a `u16`, when it would
        /// have normally been a `u8`.
        ///
        /// ```
        #[cfg_attr(feature = "step_trait", doc = "# #![feature(step_trait)]")]
        /// # mod force_item_scope {
        /// # use bounded_integer::bounded_integer;
        /// bounded_integer! {
        ///     #[repr(u16)]
        ///     pub struct S { 2..5 }
        /// }
        /// # }
        /// ```
        /// The generated item should look like this:
        /// ```
        /// #[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        /// #[repr(transparent)]
        /// pub struct S(u16);
        /// ```
        ///
        /// # Custom path to bounded integer
        ///
        /// `bounded-integer` will assume that it is located at `::bounded_integer` by default. You can
        /// override this by adding a `bounded_integer` attribute to your item. For example if
        /// `bounded_integer` is instead located at `path::to::bounded_integer`:
        ///
        /// ```ignore
        /// # mod force_item_scope {
        /// # use bounded_integer::bounded_integer;
        /// bounded_integer! {
        ///     #[repr(i8)]
        ///     #[bounded_integer = path::to::bounded_integer]
        ///     pub struct S { 5..7 }
        /// }
        /// # }
        /// ```
        ///
        /// # Limitations
        ///
        /// - Both bounds of ranges must be closed and a simple const expression involving only literals and
        /// the following operators:
        ///     - Negation (`-x`)
        ///     - Addition (`x+y`), subtraction (`x-y`), multiplication (`x*y`), division (`x/y`) and
        ///     remainder (`x%y`).
        ///     - Bitwise not (`!x`), XOR (`x^y`), AND (`x&y`) and OR (`x|y`).
        #[cfg_attr(doc_cfg, doc(cfg(feature = "macro")))]
        pub use bounded_integer_macro::$name as bounded_integer;
    };
}

#[cfg(all(feature = "macro", not(feature = "serde"), not(feature = "step_trait")))]
import_macro!(not_serde_not_step_trait);
#[cfg(all(feature = "macro", not(feature = "serde"), feature = "step_trait"))]
import_macro!(not_serde_step_trait);
#[cfg(all(feature = "macro", feature = "serde", not(feature = "step_trait")))]
import_macro!(serde_not_step_trait);
#[cfg(all(feature = "macro", feature = "serde", feature = "step_trait"))]
import_macro!(serde_step_trait);
