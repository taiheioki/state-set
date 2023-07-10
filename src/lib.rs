//! `state-set` is a Rust library for managing sets of states for types that implement the [`State`] trait.
//! It provides a [`StateSet`] data structure which uses a bit vector to efficiently store the presence of states.
//! Each state is represented by a single bit, allowing for operations like union, intersection, and difference to be
//! performed quickly using bitwise operations.
//!
//! The power of `state-set` comes from its extensibility. By implementing the [`State`] trait for a type,
//! you can use it directly with [`StateSet`] and get all the benefits of efficient state set operations.
//! This makes it possible to work with complex types like enums, tuples, or any other user-defined type.
//!
//! Additionally, `state-set` provides a derive macro for the [`State`] trait if the library is built with the `derive` feature.
//! This makes it effortless to leverage the functionality of `state-set` for your own types.
//! Just derive [`State`] for your type, and you're ready to use it in a [`StateSet`].
//!
//! # Examples
//! Here is a basic usage example of `state-set`.
//! ```
//! # use state_set::*;
//! #
//! #[derive(State)]
//! enum Example {
//!     A,
//!     B,
//!     C,
//! }
//!
//! fn main() {
//!     let mut set = StateSet::new();
//!     set.insert(Example::A);
//!     set.insert(Example::B);
//!
//!     assert!(set.contains(Example::A));
//!     assert!(!set.contains(Example::C));
//! }
//! ```
//! More examples and detailed usage instructions can be found in the documentation of [`State`] and [`StateSet`].

mod state;
pub use crate::state::State;

mod state_set;
pub use crate::state_set::{InvalidBitVectorError, Iter, StateSet};

/// A derive macro for automatically implementing the [`State`] trait.
///
/// This macro generates the necessary implementations to use the annotated type as a state within a [`StateSet`].
/// It is part of the `state-set` crate's `derive` feature.
///
/// # Example
///
/// ```
/// # use state_set::*;
/// #
/// #[derive(State)]
/// enum MyEnum {
///     A,
///     B(bool),
///     C { x: bool, y: bool },
/// }
///
/// assert_eq!(MyEnum::NUM_STATES, 7);
/// assert_eq!(MyEnum::from_index(0), Some(MyEnum::A));
/// assert_eq!(MyEnum::from_index(1), Some(MyEnum::B(false)));
/// assert_eq!(MyEnum::from_index(2), Some(MyEnum::B(false)));
/// assert_eq!(MyEnum::from_index(3), Some(MyEnum::C { x: false, y: false }));
/// assert_eq!(MyEnum::from_index(4), Some(MyEnum::C { x: false, y: true }));
/// assert_eq!(MyEnum::from_index(5), Some(MyEnum::C { x: true, y: false }));
/// assert_eq!(MyEnum::from_index(6), Some(MyEnum::C { x: true, y: true }));
/// ```
#[cfg(feature = "derive")]
pub use state_derive::State;

/// A declarative macro for creating a [`StateSet`] from a list of states.
///
/// # Examples
/// ```
/// # use state_set::*;
/// #
/// let set = state_set![(false, false), (true, true)];
/// assert_eq!(set.len(), 2);
/// assert!(set.contains((false, false)));
/// assert!(!set.contains((false, true)));
/// assert!(!set.contains((true, false)));
/// assert!(set.contains((true, true)));
/// ```
#[macro_export]
macro_rules! state_set {
    ($($state:expr),* $(,)?) => {{
        #[allow(unused_mut)]
        let mut set = $crate::StateSet::new();
        $(set.insert($state);)*
        set
    }};
}
