#![warn(
    missing_debug_implementations,
    missing_docs,
    rust_2018_idioms,
    unused,
    unreachable_pub
)]

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

mod state;
pub use crate::state::State;

mod state_set;
pub use crate::state_set::StateSet;

pub mod error;
pub mod iter;

#[cfg(feature = "derive")]
#[doc(inline)]
pub use state_derive::State;

/// A declarative macro for creating a [`StateSet`] from a list of states.
///
/// # Examples
/// ```
/// # use state_set::*;
/// let set = state_set![None, Some(false)];
///
/// assert_eq!(set.len(), 2);
/// assert!(set.contains(None));
/// assert!(set.contains(Some(false)));
/// assert!(!set.contains(Some(true)));
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
