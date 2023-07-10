use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

mod derive_states;
use derive_states::derive_state_impl;

/// A derive macro for automatically implementing the `State` trait.
///
/// This macro generates the necessary implementations to use the annotated type as a state within a `StateSet`.
/// It is part of the `state-set` crate's `derive` feature.
///
/// # Example
///
/// ```
/// use state_set::*;
///
/// #[derive(Debug, Eq, PartialEq, State)]
/// enum MyEnum {
///     A,
///     B(bool),
///     C { x: bool, y: bool },
/// }
///
/// assert_eq!(MyEnum::NUM_STATES, 7);
/// assert_eq!(MyEnum::from_index(0), Some(MyEnum::A));
/// assert_eq!(MyEnum::from_index(1), Some(MyEnum::B(false)));
/// assert_eq!(MyEnum::from_index(2), Some(MyEnum::B(true)));
/// assert_eq!(MyEnum::from_index(3), Some(MyEnum::C { x: false, y: false }));
/// assert_eq!(MyEnum::from_index(4), Some(MyEnum::C { x: false, y: true }));
/// assert_eq!(MyEnum::from_index(5), Some(MyEnum::C { x: true, y: false }));
/// assert_eq!(MyEnum::from_index(6), Some(MyEnum::C { x: true, y: true }));
/// ```
#[proc_macro_derive(State)]
pub fn derive_state(input: TokenStream) -> TokenStream {
    derive_state_impl(&parse_macro_input!(input as DeriveInput)).into()
}
