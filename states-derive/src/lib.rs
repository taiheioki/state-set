use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

mod derive_states;
use derive_states::derive_states_impl;

#[proc_macro_derive(States)]
pub fn derive_states(input: TokenStream) -> TokenStream {
    derive_states_impl(&parse_macro_input!(input as DeriveInput)).into()
}
