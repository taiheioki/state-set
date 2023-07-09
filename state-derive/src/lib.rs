use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

mod derive_states;
use derive_states::derive_state_impl;

#[proc_macro_derive(State)]
pub fn derive_state(input: TokenStream) -> TokenStream {
    derive_state_impl(&parse_macro_input!(input as DeriveInput)).into()
}
