mod state;
pub use crate::state::State;

mod state_set;
pub use crate::state_set::{IntoIter, Iter, StateSet};

#[cfg(feature = "derive")]
pub use states_derive::States;
