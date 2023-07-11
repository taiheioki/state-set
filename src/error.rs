//! A module for providing error types.

use core::fmt::{Display, Formatter, Result};

#[cfg(feature = "std")]
use thiserror::Error;

/// Represents an error when trying to convert a bit vector into a [`StateSet`](crate::StateSet).
#[allow(clippy::module_name_repetitions)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Error))]
pub struct InvalidBitVectorError;

impl Display for InvalidBitVectorError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.write_str("The value has bits set at positions exceeding than the number of states")
    }
}
