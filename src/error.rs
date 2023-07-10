//! A module for providing error types.

use thiserror::Error;

/// Represents an error when trying to convert a bit vector into a [`StateSet`](crate::StateSet).
#[derive(Clone, Copy, Debug, Eq, Error, PartialEq)]
#[error("The value has bits set at positions exceeding than the number of states")]
pub struct InvalidBitVectorError;
