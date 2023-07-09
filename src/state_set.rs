use std::{
    marker::PhantomData,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign},
};

use crate::States;

/// A set of states represented by a bit vector.
///
/// This struct manages a set of states for a type `T` that implements [`StateIndexable`].
/// It uses a [`u64`] as a bit vector to store the presence of states, where each bit represents a state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct StateSet<T> {
    data: u64,
    phantom: PhantomData<T>,
}

impl<T> StateSet<T> {
    /// Creates a new, empty [`StateSet`].
    #[inline]
    pub fn new() -> Self {
        unsafe { Self::from_u64_unchecked(0) }
    }

    /// Creates a new instance of [`StateSet`] from [`u64`] without checking the validity of the data.
    ///
    /// # Safety
    /// The caller must ensure that `data` represent a valid state. It's up to the caller to ensure this. Misuse can lead to undefined behavior.
    #[inline]
    pub unsafe fn from_u64_unchecked(data: u64) -> Self {
        Self {
            data,
            phantom: PhantomData,
        }
    }

    /// Returns the number of states in the set.
    ///
    /// This is equivalent to the count of `1`s in the bit representation.
    #[inline]
    pub fn len(&self) -> u32 {
        self.data.count_ones()
    }

    /// Returns `true` if the set contains no states.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data == 0
    }

    /// Removes all states from the set.
    #[inline]
    pub fn clear(&mut self) {
        self.data = 0;
    }
}

impl<T: States> StateSet<T> {
    /// Insert a state into the set.
    #[inline]
    pub fn insert(&mut self, state: T) {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        self.data |= 1 << state.into_index();
    }

    /// Remove a state from the set.
    #[inline]
    pub fn remove(&mut self, state: T) {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        self.data &= !(1 << state.into_index());
    }

    /// Returns `true` if the set contains the given state.
    #[inline]
    pub fn contains(&self, state: T) -> bool {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        self.data & (1 << state.into_index()) != 0
    }
}

impl<T> From<StateSet<T>> for u64 {
    /// Converts a [`StateSet`] into a [`u64`].
    #[inline]
    fn from(value: StateSet<T>) -> Self {
        value.data
    }
}

impl<T: States> TryFrom<u64> for StateSet<T> {
    type Error = ();

    /// Tries to convert a [`u64`] into a [`StateSet`].
    ///
    /// This method attempts to create a `StateSet` from a 64-bit unsigned integer. If the argument
    /// represents a valid state (that is, the bits in positions greater than `T::NUM_STATES` are not set), the
    /// method will return a [`StateSet`] wrapped in a [`Result::Ok`].
    ///
    /// If the `value` does not represent a valid state (bits in positions greater than `T::NUM_STATES` are set),
    /// the method will return [`Result::Err(())`].
    ///
    /// # Examples
    ///
    /// ```
    /// use state_set::*;
    ///
    /// let s = StateSet::<bool>::try_from(0b10);
    /// assert_eq!(s, Ok(state_set![true]));
    ///
    /// let s = StateSet::<bool>::try_from(0b11);
    /// assert_eq!(s, Ok(state_set![false, true]));
    ///
    /// let s = StateSet::<bool>::try_from(0b100);
    /// assert!(s.is_err());
    /// ```
    #[inline]
    fn try_from(value: u64) -> Result<Self, Self::Error> {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        if value & !((1 << T::NUM_STATES) - 1) == 0 {
            Ok(unsafe { Self::from_u64_unchecked(value) })
        } else {
            Err(())
        }
    }
}

impl<T: States> Not for StateSet<T> {
    type Output = Self;

    /// Returns the complement of `self`.
    #[inline]
    fn not(self) -> Self::Output {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        unsafe { Self::from_u64_unchecked(!self.data & ((1 << T::NUM_STATES) - 1)) }
    }
}

impl<T> BitAnd for StateSet<T> {
    type Output = Self;

    /// Returns the intersection of `self` and `rhs`.
    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_u64_unchecked(self.data & rhs.data) }
    }
}

impl<T> BitAndAssign for StateSet<T> {
    /// Replaces `self` with the intersection of `self` and `rhs`.
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.data &= rhs.data;
    }
}

impl<T> BitOr for StateSet<T> {
    type Output = Self;

    /// Returns the union of `self` and `rhs`.
    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_u64_unchecked(self.data | rhs.data) }
    }
}

impl<T> BitOrAssign for StateSet<T> {
    /// Replaces `self` with the union of `self` and `rhs`.
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.data |= rhs.data;
    }
}

impl<T> BitXor for StateSet<T> {
    type Output = Self;

    /// Returns the symmetric difference of `self` and `rhs`.
    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_u64_unchecked(self.data ^ rhs.data) }
    }
}

impl<T> BitXorAssign for StateSet<T> {
    /// Replaces `self` with the symmetric difference of `self` and `rhs`.
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.data ^= rhs.data;
    }
}

impl<T: States> Sub for StateSet<T> {
    type Output = Self;

    /// Returns the set difference of `self` and `rhs`.
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        self & !rhs
    }
}

impl<T: States> SubAssign for StateSet<T> {
    /// Replaces `self` with the set difference of `self` and `rhs`.
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        *self &= !rhs;
    }
}

/// A macro for creating a [`StateSet`] from a list of states.
///
/// # Examples
/// ```
/// use state_set::*;
///
/// let set = state_set![false];
/// assert_eq!(set.len(), 1);
/// assert!(set.contains(false));
/// assert!(!set.contains(true));
/// ```
#[macro_export]
macro_rules! state_set {
    ($($state:expr),* $(,)?) => {{
        #[allow(unused_mut)]
        let mut set = StateSet::new();
        $(set.insert($state);)*
        set
    }};
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn try_from_u64() {
        let try_from = StateSet::<bool>::try_from;
        assert_eq!(try_from(0b0000), Ok(state_set![]));
        assert_eq!(try_from(0b0001), Ok(state_set![false]));
        assert_eq!(try_from(0b0010), Ok(state_set![true]));
        assert_eq!(try_from(0b0011), Ok(state_set![false, true]));
        assert!(try_from(0b0100).is_err());
    }

    #[test]
    fn not() {
        let set = state_set![false];
        assert_eq!(!set, state_set![true]);
    }

    #[test]
    fn bit_and() {
        let set1 = state_set![(false, false), (false, true)];
        let set2 = state_set![(false, false), (true, false)];
        assert_eq!(set1 & set2, state_set![(false, false)]);
    }

    #[test]
    fn bit_and_assign() {
        let mut set = state_set![(false, false), (false, true)];
        let rhs = state_set![(false, false), (true, false)];
        set &= rhs;
        assert_eq!(set, state_set![(false, false)]);
    }

    #[test]
    fn bit_or() {
        let set1 = state_set![(false, false), (false, true)];
        let set2 = state_set![(false, false), (true, false)];
        assert_eq!(
            set1 | set2,
            state_set![(false, false), (false, true), (true, false)]
        );
    }

    #[test]
    fn bit_or_assign() {
        let mut set = state_set![(false, false), (false, true)];
        let rhs = state_set![(false, false), (true, false)];
        set |= rhs;
        assert_eq!(
            set,
            state_set![(false, false), (false, true), (true, false)]
        );
    }

    #[test]
    fn bit_xor() {
        let set1 = state_set![(false, false), (false, true)];
        let set2 = state_set![(false, false), (true, false)];
        assert_eq!(set1 ^ set2, state_set![(false, true), (true, false)]);
    }

    #[test]
    fn bit_xor_assign() {
        let mut set = state_set![(false, false), (false, true)];
        let rhs = state_set![(false, false), (true, false)];
        set ^= rhs;
        assert_eq!(set, state_set![(false, true), (true, false)]);
    }

    #[test]
    fn sub() {
        let set1 = state_set![(false, false), (false, true)];
        let set2 = state_set![(false, false), (true, false)];
        assert_eq!(set1 - set2, state_set![(false, true)]);
    }

    #[test]
    fn sub_assign() {
        let mut set = state_set![(false, false), (false, true)];
        let rhs = state_set![(false, false), (true, false)];
        set -= rhs;
        assert_eq!(set, state_set![(false, true)]);
    }
}