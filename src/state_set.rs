use std::{
    marker::PhantomData,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign},
};

use crate::StateIndexable;

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

    #[inline]
    pub unsafe fn from_u64_unchecked(data: u64) -> Self {
        Self {
            data,
            phantom: PhantomData,
        }
    }

    /// Returns the number of states in the set.
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

impl<T: StateIndexable> StateSet<T> {
    /// Insert a state into the set.
    #[inline]
    pub fn insert(&mut self, state: T) {
        let _ = T::CHECK_STATES_AT_MOST_64;
        self.data |= 1 << state.into_index();
    }

    /// Remove a state from the set.
    #[inline]
    pub fn remove(&mut self, state: T) {
        let _ = T::CHECK_STATES_AT_MOST_64;
        self.data &= !(1 << state.into_index());
    }

    /// Returns `true` if the set contains the given state.
    #[inline]
    pub fn contains(&self, state: T) -> bool {
        let _ = T::CHECK_STATES_AT_MOST_64;
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

impl<T: StateIndexable> TryFrom<u64> for StateSet<T> {
    type Error = ();

    /// Tries to convert a [`u64`] into a [`StateSet`].
    #[inline]
    fn try_from(value: u64) -> Result<Self, Self::Error> {
        let _ = T::CHECK_STATES_AT_MOST_64;
        if value & !((1 << T::STATES) - 1) == 0 {
            Ok(unsafe { Self::from_u64_unchecked(value) })
        } else {
            Err(())
        }
    }
}

impl<T: StateIndexable> Not for StateSet<T> {
    type Output = Self;

    /// Returns the complement of `self`.
    #[inline]
    fn not(self) -> Self::Output {
        let _ = T::CHECK_STATES_AT_MOST_64;
        unsafe { Self::from_u64_unchecked(!self.data & (1 << T::STATES) - 1) }
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

impl<T: StateIndexable> Sub for StateSet<T> {
    type Output = Self;

    /// Returns the set difference of `self` and `rhs`.
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        let _ = T::CHECK_STATES_AT_MOST_64;
        self & !rhs
    }
}

impl<T: StateIndexable> SubAssign for StateSet<T> {
    /// Replaces `self` with the set difference of `self` and `rhs`.
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        let _ = T::CHECK_STATES_AT_MOST_64;
        *self &= !rhs;
    }
}

/// A macro for creating a [`StateSet`] from a list of states.
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

    #[test]
    fn test() {
        let mut x = StateSet::<[bool; 7]>::new();
        x.insert(Default::default());
    }
}
