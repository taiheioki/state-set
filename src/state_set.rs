use std::{
    hash::{Hash, Hasher},
    iter::FusedIterator,
    marker::PhantomData,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign},
};

#[cfg(feature = "serde")]
use serde::{
    de::{SeqAccess, Visitor},
    ser::SerializeSeq,
    Deserialize, Deserializer, Serialize, Serializer,
};
use thiserror::Error;

use crate::State;

/// A set of states represented by a bit vector.
///
/// This struct manages a set of states for a type `T` that implements [`State`].
/// It uses a [`u64`] as a bit vector to store the presence of states, where each bit represents a state.
#[derive(Copy, Debug)]
pub struct StateSet<T> {
    bits: u64,
    phantom: PhantomData<T>,
}

impl<T> StateSet<T> {
    /// Creates a new, empty [`StateSet`].
    #[inline]
    pub const fn new() -> Self {
        unsafe { Self::from_u64_unchecked(0) }
    }

    /// Creates a new instance of [`StateSet`] from [`u64`] without checking the validity of the bits.
    ///
    /// # Safety
    /// The caller must ensure that `bits` represent a valid state (that is, the bits in positions greater than
    /// [`T::NUM_STATES`](State::NUM_STATES) are not set).
    #[inline]
    pub const unsafe fn from_u64_unchecked(bits: u64) -> Self {
        Self {
            bits,
            phantom: PhantomData,
        }
    }

    /// Returns the number of states in the set.
    ///
    /// This is equivalent to the count of `1`s in the bit representation.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let set = state_set![(false, false), (true, true)];
    /// assert_eq!(set.len(), 2);
    /// ```
    #[inline]
    pub const fn len(&self) -> u32 {
        self.bits.count_ones()
    }

    /// Returns `true` if the set contains no states.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    ///
    /// let set = StateSet::<bool>::new();
    /// assert!(set.is_empty());
    ///
    /// let set = state_set![(false, false), (true, true)];
    /// assert!(!set.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Removes all states from the set.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let mut set = state_set![false, true];
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.bits = 0;
    }

    /// Returns an iterator over the states in the set.
    #[inline]
    pub const fn iter(&self) -> Iter<T> {
        Iter(unsafe { Self::from_u64_unchecked(self.bits) })
    }
}

impl<T: State> StateSet<T> {
    /// Returns `true` if the set contains all the states.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let set = state_set![false, true];
    /// assert!(set.is_all());
    /// ```
    #[inline]
    pub const fn is_all(&self) -> bool {
        self.bits == u64::MAX >> (64 - T::NUM_STATES)
    }

    /// Insert a state into the set.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let mut set = StateSet::new();
    /// set.insert(false);
    /// assert!(set.contains(false));
    /// ```
    #[inline]
    pub fn insert(&mut self, state: T) {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        self.bits |= 1 << state.into_index();
    }

    /// Remove a state from the set.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let mut set = state_set![false, true];
    /// set.remove(true);
    /// assert!(!set.contains(true));
    /// ```
    #[inline]
    pub fn remove(&mut self, state: T) {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        self.bits ^= 1 << state.into_index();
    }

    /// Returns `true` if the set contains the given state.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let set = state_set![false];
    /// assert!(set.contains(false));
    /// assert!(!set.contains(true));
    /// ```
    #[inline]
    pub fn contains(&self, state: T) -> bool {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        self.bits & (1 << state.into_index()) != 0
    }
}

impl<T> Clone for StateSet<T> {
    #[inline]
    fn clone(&self) -> Self {
        unsafe { Self::from_u64_unchecked(self.bits) }
    }
}

impl<T> Default for StateSet<T> {
    /// Creates a new, empty [`StateSet`].
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Hash for StateSet<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bits.hash(state);
    }
}

impl<T> PartialEq for StateSet<T> {
    /// Returns `true` if the two sets have the same states.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let set1 = state_set![false, true];
    /// let set2 = state_set![true, false];
    /// assert_eq!(set1, set2);
    /// ```
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.bits == other.bits
    }
}

impl<T> Eq for StateSet<T> {}

impl<T> From<StateSet<T>> for u64 {
    /// Converts a [`StateSet`] into a [`u64`].
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let set = state_set![false, true];
    /// let data: u64 = set.into();
    /// assert_eq!(data, 0b11);
    /// ```
    #[inline]
    fn from(value: StateSet<T>) -> Self {
        value.bits
    }
}

/// Represents an error when trying to convert a `u64` into a [`StateSet`].
///
/// This error is used in the implementation of [`TryFrom<u64>`] for [`StateSet`].
#[derive(Clone, Copy, Debug, Eq, Error, PartialEq)]
#[error("The value has bits set at positions exceeding than the number of states")]
pub struct InvalidBitVectorError;

impl<T: State> TryFrom<u64> for StateSet<T> {
    type Error = InvalidBitVectorError;

    /// Tries to convert a [`u64`] into a [`StateSet`].
    ///
    /// This method attempts to create a [`StateSet`] from a 64-bit unsigned integer. If the argument
    /// represents a valid state (that is, the bits in positions greater than [`T::NUM_STATES`](State::NUM_STATES) are not set), the
    /// method will return a [`StateSet`] wrapped in a [`Result::Ok`]. Otherwise, the method will return a [`Result::Err`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use state_set::*;
    /// #
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
        if value & !(u64::MAX >> (64 - T::NUM_STATES)) == 0 {
            Ok(unsafe { Self::from_u64_unchecked(value) })
        } else {
            Err(InvalidBitVectorError)
        }
    }
}

impl<T: State> Not for StateSet<T> {
    type Output = Self;

    /// Returns the complement of `self`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let set = state_set![false];
    /// assert_eq!(!set, state_set![true]);
    /// ```
    #[inline]
    fn not(self) -> Self::Output {
        unsafe { Self::from_u64_unchecked(!self.bits & (u64::MAX >> (64 - T::NUM_STATES))) }
    }
}

impl<T> BitAnd for StateSet<T> {
    type Output = Self;

    /// Returns the intersection of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let lhs = state_set![(false, false), (false, true)];
    /// let rhs = state_set![(false, true), (true, false)];
    /// assert_eq!(lhs & rhs, state_set![(false, true)]);
    /// ```
    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_u64_unchecked(self.bits & rhs.bits) }
    }
}

impl<T> BitAndAssign for StateSet<T> {
    /// Replaces `self` with the intersection of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let mut set = state_set![(false, false), (false, true)];
    /// set &= state_set![(false, true), (true, false)];
    /// assert_eq!(set, state_set![(false, true)]);
    /// ```
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.bits &= rhs.bits;
    }
}

impl<T> BitOr for StateSet<T> {
    type Output = Self;

    /// Returns the union of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let lhs = state_set![(false, false), (false, true)];
    /// let rhs = state_set![(false, true), (true, false)];
    /// assert_eq!(lhs | rhs, state_set![(false, false), (false, true), (true, false)]);
    /// ```
    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_u64_unchecked(self.bits | rhs.bits) }
    }
}

impl<T> BitOrAssign for StateSet<T> {
    /// Replaces `self` with the union of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let mut set = state_set![(false, false), (false, true)];
    /// set |= state_set![(false, true), (true, false)];
    /// assert_eq!(set, state_set![(false, false), (false, true), (true, false)]);
    /// ```
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.bits |= rhs.bits;
    }
}

impl<T> BitXor for StateSet<T> {
    type Output = Self;

    /// Returns the symmetric difference of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let lhs = state_set![(false, false), (false, true)];
    /// let rhs = state_set![(false, true), (true, false)];
    /// assert_eq!(lhs ^ rhs, state_set![(false, false), (true, false)]);
    /// ```
    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_u64_unchecked(self.bits ^ rhs.bits) }
    }
}

impl<T> BitXorAssign for StateSet<T> {
    /// Replaces `self` with the symmetric difference of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let mut set = state_set![(false, false), (false, true)];
    /// set ^= state_set![(false, true), (true, false)];
    /// assert_eq!(set, state_set![(false, false), (true, false)]);
    /// ```
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.bits ^= rhs.bits;
    }
}

impl<T: State> Sub for StateSet<T> {
    type Output = Self;

    /// Returns the set difference of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let lhs = state_set![(false, false), (false, true)];
    /// let rhs = state_set![(false, true), (true, false)];
    /// assert_eq!(lhs - rhs, state_set![(false, false)]);
    /// ```
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        self & !rhs
    }
}

impl<T: State> SubAssign for StateSet<T> {
    /// Replaces `self` with the set difference of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let mut set = state_set![(false, false), (false, true)];
    /// set -= state_set![(false, true), (true, false)];
    /// assert_eq!(set, state_set![(false, false)]);
    /// ```
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self &= !rhs;
    }
}

impl<T: State> FromIterator<T> for StateSet<T> {
    /// Creates a [`StateSet`] from an iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use state_set::*;
    /// #
    /// let set = StateSet::from_iter((0..2).map(|i| i.cmp(&1)));
    /// assert_eq!(set, state_set![std::cmp::Ordering::Less, std::cmp::Ordering::Equal]);
    /// ```
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::new();
        for state in iter {
            set.insert(state);
        }
        set
    }
}

impl<T: State> Extend<T> for StateSet<T> {
    /// Extends the set with the states yielded by an iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use state_set::*;
    /// #
    /// let mut set = state_set![false];
    /// set.extend([true, false].iter().copied());
    /// assert_eq!(set, state_set![false, true]);
    /// ```
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for state in iter {
            self.insert(state);
        }
    }
}

impl<T: State> State for StateSet<T> {
    const NUM_STATES: u32 = 1 << T::NUM_STATES;

    #[inline]
    fn into_index(self) -> u32 {
        self.bits as u32
    }

    #[inline]
    unsafe fn from_index_unchecked(index: u32) -> Self {
        Self {
            bits: index as u64,
            phantom: PhantomData,
        }
    }
}

#[cfg(feature = "serde")]
impl<T: State + Serialize> Serialize for StateSet<T> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.len() as usize))?;
        for state in self.iter() {
            seq.serialize_element(&state)?;
        }
        seq.end()
    }
}

#[cfg(feature = "serde")]
struct DeserializeVisitor<T>(PhantomData<T>);

#[cfg(feature = "serde")]
impl<'de, T: State + Deserialize<'de>> Visitor<'de> for DeserializeVisitor<T> {
    type Value = StateSet<T>;

    #[inline]
    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a sequence of states")
    }

    #[inline]
    fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<Self::Value, S::Error> {
        std::iter::from_fn(|| seq.next_element().transpose()).collect::<Result<_, _>>()
    }
}

#[cfg(feature = "serde")]
impl<'de, T: State + Deserialize<'de>> Deserialize<'de> for StateSet<T> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_seq(DeserializeVisitor(PhantomData))
    }
}

impl<T: State> IntoIterator for StateSet<T> {
    type Item = T;
    type IntoIter = Iter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: State> IntoIterator for &'a StateSet<T> {
    type Item = T;
    type IntoIter = Iter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator that yields the states in a [`StateSet`].
///
/// This struct is created by the [`iter`](StateSet::iter) method on [`StateSet`].
/// Iteration will be in ascending order according to the state's index.
///
/// # Example
///
/// ```
/// # use state_set::*;
///
/// let s = state_set![true, false];
/// let mut iter = s.iter();
///
/// assert_eq!(iter.next(), Some(false));
/// assert_eq!(iter.next(), Some(true));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Iter<T>(StateSet<T>);

impl<T: State> Iterator for Iter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        (!self.0.is_empty()).then(|| {
            let index = self.0.bits.trailing_zeros();
            self.0.bits ^= 1 << index;
            unsafe { T::from_index_unchecked(index) }
        })
    }
}

impl<T: State> DoubleEndedIterator for Iter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        (!self.0.is_empty()).then(|| {
            let index = 63 - self.0.bits.leading_zeros();
            self.0.bits ^= 1 << index;
            unsafe { T::from_index_unchecked(index) }
        })
    }
}

impl<T: State> ExactSizeIterator for Iter<T> {
    #[inline]
    fn len(&self) -> usize {
        self.0.len() as usize
    }
}

impl<T: State> FusedIterator for Iter<T> {}

#[cfg(test)]
mod test {
    use crate::state_set;

    use super::*;

    #[test]
    fn test_overflow() {
        let set = !StateSet::<[bool; 6]>::new();
        assert!(set.is_all());
        assert_eq!(StateSet::<[bool; 6]>::try_from(u64::MAX), Ok(set));
    }

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
    fn iter() {
        let set = state_set![(false, false), (false, true)];
        let mut iter = set.iter();
        assert_eq!(iter.next(), Some((false, false)));
        assert_eq!(iter.next(), Some((false, true)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn into_iter() {
        let set = state_set![(false, false), (false, true)];
        let mut iter = set.into_iter();
        assert_eq!(iter.next(), Some((false, false)));
        assert_eq!(iter.next(), Some((false, true)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn state() {
        assert_eq!(StateSet::<bool>::NUM_STATES, 4);
        assert_eq!(StateSet::<bool>::from_index(0), Some(state_set![]));
        assert_eq!(StateSet::<bool>::from_index(1), Some(state_set![false]));
        assert_eq!(StateSet::<bool>::from_index(2), Some(state_set![true]));
        assert_eq!(StateSet::<bool>::from_index(3), Some(bool::all()));
    }

    #[test]
    fn send() {
        fn assert_send<T: Send>() {}
        assert_send::<StateSet<bool>>();
    }

    #[test]
    fn sync() {
        fn assert_sync<T: Sync>() {}
        assert_sync::<StateSet<bool>>();
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serde() {
        let set = state_set![(false, false), (false, true)];

        let j = serde_json::to_value(set).unwrap();
        assert_eq!(j, serde_json::json!([(false, false), (false, true)]));

        let set_deserialized: StateSet<(bool, bool)> = serde_json::from_value(j).unwrap();
        assert_eq!(set, set_deserialized);
    }
}
