use std::{
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

use crate::State;

/// A set of states represented by a bit vector.
///
/// This struct manages a set of states for a type `T` that implements [`State`].
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

    /// Returns an iterator over the states in the set.
    #[inline]
    pub fn iter(&self) -> Iter<T> {
        Iter {
            set: self,
            index: 0,
        }
    }
}

impl<T: State> StateSet<T> {
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

impl<T: State> TryFrom<u64> for StateSet<T> {
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

impl<T: State> Not for StateSet<T> {
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

impl<T: State> Sub for StateSet<T> {
    type Output = Self;

    /// Returns the set difference of `self` and `rhs`.
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        self & !rhs
    }
}

impl<T: State> SubAssign for StateSet<T> {
    /// Replaces `self` with the set difference of `self` and `rhs`.
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        *self &= !rhs;
    }
}

impl<T: State> FromIterator<T> for StateSet<T> {
    /// Creates a [`StateSet`] from an iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use state_set::*;
    ///
    /// let set = (0..4).map(|i| i % 2 == 0).collect::<StateSet<_>>();
    /// assert_eq!(set, state_set![false, true]);
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
    /// use state_set::*;
    ///
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
        let mut set = $crate::StateSet::new();
        $(set.insert($state);)*
        set
    }};
}

impl<T: State> IntoIterator for StateSet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Returns an iterator over the states.
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            set: self,
            index: 0,
        }
    }
}

/// An iterator over the states in a [`StateSet`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Iter<'a, T> {
    set: &'a StateSet<T>,
    index: u32,
}

impl<'a, T: State> Iterator for Iter<'a, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < T::NUM_STATES {
            let index = self.index;
            self.index += 1;

            if self.set.data & (1 << index) != 0 {
                return Some(unsafe { T::from_index_unchecked(index) });
            }
        }

        None
    }
}

impl<'a, T: State> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        while self.index > 0 {
            self.index -= 1;

            if self.set.data & (1 << self.index) != 0 {
                return Some(unsafe { T::from_index_unchecked(self.index) });
            }
        }

        None
    }
}

impl<'a, T: State> ExactSizeIterator for Iter<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        (self.set.len() - self.index) as usize
    }
}

impl<'a, T: State> FusedIterator for Iter<'a, T> {}

/// An iterator over the states in a [`StateSet`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntoIter<T> {
    set: StateSet<T>,
    index: u32,
}

impl<T: State> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < T::NUM_STATES {
            let index = self.index;
            self.index += 1;

            if self.set.data & (1 << index) != 0 {
                return Some(unsafe { T::from_index_unchecked(index) });
            }
        }

        None
    }
}

impl<T: State> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        while self.index > 0 {
            self.index -= 1;
            if self.set.data & (1 << self.index) != 0 {
                return Some(unsafe { T::from_index_unchecked(self.index) });
            }
        }

        None
    }
}

impl<T: State> ExactSizeIterator for IntoIter<T> {
    #[inline]
    fn len(&self) -> usize {
        (self.set.len() - self.index) as usize
    }
}

impl<T: State> FusedIterator for IntoIter<T> {}

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
    fn iter() {
        let set = state_set![(false, false), (false, true)];
        let mut iter = set.iter();
        assert_eq!(iter.next(), Some((false, false)));
        assert_eq!(iter.next(), Some((false, true)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn into_intr() {
        let set = state_set![(false, false), (false, true)];
        let mut iter = set.into_iter();
        assert_eq!(iter.next(), Some((false, false)));
        assert_eq!(iter.next(), Some((false, true)));
        assert_eq!(iter.next(), None);
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
