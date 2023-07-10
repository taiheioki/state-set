use std::{
    fmt,
    fmt::{Debug, Formatter},
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign},
};

#[cfg(feature = "serde")]
use serde::{
    de::{SeqAccess, Visitor},
    ser::SerializeSeq,
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::{error::InvalidBitVectorError, iter::Iter, State};

/// A set of states represented by a bit vector.
///
/// This struct manages a set of states for a type `T` that implements [`State`].
/// It uses a [`u64`] as a bit vector to store the presence of states, where each bit represents a state.
pub struct StateSet<T> {
    pub(crate) bits: u64,
    phantom: PhantomData<T>,
}

impl<T> StateSet<T> {
    /// Creates a new, empty [`StateSet`].
    #[inline]
    pub const fn new() -> Self {
        unsafe { Self::from_bits_unchecked(0) }
    }

    /// Creates a new instance of [`StateSet`] from [`u64`] without checking the validity of the bits.
    ///
    /// # Safety
    /// The caller must ensure that `bits` represent a valid state (that is, the bits in positions greater than
    /// [`T::NUM_STATES`](State::NUM_STATES) are not set).
    #[inline]
    pub const unsafe fn from_bits_unchecked(bits: u64) -> Self {
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
    /// let set = StateSet::<bool>::new();
    /// assert!(set.is_empty());
    /// ```
    /// ```
    /// # use state_set::*;
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
    ///
    /// assert!(set.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.bits = 0;
    }

    /// Returns an iterator over the states in the set.
    /// Iteration will be in ascending order according to the state's index.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let set = state_set![true, false];
    /// let vec: Vec<_> = set.iter().collect();
    ///
    /// assert_eq!(vec, vec![false, true]);
    /// ```
    #[inline]
    pub const fn iter(&self) -> Iter<T> {
        Iter(unsafe { Self::from_bits_unchecked(self.bits) })
    }

    /// Returns `true` if the set is disjoint from another set.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let set = state_set![false];
    ///
    /// assert!(set.is_disjoint(&state_set![]));
    /// assert!(!set.is_disjoint(&state_set![false]));
    /// assert!(set.is_disjoint(&state_set![true]));
    /// assert!(!set.is_disjoint(&state_set![true, false]));
    /// ```
    #[inline]
    pub const fn is_disjoint(&self, other: &Self) -> bool {
        (self.bits & other.bits) == 0
    }

    /// Returns `true` if the set is a subset of another set.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let set = state_set![false];
    ///
    /// assert!(!set.is_subset(&state_set![]));
    /// assert!(set.is_subset(&state_set![false]));
    /// assert!(!set.is_subset(&state_set![true]));
    /// assert!(set.is_subset(&state_set![false, true]));
    /// ```
    #[inline]
    pub const fn is_subset(&self, other: &Self) -> bool {
        (self.bits & other.bits) == self.bits
    }

    /// Returns `true` if the set is a superset of another set.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let set = state_set![false];
    ///
    /// assert!(set.is_superset(&state_set![]));
    /// assert!(set.is_superset(&state_set![false]));
    /// assert!(!set.is_superset(&state_set![true]));
    /// assert!(!set.is_superset(&state_set![false, true]));
    /// ```
    #[inline]
    pub const fn is_superset(&self, other: &Self) -> bool {
        (self.bits & other.bits) == other.bits
    }
}

impl<T: State> StateSet<T> {
    /// Returns `true` if the set contains all the states.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let set = state_set![false, true];
    /// assert!(set.is_all());
    /// ```
    #[inline]
    pub const fn is_all(&self) -> bool {
        T::NUM_STATES <= 64 && self.bits == u64::MAX >> (64 - T::NUM_STATES)
    }

    /// Insert a state into the set.
    ///
    /// # Compile Errors
    /// Fails to compile if `T::NUM_STATES > 64`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let mut set = state_set![None];
    /// set.insert(None);
    /// set.insert(Some(false));
    ///
    /// assert_eq!(set, state_set![None, Some(false)]);
    /// ```
    ///
    /// ```compile_fail
    /// # use state_set::*;
    /// let mut set = StateSet::<[bool; 10]>::new();  // <[bool; 10]>::NUM_STATES = 1024 > 64
    /// set.insert([false; 10]);
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
    /// let mut set = state_set![None, Some(false)];
    /// set.remove(Some(false));
    /// set.remove(Some(true));
    ///
    /// assert_eq!(set, state_set![None]);
    /// ```
    #[inline]
    pub fn remove(&mut self, state: T) {
        let index = state.into_index();
        if index <= 64 {
            self.bits &= !(1 << index);
        }
    }

    /// Returns `true` if the set contains the given state.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let set = state_set![false];
    ///
    /// assert!(set.contains(false));
    /// assert!(!set.contains(true));
    /// ```
    #[inline]
    pub fn contains(&self, state: T) -> bool {
        let index = state.into_index();
        index <= 64 && self.bits & (1 << index) != 0
    }
}

impl<T> Clone for StateSet<T> {
    #[inline]
    fn clone(&self) -> Self {
        unsafe { Self::from_bits_unchecked(self.bits) }
    }
}

impl<T: State + Debug> Debug for StateSet<T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
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
    /// let set1 = state_set![false, true];
    /// let set2 = state_set![true, false];
    ///
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
    /// let set = state_set![false, true];
    /// let data: u64 = set.into();
    ///
    /// assert_eq!(data, 0b11);
    /// ```
    #[inline]
    fn from(value: StateSet<T>) -> Self {
        value.bits
    }
}

impl<T: State> TryFrom<u64> for StateSet<T> {
    type Error = InvalidBitVectorError;

    /// Tries to convert a [`u64`] into a [`StateSet`].
    ///
    /// This method attempts to create a [`StateSet`] from a bit vector. The method succeeds if and only if
    /// the bit vector is valid (that is, the bits in positions greater than [`T::NUM_STATES`](State::NUM_STATES)
    /// are not set).
    ///
    /// # Examples
    ///
    /// ```
    /// # use state_set::*;
    /// let set = StateSet::<bool>::try_from(0b10);
    /// assert_eq!(set, Ok(state_set![true]));
    /// ```
    /// ```
    /// # use state_set::*;
    /// let set = StateSet::<bool>::try_from(0b11);
    /// assert_eq!(set, Ok(state_set![false, true]));
    /// ```
    /// ```
    /// # use state_set::*;
    /// let set = StateSet::<bool>::try_from(0b100);
    /// assert!(set.is_err());
    /// ```
    #[inline]
    fn try_from(value: u64) -> Result<Self, Self::Error> {
        if T::NUM_STATES >= 64 || value & !(u64::MAX >> (64 - T::NUM_STATES)) == 0 {
            Ok(unsafe { Self::from_bits_unchecked(value) })
        } else {
            Err(InvalidBitVectorError)
        }
    }
}

impl<T: State> Not for StateSet<T> {
    type Output = Self;

    /// Returns the complement of `self`.
    ///
    /// # Compile Errors
    /// Fails to compile if `T::NUM_STATES > 64`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let set = state_set![false];
    ///
    /// assert_eq!(!set, state_set![true]);
    /// ```
    /// ```compile_fail
    /// # use state_set::*;
    /// let set = !StateSet::<[bool; 10]>::new();  // <[bool; 10]>::NUM_STATES = 1024 > 64
    /// ```
    #[inline]
    fn not(self) -> Self::Output {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        unsafe { Self::from_bits_unchecked(!self.bits & (u64::MAX >> (64 - T::NUM_STATES))) }
    }
}

impl<T> BitAnd for StateSet<T> {
    type Output = Self;

    /// Returns the intersection of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let lhs = state_set![(false, false), (false, true)];
    /// let rhs = state_set![(false, true), (true, false)];
    ///
    /// assert_eq!(lhs & rhs, state_set![(false, true)]);
    /// ```
    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_bits_unchecked(self.bits & rhs.bits) }
    }
}

impl<T> BitAndAssign for StateSet<T> {
    /// Replaces `self` with the intersection of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let mut set = state_set![(false, false), (false, true)];
    /// set &= state_set![(false, true), (true, false)];
    ///
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
    ///
    /// assert_eq!(lhs | rhs, state_set![(false, false), (false, true), (true, false)]);
    /// ```
    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_bits_unchecked(self.bits | rhs.bits) }
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
    ///
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
    ///
    /// assert_eq!(lhs ^ rhs, state_set![(false, false), (true, false)]);
    /// ```
    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_bits_unchecked(self.bits ^ rhs.bits) }
    }
}

impl<T> BitXorAssign for StateSet<T> {
    /// Replaces `self` with the symmetric difference of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let mut set = state_set![(false, false), (false, true)];
    /// set ^= state_set![(false, true), (true, false)];
    ///
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
    /// let lhs = state_set![(false, false), (false, true)];
    /// let rhs = state_set![(false, true), (true, false)];
    ///
    /// assert_eq!(lhs - rhs, state_set![(false, false)]);
    /// ```
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        unsafe { Self::from_bits_unchecked(self.bits & !rhs.bits) }
    }
}

impl<T: State> SubAssign for StateSet<T> {
    /// Replaces `self` with the set difference of `self` and `rhs`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// let mut set = state_set![(false, false), (false, true)];
    /// set -= state_set![(false, true), (true, false)];
    ///
    /// assert_eq!(set, state_set![(false, false)]);
    /// ```
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.bits &= !rhs.bits;
    }
}

impl<T: State> FromIterator<T> for StateSet<T> {
    /// Creates a [`StateSet`] from an iterator.
    ///
    /// # Compile Errors
    /// Fails to compile if `T::NUM_STATES > 64`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// #
    /// let set = StateSet::from_iter((0..2).map(|i| i.cmp(&1)));
    /// assert_eq!(set, state_set![std::cmp::Ordering::Less, std::cmp::Ordering::Equal]);
    /// ```
    /// ```compile_fail
    /// # use state_set::*;
    /// let iter = [[false; 7]].into_iter();
    /// let set = StateSet::from_iter(iter); // <[bool; 7]>::NUM_STATES = 128 > 64
    /// ```
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        #[allow(clippy::let_unit_value)]
        let _ = T::CHECK_NUM_STATES_AT_MOST_64;

        let mut set = Self::new();
        for state in iter {
            set.insert(state);
        }
        set
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

impl<T: State> Extend<T> for StateSet<T> {
    /// Extends the set with the states yielded by an iterator.
    ///
    /// # Compile Errors
    /// Fails to compile if `T::NUM_STATES > 64`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use state_set::*;
    /// let mut set = state_set![None];
    /// let iter = [None, Some(false)].into_iter();
    /// set.extend(iter);
    ///
    /// assert_eq!(set, state_set![None, Some(false)]);
    /// ```
    ///
    /// ```compile_fail
    /// # use state_set::*;
    /// let mut set = state_set![];
    /// let iter = [[false; 10], [true; 10]].into_iter();
    /// set.extend(iter);  // <[bool; 10]>::NUM_STATES = 1024 > 64
    /// ```
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for state in iter {
            self.insert(state);
        }
    }
}

#[test]
fn state() {}
impl<T: State> State for StateSet<T> {
    ///
    /// The total number of distinct states that values of [`StateSet<T>`] can represent,
    /// i.e., 2 to the power of [`T::NUM_STATES`](State::NUM_STATES).
    ///
    /// # Compile Errors
    /// Using this constant fails to compile if `Self::NUM_STATES >= 2^32`, i.e., `T::NUM_STATES >= 32`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// assert_eq!(StateSet::<()>::NUM_STATES, 2);
    /// assert_eq!(StateSet::<bool>::NUM_STATES, 4);
    /// assert_eq!(StateSet::<Option<bool>>::NUM_STATES, 8);
    /// assert_eq!(StateSet::<[bool; 3]>::NUM_STATES, 256);
    /// ```
    ///
    /// ```compile_fail
    /// # use state_set::*;
    /// let num_states = StateSet::<[bool; 5]>::NUM_STATES;  // <[bool; 5]>::NUM_STATES = 32
    /// ```
    const NUM_STATES: u32 = 1 << T::NUM_STATES;

    /// Converts `self` into an index, which is an integer from `0` to `Self::NUM_STATES - 1`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// assert_eq!(StateSet::<bool>::new().into_index(), 0b00);
    /// assert_eq!(state_set![false].into_index(), 0b01);
    /// assert_eq!(state_set![true].into_index(), 0b10);
    /// assert_eq!(bool::all().into_index(), 0b11);
    /// ```
    #[inline]
    fn into_index(self) -> u32 {
        self.bits as u32
    }

    /// Converts `index` into a value of this type. Returns `None` if `index >= Self::STATUS`.
    ///
    /// # Examples
    /// ```
    /// # use state_set::*;
    /// assert_eq!(StateSet::<bool>::from_index(0), Some(state_set![]));
    /// assert_eq!(StateSet::<bool>::from_index(1), Some(state_set![false]));
    /// assert_eq!(StateSet::<bool>::from_index(2), Some(state_set![true]));
    /// assert_eq!(StateSet::<bool>::from_index(3), Some(bool::all()));
    /// assert_eq!(StateSet::<bool>::from_index(4), None);
    /// ```
    #[inline]
    fn from_index(index: u32) -> Option<Self> {
        // To avoid overflow when `T::NUM_STATES >= 32`, `index >= Self::NUM_STATES` is replaced with
        // an equivalent condition `index.checked_ilog2().map_or(true, |log| log < T::NUM_STATES)`
        (index
            .checked_ilog2()
            .map_or(true, |log| log < T::NUM_STATES))
        .then(|| unsafe { Self::from_index_unchecked(index) })
    }

    #[inline]
    unsafe fn from_index_unchecked(index: u32) -> Self {
        Self {
            bits: index as u64,
            phantom: PhantomData,
        }
    }

    /// Creates a new [`StateSet<Self>`] consisting of all the states.
    ///
    /// # Compile Errors
    /// Fails to compile if `Self::NUM_STATES > 64`, i.e., `T::NUM_STATES > 6`.
    ///
    /// # Example
    ///
    /// ```
    /// # use state_set::*;
    /// let set = StateSet::<bool>::all();
    /// assert_eq!(
    ///     set,
    ///     state_set![state_set![], state_set![false], state_set![true], state_set![false, true]]
    /// );
    /// ```
    ///
    /// ```compile_fail
    /// # use state_set::*;
    /// // <[bool; 3]>::NUM_STATES = 8 > 6
    /// // StateSet<[bool; 3]>::NUM_STATES = 2^8 = 256 > 64
    /// let set = StateSet::<[bool; 3]>::all();
    /// ```
    #[inline]
    fn all() -> StateSet<Self> {
        !StateSet::new()
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
    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

#[cfg(test)]
mod test {
    use crate::state_set;

    use super::*;

    #[test]
    fn debug() {
        assert_eq!(format!("{:?}", StateSet::<bool>::new()), "{false}");
        assert_eq!(format!("{:?}", state_set![false]), "{false}");
        assert_eq!(format!("{:?}", state_set![true]), "{true}");
        assert_eq!(format!("{:?}", bool::all()), "{false, true}");
    }

    #[test]
    fn is_all_overflow() {
        let set = StateSet::<[bool; 10]>::new();
        assert!(!set.is_all());
    }

    #[test]
    fn remove_overflow() {
        let mut set = StateSet::<[bool; 10]>::new();
        set.remove([false; 10]);
        set.remove([true; 10]);
        assert!(set.is_empty());
    }

    #[test]
    fn contains_overflow() {
        let mut set = StateSet::<[bool; 10]>::new();
        set.remove([false; 10]);
        set.remove([true; 10]);
        assert!(set.is_empty());
    }

    #[test]
    fn try_from_overflow() {
        assert!(StateSet::<[bool; 6]>::try_from(u64::MAX).is_ok_and(|set| set.is_all()));
        assert!(StateSet::<[bool; 10]>::try_from(u64::MAX).is_ok_and(|set| set.len() == 64));
    }

    #[test]
    fn state_overflow() {
        assert_eq!(StateSet::<[bool; 5]>::from_index(0), Some(state_set![]));
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

        let j = serde_json::to_value(&set).unwrap();
        assert_eq!(j, serde_json::json!([(false, false), (false, true)]));

        let set_deserialized: StateSet<(bool, bool)> = serde_json::from_value(j).unwrap();
        assert_eq!(set, set_deserialized);
    }
}
