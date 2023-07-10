//! A module for providing iterators.

use std::{
    fmt::{Debug, Formatter, Result},
    hash::{Hash, Hasher},
    iter::FusedIterator,
};

use crate::{State, StateSet};

/// An iterator that yields the states in a [`StateSet`].
///
/// This struct is created by the [`iter`](StateSet::iter) method on [`StateSet`].
/// Iteration will be in ascending order according to the state's index.
///
/// # Example
///
/// ```
/// # use state_set::*;
/// let s = state_set![true, false];
/// let mut iter = s.iter();
///
/// assert_eq!(iter.next(), Some(false));
/// assert_eq!(iter.next(), Some(true));
/// assert_eq!(iter.next(), None);
/// ```
pub struct Iter<T>(pub(crate) StateSet<T>);

impl<T> Clone for Iter<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> Debug for Iter<T>
where
    StateSet<T>: Debug,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_tuple("Iter").field(&self.0).finish()
    }
}

impl<T> PartialEq for Iter<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for Iter<T> {}

impl<T> Hash for Iter<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

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

    #[test]
    fn iter() {
        let set = state_set![(false, false), (false, true), (true, true)];
        let mut iter = set.iter();
        assert_eq!(iter.next(), Some((false, false)));
        assert_eq!(iter.next_back(), Some((true, true)));
        assert_eq!(iter.next(), Some((false, true)));
        assert_eq!(iter.next(), None);
    }
}
