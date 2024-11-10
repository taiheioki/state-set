//! A module for providing iterators.

use core::{
    fmt::{Debug, Formatter, Result},
    hash::{Hash, Hasher},
    iter::FusedIterator,
};

use crate::{bits::Bits, State, StateSet};

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
pub struct Iter<T, const B: usize>(pub(crate) StateSet<T, B>);

impl<T, const B: usize> Clone for Iter<T, B> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T, const B: usize> Debug for Iter<T, B>
where
    StateSet<T, B>: Debug,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_tuple("Iter").field(&self.0).finish()
    }
}

impl<T, const B: usize> PartialEq for Iter<T, B> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T, const B: usize> Eq for Iter<T, B> {}

impl<T, const B: usize> Hash for Iter<T, B> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T: State, const B: usize> Iterator for Iter<T, B> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        (!self.0.is_empty()).then(|| {
            let index = self.0.bits.trailing_zeros();
            self.0.bits.unset_bit(index);
            unsafe { T::from_index_unchecked(index) }
        })
    }
}

impl<T: State, const B: usize> DoubleEndedIterator for Iter<T, B> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        (!self.0.is_empty()).then(|| {
            let index = B::BITS - 1 - self.0.bits.leading_zeros();
            self.0.bits.unset_bit(index);
            unsafe { T::from_index_unchecked(index) }
        })
    }
}

impl<T: State, const B: usize> ExactSizeIterator for Iter<T, B> {
    #[inline]
    fn len(&self) -> usize {
        self.0.len() as usize
    }
}

impl<T: State, const B: usize> FusedIterator for Iter<T, B> {}

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
