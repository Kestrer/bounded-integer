//! Indexing operations on [T; N], Vec<T> and VecDeque<T> for BoundedUsize

use super::BoundedUsize;
use core::ops::Index;
use core::ops::IndexMut;

impl<const MIN: usize, const MAX: usize, T> Index<BoundedUsize<MIN, MAX>> for [T] {
    type Output = T;

    #[inline]
    fn index(&self, index: BoundedUsize<MIN, MAX>) -> &Self::Output {
        &self[index.get()]
    }
}

impl<const MIN: usize, const MAX: usize, T> IndexMut<BoundedUsize<MIN, MAX>> for [T] {
    #[inline]
    fn index_mut(&mut self, index: BoundedUsize<MIN, MAX>) -> &mut Self::Output {
        &mut self[index.get()]
    }
}

#[cfg(feature = "std")]
impl<const MIN: usize, const MAX: usize, T> Index<BoundedUsize<MIN, MAX>> for std::vec::Vec<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: BoundedUsize<MIN, MAX>) -> &Self::Output {
        &self[index.get()]
    }
}

#[cfg(feature = "std")]
impl<const MIN: usize, const MAX: usize, T> IndexMut<BoundedUsize<MIN, MAX>> for std::vec::Vec<T> {
    #[inline]
    fn index_mut(&mut self, index: BoundedUsize<MIN, MAX>) -> &mut Self::Output {
        &mut self[index.get()]
    }
}

#[cfg(feature = "std")]
impl<const MIN: usize, const MAX: usize, T> Index<BoundedUsize<MIN, MAX>>
    for std::collections::VecDeque<T>
{
    type Output = T;

    #[inline]
    fn index(&self, index: BoundedUsize<MIN, MAX>) -> &Self::Output {
        &self[index.get()]
    }
}

#[cfg(feature = "std")]
impl<const MIN: usize, const MAX: usize, T> IndexMut<BoundedUsize<MIN, MAX>>
    for std::collections::VecDeque<T>
{
    #[inline]
    fn index_mut(&mut self, index: BoundedUsize<MIN, MAX>) -> &mut Self::Output {
        &mut self[index.get()]
    }
}

#[cfg(test)]
mod tests {
    use crate::types::BoundedUsize;

    #[test]
    fn indexing() {
        let arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

        for i in 0..arr.len() {
            let b_u = BoundedUsize::<0, 30>::new(i).unwrap();
            assert_eq!(arr[b_u], i);
        }
    }

    #[test]
    #[cfg(feature = "std")]
    fn indexing_std() {
        let vec = (0..20).collect::<std::vec::Vec<usize>>();
        let deq = vec
            .clone()
            .into_iter()
            .rev()
            .collect::<std::collections::VecDeque<_>>();

        for i in 0..vec.len() {
            let b_u = BoundedUsize::<0, 30>::new(i).unwrap();

            assert_eq!(vec[b_u], i);
            assert_eq!(deq[b_u], 19 - i);
        }
    }

    #[test]
    fn indexing_mut() {
        let mut arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

        for i in 0..arr.len() {
            let b_u = BoundedUsize::<0, 30>::new(i).unwrap();

            arr[b_u] += 5;

            assert_eq!(arr[b_u], i + 5);
        }
    }

    #[test]
    #[cfg(feature = "std")]
    fn indexing_mut_std() {
        let mut vec = (0..20).collect::<std::vec::Vec<usize>>();
        let mut deq = vec
            .clone()
            .into_iter()
            .rev()
            .collect::<std::collections::VecDeque<_>>();

        for i in 0..vec.len() {
            let b_u = BoundedUsize::<0, 30>::new(i).unwrap();

            vec[b_u] += 5;
            deq[b_u] += 10;

            assert_eq!(vec[b_u], i + 5);
            assert_eq!(deq[b_u], (19 - i) + 10);
        }
    }
}
