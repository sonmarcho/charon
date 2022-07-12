#![allow(dead_code)]
//! A vector with custom index types.
//!
//! This data-structure is mostly meant to be used with the index types defined
//! with [generate_index_type](aenea_macros::generate_index_type): by using custom index types, we
//! leverage the type checker to prevent us from mixing them.
//!
//! Note that this data structure is implemented by using persistent vectors.
//! This makes the clone operation almost a no-op.

use serde::{Serialize, Serializer};
use std::iter::{FromIterator, IntoIterator};

pub use std::collections::hash_map::Iter as IterAll;
pub use std::collections::hash_map::IterMut as IterAllMut;

pub trait ToUsize {
    fn to_usize(&self) -> usize;
}

pub trait Increment {
    fn incr(&mut self);
}

pub trait Zero {
    fn zero() -> Self;
}

/// Indexed vector
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Vector<I, T>
where
    I: ToUsize,
    T: Clone,
{
    vector: im::Vector<T>,
    /// This is a bit annoying, but we need to use `I` somewhere.
    phantom: std::marker::PhantomData<I>,
}

/// Immutable iterator for indexed vectors, to iter over pairs of (index, value)
#[derive(Debug)]
pub struct IndexValueImmutIterator<'a, I, T>
where
    I: ToUsize + Increment,
    T: Clone,
{
    vector: &'a Vector<I, T>,
    index: I,
}

impl<'a, I, T> Iterator for IndexValueImmutIterator<'a, I, T>
where
    I: ToUsize + Increment + Copy,
    T: Clone,
{
    type Item = (I, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index.to_usize() < self.vector.len() {
            let index = self.index;
            let obj = self.vector.get(self.index).unwrap();
            self.index.incr();
            Some((index, obj))
        } else {
            None
        }
    }
}

impl<I, T> Vector<I, T>
where
    I: ToUsize + Increment + Copy + Zero,
    T: Clone,
{
    pub fn iter_indexed_values<'a>(&'a self) -> IndexValueImmutIterator<'a, I, T> {
        IndexValueImmutIterator {
            vector: self,
            index: I::zero(),
        }
    }
}

/// Iterator to iterate over the indices in an id vector
#[derive(Debug)]
pub struct IndexIterator<I>
where
    I: ToUsize + Increment + Copy,
{
    len: usize,
    index: I,
}

impl<I> Iterator for IndexIterator<I>
where
    I: ToUsize + Increment + Copy,
{
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index.to_usize() < self.len {
            let index = self.index;
            self.index.incr();
            Some(index)
        } else {
            None
        }
    }
}

impl<I, T> Vector<I, T>
where
    I: ToUsize + Increment + Copy + Zero,
    T: Clone,
{
    pub fn iter_indices<'a>(&'a self) -> IndexIterator<I> {
        IndexIterator {
            len: self.vector.len(),
            index: I::zero(),
        }
    }
}

impl<I, T> Vector<I, T>
where
    I: ToUsize,
    T: Clone,
{
    pub fn new() -> Self {
        Vector {
            vector: im::Vector::new(),
            phantom: std::marker::PhantomData,
        }
    }

    pub fn get(&self, i: I) -> Option<&T> {
        self.vector.get(i.to_usize())
    }

    pub fn get_mut(&mut self, i: I) -> Option<&mut T> {
        self.vector.get_mut(i.to_usize())
    }

    pub fn set(&mut self, i: I, x: T) {
        self.vector.set(i.to_usize(), x);
    }

    pub fn insert(&mut self, i: I, x: T) {
        self.vector.insert(i.to_usize(), x);
    }

    pub fn is_empty(&self) -> bool {
        self.vector.is_empty()
    }

    pub fn len(&self) -> usize {
        self.vector.len()
    }

    pub fn push_back(&mut self, x: T) {
        self.vector.push_back(x);
    }

    pub fn pop_back(&mut self) -> Option<T> {
        self.vector.pop_back()
    }

    pub fn push_front(&mut self, x: T) {
        self.vector.push_front(x);
    }

    pub fn pop_front(&mut self) -> Option<T> {
        self.vector.pop_front()
    }

    pub fn iter(&self) -> im::vector::Iter<T> {
        self.vector.iter()
    }

    pub fn iter_mut(&mut self) -> im::vector::IterMut<T> {
        self.vector.iter_mut()
    }
}

impl<I: ToUsize, T: Clone> Default for Vector<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, I, T> IntoIterator for &'a Vector<I, T>
where
    I: ToUsize,
    T: Clone,
{
    type Item = &'a T;
    type IntoIter = im::vector::Iter<'a, T>;

    fn into_iter(self) -> im::vector::Iter<'a, T> {
        self.vector.iter()
    }
}

impl<I, T> IntoIterator for Vector<I, T>
where
    I: ToUsize,
    T: Clone,
{
    type Item = T;
    type IntoIter = im::vector::ConsumingIter<T>;

    fn into_iter(self) -> im::vector::ConsumingIter<T> {
        self.vector.into_iter()
    }
}

impl<I, T> FromIterator<T> for Vector<I, T>
where
    I: ToUsize,
    T: Clone,
{
    #[inline]
    fn from_iter<It: IntoIterator<Item = T>>(iter: It) -> Vector<I, T> {
        Vector {
            vector: im::Vector::from_iter(iter),
            phantom: std::marker::PhantomData,
        }
    }
}

impl<I, T> From<Vec<T>> for Vector<I, T>
where
    I: ToUsize,
    T: Clone,
{
    fn from(v: Vec<T>) -> Self {
        Vector {
            vector: im::Vector::from(v),
            phantom: std::marker::PhantomData,
        }
    }
}

impl<I, T> From<im::Vector<T>> for Vector<I, T>
where
    I: ToUsize,
    T: Clone,
{
    fn from(v: im::Vector<T>) -> Self {
        Vector {
            vector: v.clone(),
            phantom: std::marker::PhantomData,
        }
    }
}

impl<I: ToUsize, T: Clone + Serialize> Serialize for Vector<I, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeSeq;

        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for e in self {
            seq.serialize_element(e)?;
        }
        seq.end()
    }
}
