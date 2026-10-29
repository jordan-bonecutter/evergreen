//! Snapshots share plane headers in chunks. Mutation copies only the affected
//! chunk; all worlds share a counter so even discarded branch copies are metered.

use super::*;
use std::ops::{Index, IndexMut};

const CHUNK_SIZE: usize = 32;

#[derive(Debug)]
pub(super) struct Store<T> {
    chunks: Vec<Arc<Vec<Plane<T>>>>,
    len: usize,
    copied: Arc<AtomicUsize>,
}

impl<T> Default for Store<T> {
    fn default() -> Self {
        Self {
            chunks: Vec::new(),
            len: 0,
            copied: Arc::new(AtomicUsize::new(0)),
        }
    }
}

impl<T> Clone for Store<T> {
    fn clone(&self) -> Self {
        Self {
            chunks: self.chunks.clone(),
            len: self.len,
            copied: Arc::clone(&self.copied),
        }
    }
}

impl<T> Store<T> {
    pub(super) fn len(&self) -> usize {
        self.len
    }

    pub(super) fn snapshot_weight(&self) -> usize {
        self.chunks.len() + 1
    }

    pub(super) fn take_copy_work(&self) -> usize {
        self.copied.swap(0, Ordering::Relaxed)
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = &Plane<T>> {
        self.chunks.iter().flat_map(|chunk| chunk.iter())
    }

    pub(super) fn get(&self, index: usize) -> Option<&Plane<T>> {
        self.chunks.get(index / CHUNK_SIZE)?.get(index % CHUNK_SIZE)
    }

    fn writable_chunk(&mut self, index: usize) -> &mut Vec<Plane<T>> {
        let chunk = &mut self.chunks[index];
        if Arc::strong_count(chunk) > 1 {
            let cost = chunk.iter().fold(chunk.len(), |cost, plane| {
                cost.saturating_add(plane.ownership.snapshot_weight())
            });
            let _ = self
                .copied
                .try_update(Ordering::Relaxed, Ordering::Relaxed, |total| {
                    Some(total.saturating_add(cost))
                });
        }
        Arc::make_mut(chunk)
    }

    pub(super) fn get_mut(&mut self, index: usize) -> Option<&mut Plane<T>> {
        if index >= self.len {
            return None;
        }
        self.writable_chunk(index / CHUNK_SIZE)
            .get_mut(index % CHUNK_SIZE)
    }

    pub(super) fn push(&mut self, plane: Plane<T>) {
        if self.len % CHUNK_SIZE == 0 {
            self.chunks.push(Arc::new(Vec::with_capacity(CHUNK_SIZE)));
        }
        self.writable_chunk(self.len / CHUNK_SIZE).push(plane);
        self.len += 1;
    }
}

impl<T> Index<usize> for Store<T> {
    type Output = Plane<T>;
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("plane index out of bounds")
    }
}

impl<T> IndexMut<usize> for Store<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).expect("plane index out of bounds")
    }
}
