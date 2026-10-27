//! Generation-based plane store shared by elaboration and reference execution.
//! Handles are opaque; invalidation is checked independently of the prover.
//! The checker and interpreter instantiate this store with their own value types.
//! Generated executables use the native backend's Linux allocator.

use std::sync::{
    atomic::{AtomicU64, AtomicUsize, Ordering},
    Arc,
};

mod owners;
pub use owners::OwnedReference;

static NEXT_ARENA: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Reference {
    owner: u64,
    slot: usize,
    generation: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PlaneId {
    owner: u64,
    slot: usize,
}

impl Reference {
    /// Identity for historical proof lookup. This does not check liveness or
    /// authorize a memory read; operational reads still go through `Memory`.
    pub(crate) fn plane_identity(self) -> PlaneId {
        PlaneId {
            owner: self.owner,
            slot: self.slot,
        }
    }
}

impl PlaneId {
    /// Internal exact key. The store bounds slots to 100,000, well below 2^64.
    /// Arena identities remain opaque to Evergreen programs and proof artifacts.
    pub(crate) fn state_key(self) -> u128 {
        (u128::from(self.owner) << 64) | self.slot as u128
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Projection<I = usize> {
    Field(String),
    Index(I),
}

#[derive(Clone, Debug)]
struct Plane<T> {
    ownership: owners::Ownership,
    generation: u64,
    value: Option<T>,
}

#[derive(Debug)]
pub struct Memory<T> {
    owner: u64,
    next_slot: Arc<AtomicUsize>,
    planes: Vec<Plane<T>>,
}

impl<T> Default for Memory<T> {
    fn default() -> Self {
        let mut owner = NEXT_ARENA.load(Ordering::Relaxed);
        loop {
            let next = owner
                .checked_add(1)
                .expect("memory arena identity exhausted");
            match NEXT_ARENA.compare_exchange_weak(
                owner,
                next,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(current) => owner = current,
            }
        }
        Self {
            owner,
            next_slot: Arc::new(AtomicUsize::new(0)),
            planes: Vec::new(),
        }
    }
}

impl<T> Memory<T> {
    pub(crate) fn snapshot(&self) -> Self
    where
        T: Clone,
    {
        Self {
            owner: self.owner,
            next_slot: Arc::clone(&self.next_slot),
            planes: self.planes.clone(),
        }
    }

    pub(crate) fn states(&self) -> Vec<(PlaneId, u64, Option<&T>)> {
        self.planes
            .iter()
            .enumerate()
            .map(|(slot, plane)| {
                (
                    PlaneId {
                        owner: self.owner,
                        slot,
                    },
                    plane.generation,
                    plane.value.as_ref(),
                )
            })
            .collect()
    }

    pub fn allocate(&mut self, value: T) -> Result<PlaneId, String> {
        let slot = self
            .next_slot
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |slot| {
                (slot < 100_000).then_some(slot + 1)
            })
            .map_err(|_| "plane allocation limit reached")?;
        let id = PlaneId {
            owner: self.owner,
            slot,
        };
        self.pad_to(slot);
        self.planes.push(Plane {
            ownership: owners::Ownership::Unique,
            generation: 0,
            value: Some(value),
        });
        Ok(id)
    }

    fn pad_to(&mut self, length: usize) {
        while self.planes.len() < length {
            self.planes.push(Plane {
                ownership: owners::Ownership::Unique,
                generation: 0,
                value: None,
            });
        }
    }

    /// Import allocations born after a saved world, keeping their globally
    /// unique IDs. Their conditional presence is checked by the frontend.
    pub(crate) fn import_new_planes(
        &mut self,
        branch: &Self,
        base: &Self,
    ) -> Result<Vec<PlaneId>, String>
    where
        T: Clone,
    {
        if self.owner != branch.owner || self.owner != base.owner {
            return Err("cannot join different plane arenas".into());
        }
        let mut imported = Vec::new();
        for slot in base.planes.len()..branch.planes.len() {
            let plane = &branch.planes[slot];
            if plane.value.is_none() {
                continue;
            }
            self.pad_to(slot + 1);
            if self.planes[slot].value.is_some() {
                return Err("branch allocation identity collision".into());
            }
            self.planes[slot] = plane.clone();
            imported.push(PlaneId {
                owner: self.owner,
                slot,
            });
        }
        Ok(imported)
    }

    pub fn borrow(&self, id: PlaneId) -> Result<Reference, String> {
        if id.owner != self.owner {
            return Err("plane belongs to a different arena".into());
        }
        let p = self.planes.get(id.slot).ok_or("unknown plane")?;
        if p.value.is_none() {
            return Err("cannot reference shape(T): plane is moved or dropped".into());
        }
        Ok(Reference {
            owner: self.owner,
            slot: id.slot,
            generation: p.generation,
        })
    }

    pub fn get(&self, id: PlaneId) -> Result<&T, String> {
        if id.owner != self.owner {
            return Err("plane belongs to a different arena".into());
        }
        self.planes
            .get(id.slot)
            .and_then(|p| p.value.as_ref())
            .ok_or_else(|| "use of shape(T): plane is moved or dropped".into())
    }

    pub fn read(&self, reference: Reference) -> Result<&T, String> {
        if reference.owner != self.owner {
            return Err("reference belongs to a different arena".into());
        }
        let p = self
            .planes
            .get(reference.slot)
            .ok_or("unknown reference plane")?;
        if reference.generation != p.generation || p.value.is_none() {
            return Err(
                "reference has type never: its plane was replaced, moved, or dropped".into(),
            );
        }
        p.value.as_ref().ok_or_else(|| "dropped plane".into())
    }

    pub fn plane(&self, reference: Reference) -> Result<PlaneId, String> {
        self.read(reference)?;
        Ok(PlaneId {
            owner: self.owner,
            slot: reference.slot,
        })
    }

    pub fn write(&mut self, id: PlaneId, value: T, replace: bool) -> Result<(), String> {
        if id.owner != self.owner {
            return Err("plane belongs to a different arena".into());
        }
        let p = self.planes.get_mut(id.slot).ok_or("unknown plane")?;
        if (replace || p.value.is_none()) && !p.ownership.is_unique() {
            return Err("replacing a shared plane requires recovering its unique owner".into());
        }
        if replace || p.value.is_none() {
            p.generation = p
                .generation
                .checked_add(1)
                .ok_or("plane generation exhausted")?;
        }
        p.value = Some(value);
        Ok(())
    }

    pub fn take(&mut self, id: PlaneId) -> Result<T, String> {
        if id.owner != self.owner {
            return Err("plane belongs to a different arena".into());
        }
        let p = self.planes.get_mut(id.slot).ok_or("unknown plane")?;
        if p.value.is_none() {
            return Err("cannot move shape(T)".into());
        }
        if !p.ownership.is_unique() {
            return Err(
                "moving or dropping a shared plane requires recovering its unique owner".into(),
            );
        }
        p.generation = p
            .generation
            .checked_add(1)
            .ok_or("plane generation exhausted")?;
        p.value.take().ok_or_else(|| "cannot move shape(T)".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn branch_allocations_keep_distinct_identities_after_restore_and_join() {
        let mut base = Memory::default();
        let original = base.allocate(7).unwrap();
        let mut original_world = base.snapshot();
        let mut left = base.snapshot();
        let mut right = base.snapshot();
        let a = left.allocate(41).unwrap();
        let b = right.allocate(42).unwrap();
        assert_ne!(a, b);
        let old_left = left.borrow(a).unwrap();
        assert!(right.read(old_left).is_err());
        assert_eq!(base.import_new_planes(&left, &original_world).unwrap(), [a]);
        // Use the original world as the import boundary for both branches.
        assert_eq!(
            base.import_new_planes(&right, &original_world).unwrap(),
            [b]
        );
        assert_eq!(*base.get(original).unwrap(), 7);
        assert_eq!(*base.read(old_left).unwrap(), 41);
        assert_eq!(*base.get(b).unwrap(), 42);
        let c = original_world.allocate(99).unwrap();
        assert_ne!(c, a);
        assert_ne!(c, b);
        assert!(original_world.read(old_left).is_err());
    }

    #[test]
    fn plane_import_rejects_collisions_and_foreign_arenas() {
        let base = Memory::default();
        let mut branch = base.snapshot();
        let id = branch.allocate(42).unwrap();
        let mut joined = base.snapshot();
        joined.import_new_planes(&branch, &base).unwrap();
        assert!(joined.import_new_planes(&branch, &base).is_err());
        let unrelated = Memory::<i32>::default();
        assert!(joined.import_new_planes(&unrelated, &base).is_err());
        branch.take(id).unwrap();
        let mut empty_join = base.snapshot();
        assert!(empty_join
            .import_new_planes(&branch, &base)
            .unwrap()
            .is_empty());
        assert!(empty_join.get(id).is_err());
    }

    #[test]
    fn proof_snapshots_isolate_branch_writes_and_consumption() {
        let mut original = Memory::default();
        let plane = original.allocate(7).unwrap();
        let reference = original.borrow(plane).unwrap();
        let mut branch = original.snapshot();
        branch.write(plane, 42, false).unwrap();
        assert_eq!(*original.read(reference).unwrap(), 7);
        assert_eq!(*branch.read(reference).unwrap(), 42);
        branch.take(plane).unwrap();
        assert!(branch.read(reference).is_err());
        assert_eq!(*original.read(reference).unwrap(), 7);
    }

    #[test]
    fn aliases_observe_scalar_writes() {
        let mut m = Memory::default();
        let p = m.allocate(1).unwrap();
        let a = m.borrow(p).unwrap();
        let b = m.borrow(p).unwrap();
        m.write(p, 2, false).unwrap();
        assert_eq!(*m.read(a).unwrap(), 2);
        assert_eq!(*m.read(b).unwrap(), 2);
    }

    #[test]
    fn replacing_or_moving_invalidates_all_aliases() {
        let mut m = Memory::default();
        let p = m.allocate(1).unwrap();
        let other = m.allocate(5).unwrap();
        let a = m.borrow(p).unwrap();
        let b = m.borrow(p).unwrap();
        let c = m.borrow(other).unwrap();
        m.write(p, 2, true).unwrap();
        assert!(m.read(a).is_err());
        assert!(m.read(b).is_err());
        assert!(m.read(c).is_ok());
        let d = m.borrow(p).unwrap();
        assert_eq!(m.take(p).unwrap(), 2);
        assert!(m.read(d).is_err());
        assert!(m.get(p).is_err());
        assert!(m.borrow(p).is_err());
        m.write(p, 3, false).unwrap();
        assert!(m.read(a).is_err());
        assert!(m.read(d).is_err());
        assert_eq!(*m.get(p).unwrap(), 3);
    }

    #[test]
    fn handles_cannot_cross_arenas() {
        let mut a = Memory::default();
        let mut b = Memory::default();
        let pa = a.allocate(1).unwrap();
        let pb = b.allocate(2).unwrap();
        let r = a.borrow(pa).unwrap();
        assert!(b.read(r).is_err());
        assert!(b.get(pa).is_err());
        assert!(b.borrow(pa).is_err());
        assert!(b.write(pa, 3, false).is_err());
        assert!(b.take(pa).is_err());
        assert_eq!(*b.get(pb).unwrap(), 2);
    }
}
