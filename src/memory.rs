//! Generation-based plane store shared by elaboration and reference execution.
//! Handles are opaque; invalidation is checked independently of the prover.
use std::sync::atomic::{AtomicU64, Ordering};
static NEXT_ARENA: AtomicU64 = AtomicU64::new(1);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Projection {
    Field(String),
    Index(usize),
}
#[derive(Clone, Debug)]
struct Plane<T> {
    generation: u64,
    value: Option<T>,
}
#[derive(Debug)]
pub struct Memory<T> {
    owner: u64,
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
            planes: Vec::new(),
        }
    }
}
impl<T> Memory<T> {
    pub fn allocate(&mut self, value: T) -> Result<PlaneId, String> {
        if self.planes.len() >= 100_000 {
            return Err("plane allocation limit reached".into());
        }
        let id = PlaneId {
            owner: self.owner,
            slot: self.planes.len(),
        };
        self.planes.push(Plane {
            generation: 0,
            value: Some(value),
        });
        Ok(id)
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
