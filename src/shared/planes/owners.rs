//! Generic owner identities for one plane. These are host-side semantic handles,
//! not an Rc counter or a source-language owner type. Copying a handle denotes
//! the same token; only duplicate_owner creates another owner.

use super::*;
use std::collections::BTreeMap;

mod census;
mod early;
mod joins;
use census::fresh_revision;
pub use census::OwnerCensus;
pub use early::{EarlyOwner, OwnerCopy, OwnerScope};

static NEXT_OWNER: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OwnedReference {
    reference: Reference,
    token: u64,
}

impl OwnedReference {
    /// Observe the pointer identity without granting the token's authority.
    /// Memory reads still check generation/liveness; owner operations check token membership.
    pub fn reference(self) -> Reference {
        self.reference
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Ownership {
    Unique,
    Shared(BTreeMap<u64, OwnerState>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum OwnerState {
    Early,
    Materialized,
}

impl Ownership {
    pub(super) fn early_count(&self) -> usize {
        match self {
            Self::Unique => 0,
            Self::Shared(tokens) => tokens
                .values()
                .filter(|state| **state == OwnerState::Early)
                .count(),
        }
    }

    pub(super) fn is_unique(&self) -> bool {
        matches!(self, Self::Unique)
    }
}

fn fresh_token() -> Result<u64, String> {
    NEXT_OWNER
        .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
            next.checked_add(1)
        })
        .map_err(|_| "owner identity exhausted".into())
}

impl<T> Memory<T> {
    /// Transfer the existing unique plane owner into a tracked owning reference.
    /// A borrowed PlaneId is not a source-level right to invoke this operation;
    /// the verifier must check the corresponding unique binding is consumed.
    pub fn share_owner(&mut self, id: PlaneId) -> Result<OwnedReference, String> {
        let reference = self.borrow(id)?;
        if !self.planes[id.slot].ownership.is_unique() {
            return Err("plane is already managed by owning references".into());
        }
        let token = fresh_token()?;
        let revision = fresh_revision()?;
        self.planes[id.slot].ownership =
            Ownership::Shared(BTreeMap::from([(token, OwnerState::Materialized)]));
        self.planes[id.slot].census_revision = revision;
        Ok(OwnedReference { reference, token })
    }

    fn owner_plane(&self, owner: OwnedReference) -> Result<PlaneId, String> {
        let id = self.plane(owner.reference)?;
        match &self.planes[id.slot].ownership {
            Ownership::Shared(tokens)
                if tokens.get(&owner.token) == Some(&OwnerState::Materialized) =>
            {
                Ok(id)
            }
            _ => Err("owning reference was consumed or does not belong to this plane".into()),
        }
    }

    pub fn borrow_owned(&self, owner: OwnedReference) -> Result<Reference, String> {
        self.owner_plane(owner)?;
        Ok(owner.reference)
    }

    pub fn duplicate_owner(&mut self, owner: OwnedReference) -> Result<OwnedReference, String> {
        let early = self.begin_owner(owner)?;
        self.materialize_owner(early)
    }

    /// Consume a lifetime claim, without dropping the allocation's payload.
    /// Releasing the final claim leaks the allocation; it does not create a new
    /// right to reclaim it through an old PlaneId or a borrowed reference.
    pub fn release_owner(&mut self, owner: OwnedReference) -> Result<(), String> {
        let id = self.owner_plane(owner)?;
        let revision = fresh_revision()?;
        let Ownership::Shared(tokens) = &mut self.planes[id.slot].ownership else {
            unreachable!()
        };
        tokens.remove(&owner.token);
        self.planes[id.slot].census_revision = revision;
        Ok(())
    }

    /// Consume the sole tracked owner and recover the ordinary unique plane.
    /// Payload identity/generation stays unchanged until that plane is dropped.
    pub fn recover_unique_owner(&mut self, owner: OwnedReference) -> Result<PlaneId, String> {
        let id = self.owner_plane(owner)?;
        let Ownership::Shared(tokens) = &self.planes[id.slot].ownership else {
            unreachable!()
        };
        if tokens.len() != 1 {
            return Err("unique recovery requires exactly one owner".into());
        }
        let revision = fresh_revision()?;
        self.planes[id.slot].ownership = Ownership::Unique;
        self.planes[id.slot].census_revision = revision;
        Ok(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn borrows_do_not_count_and_only_the_last_owner_recovers_uniqueness() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let borrow = memory.borrow(plane).unwrap();
        let first = memory.share_owner(plane).unwrap();
        assert_eq!(memory.owner_count(borrow).unwrap(), 1);
        assert_eq!(memory.borrow_owned(first).unwrap(), borrow);
        let second = memory.duplicate_owner(first).unwrap();
        assert_eq!(memory.owner_count(borrow).unwrap(), 2);
        assert!(memory.recover_unique_owner(first).is_err());
        assert!(memory.take(plane).is_err());
        assert!(memory.write(plane, 7, true).is_err());
        assert_eq!(*memory.read(borrow).unwrap(), 42);
        memory.write(plane, 7, false).unwrap();
        assert_eq!(*memory.read(borrow).unwrap(), 7);
        memory.release_owner(first).unwrap();
        assert!(memory.borrow_owned(first).is_err());
        assert!(memory.release_owner(first).is_err());
        assert_eq!(memory.owner_count(borrow).unwrap(), 1);
        assert_eq!(memory.recover_unique_owner(second).unwrap(), plane);
        assert!(memory.borrow_owned(second).is_err());
        assert_eq!(*memory.read(borrow).unwrap(), 7);
        assert_eq!(memory.take(plane).unwrap(), 7);
        assert!(memory.read(borrow).is_err());
    }

    #[test]
    fn no_owner_can_be_resurrected_after_its_final_release() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let owner = memory.share_owner(plane).unwrap();
        let borrow = memory.borrow_owned(owner).unwrap();
        memory.release_owner(owner).unwrap();
        assert_eq!(memory.owner_count(borrow).unwrap(), 0);
        assert!(memory.duplicate_owner(owner).is_err());
        assert!(memory.recover_unique_owner(owner).is_err());
        assert!(memory.share_owner(plane).is_err());
        assert!(memory.take(plane).is_err());
        assert_eq!(*memory.read(borrow).unwrap(), 42); // leaked, still allocated
    }

    #[test]
    fn consumed_tokens_cannot_reappear_after_unique_recovery_and_resharing() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let old = memory.share_owner(plane).unwrap();
        let plane = memory.recover_unique_owner(old).unwrap();
        let current = memory.share_owner(plane).unwrap();
        assert_ne!(old, current);
        assert!(memory.borrow_owned(old).is_err());
        assert!(memory.release_owner(old).is_err());
        assert!(memory.borrow_owned(current).is_ok());
    }

    #[test]
    fn token_identity_generation_and_arena_are_checked_independently() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let owner = memory.share_owner(plane).unwrap();
        let forged = OwnedReference {
            token: owner.token + 1,
            ..owner
        };
        assert!(memory.duplicate_owner(forged).is_err());
        let other_plane = memory.allocate(7).unwrap();
        let wrong_plane = OwnedReference {
            reference: memory.borrow(other_plane).unwrap(),
            ..owner
        };
        assert!(memory.recover_unique_owner(wrong_plane).is_err());
        let mut other = Memory::default();
        other.allocate(9).unwrap();
        assert!(other.release_owner(owner).is_err());
        let plane = memory.recover_unique_owner(owner).unwrap();
        memory.take(plane).unwrap();
        memory.write(plane, 99, false).unwrap();
        assert!(memory.borrow_owned(owner).is_err());
    }

    #[test]
    fn owner_census_snapshots_do_not_share_mutable_state_or_new_token_ids() {
        let mut original = Memory::default();
        let plane = original.allocate(42).unwrap();
        let first = original.share_owner(plane).unwrap();
        let borrow = original.borrow_owned(first).unwrap();
        let mut branch = original.snapshot();
        let branch_owner = branch.duplicate_owner(first).unwrap();
        let original_owner = original.duplicate_owner(first).unwrap();
        assert_ne!(branch_owner, original_owner);
        assert!(original.borrow_owned(branch_owner).is_err());
        assert!(branch.borrow_owned(original_owner).is_err());
        branch.release_owner(first).unwrap();
        assert_eq!(branch.owner_count(borrow).unwrap(), 1);
        assert_eq!(original.owner_count(borrow).unwrap(), 2);
    }
}
