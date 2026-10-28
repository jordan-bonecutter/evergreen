//! State-indexed owner observations. Payload and census revisions are separate.

use super::*;

static NEXT_CENSUS: AtomicU64 = AtomicU64::new(1);

/// An immutable observation of one live plane's owner census. It grants no
/// ownership. The revision distinguishes count-preserving transitions and ABA.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OwnerCensus {
    reference: Reference,
    revision: u64,
    count: usize,
}

impl OwnerCensus {
    pub fn count(self) -> usize {
        self.count
    }
}

pub(super) fn fresh_revision() -> Result<u64, String> {
    NEXT_CENSUS
        .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
            next.checked_add(1)
        })
        .map_err(|_| "owner census revision exhausted".into())
}

impl<T> Memory<T> {
    /// An observation does not register an owner or consume the observed token.
    pub fn owner_count(&self, reference: Reference) -> Result<usize, String> {
        Ok(self.owner_census(reference)?.count())
    }

    pub fn owner_census(&self, reference: Reference) -> Result<OwnerCensus, String> {
        let id = self.plane(reference)?;
        let count = match &self.planes[id.slot].ownership {
            Ownership::Unique => 1,
            Ownership::Shared(tokens) => tokens.len()?,
        };
        Ok(OwnerCensus {
            reference,
            revision: self.planes[id.slot].census_revision,
            count,
        })
    }

    /// Payload writes and ordinary borrows do not change this observation.
    /// Ownership transitions, generation changes, and foreign arenas invalidate it.
    pub fn census_is_current(&self, census: OwnerCensus) -> bool {
        self.owner_census(census.reference)
            .is_ok_and(|current| current == census)
    }

    /// Recover only under an observation of this plane's current sole owner.
    /// Supplying a census does not replace the live owning token requirement.
    pub fn recover_unique_owner_at(
        &mut self,
        owner: OwnedReference,
        census: OwnerCensus,
    ) -> Result<PlaneId, String> {
        if census.reference != owner.reference
            || census.count != 1
            || !self.census_is_current(census)
        {
            return Err(
                "unique recovery requires a current sole-owner census for the same plane".into(),
            );
        }
        self.recover_unique_owner(owner)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn count_preserving_transitions_do_not_revive_old_census_observations() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let reference = memory.borrow(plane).unwrap();
        let unique = memory.owner_census(reference).unwrap();
        let owner = memory.share_owner(plane).unwrap();
        assert_eq!(unique.count(), 1);
        assert!(!memory.census_is_current(unique));
        let sole = memory.owner_census(reference).unwrap();
        let second = memory.duplicate_owner(owner).unwrap();
        assert!(!memory.census_is_current(sole));
        memory.release_owner(second).unwrap();
        assert_eq!(memory.owner_count(reference).unwrap(), sole.count());
        assert!(!memory.census_is_current(sole));
        assert!(memory.recover_unique_owner_at(owner, sole).is_err());
        let fresh = memory.owner_census(reference).unwrap();
        assert!(memory.census_is_current(fresh));
        assert_eq!(memory.recover_unique_owner_at(owner, fresh).unwrap(), plane);
        assert!(!memory.census_is_current(fresh));
        assert_eq!(*memory.read(reference).unwrap(), 42);
    }

    #[test]
    fn census_dependencies_are_independent_of_payload_and_other_planes() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let owner = memory.share_owner(plane).unwrap();
        let reference = memory.borrow_owned(owner).unwrap();
        let census = memory.owner_census(reference).unwrap();
        for _ in 0..4 {
            assert_eq!(memory.borrow(plane).unwrap(), reference);
            memory.write(plane, 7, false).unwrap();
            let other = memory.allocate(1).unwrap();
            let token = memory.share_owner(other).unwrap();
            let another = memory.duplicate_owner(token).unwrap();
            memory.release_owner(another).unwrap();
            let other = memory.recover_unique_owner(token).unwrap();
            memory.take(other).unwrap();
            assert!(memory.census_is_current(census));
        }
        assert_eq!(
            memory.recover_unique_owner_at(owner, census).unwrap(),
            plane
        );
    }

    #[test]
    fn census_recovery_needs_a_live_token_for_the_same_plane() {
        let mut memory = Memory::default();
        let first_plane = memory.allocate(42).unwrap();
        let first = memory.share_owner(first_plane).unwrap();
        let first_ref = memory.borrow_owned(first).unwrap();
        let second_plane = memory.allocate(7).unwrap();
        let second = memory.share_owner(second_plane).unwrap();
        let census = memory.owner_census(first_ref).unwrap();
        assert!(memory.recover_unique_owner_at(second, census).is_err());
        assert!(memory.census_is_current(census));
        let forged = OwnedReference {
            token: second.token,
            ..first
        };
        assert!(memory.recover_unique_owner_at(forged, census).is_err());
        assert!(memory.census_is_current(census));
        let duplicate = memory.duplicate_owner(first).unwrap();
        let two = memory.owner_census(first_ref).unwrap();
        assert_eq!(two.count(), 2);
        assert!(memory.recover_unique_owner_at(first, two).is_err());
        assert!(memory.census_is_current(two));
        memory.release_owner(first).unwrap();
        let sole = memory.owner_census(first_ref).unwrap();
        assert!(memory.recover_unique_owner_at(first, sole).is_err());
        assert!(memory.census_is_current(sole));
        assert_eq!(
            memory.recover_unique_owner_at(duplicate, sole).unwrap(),
            first_plane
        );
    }

    #[test]
    fn branch_censuses_use_fresh_revisions_even_when_the_counts_reconverge() {
        let mut original = Memory::default();
        let plane = original.allocate(42).unwrap();
        let owner = original.share_owner(plane).unwrap();
        let reference = original.borrow_owned(owner).unwrap();
        let before = original.owner_census(reference).unwrap();
        let mut left = original.snapshot();
        let mut right = original.snapshot();
        let a = left.duplicate_owner(owner).unwrap();
        let b = right.duplicate_owner(owner).unwrap();
        left.release_owner(a).unwrap();
        right.release_owner(b).unwrap();
        let left_census = left.owner_census(reference).unwrap();
        let right_census = right.owner_census(reference).unwrap();
        assert_eq!(left_census.count(), right_census.count());
        assert_ne!(left_census, right_census);
        assert!(!left.census_is_current(before));
        assert!(!right.census_is_current(before));
        assert!(!left.census_is_current(right_census));
        assert!(!right.census_is_current(left_census));
        assert!(original.census_is_current(before));
    }

    #[test]
    fn replaced_and_foreign_planes_cannot_match_a_saved_census() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let reference = memory.borrow(plane).unwrap();
        let census = memory.owner_census(reference).unwrap();
        let mut foreign = Memory::default();
        foreign.allocate(42).unwrap();
        assert!(!foreign.census_is_current(census));
        memory.take(plane).unwrap();
        assert!(!memory.census_is_current(census));
        memory.write(plane, 42, false).unwrap();
        let next = memory.owner_census(memory.borrow(plane).unwrap()).unwrap();
        assert_eq!(census.count(), next.count());
        assert_ne!(census, next);
        assert!(!memory.census_is_current(census));
    }
}
