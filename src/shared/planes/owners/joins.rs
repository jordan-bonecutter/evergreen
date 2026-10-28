//! Reconvergent token states. Different token sets need guarded capabilities,
//! even when their lengths or symbolic total counts happen to be equal.

use super::*;

impl<T> Memory<T> {
    pub(crate) fn join_ownership(
        &mut self,
        base: &Self,
        left: &Self,
        right: &Self,
    ) -> Result<(), String> {
        if [base.owner, left.owner, right.owner]
            .iter()
            .any(|owner| *owner != self.owner)
        {
            return Err("cannot join ownership from different plane arenas".into());
        }
        let mut updates = Vec::new();
        for (slot, original) in base.planes.iter().enumerate() {
            let destination = self.planes.get(slot).ok_or("missing join destination")?;
            if destination.generation != original.generation
                || destination.ownership != original.ownership
                || destination.census_revision != original.census_revision
            {
                return Err("ownership join destination is not the saved branch state".into());
            }
            let a = left.planes.get(slot).ok_or("missing left owner state")?;
            let b = right.planes.get(slot).ok_or("missing right owner state")?;
            if a.ownership != b.ownership {
                return Err(
                    "conditional owner tokens differ; guarded token joins are not implemented"
                        .into(),
                );
            }
            if a.ownership != original.ownership
                || a.census_revision != original.census_revision
                || b.census_revision != original.census_revision
            {
                // A count-preserving round trip still changes the census.
                // Neither predecessor's observation denotes the joined state.
                updates.push((slot, a.ownership.clone(), fresh_revision()?));
            }
        }
        let mut outstanding = self.early_owners;
        for (slot, ownership, _) in &updates {
            outstanding = outstanding
                .checked_sub(self.planes[*slot].ownership.early_count())
                .and_then(|count| count.checked_add(ownership.early_count()))
                .ok_or("joined early owner bookkeeping is inconsistent")?;
        }
        for (slot, ownership, revision) in updates {
            self.planes[slot].ownership = ownership;
            self.planes[slot].census_revision = revision;
        }
        self.early_owners = outstanding;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_releases_join_tokens_without_reviving_a_predecessor_census() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let first = memory.share_owner(plane).unwrap();
        let second = memory.duplicate_owner(first).unwrap();
        let reference = first.reference();
        let before = memory.owner_census(reference).unwrap();
        let base = memory.snapshot();
        let mut left = base.snapshot();
        let mut right = base.snapshot();
        left.release_owner(second).unwrap();
        right.release_owner(second).unwrap();
        let a = left.owner_census(reference).unwrap();
        let b = right.owner_census(reference).unwrap();

        memory.join_ownership(&base, &left, &right).unwrap();
        assert_eq!(memory.owner_count(reference).unwrap(), 1);
        assert!(memory.borrow_owned(first).is_ok());
        assert!(memory.borrow_owned(second).is_err());
        for stale in [before, a, b] {
            assert!(!memory.census_is_current(stale));
            assert!(memory.recover_unique_owner_at(first, stale).is_err());
        }
        let fresh = memory.owner_census(reference).unwrap();
        assert_eq!(memory.recover_unique_owner_at(first, fresh).unwrap(), plane);
    }

    #[test]
    fn a_round_trip_on_one_path_expires_the_unchanged_paths_observation() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let owner = memory.share_owner(plane).unwrap();
        let reference = owner.reference();
        let before = memory.owner_census(reference).unwrap();
        let base = memory.snapshot();
        let mut left = base.snapshot();
        let right = base.snapshot();
        let temporary = left.duplicate_owner(owner).unwrap();
        left.release_owner(temporary).unwrap();

        memory.join_ownership(&base, &left, &right).unwrap();
        assert_eq!(memory.owner_count(reference).unwrap(), 1);
        assert!(!memory.census_is_current(before));
        assert!(!memory.census_is_current(left.owner_census(reference).unwrap()));
        assert!(memory.borrow_owned(owner).is_ok());
        assert!(memory.borrow_owned(temporary).is_err());
    }

    #[test]
    fn equal_counts_do_not_join_different_live_tokens_or_foreign_arenas() {
        let mut memory = Memory::default();
        let plane = memory.allocate(42).unwrap();
        let first = memory.share_owner(plane).unwrap();
        let second = memory.duplicate_owner(first).unwrap();
        let before = memory.owner_census(first.reference()).unwrap();
        let base = memory.snapshot();
        let mut left = base.snapshot();
        let mut right = base.snapshot();
        left.release_owner(first).unwrap();
        right.release_owner(second).unwrap();
        assert!(memory.join_ownership(&base, &left, &right).is_err());
        assert!(memory.census_is_current(before));
        assert!(memory.borrow_owned(first).is_ok());
        assert!(memory.borrow_owned(second).is_ok());
        let foreign = Memory::default();
        assert!(memory.join_ownership(&base, &left, &foreign).is_err());
        assert!(memory.census_is_current(before));
    }
}
