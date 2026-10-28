use super::*;

#[test]
fn early_ownership_counts_immediately_without_early_access_or_drop_authority() {
    let mut memory = Memory::default();
    let plane = memory.allocate(42).unwrap();
    let owner = memory.share_owner(plane).unwrap();
    let reference = owner.reference();
    let before = memory.owner_census(reference).unwrap();
    let early = memory.begin_owner(owner).unwrap();
    assert_eq!(memory.owner_count(reference).unwrap(), 2);
    assert!(!memory.census_is_current(before));
    assert!(memory.require_materialized_owners().is_err());
    assert!(memory.recover_unique_owner(owner).is_err());
    assert!(memory.take(plane).is_err());
    assert!(memory.write(plane, 7, true).is_err());
    let forged = OwnedReference {
        reference: early.reference,
        token: early.token,
    };
    let census = memory.owner_census(reference).unwrap();
    assert!(memory.borrow_owned(forged).is_err());
    assert!(memory.release_owner(forged).is_err());
    assert!(memory.duplicate_owner(forged).is_err());
    assert!(memory.recover_unique_owner(forged).is_err());
    assert!(memory.census_is_current(census));
    let actual = memory.materialize_owner(early).unwrap();
    assert_eq!(memory.owner_count(reference).unwrap(), 2);
    assert!(memory.census_is_current(census));
    assert_eq!(memory.borrow_owned(actual).unwrap(), reference);
    memory.require_materialized_owners().unwrap();
    assert!(memory.materialize_owner(early).is_err());
    assert!(memory.census_is_current(census));
    memory.release_owner(owner).unwrap();
    let sole = memory.owner_census(reference).unwrap();
    assert_eq!(memory.recover_unique_owner_at(actual, sole).unwrap(), plane);
    assert_eq!(memory.take(plane).unwrap(), 42);
}

#[test]
fn a_future_owner_keeps_storage_alive_after_the_originating_owner_is_gone() {
    let mut memory = Memory::default();
    let plane = memory.allocate(42).unwrap();
    let owner = memory.share_owner(plane).unwrap();
    let reference = owner.reference();
    let early = memory.begin_owner(owner).unwrap();
    memory.release_owner(owner).unwrap();
    assert_eq!(memory.owner_count(reference).unwrap(), 1);
    assert!(memory.borrow_owned(owner).is_err());
    assert!(memory.recover_unique_owner(owner).is_err());
    assert!(memory.take(plane).is_err());
    assert!(memory.require_materialized_owners().is_err());
    let actual = memory.materialize_owner(early).unwrap();
    assert_eq!(memory.owner_count(reference).unwrap(), 1);
    memory.require_materialized_owners().unwrap();
    assert_eq!(memory.recover_unique_owner(actual).unwrap(), plane);
    assert_eq!(memory.take(plane).unwrap(), 42);
    assert!(memory.read(reference).is_err());
    assert!(memory.materialize_owner(early).is_err());
}

#[test]
fn fulfillment_checks_the_allocation_arena_and_generation() {
    let mut memory = Memory::default();
    let plane = memory.allocate(42).unwrap();
    let owner = memory.share_owner(plane).unwrap();
    let early = memory.begin_owner(owner).unwrap();
    let other_plane = memory.allocate(7).unwrap();
    let other = memory.share_owner(other_plane).unwrap();
    let before = memory.owner_census(owner.reference()).unwrap();
    let wrong_plane = EarlyOwner {
        reference: other.reference(),
        ..early
    };
    assert!(memory.materialize_owner(wrong_plane).is_err());
    let wrong_token = EarlyOwner {
        token: other.token,
        ..early
    };
    assert!(memory.materialize_owner(wrong_token).is_err());
    let mut foreign = Memory::default();
    let foreign_plane = foreign.allocate(42).unwrap();
    foreign.share_owner(foreign_plane).unwrap();
    assert!(foreign.materialize_owner(early).is_err());
    assert!(foreign.begin_owner(owner).is_err());
    assert!(memory.census_is_current(before));
    let actual = memory.materialize_owner(early).unwrap();
    memory.release_owner(owner).unwrap();
    memory.recover_unique_owner(actual).unwrap();
    memory.take(plane).unwrap();
    memory.write(plane, 99, false).unwrap();
    assert!(memory.materialize_owner(early).is_err());
    assert_eq!(*memory.read(memory.borrow(plane).unwrap()).unwrap(), 99);
}

#[test]
fn branch_joins_preserve_fulfillment_and_reject_a_path_with_an_unfulfilled_owner() {
    let mut memory = Memory::default();
    let plane = memory.allocate(42).unwrap();
    let owner = memory.share_owner(plane).unwrap();
    let early = memory.begin_owner(owner).unwrap();
    let base = memory.snapshot();
    let mut left = base.snapshot();
    let mut right = base.snapshot();
    let a = left.materialize_owner(early).unwrap();
    assert!(memory.join_ownership(&base, &left, &right).is_err());
    assert!(memory.require_materialized_owners().is_err());
    let b = right.materialize_owner(early).unwrap();
    assert_eq!(a, b);
    let prior = memory.owner_census(owner.reference()).unwrap();
    memory.join_ownership(&base, &left, &right).unwrap();
    memory.require_materialized_owners().unwrap();
    assert!(memory.borrow_owned(a).is_ok());
    assert_eq!(memory.owner_count(owner.reference()).unwrap(), 2);
    assert!(!memory.census_is_current(prior));
    assert!(memory.materialize_owner(early).is_err());
    // A completion in one snapshot cannot fulfill the saved snapshot's promise.
    assert!(base.require_materialized_owners().is_err());
}

#[derive(Clone, Copy)]
enum Capability {
    Active(OwnedReference),
    Early(EarlyOwner),
    Released(OwnedReference),
}

#[test]
fn short_owner_histories_agree_with_an_independent_lifetime_oracle() {
    fn explore(memory: &Memory<usize>, reference: Reference, caps: &[Capability], depth: usize) {
        let count = caps
            .iter()
            .filter(|cap| !matches!(cap, Capability::Released(_)))
            .count();
        let pending = caps.iter().any(|cap| matches!(cap, Capability::Early(_)));
        assert_eq!(memory.owner_count(reference).unwrap(), count);
        assert_eq!(memory.require_materialized_owners().is_err(), pending);
        for (index, cap) in caps.iter().enumerate() {
            match *cap {
                Capability::Active(owner) => {
                    assert!(memory.borrow_owned(owner).is_ok());
                    let mut recovered = memory.snapshot();
                    assert_eq!(recovered.recover_unique_owner(owner).is_ok(), count == 1);
                    if depth == 0 {
                        continue;
                    }
                    let mut started = memory.snapshot();
                    let early = started.begin_owner(owner).unwrap();
                    let mut next = caps.to_vec();
                    next.push(Capability::Early(early));
                    explore(&started, reference, &next, depth - 1);
                    let mut released = memory.snapshot();
                    released.release_owner(owner).unwrap();
                    let mut next = caps.to_vec();
                    next[index] = Capability::Released(owner);
                    explore(&released, reference, &next, depth - 1);
                }
                Capability::Early(early) => {
                    let forged = OwnedReference {
                        reference: early.reference,
                        token: early.token,
                    };
                    assert!(memory.borrow_owned(forged).is_err());
                    let mut dropped = memory.snapshot();
                    assert!(dropped.release_owner(forged).is_err());
                    assert_eq!(dropped.owner_count(reference).unwrap(), count);
                    if depth == 0 {
                        continue;
                    }
                    let mut completed = memory.snapshot();
                    let owner = completed.materialize_owner(early).unwrap();
                    let mut next = caps.to_vec();
                    next[index] = Capability::Active(owner);
                    explore(&completed, reference, &next, depth - 1);
                }
                Capability::Released(owner) => {
                    assert!(memory.borrow_owned(owner).is_err());
                    let mut invalid = memory.snapshot();
                    assert!(invalid.begin_owner(owner).is_err());
                    assert!(invalid.release_owner(owner).is_err());
                    assert_eq!(invalid.owner_count(reference).unwrap(), count);
                }
            }
        }
    }
    let mut memory = Memory::default();
    let plane = memory.allocate(42usize).unwrap();
    let owner = memory.share_owner(plane).unwrap();
    explore(&memory, owner.reference(), &[Capability::Active(owner)], 6);
}

#[test]
fn nested_scopes_preserve_caller_promises_but_cannot_abandon_new_owners() {
    let mut memory = Memory::default();
    let plane = memory.allocate(42).unwrap();
    let owner = memory.share_owner(plane).unwrap();
    let outer = memory.owner_scope();
    let first = memory.begin_owner(owner).unwrap();
    let nested = memory.owner_scope();
    memory.require_owner_scope(&nested).unwrap();
    assert!(memory.require_owner_scope(&outer).is_err());
    let second = memory.begin_owner(owner).unwrap();
    assert!(memory.require_owner_scope(&nested).is_err());
    memory.materialize_owner(second).unwrap();
    memory.require_owner_scope(&nested).unwrap();
    assert!(memory.require_owner_scope(&outer).is_err());
    memory.materialize_owner(first).unwrap();
    memory.require_owner_scope(&outer).unwrap();
    assert!(Memory::<usize>::default()
        .require_owner_scope(&outer)
        .is_err());
}

#[test]
fn ordinary_copies_fulfill_nested_obligations_before_caller_obligations() {
    let mut memory = Memory::default();
    let plane = memory.allocate(42).unwrap();
    let owner = memory.share_owner(plane).unwrap();
    let outer = memory.begin_owner(owner).unwrap();
    let nested = memory.owner_scope();
    let inner = memory.begin_owner(owner).unwrap();
    let census = memory.owner_census(owner.reference()).unwrap();
    let copy = memory.copy_owner(owner).unwrap();
    assert!(!copy.started_lifetime());
    assert_eq!(copy.owner().token, inner.token);
    memory.require_owner_scope(&nested).unwrap();
    assert!(memory.require_materialized_owners().is_err());
    assert!(memory.census_is_current(census));
    let next = memory.copy_owner(owner).unwrap();
    assert!(!next.started_lifetime());
    assert_eq!(next.owner().token, outer.token);
    memory.require_materialized_owners().unwrap();
    assert!(memory.census_is_current(census));
    let extra = memory.copy_owner(owner).unwrap();
    assert!(extra.started_lifetime());
    assert_eq!(memory.owner_count(owner.reference()).unwrap(), 4);
    assert!(!memory.census_is_current(census));
}

#[test]
fn many_live_pointers_do_not_hide_pending_tokens_in_this_or_another_plane() {
    let mut memory = Memory::default();
    let origin = memory.allocate(42).unwrap();
    let origin = memory.share_owner(origin).unwrap();
    let waiting = memory.begin_owner(origin).unwrap();
    let inherited = memory.owner_scope();
    let other = memory.allocate(7).unwrap();
    let other = memory.share_owner(other).unwrap();
    let mut copies = Vec::new();
    for _ in 0..20_000 {
        assert!(!memory.has_early_owner(other).unwrap());
        let copy = memory.copy_owner(other).unwrap();
        assert!(copy.started_lifetime());
        copies.push(copy.owner());
    }
    let nested = memory.begin_owner(other).unwrap();
    let before = memory.owner_census(other.reference()).unwrap();
    assert!(memory.require_owner_scope(&inherited).is_err());
    let completed = memory.copy_owner(other).unwrap();
    assert!(!completed.started_lifetime());
    assert_eq!(completed.owner().token, nested.token);
    assert!(memory.census_is_current(before));
    assert!(!memory.has_early_owner(other).unwrap());
    memory.require_owner_scope(&inherited).unwrap();
    let caller_copy = memory.copy_owner(origin).unwrap();
    assert!(!caller_copy.started_lifetime());
    assert_eq!(caller_copy.owner().token, waiting.token);
    memory.require_materialized_owners().unwrap();
    assert_eq!(
        memory.owner_count(other.reference()).unwrap(),
        copies.len() + 2
    );
    for copy in copies {
        memory.release_owner(copy).unwrap();
    }
    memory.release_owner(completed.owner()).unwrap();
    let plane = memory.recover_unique_owner(other).unwrap();
    assert_eq!(memory.take(plane).unwrap(), 7);
    memory.release_owner(caller_copy.owner()).unwrap();
    let plane = memory.recover_unique_owner(origin).unwrap();
    assert_eq!(memory.take(plane).unwrap(), 42);
}
