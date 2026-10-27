use super::*;

#[test]
fn source_allocation_credits_preserve_real_authority_and_plane_identity() {
    let source = include_str!("../../../../examples/allocation_credits.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn allocation_credits_cannot_be_copied_forged_or_recovered_while_shared() {
    for source in [
        "fn main() {let credit = allocation_credits::Credit {allocation: share_owner(alloc(42))};}",
        "impl Copy for allocation_credits::Credit {} fn main() {}",
        "fn main() {let credit = allocation_credits::attach(alloc(42)); let moved = credit; let again = credit;}",
        "fn main() {let first = allocation_credits::attach(alloc(42)); let second = allocation_credits::duplicate(&first); let unique = allocation_credits::recover(first);}",
        "fn main() {let first = allocation_credits::attach(alloc(42)); let second = allocation_credits::duplicate(&first); proof lie: allocation_credits::outstanding(&first) == 1 by {trustme}; let unique = allocation_credits::recover(first);}",
        "fn main() {let first = allocation_credits::attach(alloc(42)); let second = allocation_credits::attach(alloc(7)); let wrong = allocation_credits::merge(first, second);}",
        "fn main() -> usize {let credit = allocation_credits::attach(alloc(42)); let target = allocation_credits::target(&credit); drop(credit); *target}",
        "fn main() {let first = allocation_credits::attach(alloc(42)); let second = allocation_credits::duplicate(&first);}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn entry_reference_observations_preserve_identity_and_read_current_contents() {
    for source in [
        "fn identity(r: &usize) -> &usize borrows(r) {r} fn inspect(r: &usize) {proof original: old(identity(r)) == r;} fn main() -> usize {let value: usize = 42; inspect(&value); value}",
        "fn inspect(a: &usize) {proof same_slot: old(&a) == &a;} fn main() -> usize {let value: usize = 42; inspect(&value); value}",
        "fn identity(value: &usize) -> &usize borrows(value) {value} fn inspect(value: &usize, replacement: &usize) {ideal let saved = old(identity(value)); value = replacement; proof original: saved == old(value);} fn main() -> usize {let a: usize = 7; let b: usize = 42; inspect(&a, &b); b}",
        "fn inspect(value: usize) -> usize {ideal let address = old(&value); value = 42; proof same_slot: address == &value; proof live_contents: *address == 42; value} fn main() -> usize {inspect(7)}",
        "type Point struct {value: usize} fn project(point: &Point) -> &usize borrows(&point.value) {&point.value} fn inspect(point: Point) -> usize {ideal let saved = old(project(&point)); point.value = 42; proof live_contents: *saved == 42; point.value} fn main() -> usize {inspect(Point {value: 7})}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
    for source in [
        "type Point struct {value: usize} fn wrong() {ideal let saved = old(&Point {value: 42});}",
        "fn wrong() {let value: usize = 42; ideal let saved = old(&value);}",
        "fn wrong(a: &usize, b: &usize) where a != b {ideal let saved = old(&a); a = b; proof changed: *saved == old(a);}",
        "type Point struct {value: usize} fn wrong(point: Point) {ideal let address = old(&point); let moved = point; proof stale: address.value == 42;}",
        "fn change(value: &usize) -> &usize modifies(value) borrows(value) {*value = 42; value} fn wrong(value: &usize) {ideal let saved = old(change(value));}",
        "fn view(value: &owner(usize)) -> &usize borrows(&**value) {let temporary = duplicate_owner(value); release_owner(temporary); &**value} fn wrong(value: &owner(usize)) {ideal let saved = old(view(value));}",
        "fn observe(value: &owner(usize)) -> usize {let temporary = duplicate_owner(value); release_owner(temporary); 42} fn wrong(value: &owner(usize)) {ideal let saved = old(observe(value));}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn generic_owning_references_count_claims_and_recover_the_same_plane() {
    let source = include_str!("../../../../examples/owning_references.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn a_visible_input_owner_does_not_establish_uniqueness() {
    let source = "fn reclaim(value: owner(usize)) -> plane(usize) {recover_owner(value)} fn main() -> usize {42}";
    let error = verify(source).unwrap_err();
    assert!(error.contains("unique owner recovery"), "{error}");
    let valid = "fn reclaim(value: owner(usize)) -> plane(usize) where owners(value) == 1 {recover_owner(value)} fn main() -> usize {let unique: plane(usize) = alloc(42); let owned = share_owner(unique); let recovered = reclaim(owned); *recovered}";
    let (program, bundle) = prove(valid).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(valid, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let invalid = valid.replace(
        "let recovered = reclaim(owned);",
        "let another = duplicate_owner(&owned); let recovered = reclaim(owned);",
    );
    assert!(verify(&invalid)
        .unwrap_err()
        .contains("precondition of reclaim"));
}

#[test]
fn callee_cleanup_releases_only_its_claim_including_hidden_caller_owners() {
    let source = "fn release(value: owner(usize)) where owners(value) > 1 {release_owner(value);} fn main() -> usize {let unique: plane(usize) = alloc(42); let first = share_owner(unique); let second = duplicate_owner(&first); release(first); proof sole: owners(second) == 1; let recovered = recover_owner(second); *recovered}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn cloning_and_entry_snapshots_preserve_opaque_caller_counts() {
    let source = "fn duplicate(value: &owner(usize)) -> owner(usize) ensures owners(result) == old(owners(value)) + 1 {duplicate_owner(value)} fn main() -> usize {let unique: plane(usize) = alloc(42); let first = share_owner(unique); let second = duplicate(&first); proof shared: owners(first) == 2; release_owner(first); let recovered = recover_owner(second); *recovered}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn borrowed_views_survive_handle_moves_and_expire_after_final_destruction() {
    let source = "fn main() -> usize {let unique: plane(usize) = alloc(42); let first = share_owner(unique); let view = &*first; let second = duplicate_owner(&first); let moved = first; release_owner(moved); proof sole: owners(second) == 1; let recovered = recover_owner(second); *view}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let dead = source.replace(
        "let recovered = recover_owner(second);",
        "let recovered = recover_owner(second); drop(recovered);",
    );
    assert!(verify(&dead).is_err());
    let moved = source.replace("release_owner(moved);", "release_owner(first);");
    assert!(verify(&moved).is_err());
}

#[test]
fn census_admissions_expire_on_owner_transitions_even_when_the_count_returns() {
    for transition in [
        "let other = duplicate_owner(&value);",
        "let other = duplicate_owner(&value); release_owner(other);",
    ] {
        let source = format!("fn reclaim(value: owner(usize)) -> plane(usize) {{proof admitted: owners(value) == 1 by {{trustme}}; {transition} recover_owner(value)}} fn main() -> usize {{42}}");
        let error = verify(&source).unwrap_err();
        assert!(error.contains("unique owner recovery"), "{error}");
    }
}

#[test]
fn ownership_transitions_cannot_silently_break_a_nominal_invariant() {
    let prefix = "type Counted struct {count: usize, data: owner(usize)} where nat(count) == owners(data); fn duplicate(value: &owner(usize)) -> owner(usize) {duplicate_owner(value)}";
    for operation in ["duplicate_owner(&value.data)", "duplicate(&value.data)"] {
        let source = format!("{prefix} fn main() {{let unique: plane(usize) = alloc(42); let value = Counted {{count: 1, data: share_owner(unique)}}; let other = {operation};}}");
        assert!(verify(&source).is_err(), "accepted {operation}");
    }
}

#[test]
fn owners_cannot_be_forged_or_consumed_by_erased_execution() {
    for source in [
        "fn main() {let forged: owner(usize) = 42;}",
        "fn main() {let unique: plane(usize) = alloc(42); let owned = share_owner(unique); let count = owners(owned);}",
        "fn main() {let unique: plane(usize) = alloc(42); ideal let owned = share_owner(unique);}",
        "fn main() {let unique: plane(usize) = alloc(42); let owned = share_owner(unique); let recovered = recover_owner(&owned);}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn raw_owners_require_uniqueness_to_drop_and_cannot_release_the_last_claim() {
    for source in [
        "fn discard(value: owner(usize)) {}",
        "fn main() {let unique: plane(usize) = alloc(42); let first = share_owner(unique); let second = duplicate_owner(&first);}",
        "fn main() {let unique: plane(usize) = alloc(42); let owned = share_owner(unique); release_owner(owned);}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
    let source = "type Resource struct {value: usize} where value == 42; impl Drop for Resource {fn drop(self) {proof valid: self.value == 42;}} fn main() -> usize {let unique: plane(Resource) = alloc(Resource {value: 42}); let first = share_owner(unique); let second = duplicate_owner(&first); release_owner(first); second.value}";
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn ordinary_borrows_do_not_count_and_keep_the_original_allocation_provenance() {
    let source = "fn borrow(value: &owner(usize)) -> &usize borrows(&**value) {&**value} fn main() -> usize {let unique: plane(usize) = alloc(42); let first = share_owner(unique); let view = borrow(&first); let another_view = &*first; proof one: owners(first) == 1 && owners(view) == 1 && owners(another_view) == 1; let second = duplicate_owner(&first); release_owner(first); *view}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let invalid = source.replace(
        "release_owner(first); *view",
        "release_owner(first); drop(second); *view",
    );
    assert!(verify(&invalid).is_err());
}

#[test]
fn census_evidence_survives_payload_writes_without_gaining_extra_trust() {
    let source = "fn admitted(value: owner(usize)) -> plane(usize) {proof sole: owners(value) == 1 by {trustme}; *value = 7; recover_owner(value)} fn main() -> usize {42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(
        program
            .function_safety_assumptions("admitted")
            .unwrap()
            .count(),
        1
    );
    assert_eq!(
        program.function_safety_assumptions("main").unwrap().count(),
        0
    );
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn old_owner_views_are_observations_without_recreating_a_consumed_claim() {
    let source = "fn reclaim(value: owner(usize)) -> usize where owners(value) == 1 {let unique = recover_owner(value); proof entry_value: *old(value) == old(*value); *unique} fn main() -> usize {let unique: plane(usize) = alloc(42); reclaim(share_owner(unique))}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}
