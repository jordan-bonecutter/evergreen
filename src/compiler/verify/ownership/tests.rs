use super::*;
use crate::syntax::format::test_edit::SourceEdit;

#[test]
fn shared_pointer_values_copy_claims_and_move_to_unique_authority() {
    for source in [
        "fn main() -> usize {let first: shared(usize) = alloc(42); let slot = first; slot = first; proof two: owner_count(first) == 2; leak(slot); let final: unique(usize) = move(first); *final}",
        "fn main() -> usize {let first: shared(usize, 2) = alloc(2, 42); let second = first; leak(second); let final: unique(usize, 2) = move(first); (*final)[1]}",
        "fn main() -> usize {let first: shared(usize) = alloc(42); let second = first; proof two: owner_count(first) == 2; leak(second); proof one: owner_count(first) == 1; let final: unique(usize) = move(first); *final}",
        "fn main() -> usize {let first: shared(usize) = alloc(42); let view = &*first; leak(first); proof none: owner_count(view) == 0; *view}",
        "fn discard(value: shared(usize)) {} fn main() -> usize {let first: shared(usize) = alloc(42); discard(first); proof one: owner_count(first) == 1; let final: unique(usize) = move(first); *final}",
        "fn main() -> usize {let first: shared(usize) = alloc(42); let items = [first, first]; proof three: owner_count(first) == 3; let other = items; proof five: owner_count(first) == 5; leak(other); leak(items); let final: unique(usize) = move(first); *final}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42", "{source}");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
    for source in [
        "fn main() {let first: shared(usize) = alloc(42); let second = first; let final: unique(usize) = move(first);}",
        "fn main() {let first: shared(usize) = alloc(42); let final: unique(usize) = first;}",
        "fn main() {let first: shared(usize) = alloc(42); drop(first);}",
        "fn main() {let first: shared(usize) = alloc(42); let view = &*first; let final: unique(usize) = view;}",
        "fn main() {let first: shared(usize) = alloc(42); let final: unique(usize) = move(first); let second = first;}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn aggregate_and_temporary_shared_reads_have_exact_copy_effects() {
    for source in [
        "type Handle struct {data: shared(usize)} impl Copy for Handle {} fn main() -> usize {let original: shared(usize) = alloc(42); let handle = Handle {data: original}; let copy = handle; proof three: owner_count(original) == 3; leak(copy); leak(handle); let final: unique(usize) = move(original); *final}",
        "fn main() -> usize {let original: shared(usize) = alloc(42); let items = [original, original]; let selected = items[0]; proof four: owner_count(original) == 4; leak(selected); leak(items); let final: unique(usize) = move(original); *final}",
        "fn copy(value: &shared(usize)) -> shared(usize) {*value} fn main() -> usize {let original: shared(usize) = alloc(42); let view = &*copy(&original); proof one: owner_count(original) == 1; original; proof one_again: owner_count(original) == 1; let final: unique(usize) = move(original); *view}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
    let bad_copy = "type Counted struct {count: usize, data: shared(usize)} where nat(count) == owner_count(data); impl Copy for Counted {} fn main() {}";
    assert!(verify(bad_copy).unwrap_err().contains("Copy must preserve"));
}

#[test]
fn former_owner_operation_names_are_ordinary_source_functions() {
    let source = "fn share_owner(x: usize) -> usize {x} fn duplicate_owner(x: usize) -> usize {share_owner(x)} fn release_owner(x: usize) -> usize {duplicate_owner(x)} fn recover_owner(x: usize) -> usize {release_owner(x)} fn main() -> usize {recover_owner(42)}";
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
fn conditional_owner_releases_join_the_same_remaining_claims() {
    for source in [
        "fn release(value: shared(usize), flag: bool) where owner_count(value) > 1 {if flag {leak(value);} else {leak(value);}} fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let second = first; let view = &*first; release(move(second), true); proof sole: owner_count(first) == 1; *view}",
        "fn release(value: shared(usize), flag: bool) where owner_count(value) == 1 {if flag {let unique: unique(usize) = move(value); drop(unique);} else {let unique: unique(usize) = move(value); drop(unique);}} fn main() -> usize {let unique: unique(usize) = alloc(7); let value: shared(usize) = move(unique); release(move(value), false); 42}",
        "fn observe(value: &shared(usize), flag: bool) {if flag {let temporary = *value; leak(temporary);} else {}} fn main() -> usize {let unique: unique(usize) = alloc(42); let value: shared(usize) = move(unique); let view = &*value; observe(&value, true); proof sole: owner_count(value) == 1; *view}",
        "fn release(value: rc::Rc, flag: bool) where value.strong_count() > 1 {match flag {true => {value.release_nonfinal();}, false => {value.release_nonfinal();}}} fn main() -> usize {let first = rc::new(42); let second = first.clone(); release(move(second), false); proof sole: first.strong_count() == 1; *first.value()}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn conditional_owner_transitions_do_not_preserve_admissions_or_invent_tokens() {
    for transition in [
        "if flag {let temporary = value; leak(temporary);} else {}",
        "if flag {let temporary = value; leak(temporary);} else {let temporary = value; leak(temporary);}",
    ] {
        let source = format!("fn reclaim(value: shared(usize), flag: bool) -> unique(usize) {{proof admitted: owner_count(value) == 1 by {{trustme}}; {transition} move(value)}} fn main() -> usize {{42}}");
        let error = verify(&source).unwrap_err();
        assert!(error.contains("unique owner recovery"), "{error}");
    }
    for source in [
        "fn bad(first: shared(usize), second: shared(usize), flag: bool) where owner_count(first) > 1 && owner_count(second) > 1 {if flag {leak(first);} else {leak(second);} proof both_live: owner_count(first) > 0 && owner_count(second) > 0;}",
        "fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let second = first; if true {leak(second);} else {leak(second);} *second}",
        "fn main() -> usize {let unique: unique(usize) = alloc(42); let value: shared(usize) = move(unique); let view = &*value; if true {drop(value);} else {drop(value);} *view}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn conditional_owner_changes_keep_other_allocations_evidence_separate() {
    let source = "fn reclaim(value: shared(usize), flag: bool) -> unique(usize) {proof sole: owner_count(value) == 1 by {trustme}; let unique: unique(usize) = alloc(7); let other: shared(usize) = move(unique); if flag {let temporary = other; leak(temporary);} else {} leak(other); move(value)} fn main() -> usize {42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(
        program
            .function_safety_assumptions("reclaim")
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
fn source_rc_updates_a_real_counter_alongside_allocation_claims() {
    let source = include_str!("../../../../examples/rc.evg");
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}"));
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
fn source_rc_shares_generic_payloads_and_destroys_them_once() {
    for source in [
        "fn prepare() -> rc::Rc<unique(u8, 1000000000)> {let data: unique(u8, 1000000000) = alloc(1000000000, 0); rc::new::<unique(u8, 1000000000)>(data)} fn main() -> usize {42}",
        include_str!("../../../../examples/rc_generic.evg"),
        "fn main() -> usize {let first = rc::new::<unique(usize)>(alloc(42)); let view = &**first.value(); let second = first.clone(); drop(first); proof sole: second.strong_count() == 1; *view}",
        "fn main() -> u8 {let first = rc::new::<[u8; 2]>([7, 42]); let view = first.value(); let second = first.clone(); drop(first); (*view)[1]}",
        "type Resource struct {tag: usize} where tag == 42; impl Drop for Resource {fn drop(self) {proof valid: self.tag == 42;}} fn main() -> usize {let inner = rc::new::<Resource>(Resource {tag: 42}); let outer = rc::new::<rc::Rc<Resource>>(inner); let second = outer.clone(); drop(outer); second.value().value().tag}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        let (value, events) = program.run_with_events().unwrap();
        assert_eq!(value.to_string(), "42");
        assert_eq!(events.iter().filter(|event| event.as_str() == "drop Resource").count(), usize::from(source.contains("type Resource")));
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn cloning_rc_does_not_copy_an_owning_payload() {
    let source = "fn main() -> usize {let payload: shared(usize) = alloc(42); let first = rc::new::<shared(usize)>(payload); proof two: owner_count(payload) == 2; let second = first.clone(); proof still_two: owner_count(payload) == 2; drop(first); drop(second); proof one: owner_count(payload) == 1; let final: unique(usize) = move(payload); *final}";
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn generic_rc_payloads_keep_their_ownership_and_borrow_lifetimes() {
    for source in [
        "fn main() -> usize {let first = rc::new::<unique(usize)>(alloc(42)); let view = &**first.value(); let second = first.clone(); drop(first); drop(second); *view}",
        "fn main() {let first = rc::new::<unique(usize)>(alloc(42)); let stolen = *first.value();}",
        "type Resource struct {tag: usize} where tag == 42; fn main() -> usize {let first = rc::new::<Resource>(Resource {tag: 42}); let view = first.value(); let second = first.clone(); drop(first); drop(second); view.tag}",
        "type Resource struct {tag: usize} where tag == 42; fn main() {let value = rc::new::<Resource>(Resource {tag: 42}); value.value().tag = 7;}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn source_rc_rejects_counter_drift_overflow_and_missing_claims() {
    let library = include_str!("../../../../stdlib/rc/rc.evg");
    for (from, to, expected) in [
        (
            "self.data.count = self.data.count + 1 starts_owner(self.data);",
            "",
            "invariant",
        ),
        (
            "Self {data: self.data}",
            "Self {data: shape(shared(Data::<T>))}",
            "type mismatch",
        ),
        ("data.count = data.count - 1;", "", "postcondition"),
        (
            "data.count = data.count - 1;",
            "data.count = data.count - 2;",
            "postcondition",
        ),
        ("where self.data.count < usize::MAX", "", "upper bound"),
    ] {
        let wrong = library.replace_evg(from, to);
        assert_ne!(wrong, library);
        let wrong = format!("{wrong}\nfn exercise_counter() -> usize {{let first = new(42); let second = first.clone(); second.release_nonfinal(); *first.value()}}");
        let error = verify(&wrong).unwrap_err();
        assert!(error.contains(expected), "{error}\n{wrong}");
    }
}

#[test]
fn source_rc_clones_through_nested_places_and_preserves_payload_loans() {
    for source in [
        "fn main() -> usize {let items = [rc::new(42)]; let view = items[0].value(); let second = items[0].clone(); second.release_nonfinal(); proof unique: items[0].strong_count() == 1; *view}",
        "type Holder struct {shared: rc::Rc} fn main() -> usize {let holder = Holder {shared: rc::new(7)}; let view = holder.shared.value(); let second = holder.shared.clone(); *view = 42; second.release_nonfinal(); proof unique: holder.shared.strong_count() == 1; *holder.shared.value()}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn source_rc_lifetimes_keep_payload_and_handle_planes_distinct() {
    for source in [
        "fn main() {let first = rc::new(42); let second = first.clone(); first.release_last();}",
        "fn main() {let first = rc::new(42); first.release_nonfinal();}",
        "fn main() -> usize {let first = rc::new(42); let view = first.value(); first.release_last(); *view}",
        "fn main() -> usize {let first = rc::new(42); let second = first.clone(); let handle = &first; first.release_nonfinal(); handle.strong_count()}",
        "fn main() {let first = rc::new(42); let moved = move(first); first.strong_count();}",
        "impl Copy for rc::Rc {} fn main() {}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

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
        "fn main() {let credit = allocation_credits::Credit {allocation: alloc(42)};}",
        "impl Copy for allocation_credits::Credit {} fn main() {}",
        "fn main() {let credit = allocation_credits::attach(alloc(42)); let moved = credit; let again = credit;}",
        "fn main() {let first = allocation_credits::attach(alloc(42)); let second = allocation_credits::duplicate(&first); let unique = allocation_credits::recover(first);}",
        "fn main() {let first = allocation_credits::attach(alloc(42)); let second = allocation_credits::duplicate(&first); proof lie: allocation_credits::outstanding(&first) == 1 by {trustme}; let unique = allocation_credits::recover(first);}",
        "fn main() {let first = allocation_credits::attach(alloc(42)); let second = allocation_credits::attach(alloc(7)); let wrong = allocation_credits::merge(first, second);}",
        "fn main() -> usize {let credit = allocation_credits::attach(alloc(42)); let target = allocation_credits::target(&credit); let final = allocation_credits::recover(credit); drop(final); *target}",
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
        "fn view(value: &shared(usize)) -> &usize borrows(&**value) {let temporary = *value; leak(temporary); &**value} fn wrong(value: &shared(usize)) {ideal let saved = old(view(value));}",
        "fn observe(value: &shared(usize)) -> usize {let temporary = *value; leak(temporary); 42} fn wrong(value: &shared(usize)) {ideal let saved = old(observe(value));}",
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
    let source =
        "fn reclaim(value: shared(usize)) -> unique(usize) {move(value)} fn main() -> usize {42}";
    let error = verify(source).unwrap_err();
    assert!(error.contains("unique owner recovery"), "{error}");
    let valid = "fn reclaim(value: shared(usize)) -> unique(usize) where owner_count(value) == 1 {move(value)} fn main() -> usize {let unique: unique(usize) = alloc(42); let owned: shared(usize) = move(unique); let recovered = reclaim(move(owned)); *recovered}";
    let (program, bundle) = prove(valid).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(valid, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let invalid = valid.replace_evg(
        "let recovered = reclaim(move(owned));",
        "let another = owned; let recovered = reclaim(move(owned));",
    );
    assert!(verify(&invalid)
        .unwrap_err()
        .contains("precondition of reclaim"));
}

#[test]
fn callee_cleanup_releases_only_its_claim_including_hidden_caller_owners() {
    let source = "fn release(value: shared(usize)) where owner_count(value) > 1 {leak(value);} fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let second = first; release(move(first)); proof sole: owner_count(second) == 1; let recovered: unique(usize) = move(second); *recovered}";
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
    let source = "fn duplicate(value: &shared(usize)) -> shared(usize) ensures owner_count(result) == old(owner_count(value)) + 1 {*value} fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let second = duplicate(&first); proof shared: owner_count(first) == 2; leak(first); let recovered: unique(usize) = move(second); *recovered}";
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
    let source = "fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let view = &*first; let second = first; let moved = move(first); leak(moved); proof sole: owner_count(second) == 1; let recovered: unique(usize) = move(second); *view}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let dead = source.replace_evg(
        "let recovered: unique(usize) = move(second);",
        "let recovered: unique(usize) = move(second); drop(recovered);",
    );
    assert!(verify(&dead).is_err());
    let moved = source.replace_evg("leak(moved);", "leak(first);");
    assert!(verify(&moved).is_err());
}

#[test]
fn census_admissions_expire_on_owner_transitions_even_when_the_count_returns() {
    for transition in ["let other = value;", "let other = value; leak(other);"] {
        let source = format!("fn reclaim(value: shared(usize)) -> unique(usize) {{proof admitted: owner_count(value) == 1 by {{trustme}}; {transition} move(value)}} fn main() -> usize {{42}}");
        let error = verify(&source).unwrap_err();
        assert!(error.contains("unique owner recovery"), "{error}");
    }
}

#[test]
fn ownership_transitions_cannot_silently_break_a_nominal_invariant() {
    let prefix = "type Counted struct {count: usize, data: shared(usize)} where nat(count) == owner_count(data); fn duplicate(value: &shared(usize)) -> shared(usize) {*value}";
    for operation in ["value.data", "duplicate(&value.data)"] {
        let source = format!("{prefix} fn main() {{let unique: unique(usize) = alloc(42); let value = Counted {{count: 1, data: unique}}; let other = {operation};}}");
        assert!(verify(&source).is_err(), "accepted {operation}");
    }
}

#[test]
fn owners_cannot_be_forged_or_consumed_by_erased_execution() {
    for source in [
        "fn main() {let forged: shared(usize) = 42;}",
        "fn main() {let unique: unique(usize) = alloc(42); let owned: shared(usize) = move(unique); let count = owner_count(owned);}",
        "fn main() {let unique: unique(usize) = alloc(42); ideal let owned: shared(usize) = move(unique);}",
        "fn main() {let unique: unique(usize) = alloc(42); let owned: shared(usize) = move(unique); let recovered = move(&owned);}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn raw_shared_cleanup_leaks_and_promotion_enables_payload_destruction() {
    let source = "type Resource struct {value: usize} where value == 42; impl Drop for Resource {fn drop(self) {proof valid: self.value == 42;}} fn main() -> usize {let first: shared(Resource) = alloc(Resource {value: 42}); let view = &*first; let second = first; leak(first); let answer = second.value; CLEANUP answer}";
    for (cleanup, expected) in [
        ("leak(second); proof zero: owner_count(view) == 0;", 0),
        (
            "let final: unique(Resource) = move(second); drop(final);",
            1,
        ),
    ] {
        let source = source.replace_evg("CLEANUP", cleanup);
        let (program, bundle) = prove(&source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        let (value, events) = program.run_with_events().unwrap();
        assert_eq!(value.to_string(), "42");
        assert_eq!(events.len(), expected);
        assert_eq!(
            verify_with_certificate(&source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
    }
}

#[test]
fn ordinary_borrows_do_not_count_and_keep_the_original_allocation_provenance() {
    let source = "fn borrow(value: &shared(usize)) -> &usize borrows(&**value) {&**value} fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let view = borrow(&first); let another_view = &*first; proof one: owner_count(first) == 1 && owner_count(view) == 1 && owner_count(another_view) == 1; let second = first; leak(first); *view}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let invalid = source.replace_evg(
        "leak(first); *view",
        "leak(first); let final: unique(usize) = move(second); drop(final); *view",
    );
    assert!(verify(&invalid).is_err());
}

#[test]
fn census_evidence_survives_payload_writes_without_gaining_extra_trust() {
    let source = "fn admitted(value: shared(usize)) -> unique(usize) {proof sole: owner_count(value) == 1 by {trustme}; *value = 7; move(value)} fn main() -> usize {42}";
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
    let source = "fn reclaim(value: shared(usize)) -> usize where owner_count(value) == 1 {let unique: unique(usize) = move(value); proof entry_value: *old(value) == old(*value); *unique} fn main() -> usize {let unique: unique(usize) = alloc(42); reclaim(unique)}";
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
fn early_ownership_arithmetic_replays_and_rejects_early_drop_or_double_materialization() {
    let source = include_str!("../../../../proofs/early_ownership.evg");
    let (program, bundle) = prove(source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for invalid in [
        source.replace_evg("count: state.count + 1", "count: state.count"),
        source.replace_evg("materialized: state.materialized + 1", "materialized: state.materialized + 2"),
        source.replace_evg("early: state.early - 1", "early: state.early"),
        source.replace_evg("state.count == 1 && state.materialized > 0", "state.count == 1"),
        format!("{source} ideal fn early_drop() {{final_release(EarlyOwnership {{count: 1, materialized: 0, early: 1}});}}"),
        format!("{source} ideal fn double_materialization() {{let future = EarlyOwnership {{count: 1, materialized: 0, early: 1}}; let actual = materialize(future); materialize(actual);}}"),
    ] { assert!(verify(&invalid).is_err(), "accepted {invalid}"); }
}

#[test]
fn direct_rc_cloning_cannot_reuse_accuracy_before_its_pointer_copy() {
    let library =
        include_str!("../../../../stdlib/rc/rc.evg").replace_evg("starts_owner(self.data)", "");
    let exercise = "fn exercise() -> usize {let first = new(42); let second = first.clone(); second.release_nonfinal(); *first.value()}";
    let observer =
        "fn accuracy<T>(value: &Rc<T>) ensures nat(value.data.count) == owner_count(value.data) {}";
    let early_call = library.replace_evg(
        "self.data.count = self.data.count + 1;",
        "self.data.count = self.data.count + 1; accuracy::<T>(self);",
    );
    let error = verify(&format!("{early_call}\n{observer}\n{exercise}")).unwrap_err();
    assert!(error.contains("invariant"), "{error}");
    let early_fact = library.replace_evg(
        "self.data.count = self.data.count + 1;",
        "self.data.count = self.data.count + 1; proof prematurely_accurate: nat(self.data.count) == owner_count(self.data);",
    );
    let error = verify(&format!("{early_fact}\n{exercise}")).unwrap_err();
    assert!(error.contains("prematurely_accurate"), "{error}");
}

#[test]
fn an_explicit_owner_start_keeps_rc_accuracy_available_before_materialization() {
    let library = include_str!("../../../../stdlib/rc/rc.evg");
    let checked = library.replace_evg(
        "self.data.count = self.data.count + 1 starts_owner(self.data);",
        "self.data.count = self.data.count + 1 starts_owner(self.data); proof accurate: nat(self.data.count) == owner_count(self.data); accuracy::<T>(self);",
    );
    let source = syntax::join_source_units(&[
        format!("{checked}\nfn accuracy<T>(value: &Rc<T>) ensures nat(value.data.count) == owner_count(value.data) {{}}"),
        "fn main() -> usize {let first = rc::new(42); let second = first.clone(); second.release_nonfinal(); *first.value()}".into(),
    ]).unwrap();
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
}

#[test]
fn explicit_owner_starts_are_fulfilled_once_and_preserve_census_proofs() {
    for source in [
        "fn main() -> usize {let first: shared(usize) = alloc(42); let n: usize = 0; n = 1 starts_owner(first); proof two: owner_count(first) == 2; let second = first; proof unchanged: owner_count(first) == 2 by {exact two}; let third = first; proof three: owner_count(first) == 3; leak(third); leak(first); let unique: unique(usize) = move(second); *unique}",
        "fn main() -> usize {let first: shared(usize) = alloc(42); let n: usize = 0; n = 2 starts_owner(first, first); let copies = [first, first]; proof three: owner_count(first) == 3; leak(copies); let unique: unique(usize) = move(first); *unique}",
        "fn copy(value: &shared(usize)) -> shared(usize) {*value} fn main() -> usize {let first: shared(usize) = alloc(42); let n: usize = 0; n = 1 starts_owner(first); let second = copy(&first); proof two: owner_count(first) == 2; leak(first); let unique: unique(usize) = move(second); *unique}",
        "fn nested(value: &shared(usize)) -> shared(usize) {let n: usize = 0; n = 1 starts_owner(*value); *value} fn main() -> usize {let first: shared(usize) = alloc(42); let n: usize = 0; n = 1 starts_owner(first); let inner = nested(&first); proof three: owner_count(first) == 3; let outer = first; proof still_three: owner_count(first) == 3; leak(inner); leak(first); let unique: unique(usize) = move(outer); *unique}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|e| panic!("{e}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
        crate::compiler::native::emit(&program).unwrap();
    }
}

#[test]
fn owner_starts_cannot_escape_unfulfilled_or_grant_early_destruction() {
    for source in [
        "fn main() {let p: shared(usize) = alloc(42); let n: usize = 0; n = 1 starts_owner(p);}",
        "fn main() {let p: shared(usize) = alloc(42); let n: usize = 0; n = 1 starts_owner(p, p); let only_one = p;}",
        "fn main() {let p: shared(usize) = alloc(42); let q: shared(usize) = alloc(7); let n: usize = 0; n = 1 starts_owner(p); let wrong_plane = q;}",
        "fn main() {let p: shared(usize) = alloc(42); let n: usize = 0; n = 1 starts_owner(p); let early: unique(usize) = move(p);}",
        "fn main() {let p: shared(usize) = alloc(42); let n: usize = 0; n = 1 starts_owner(p); proof lie: owner_count(p) == 1 by {trustme}; let early: unique(usize) = move(p);}",
        "fn main() {let p: unique(usize) = alloc(42); let n: usize = 0; n = 1 starts_owner(p);}",
        "fn main() {let p: shared(usize) = alloc(42); let view = &p; let n: usize = 0; n = 1 starts_owner(view);}",
        "fn main() {let p: shared(usize) = alloc(42); leak(p); let n: usize = 0; n = 1 starts_owner(p);}",
        "fn bad(flag: bool) {let p: shared(usize) = alloc(42); let n: usize = 0; n = 1 starts_owner(p); if flag {let copy = p;} else {}}",
        "fn main() {let p: shared(usize) = alloc(42); ideal let n: nat = 0; ideal n = 1 starts_owner(p);}",
    ] { assert!(verify(source).is_err(), "accepted {source}"); }
}
