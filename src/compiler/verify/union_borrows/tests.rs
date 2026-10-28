use super::*;

#[test]
fn member_view_proof_subjects_follow_the_separate_payload_plane() {
    let source = "fn process(value: &usize) where(*value == 7) {} fn main() -> usize {let slot: unique(usize) | shape(unique(usize)) = alloc(42); let view: &unique(usize) = &slot; proof admitted: **view == 7 by {trustme}; let payload = &**view; let value: unique(usize) = slot; process(payload); *value}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let changed = source.replace("process(payload)", "*payload = 99; process(payload)");
    assert!(verify(&changed).is_err());
    let unrelated = source.replace(
        "process(payload)",
        "let other = alloc(42); process(&*other)",
    );
    assert!(verify(&unrelated).is_err());
}

#[test]
fn typed_member_borrows_preserve_the_existing_slot_and_function_provenance() {
    let source = "fn payload<T>(slot: &(T | shape(T))) -> &T where(typeof(*slot) == T) borrows(slot) {slot} fn main() -> usize {let slot: usize | shape(usize) = 42; let view: &usize = &slot; proof value: *view == 42; let other = payload::<usize>(&slot); let seen = *other; let moved: usize = slot; seen + moved - 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
}

#[test]
fn typed_record_member_fields_use_the_member_layout() {
    let source = "type Item struct {pad: u8, data: usize} fn main() -> usize {let slot: Item | shape(Item) = Item {pad: 7, data: 42}; let view: &Item = &slot; let seen = view.data; let item: Item = slot; seen}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
}

#[test]
fn extraction_invalidates_the_slot_view_and_preserves_a_separate_payload_plane() {
    let source = include_str!("../../../../examples/member_borrows.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let stale = source.replace(
        "let empty: unique(shape(unique(usize)), 8) = buffer;",
        "proof invalid: **view == 42; let empty: unique(shape(unique(usize)), 8) = buffer;",
    );
    assert!(verify(&stale).unwrap_err().contains("member view"));
    let census = source.replace(
        "let empty: unique(shape(unique(usize)), 8) = buffer;",
        "proof invalid: owner_count(view) == 1; let empty: unique(shape(unique(usize)), 8) = buffer;",
    );
    assert!(verify(&census).unwrap_err().contains("member view"));
    let freed = source.replace("    *payload", "    drop(value); *payload");
    assert!(verify(&freed).unwrap_err().contains("never"));
    let stolen = source.replace(
        "    let payload = &**view;",
        "    let stolen: unique(usize) = *view; let payload = &**view;",
    );
    assert!(verify(&stolen)
        .unwrap_err()
        .contains("moving owning fields"));
}

#[test]
fn member_views_require_the_current_tag_and_recheck_after_rhs_effects() {
    for source in [
        "fn payload(slot: &(usize | shape(usize))) -> &usize borrows(slot) {slot}",
        "fn main() {let slot: usize | shape(usize) = shape(usize); let wrong: &usize = &slot; let retired: shape(usize) = slot;}",
        "fn main() -> usize {let slot: usize | bool | shape(usize) = 42; let view: &usize = &slot; let raw = &slot; let old: usize = move(*raw); *raw = true; *view}",
    ] { assert!(verify(source).is_err(), "accepted {source}"); }
    let write = "fn change(v: &usize) modifies(v) {*v = 42;} fn main() -> usize {let slot: usize | shape(usize) = 7; let view: &usize = &slot; change(view); proof same: view == view; let value: usize = slot; value}";
    let (program, bundle) = prove(write).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(write, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let rhs = "fn take(slot: &(usize | shape(usize))) -> usize where(typeof(*slot) == usize) modifies(slot) {move(*slot)} fn main() -> usize {let slot: usize | shape(usize) = 42; let view: &usize = &slot; *view = take(&slot); let value: usize = slot; value}";
    let error = verify(rhs).unwrap_err();
    assert!(error.contains("member view"), "{error}");
}

#[test]
fn conditional_member_borrows_retain_each_incoming_plane() {
    let source = "fn choose(flag: bool, a: &(usize | shape(usize)), b: &(usize | shape(usize))) -> &usize where(typeof(*a) == usize && typeof(*b) == usize) borrows(a) when flag else borrows(b) {if flag {a} else {b}} fn main() -> usize {let a: usize | shape(usize) = 7; let b: usize | shape(usize) = 42; let view = choose(false, &a, &b); let seen = *view; let a: usize = a; let b: usize = b; seen}";
    let source = source.replace(
        "let a: usize = a; let b: usize = b;",
        "let av: usize = a; let bv: usize = b;",
    );
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
}

#[test]
fn member_view_facts_expire_on_alias_writes_and_reinitialization() {
    let source = "fn main() -> usize {let slot: usize | shape(usize) = 7; let view: &usize = &slot; proof saved: *view == 7; let raw = &slot; let retired: usize = move(*raw); *raw = 42; proof current: *view == 42; let outcome: usize = slot; outcome}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let stale = source.replace(
        "proof current: *view == 42;",
        "proof stale: *view == 7 by {exact saved};",
    );
    assert!(verify(&stale).is_err());
    let indirect = "fn main() -> usize {let slot: usize | shape(usize) = 7; let view: &usize = &slot; proof saved: *view == 7; *view = 42; proof stale: *view == 7 by {exact saved}; let outcome: usize = slot; outcome}";
    assert!(verify(indirect).is_err());
}

#[test]
fn member_array_borrows_keep_bounds_and_expire_projected_views() {
    let source = "fn main() -> usize {let slot: [usize; 2] | shape([usize; 2]) = [7, 42]; let view: &[usize; 2] = &slot; let cell = &(*view)[1]; let seen = *cell; let data: [usize; 2] = slot; seen}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    assert!(verify(&source.replace("(*view)[1]", "(*view)[2]")).is_err());
    let extracted = source.replace(
        "let seen = *cell; let data: [usize; 2] = slot; seen",
        "let data: [usize; 2] = slot; *cell",
    );
    assert!(verify(&extracted).is_err());
}
