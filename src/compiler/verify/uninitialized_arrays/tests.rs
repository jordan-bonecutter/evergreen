use super::*;

#[test]
fn sparse_shape_buffers_initialize_extract_and_free() {
    for source in [
        include_str!("../../../../examples/sparse_slots.evg"),
        include_str!("../../../../examples/sparse_slot_aliases.evg"),
        include_str!("../../../../examples/sparse_rc_slots.evg"),
        "fn clear(buffer: unique(unique(usize) | shape(unique(usize)), 0)) -> unique(shape(unique(usize)), 0) {buffer} fn main() -> usize {let buffer: unique(unique(usize) | shape(unique(usize)), 0) = alloc(0, shape(unique(usize))); let empty = clear(buffer); drop(empty); 42}",
        "fn main() -> usize {let buffer: unique(unique(usize) | shape(unique(usize)), 2) = alloc([alloc(7), alloc(42)]); let first: unique(usize) = (*buffer)[0]; let second: unique(usize) = (*buffer)[1]; let empty: unique(shape(unique(usize)), 2) = buffer; drop(empty); *second}",
        "fn drain(buffer: unique(unique(usize) | shape(unique(usize)), 2)) -> usize where typeof((*buffer)[0]) == unique(usize) && typeof((*buffer)[1]) == unique(usize) {let first: unique(usize) = (*buffer)[0]; let second: unique(usize) = (*buffer)[1]; let empty: unique(shape(unique(usize)), 2) = buffer; drop(empty); *second} fn main() -> usize {let buffer: unique(unique(usize) | shape(unique(usize)), 2) = alloc([alloc(7), alloc(42)]); drain(buffer)}",
        "fn main() -> usize {let owner: shared(usize) = alloc(42); let buffer: unique(shared(usize) | shape(shared(usize)), 8) = alloc(8, shape(shared(usize))); (*buffer)[1] = owner; proof copied: owner_count(owner) == 2; let value: shared(usize) = move((*buffer)[1]); let empty: unique(shape(shared(usize)), 8) = buffer; drop(empty); leak(value); let final: unique(usize) = move(owner); *final}",
        "fn main() -> usize {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); let view = &(*buffer)[2]; *view = alloc(42); let value: unique(usize) = *view; let empty: unique(shape(unique(usize)), 8) = buffer; proof shaped: typeof(*view) == shape(unique(usize)); let answer = if view == view {*value} else {1}; drop(empty); answer}",
        "fn main() -> usize {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); (*buffer)[2] = alloc(42); let payload = &*(*buffer)[2]; let value: unique(usize) = (*buffer)[2]; let empty: unique(shape(unique(usize)), 8) = buffer; drop(empty); *payload}",
        "fn main() -> usize {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); let a = &(*buffer)[2]; let b = &(*buffer)[2]; *a = alloc(42); let value: unique(usize) = *b; let empty: unique(shape(unique(usize)), 8) = buffer; drop(empty); *value}",
        "fn put(slot: &(unique(usize) | shape(unique(usize))), value: unique(usize)) where typeof(*slot) == shape(unique(usize)) modifies(slot) ensures typeof(old(*slot)) == shape(unique(usize)) && typeof(*slot) == unique(usize) {*slot = value;} fn main() -> usize {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); put(&(*buffer)[3], alloc(42)); let value: unique(usize) = (*buffer)[3]; let empty: unique(shape(unique(usize)), 8) = buffer; *value}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn sparse_shape_buffers_do_not_expand_a_billion_cells() {
    let source = include_str!("../../../../examples/sparse_slots.evg")
        .replace("(8)", "(1000000000)")
        .replace("[7]", "[999999999]")
        .replace(", 8)", ", 1000000000)");
    let (program, bundle) = prove(&source).unwrap_or_else(|error| panic!("{error}"));
    let binary = crate::compiler::native::emit(&program).unwrap();
    assert!(binary.len() < 16384);
    assert!(program.run().unwrap_err().contains("before allocation"));
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn sparse_shape_buffers_reject_lost_owners_and_uninitialized_reads() {
    for source in [
        "fn main() {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); (*buffer)[2] = alloc(42); let empty: unique(shape(unique(usize)), 8) = buffer;}",
        "fn main() -> usize {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); let value: unique(usize) = (*buffer)[2]; let empty: unique(shape(unique(usize)), 8) = buffer; *value}",
        "fn main() {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); let empty: unique(shape(unique(usize)), 9) = buffer;}",
        "fn main() {let buffer: unique(u8 | usize | shape(u8), 8) = alloc(8, shape(u8)); let empty: unique(shape(u8), 8) = buffer;}",
        "fn main() {let value: unique(usize) = alloc(42); let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, value);}",
        "fn main() {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); (*buffer)[2] = alloc(42); proof assumed_empty: typeof((*buffer)[2]) == shape(unique(usize)) by {trustme}; let empty: unique(shape(unique(usize)), 8) = buffer;}",
        "fn main() {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); let view = &(*buffer)[2]; let empty: unique(shape(unique(usize)), 8) = buffer; drop(empty); proof bad: typeof(*view) == shape(unique(usize));}",
        "fn main() {let owner: shared(usize) = alloc(42); let buffer: unique(shared(usize) | shape(shared(usize)), 8) = alloc(8, shape(shared(usize))); (*buffer)[1] = owner; let copied: shared(usize) = (*buffer)[1]; let empty: unique(shape(shared(usize)), 8) = buffer;}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
    let overlapping = "fn bad(i: usize, j: usize) where i < 8 && j < 8 {let buffer: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); let a = &(*buffer)[i]; let b = &(*buffer)[j]; proof was_empty: typeof(*b) == shape(unique(usize)); *a = alloc(7); *b = alloc(42); let x: unique(usize) = *a; let y: unique(usize) = *b; let empty: unique(shape(unique(usize)), 8) = buffer;} fn main() {}";
    let error = verify(overlapping).unwrap_err();
    assert!(
        error.contains("current uninitialized shape member"),
        "{error}"
    );
    let disjoint = overlapping.replace("where i < 8 && j < 8", "where i < 8 && j < 8 && i != j");
    verify(&disjoint).unwrap_or_else(|error| panic!("{error}"));
}
