use super::*;
use crate::syntax::format::test_edit::SourceEdit;

#[test]
fn sparse_range_premises_specialize_without_materializing_bound_cells() {
    let source = include_str!("../../../../examples/sparse_ranges.evg");
    let theorem = "proof restrict: (forall(i: integer) where(0 <= i && i < 8) {typeof((*buffer)[i]) == shape(unique(usize))}) => (forall(j: integer) where(4 <= j && j < 8) {typeof((*buffer)[j]) == shape(unique(usize))}) by {intro all; intro j; specialize all(j); omega};";
    let source = source.replace_evg(
        "(*buffer)[3] = alloc(42);",
        &format!("{theorem}\n(*buffer)[3] = alloc(42);"),
    );
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let huge = source
        .replace_evg("(8)", "(1000000000)")
        .replace_evg("i < 8", "i < 1000000000")
        .replace_evg("j < 8", "j < 1000000000")
        .replace_evg(", 8)", ", 1000000000)");
    let (large, large_bundle) = prove(&huge).unwrap();
    assert_eq!(program.obligations, large.obligations);
    assert_eq!(bundle.certificate_count(), large_bundle.certificate_count());
    assert!(crate::compiler::native::emit(&large).unwrap().len() < 16384);
}

#[test]
fn indexed_memory_ranges_follow_initialization_and_extraction_without_trust() {
    let source = include_str!("../../../../examples/sparse_ranges.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let false_range = source.replace_evg("(4 <= i && i < 8)", "(0 <= i && i < 8)");
    assert!(verify(&false_range).unwrap_err().contains("cannot prove"));
    let stale = source.replace_evg(
        "} by {intro i; omega};\n\n    let value:",
        "} by {exact initially_empty};\n\n    let value:",
    );
    assert!(verify(&stale)
        .unwrap_err()
        .contains("different proposition"));
}

#[test]
fn indexed_ranges_do_not_enumerate_capacity_or_mint_runtime_storage() {
    let small = include_str!("../../../../examples/sparse_ranges.evg");
    let huge = small
        .replace_evg("(8)", "(1000000000)")
        .replace_evg("i < 8", "i < 1000000000")
        .replace_evg(", 8)", ", 1000000000)");
    let (small_program, small_bundle) = prove(small).unwrap();
    let (large_program, large_bundle) = prove(&huge).unwrap();
    assert_eq!(small_program.obligations, large_program.obligations);
    assert_eq!(
        small_bundle.certificate_count(),
        large_bundle.certificate_count()
    );
    assert_eq!(
        verify_with_certificate(&huge, &large_bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(crate::compiler::native::emit(&large_program).unwrap().len() < 16384);
    // Execution limits are separate; do not allocate a billion runtime cells.
    let error = large_program.run().unwrap_err();
    assert!(error.contains("before allocation"), "{error}");
}

#[test]
fn indexed_ranges_capture_runtime_bounds_and_reuse_theorems_at_an_index() {
    let source = "fn test(n: usize) -> usize where(integer(n) * 8 <= integer(isize::MAX)) {let data: unique(usize | shape(usize), n) = alloc(n, shape(usize)); proof all: forall(i: integer) where(0 <= i && i < integer(n)) {typeof((*data)[i]) == shape(usize)} by {intro i; omega}; let empty: unique(shape(usize), n) = data; drop(empty); 42} fn main() -> usize {test(8)}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let source = include_str!("../../../../examples/sparse_ranges.evg");
    let generic = source.replace_evg("    alloc(capacity, shape(T))", "    let data: unique(T | shape(T), capacity) = alloc(capacity, shape(T)); proof initialized: forall(i: integer) where(0 <= i && i < integer(capacity)) {typeof((*data)[i]) == shape(T)} by {intro i; omega}; data");
    let (generic_program, generic_bundle) = prove(&generic).unwrap();
    assert_eq!(generic_program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&generic, &generic_bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let nested = "proof shifted: forall(i: integer) where(1 <= i && i < 9) {typeof((*buffer)[i - 1]) == shape(unique(usize))} by {intro x; omega}; proof nested: forall(i: integer) where(0 <= i && i < 8) {forall(j: integer) where(j == i) {typeof((*buffer)[j]) == shape(unique(usize))}} by {intro x; intro y; omega};";
    let nested_source = source.replace_evg(
        "(*buffer)[3] = alloc(42);",
        &format!("{nested}\n(*buffer)[3] = alloc(42);"),
    );
    let (nested_program, nested_bundle) = prove(&nested_source).unwrap();
    assert_eq!(nested_program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&nested_source, &nested_bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let extra = "proof cell: forall(k: integer) where(k == 7) {typeof((*buffer)[k]) == shape(unique(usize))} by {intro k; specialize empty_suffix(k); omega}; proof live: forall(k: integer) where(k == 3) {typeof((*buffer)[k]) == unique(usize)} by {intro k; omega}; proof absent: forall(k: integer) where(4 <= k && k < 8) {typeof((*buffer)[k]) != unique(usize)} by {intro k; omega};";
    let source = source.replace_evg(
        "let value: unique(usize)",
        &format!("{extra}\nlet value: unique(usize)"),
    );
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn indexed_ranges_do_not_reuse_wrong_versions_types_or_missing_bounds() {
    let original = include_str!("../../../../examples/sparse_ranges.evg");
    for (source, fragment) in [
        (
            original.replace_evg("(0 <= i && i < 8)", "(i < 8)"),
            "cannot prove",
        ),
        (
            original.replace_evg("(0 <= i && i < 8)", "(0 <= i && i <= 8)"),
            "cannot prove",
        ),
        (
            original.replacen_evg("== shape(unique(usize))", "== unique(usize)", 1),
            "cannot prove",
        ),
        (
            original.replace_evg("let buffer =", "let usize = true; let buffer ="),
            "literal member type",
        ),
        (
            original
                .replacen_evg("(0 <= i && i < 8)", "(i < 8)", 1)
                .replacen_evg("== shape(unique(usize))", "!= unique(usize)", 1),
            "cannot prove",
        ),
    ] {
        let error = verify(&source).unwrap_err();
        assert!(error.contains(fragment), "{error}");
    }
}

#[test]
fn indexed_ranges_observe_alias_writes_and_preserve_payload_authority() {
    let original = include_str!("../../../../examples/sparse_ranges.evg");
    let aliased = original
        .replace_evg(
            "(*buffer)[3] = alloc(42);",
            "let slot = &(*buffer)[3]; *slot = alloc(42);",
        )
        .replace_evg(
            "let value: unique(usize) = (*buffer)[3];",
            "let value: unique(usize) = *slot;",
        );
    let (program, bundle) = prove(&aliased).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&aliased, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let false_range = aliased.replace_evg("(4 <= i && i < 8)", "(0 <= i && i < 8)");
    assert!(verify(&false_range).unwrap_err().contains("cannot prove"));
    // An admitted observation does not replace the operational ownership checks.
    let forged = aliased.replace_evg("} by {intro i; omega};\n\n    let value:", "} by {trustme};\nproof fake: forall(i: integer) where(0 <= i && i < 8) {typeof((*buffer)[i]) == shape(unique(usize))} by {trustme};\nlet empty: unique(shape(unique(usize)), 8) = buffer; drop(empty);\nlet value:");
    assert!(verify(&forged)
        .unwrap_err()
        .contains("would discard an initialized member"));
}
