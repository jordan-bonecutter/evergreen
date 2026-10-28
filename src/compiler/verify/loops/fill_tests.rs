use super::*;
use crate::syntax::format::test_edit::SourceEdit;

fn replay(source: &str) -> VerifiedProgram {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    program
}

#[test]
fn source_range_fill_proves_payloads_and_preservation_with_a_runtime_loop() {
    let source = include_str!("../../../../examples/array_fill_range.evg");
    let program = replay(source);
    assert_eq!(program.run().unwrap().to_string(), "42");
    let fill = program
        .functions
        .iter()
        .find(|function| function.name.ends_with("_fill_range"))
        .unwrap();
    assert!(!crate::compiler::effects::recursive(fill));
    assert!(fill
        .body
        .iter()
        .any(|statement| matches!(statement, Statement::While { .. })));
    for bad in [
        source.replace_evg("1, 3, 42", "3, 1, 42"),
        source.replace_evg("1, 3, 42", "1, 5, 42"),
        source.replace_evg("data[0] == 7", "data[0] == 42"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn source_range_fill_handles_empty_full_and_signed_ranges() {
    for source in [
        "fn main() -> usize {let data: [usize; 0] = []; arrays::fill_range(&data, 0, 0, 7); 42}",
        "fn main() -> usize ensures result == 42 {let data: [usize; 3] = [7, 42, 11]; arrays::fill_range(&data, 1, 1, 0); proof _: data[0] == 7 && data[2] == 11; data[1]}",
        "fn main() -> usize ensures result == 42 {let data: [usize; 3] = [7, 9, 11]; arrays::fill_range(&data, 0, 3, 42); proof _: data[0] == 42 && data[2] == 42; data[1]}",
        "fn main() -> usize {let data: [i16; 3] = [1, 2, 3]; arrays::fill_range::<i16>(&data, 1, 3, -7); proof _: data[0] == 1 && data[1] == -7 && data[2] == -7; 42}",
    ] {
        assert_eq!(replay(source).run().unwrap().to_string(), "42");
    }
}

#[test]
fn source_range_fill_supports_runtime_extents_and_billion_slot_proofs() {
    let dynamic = "fn fill(capacity: usize, data: linear_plane(u8, capacity)) where(capacity > 0) modifies(data) ensures (*data)[capacity - 1] == 42 {arrays::fill_range::<u8>(capacity, data, 0, capacity, 42);} fn main() -> u8 ensures result == 42 {let data: unique(u8, 8) = alloc(8, 7); fill(&*data); (*data)[7]}";
    assert_eq!(replay(dynamic).run().unwrap().to_string(), "42");
    let small = "fn fill(data: &[u8; 8]) modifies(data) ensures (*data)[2] == 42 {arrays::fill_range::<u8>(data, 1, 3, 42);} fn main() -> usize {42}";
    let huge = small.replace("; 8]", "; 1000000000]");
    let (small, small_bundle) = prove(small).unwrap();
    let (large, large_bundle) = prove(&huge).unwrap();
    assert_eq!(small.obligations, large.obligations);
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
    assert!(crate::compiler::native::emit(&large).unwrap().len() < 16384);
}

#[test]
fn source_range_fill_rejects_wrong_writes_and_skipped_elements() {
    let library = include_str!("../../../../stdlib/arrays/fill.evg");
    let example = include_str!("../../../../examples/array_fill_range.evg");
    for bad in [
        library.replace_evg("(*data)[cursor] = value", "(*data)[start] = value"),
        library.replace_evg("cursor = cursor + 1", "cursor = cursor + 2"),
    ] {
        let error = verify(&format!("{bad}\u{1e}{example}")).unwrap_err();
        assert!(error.contains("cannot prove"), "{error}");
    }
}
