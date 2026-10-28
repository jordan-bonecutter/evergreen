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
fn source_range_copy_proves_values_and_target_preservation() {
    let source = include_str!("../../../../examples/array_copy_range.evg");
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    for bad in [
        source.replace_evg("1, 3", "3, 1"),
        source.replace_evg("1, 3", "1, 5"),
        source.replace_evg("1, 3", "1, 6"),
        source.replace_evg("target[0] == 1", "target[0] == 7"),
        source.replace_evg("source[1] = 0", "target[1] = 0"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn source_range_copy_handles_self_copy_empty_and_signed_arrays() {
    for source in [
        "fn main() -> u8 ensures result == 42 {let data: [u8; 3] = [7, 42, 11]; arrays::copy_range(&data, &data, 0, 3); data[1]}",
        "fn main() -> usize {let a: [u8; 0] = []; let b: [u8; 0] = []; arrays::copy_range(&a, &b, 0, 0); 42}",
        "fn main() -> i16 ensures result == 42 {let a: [i16; 3] = [-7, 9, 11]; let b: [i16; 3] = [1, 42, 3]; arrays::copy_range(&a, &b, 1, 1); b[1]}",
        "fn main() -> i16 ensures result == 42 {let a: [i16; 3] = [-7, 42, 11]; let b: [i16; 4] = [1, 2, 3, 4]; arrays::copy_range(&a, &b, 0, 3); proof _: b[0] == -7 && b[2] == 11 && b[3] == 4; b[1]}",
    ] {assert_eq!(replay(source).run().unwrap().to_string(), "42");}
}

#[test]
fn source_range_copy_supports_runtime_lengths_and_sparse_proofs() {
    let source = "fn copy(n: usize, source: linear_plane(u8, n), m: usize, target: linear_plane(u8, m)) where n > 0 && n <= m modifies(target) ensures (*target)[0] == old(*source)[0] {arrays::copy_range(source, target, 0, n);} fn main() -> u8 ensures result == 42 {let source: [u8; 1] = [42]; let target: [u8; 2] = [7, 9]; copy(&source, &target); target[0]}";
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    let small = "fn copy(source: &[u8; 8], target: &[u8; 8]) modifies(target) ensures (*target)[2] == old(*source)[2] {arrays::copy_range(source, target, 0, 8);} fn main() -> usize {42}";
    let huge = small
        .replace("; 8]", "; 1000000000]")
        .replace(", 0, 8)", ", 0, 1000000000)");
    let (a, ca) = prove(small).unwrap();
    let (b, cb) = prove(&huge).unwrap();
    assert_eq!(a.obligations, b.obligations);
    assert_eq!(ca.certificate_count(), cb.certificate_count());
    verify_with_certificate(&huge, &cb).unwrap();
    assert!(crate::compiler::native::emit(&b).unwrap().len() < 16384);
}

#[test]
fn source_range_copy_rejects_wrong_reads_writes_and_skipped_elements() {
    let library = include_str!("../../../../stdlib/arrays/copy.evg");
    let example = include_str!("../../../../examples/array_copy_range.evg");
    for bad in [
        library.replace_evg("(*source)[cursor]", "(*source)[start]"),
        library.replace_evg("(*target)[cursor] =", "(*target)[start] ="),
        library.replace_evg("cursor = cursor + 1", "cursor = cursor + 2"),
    ] {
        let error = verify(&format!("{bad}\u{1e}{example}")).unwrap_err();
        assert!(error.contains("cannot prove"), "{error}");
    }
}
