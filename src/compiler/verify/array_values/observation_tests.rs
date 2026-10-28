use super::*;

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
fn numeric_array_contracts_describe_ordinary_reads() {
    let source = include_str!("../../../../examples/array_value_store.evg");
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    let implicit = source
        .lines()
        .filter(|line| !line.contains("proof updated:"))
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(replay(&implicit).run().unwrap().to_string(), "42");
    let source = "fn read(data: &[u8; 8], index: usize) -> u8 where(index < 8 && (forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == 7})) ensures result == 7 {(*data)[index]} fn main() -> usize {42}";
    replay(source);
    replay(&source.replace("(*data)[i] == 7", "7 == (*data)[i]"));
    replay(&source.replace("(*data)[i] == 7", "(*data)[i] != 0 && (*data)[i] == 7"));
    replay(
        &source
            .replace("result == 7", "result != 0")
            .replace("(*data)[i] == 7", "(*data)[i] != 0"),
    );
}

#[test]
fn numeric_observations_specialize_shifted_indices_without_sampling() {
    let source = "fn read(data: &[u8; 8], index: usize) -> u8 where(index < 7 && (forall(i: integer) where(0 <= i && i < 7) {(*data)[i + 1] == 7})) ensures result == 7 {(*data)[index + 1]} fn main() -> usize {42}";
    replay(source);
    let outside = source.replace("(*data)[index + 1]", "(*data)[0]");
    assert!(verify(&outside).is_err());
    let scaled = "fn read(data: &[u8; 8]) -> u8 where(forall(i: integer) where(0 <= i && i < 4) {(*data)[2 * i] == 7}) ensures result == 7 {(*data)[6]} fn main() -> usize {42}";
    replay(scaled);
    assert!(verify(&scaled.replace("(*data)[6]", "(*data)[7]")).is_err());
}

#[test]
fn numeric_observations_require_a_current_proof_for_the_right_plane_and_domain() {
    for source in [
        "fn read(data: &[u8; 8]) -> u8 {fact unknown = forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == 7}; proof _: (*data)[0] == 7; (*data)[0]}",
        "fn read(data: &[u8; 8], other: &[u8; 8]) -> u8 where(forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == 7}) ensures result == 7 {(*other)[0]}",
        "fn read(data: &[u8; 8]) -> u8 where(forall(i: integer) where(0 <= i && i < 7) {(*data)[i] == 7}) ensures result == 7 {(*data)[7]}",
        "fn read(data: &[u8; 8]) -> u8 where(forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == 7}) modifies(&(*data)[0]) ensures result == 7 {(*data)[0] = 9; (*data)[0]}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("cannot prove"), "{source}\n{error}");
    }
}

#[test]
fn numeric_observations_do_not_automatically_import_admissions() {
    let source = "fn read(data: &[u8; 8]) -> u8 {proof untrusted: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == 7} by {trustme}; proof _: (*data)[0] == 7; (*data)[0]}";
    assert!(verify(source).is_err());
}

#[test]
fn numeric_observations_link_two_observed_arrays_in_either_read_order() {
    let source = "fn compare(a: &[u8; 8], b: &[u8; 8], index: usize) where(index < 8 && (forall(i: integer) where(0 <= i && i < 8) {(*a)[i] == (*b)[i]})) {let first = (*a)[index]; let second = (*b)[index]; proof _: first == second;} fn main() -> usize {42}";
    replay(source);
    replay(&source.replace(
        "let first = (*a)[index]; let second = (*b)[index];",
        "let second = (*b)[index]; let first = (*a)[index];",
    ));
    assert!(verify(&source.replace("(*b)[index]", "(*b)[7 - index]")).is_err());
}

#[test]
fn numeric_observations_do_not_cache_branch_specific_proofs_as_values() {
    let source = "fn read(data: &[u8; 8], flag: bool) where(forall(i: integer) where(flag && 0 <= i && i < 8) {(*data)[i] == 7}) {if flag {let first = (*data)[0]; proof _: first == 7;} if flag {let second = (*data)[0]; proof _: second == 7;}} fn main() -> usize {42}";
    replay(source);
    let escaped = source.replace("if flag {let second", "{let second");
    let error = verify(&escaped).unwrap_err();
    assert!(error.contains("cannot prove"), "{error}");
}

#[test]
fn numeric_read_proofs_remain_sparse_for_billion_element_inputs() {
    let source = "fn read(data: &[u8; 8], index: usize) -> u8 where(index < 8 && (forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == 7})) ensures result == 7 {(*data)[index]} fn main() -> usize {42}";
    let huge = source
        .replace("; 8]", "; 1000000000]")
        .replace("< 8", "< 1000000000");
    let (small, small_bundle) = prove(source).unwrap();
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
