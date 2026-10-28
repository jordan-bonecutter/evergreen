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
fn numeric_read_bindings_prove_only_the_observed_input_cell() {
    let source = "fn read(data: &[u8; 8], at: usize) where at < 8 {let value = (*data)[at]; proof _: forall(i: integer) where(i == integer::from(at)) {(*data)[i] == value} by {intro i; omega};} fn main() -> usize {let data: [u8; 8] = [7, 9, 11, 13, 15, 17, 19, 21]; read(&data, 3); 42}";
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    replay(&source.replace("(*data)[i] == value", "value == (*data)[i]"));
    for bad in [
        source.replace("i == integer::from(at)", "0 <= i && i < 8"),
        source.replace("i == integer::from(at)", "i == 7"),
        source.replace("== value}", "== 0}"),
        source.replace("let value = (*data)[at]", "let value = 42"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn read_equations_capture_the_original_index_and_memory_revision() {
    let source = "fn read(data: &[u8; 8], at: usize) where at < 8 modifies(data) {let saved_index = at; let value = (*data)[at]; at = 7; (*data)[saved_index] = 42; proof _: forall(i: integer) where(i == integer::from(saved_index)) {old(*data)[i] == value} by {intro i; omega};} fn main() -> usize {42}";
    replay(source);
    for bad in [
        source.replace("old(*data)[i]", "(*data)[i]"),
        source.replace("i == integer::from(saved_index)", "i == integer::from(at)"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
    assert!(verify("fn read(a: &[u8; 8], b: &[u8; 8]) {let value = (*a)[0]; proof _: forall(i: integer) where(i == 0) {(*b)[i] == value} by {intro i; omega};}").is_err());
}

#[test]
fn read_equations_support_single_cell_copy_contracts() {
    let source = "fn copy(source: &[u8; 8], target: &[u8; 8], at: usize) where at < 8 modifies(&(*target)[at]) ensures forall(i: integer) where(i == integer::from(at)) {(*target)[i] == old(*source)[i]} {(*target)[at] = (*source)[at];} fn main() -> usize {42}";
    replay(source);
    for bad in [
        source.replace("= (*source)[at]", "= 42"),
        source.replace("= (*source)[at]", "= (*source)[7]"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
    let huge = source
        .replace("; 8]", "; 1000000000]")
        .replace("at < 8", "at < 1000000000");
    let (small, a) = prove(source).unwrap();
    let (large, b) = prove(&huge).unwrap();
    assert_eq!(small.obligations, large.obligations);
    assert_eq!(a.certificate_count(), b.certificate_count());
    verify_with_certificate(&huge, &b).unwrap();
}

#[test]
fn read_bindings_do_not_import_branch_facts_or_guessed_values() {
    for source in [
        "fn read(data: &[u8; 8], flag: bool) {if flag {let value = (*data)[0]; proof lie: value == 42 by {trustme};} proof _: forall(i: integer) where(i == 0) {(*data)[i] == 42} by {intro i; omega};}",
        "fn read(data: &[u8; 8], flag: bool) {if flag {let value = (*data)[0];} proof _: forall(i: integer) where(i == 0) {(*data)[i] == 42} by {intro i; omega};}",
        "fn read(data: &[usize; 8]) {let value = (*data)[0]; proof _: forall(i: integer) where(i == 0) {(*data)[i] == usize::MAX + 1} by {intro i; omega};}",
    ] {assert!(verify(source).is_err(), "{source}");}
}
