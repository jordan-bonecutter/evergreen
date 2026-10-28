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
fn numeric_stores_preserve_unobserved_input_values_at_other_indices() {
    let source = "fn set(data: &[u8; 8], at: usize, value: u8) where(at < 8) modifies(&(*data)[at]) {(*data)[at] = value; proof written: forall(i: integer) where(i == integer(at)) {(*data)[i] == value} by {intro i; omega}; proof frame: forall(i: integer) where(0 <= i && i < 8 && i != integer(at)) {(*data)[i] == old(*data)[i]} by {intro i; omega};} fn main() -> usize {let data: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8]; set(&data, 3, 42); 42}";
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    let reversed = source
        .replace("(*data)[i] == value", "value == (*data)[i]")
        .replace("(*data)[i] == old(*data)[i]", "old(*data)[i] == (*data)[i]");
    assert_eq!(replay(&reversed).run().unwrap().to_string(), "42");
    for bad in [
        source.replace(" && i != integer(at)", ""),
        source.replace("== value}", "== 0}"),
        source.replace("i == integer(at)", "0 <= i && i < 8"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn numeric_stores_follow_fills_literals_and_last_write() {
    for setup in [
        "let data: [u8; 3] = [7, 7, 7];",
        "let allocation: unique(u8, 3) = alloc(3, 7); let data = &*allocation;",
    ] {
        let place = if setup.contains("allocation") {
            "(*data)"
        } else {
            "data"
        };
        let source = format!("fn main() -> usize {{{setup} {place}[1] = 9; {place}[1] = 11; proof frame: forall(i: integer) where(0 <= i && i < 3 && i != 1) {{{place}[i] == 7}} by {{intro i; omega}}; proof written: forall(i: integer) where(i == 1) {{{place}[i] == 11}} by {{intro i; omega}}; proof different: forall(i: integer) where(i == 1) {{{place}[i] != 9}} by {{intro i; omega}}; 42}}");
        assert_eq!(replay(&source).run().unwrap().to_string(), "42");
        let bad = source.replace("== 11}", "== 9}");
        assert!(verify(&bad).is_err(), "{bad}");
    }
    let literal = "fn main() -> usize {let data: [u8; 3] = [7, 9, 11]; proof first: forall(i: integer) where(i == 0) {data[i] == 7} by {intro i; omega}; data[1] = 42; proof last: forall(i: integer) where(i == 2) {data[i] == 11} by {intro i; omega}; 42}";
    assert_eq!(replay(literal).run().unwrap().to_string(), "42");
}

#[test]
fn numeric_store_comparisons_capture_values_and_indices_before_reassignment() {
    let source = "fn check(at: usize, value: u8) where(at < 8) {let saved_at = at; let saved_value = value; let data: unique(u8, 8) = alloc(8, 0); (*data)[at] = value; at = 7; value = 42; proof written: forall(i: integer) where(i == integer(saved_at)) {(*data)[i] == saved_value} by {intro i; omega}; proof frame: forall(i: integer) where(0 <= i && i < 8 && i != integer(saved_at)) {(*data)[i] == 0} by {intro i; omega};} fn main() -> usize {check(2, 9); 42}";
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    for bad in [
        source.replace("== saved_value", "== value"),
        source.replace("i == integer(saved_at)", "i == integer(at)"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn numeric_join_histories_require_the_guard_of_the_selected_write() {
    let source = "fn check(flag: bool) {let data: unique(u8, 8) = alloc(8, 7); if flag {(*data)[0] = 9;} else {(*data)[1] = 11;} proof frame: forall(i: integer) where(2 <= i && i < 8) {(*data)[i] == 7} by {intro i; omega}; if flag {proof written: forall(i: integer) where(i == 0) {(*data)[i] == 9} by {intro i; omega};} else {proof written: forall(i: integer) where(i == 1) {(*data)[i] == 11} by {intro i; omega};}} fn main() -> usize {check(true); check(false); 42}";
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    let bad = source.replace("2 <= i", "0 <= i");
    assert!(verify(&bad).is_err());
}

#[test]
fn numeric_store_contracts_publish_quantified_payload_guarantees() {
    let source = include_str!("../../../../examples/array_value_store.evg");
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    for bad in [
        source.replace("{data[i] == 42}", "{data[i] == 9}"),
        source.replace("proof updated:", "data[1] = 9; proof updated:"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn numeric_history_proofs_do_not_invent_values_from_observed_cells() {
    for source in [
        "fn check(data: &[u8; 8]) modifies(&(*data)[1]) {let observed = (*data)[0]; (*data)[1] = 7; proof _: forall(i: integer) where(0 <= i && i < 8 && i != 1) {(*data)[i] == observed} by {intro i; omega};}",
        "fn check(data: &[u8; 8], other: &[u8; 8]) modifies(&(*data)[1]) {(*data)[1] = 7; proof _: forall(i: integer) where(0 <= i && i < 8 && i != 1) {(*data)[i] == old(*other)[i]} by {intro i; omega};}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("cannot prove"), "{error}");
    }
}

#[test]
fn numeric_history_size_depends_on_writes_not_capacity() {
    let source = "fn check(position: usize) where(position < 8) {let data: unique(u8, 8) = alloc(8, 7); (*data)[position] = 9; proof frame: forall(i: integer) where(0 <= i && i < 8 && i != integer(position)) {(*data)[i] == 7} by {intro i; omega}; proof written: forall(i: integer) where(i == integer(position)) {(*data)[i] == 9} by {intro i; omega};} fn main() -> usize {42}";
    let large = source
        .replace("< 8", "< 1000000000")
        .replace(", 8)", ", 1000000000)")
        .replace("alloc(8", "alloc(1000000000");
    let (small, small_bundle) = prove(source).unwrap();
    let (big, big_bundle) = prove(&large).unwrap();
    assert_eq!(small.obligations, big.obligations);
    assert_eq!(
        small_bundle.certificate_count(),
        big_bundle.certificate_count()
    );
    assert_eq!(
        verify_with_certificate(&large, &big_bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(crate::compiler::native::emit(&big).unwrap().len() < 16384);
}

#[test]
fn numeric_store_histories_preserve_unspecified_values_without_guessing_them() {
    let source = "fn main() -> usize {let value = usize::MAX + 1; let data: [usize; 3] = [7, 9, 11]; data[1] = value; proof written: forall(i: integer) where(i == 1) {data[i] == value} by {intro i; omega}; 42}";
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    for unsupported in ["0", "usize::MAX"] {
        assert!(verify(&source.replace("== value", &format!("== {unsupported}"))).is_err());
    }
}

#[test]
fn numeric_equality_can_compare_two_independently_written_arrays() {
    let source = "fn main() -> usize {let a: unique(u8, 8) = alloc(8, 7); let b: unique(u8, 8) = alloc(8, 7); (*a)[2] = 42; (*b)[2] = 42; proof same: forall(i: integer) where(0 <= i && i < 8) {(*a)[i] == (*b)[i]} by {intro i; omega}; 42}";
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    let bad = source.replace("(*b)[2] = 42", "(*b)[2] = 9");
    assert!(verify(&bad).is_err());
}
