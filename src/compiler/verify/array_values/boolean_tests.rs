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
fn boolean_range_copy_and_fill_prove_ordinary_values() {
    for source in [
        include_str!("../../../../examples/boolean_array_proofs.evg"),
        "fn main() -> usize {let data: [bool; 3] = [false, true, false]; arrays::copy_range(&data, &data, 0, 3); proof _: !data[0] && data[1] && !data[2]; 42}",
        "fn main() -> usize {let a: [bool; 0] = []; let b: [bool; 0] = []; arrays::copy_range(&a, &b, 0, 0); arrays::fill_range(&b, 0, 0, true); 42}",
        "fn fill(data: &[bool; 4], a: bool, b: bool) modifies(data) ensures (*data)[2] == (a && !b) {arrays::fill_range(data, 1, 3, a && !b);} fn main() -> usize {let data: [bool; 4] = [true, false, false, true]; fill(&data, true, false); proof _: data[2]; 42}",
    ] {assert_eq!(replay(source).run().unwrap().to_string(), "42");}
}

#[test]
fn boolean_histories_keep_compound_formulas_and_captured_inputs() {
    let source = "fn check(n: usize, a: bool, b: bool) {let flags: unique(bool, 8) = alloc(8, n == 1); proof _: forall(i: integer) where(0 <= i && i < 8) {(*flags)[i] == (n == 1)} by {intro i; omega}; let saved = a && !b; (*flags)[3] = saved; a = !a; b = !b; proof _: forall(i: integer) where(i == 3) {(*flags)[i] == saved} by {intro i; omega}; proof _: forall(i: integer) where(0 <= i && i < 8 && i != 3) {(*flags)[i] == (n == 1)} by {intro i; omega};} fn main() -> usize {check(2, true, false); 42}";
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    for bad in [
        source.replace("== saved}", "== (a && !b)}"),
        source.replace("== saved}", "== false}"),
        source.replace(" && i != 3", ""),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
    // An arbitrary integer compared with one is a formula, not a zero-or-one word.
    replay("fn check(n: usize) where n == 2 {let flags: unique(bool, 8) = alloc(8, n == 1); proof _: forall(i: integer) where(0 <= i && i < 8) {(*flags)[i] == false} by {intro i; omega};} fn main() -> usize {check(2); 42}");
}

#[test]
fn boolean_reads_retain_their_exact_index_and_version() {
    let source = "fn read(data: &[bool; 8], at: usize) where at < 8 modifies(data) {let saved = (*data)[at]; proof _: forall(i: integer) where(i == integer(at)) {(*data)[i] == saved} by {intro i; omega}; (*data)[at] = !saved; proof _: forall(i: integer) where(i == integer(at)) {old(*data)[i] == saved} by {intro i; omega};} fn main() -> usize {42}";
    replay(source);
    for bad in [
        source.replace("old(*data)[i]", "(*data)[i]"),
        source.replace("i == integer(at)", "0 <= i && i < 8"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
    for domain in ["true", "0 <= i && i <= 8"] {
        assert!(verify(&format!("fn read(data: &[bool; 8]) {{proof _: forall(i: integer) where({domain}) {{(*data)[i] == (*data)[i]}} by {{intro i; omega}};}}")).is_err());
    }
}

#[test]
fn compound_boolean_observations_preserve_all_connectives() {
    let guarded = "fn read(data: &[bool; 8], flag: bool) -> bool where forall(i: integer) where(0 <= i && i < 8) {flag => (*data)[i] == true} ensures flag => result {(*data)[0]} fn main() -> usize {42}";
    replay(guarded);
    assert!(verify(&guarded.replace("ensures flag => result", "ensures result")).is_err());
    let disjunctive = "fn read(data: &[bool; 8], flag: bool) -> bool where forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == flag || (*data)[i] != flag} ensures result == flag {(*data)[0]}";
    assert!(verify(disjunctive).is_err());
    let negated = "fn read(data: &[bool; 8], a: bool, b: bool) -> bool where forall(i: integer) where(0 <= i && i < 8) {(*data)[i] != (a && b)} ensures result != (a && b) {(*data)[0]} fn main() -> usize {42}";
    replay(negated);
    assert!(verify(&negated.replace("ensures result !=", "ensures result ==")).is_err());
    let stale = "fn read(data: &[bool; 8], flag: bool) -> bool where forall(i: integer) where(0 <= i && i < 8) {flag => (*data)[i] == true} modifies(data) ensures flag => result {(*data)[0] = false; (*data)[0]}";
    assert!(verify(stale).is_err());
}

#[test]
fn boolean_observations_remain_sparse_and_do_not_import_admissions() {
    let source = "fn fill(data: &[bool; 8], a: bool, b: bool) modifies(data) ensures (*data)[2] == (a && !b) {arrays::fill_range(data, 0, 8, a && !b);} fn main() -> usize {42}";
    let huge = source
        .replace("; 8]", "; 1000000000]")
        .replace(", 0, 8,", ", 0, 1000000000,");
    let (a, ca) = prove(source).unwrap();
    let (b, cb) = prove(&huge).unwrap();
    assert_eq!(a.obligations, b.obligations);
    assert_eq!(ca.certificate_count(), cb.certificate_count());
    assert_eq!(
        verify_with_certificate(&huge, &cb)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(crate::compiler::native::emit(&b).unwrap().len() < 16384);
    assert!(verify("fn read(data: &[bool; 8], a: bool, b: bool) -> bool ensures result == (a && b) {proof lie: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == (a && b)} by {trustme}; (*data)[0]}").is_err());
}
