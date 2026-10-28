use crate::compiler::verify::{prove, verify, verify_with_certificate};

#[test]
fn ideal_definitions_expose_exact_symbolic_scalar_results() {
    for source in [
        "ideal fn affine(n: integer) -> integer {3 * n + 2} ideal fn check(n: integer) {proof _: affine(n) == 3 * n + 2;} fn main() -> usize {42}",
        "ideal fn negate(n: integer) -> integer {-n} ideal fn check(n: integer) {proof _: negate(n) + n == 0;} fn main() -> usize {42}",
        "ideal fn both(a: bool, b: bool) -> bool {a && b} ideal fn same(a: bool, b: bool) -> bool {a == b} ideal fn check(a: bool, b: bool) {proof _: both(a, b) == (a && b); proof _: same(a, b) == (a == b);} fn main() -> usize {42}",
        "ideal fn plus(n: nat) -> nat {n + 1} ideal fn check(n: nat) {proof _: integer(plus(n)) == integer(n) + 1;} fn main() -> usize {42}",
        "ideal fn equal_to_self(n: integer) -> integer {if n == n {n} else {n + 1}} ideal fn check(n: integer) {proof _: equal_to_self(n) == n;} fn main() -> usize {42}",
        "ideal fn local(n: integer) -> integer {let copy = n; copy = copy + 2; copy - old(n)} ideal fn check(n: integer) {proof _: local(n) == 2;} fn main() -> usize {42}",
        "ideal fn view(n: &usize) -> integer {integer(*n)} fn check(n: &usize) {proof _: view(n) == integer(*n);} fn main() -> usize {42}",
        "ideal fn bump(n: integer) -> integer {n + 1} ideal fn twice(n: integer) -> integer {bump(bump(n))} ideal fn check(n: integer) {proof _: twice(n) == n + 2;} fn main() -> usize {42}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn symbolic_scalar_computation_does_not_grant_false_facts() {
    for source in [
        "ideal fn positive(n: usize) -> bool {n > 0} fn check(n: usize) {proof _: positive(n);}",
        "ideal fn affine(n: integer) -> integer {3 * n + 2} ideal fn check(n: integer) {proof _: affine(n) == 3 * n + 3;}",
        "ideal fn minus(n: nat) -> nat {n - 1} ideal fn check(n: nat) {proof _: integer(minus(n)) == integer(n) - 1;}",
        "ideal fn see(n: &usize) -> integer {integer(*n)} fn check(n: &usize) modifies(n) {ideal let before = see(n); *n = 0; proof _: before == see(n);}",
        "ideal fn needs(n: usize) -> bool where n == 42 {true} fn check(n: usize) {proof _: needs(n);}",
        "ideal fn identity(n: integer) -> integer {n} fn main() {ideal let value = identity(42); let runtime: usize = value;}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn symbolic_bounded_results_do_not_depend_on_saved_branch_assumptions() {
    let source = "ideal fn successor(n: nat) -> nat {n + 1} ideal fn view(n: u8) -> u16 {u16(n)} fn check(n: usize, byte: u8, flag: bool) {if flag {proof _: successor(nat(n)) > nat(n); proof _: view(byte) == u16(byte);} else {proof _: successor(nat(n)) > nat(n); proof _: view(byte) == u16(byte);}}";
    let (_, certificate) = prove(source).unwrap();
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    // Unknown branches remain opaque even if a caller happens to know a guard;
    // an earlier cache entry must not import that guard into another path.
    let source = "ideal fn select(n: usize) -> integer {if n == 42 {7} else {8}} fn check(n: usize) {if n == 42 {proof _: select(n) == select(n);} else {proof _: select(n) == 7;}}";
    assert!(verify(source).is_err());
}

#[test]
fn symbolic_reduction_keeps_trusted_safety_dependencies_local() {
    let source = "ideal fn requires_42(n: usize) where n == 42 {} ideal fn positive(n: usize) -> bool {proof admitted: n == 42 by {trustme}; requires_42(n); n > 0} fn check(n: usize) where n > 0 {proof first: positive(n); proof again: positive(n);} fn main() -> usize {check(7); 42}";
    let (program, certificate) = prove(source).unwrap();
    assert_eq!(
        program
            .function_safety_assumptions("check")
            .unwrap()
            .count(),
        1
    );
    assert_eq!(
        program.function_safety_assumptions("main").unwrap().count(),
        1
    );
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace(
        "proof again: positive(n);",
        "proof again: positive(n); proof unrelated: false;"
    ))
    .is_err());
}

#[test]
fn quantified_user_calls_cannot_generalize_a_predicate_over_the_wrong_domain() {
    // Reduction outside a binder must not enable the old, unsound shortcut of
    // hiding a bound argument inside a fresh uninterpreted scalar variable.
    let source = "ideal fn positive(n: integer) -> bool {n > 0} fn check() {proof _: forall(n: integer) where(n >= 0) {positive(n)} by {intro n; omega};}";
    let error = verify(source).unwrap_err();
    assert!(error.contains("cannot prove"), "{error}");
}

#[test]
fn utf8_byte_rules_are_proven_for_symbolic_inputs_without_trust() {
    let source = include_str!("../../../../../examples/utf8_byte_proofs.evg");
    let (program, certificate) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(
        verify("fn wrong(byte: u8) where byte == 128 {proof _: utf8::lead_valid(byte);}").is_err()
    );
    assert!(verify(
        "fn wrong(byte: u8) where byte == 237 {proof _: utf8::first_high(byte) == 191;}"
    )
    .is_err());
}
