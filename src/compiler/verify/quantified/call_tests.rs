use super::*;

#[test]
fn quantified_ideal_calls_preserve_bound_variables_in_exact_results() {
    for source in [
        "ideal fn positive(n: integer) -> bool {n >= 0} fn main() -> usize {proof _: forall(i: integer) where(i >= 0) {positive(i)} by {intro i; omega}; 42}",
        "ideal fn affine(n: integer) -> integer {3 * n + 2} fn main() -> usize {proof _: forall(i: integer) {affine(i) == 3 * i + 2} by {intro i; omega}; 42}",
        "ideal fn positive(n: integer) -> bool {n >= 0} fn main() -> usize {proof _: forall(i: integer) where(positive(i)) {i >= 0} by {intro i; omega}; 42}",
        "fn main() -> usize {proof _: forall(i: integer) {integer::from(i) == i} by {intro i; omega}; 42}",
        "ideal fn add(a: integer, b: integer) -> integer {a + b} fn main() -> usize {proof _: forall(i: integer) {forall(j: integer) {add(i, j) == i + j}} by {intro i; intro j; omega}; 42}",
        "ideal fn bump(n: integer) -> integer {n + 1} ideal fn twice(n: integer) -> integer {bump(bump(n))} fn main() -> usize {proof _: forall(i: integer) {twice(i) == i + 2} by {intro i; omega}; 42}",
        "ideal fn select(n: integer) -> integer {if n == 0 {7} else {8}} fn main() -> usize {proof _: forall(i: integer) {select(0) + i == 7 + i} by {intro i; omega}; 42}",
        "fn check(byte: u8) {proof _: forall(i: integer) {integer::from(byte) + i >= i} by {intro i; omega};} fn main() -> usize {check(7); 42}",
        "ideal fn identity(n: integer) -> integer {n} fn main() -> usize {proof _: forall(i: integer) {forall(i: integer) {identity(i) == i}} by {intro a; intro b; omega}; 42}",
    ] {
        let (program, certificate) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &certificate).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn quantified_calls_distinguish_describing_a_fact_from_proving_it() {
    let source = "ideal fn positive(n: integer) -> bool {n >= 0} fn main() -> usize {fact statement = forall(i: integer) {positive(i)}; 42}";
    assert!(verify(source).is_ok());
    let false_proof = source.replace("; 42}", "; proof _: statement by {intro i; omega}; 42}");
    assert!(verify(&false_proof).unwrap_err().contains("cannot prove"));
}

#[test]
fn quantified_calls_reject_opaque_results_unchecked_domains_and_trusted_safety() {
    for (source, fragment) in [
        ("ideal fn select(n: integer) -> integer {if n == 0 {7} else {8}} fn main() {fact p = forall(i: integer) {select(i) == 7};}", "exact scalar expression"),
        ("ideal fn square(n: integer) -> integer {n * n} fn main() {fact p = forall(i: integer) {square(i) >= 0};}", "nonlinear"),
        ("fn runtime(n: usize) -> bool {n > 0} fn main() {fact p = forall(i: integer) {runtime(0)};}", "verified ideal scalar"),
        ("ideal fn view(n: &usize) -> integer {integer(*n)} fn main() {let n: usize = 7; fact p = forall(i: integer) {view(&n) >= i};}", "verified ideal scalar"),
        ("ideal fn needs(n: integer) where n == 42 {} ideal fn unsafe_call(n: integer) -> bool {proof lie: n == 42 by {trustme}; needs(n); true} fn main() {fact p = forall(i: integer) {unsafe_call(i)};}", "trusted safety dependency"),
        ("ideal fn identity(n: integer) -> integer {n} fn main() {fact p = forall(i: integer) {identity(true) == i};}", "type mismatch"),
        ("ideal fn identity(n: integer) -> integer {n} fn main() {fact p = forall(i: integer) {identity() == i};}", "requires all 1 arguments"),
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains(fragment), "expected {fragment}: {error}\n{source}");
    }
}

#[test]
fn quantified_calls_compute_the_body_without_importing_trusted_postconditions() {
    let source = "ideal fn false_claim(n: integer) -> integer ensures result == n + 1 {n} proof {trustme} fn main() -> usize {proof _: forall(i: integer) {false_claim(i) == i} by {intro i; omega}; 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(
        program.function_safety_assumptions("main").unwrap().count(),
        0
    );
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let wrong = source.replace("false_claim(i) == i}", "false_claim(i) == i + 1}");
    assert!(verify(&wrong).unwrap_err().contains("cannot prove"));
    let wrong_domain = source.replace(
        "{false_claim(i) == i}",
        "where(false_claim(i) == 0) {i == 1}",
    );
    assert!(verify(&wrong_domain).unwrap_err().contains("cannot prove"));
}

#[test]
fn quantified_call_subjects_preserve_definition_arguments_and_revisions() {
    let source = "ideal fn add(a: integer, b: integer) -> integer {a + b} fn main() -> usize {let n: usize = 7; proof external: forall(i: integer) {add(i, integer(n)) == i + 42} by {trustme}; proof selected: add(0, integer(n)) == 0 + 42 by {specialize external(0); omega}; 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for bad in [
        source.replace("proof selected:", "n = 8; proof selected:"),
        source.replace(
            "proof selected: add(0, integer(n))",
            "let m: usize = 7; proof selected: add(0, integer(m))",
        ),
        source
            .replace(
                "fn main()",
                "ideal fn other(a: integer, b: integer) -> integer {a + b} fn main()",
            )
            .replace("proof selected: add(", "proof selected: other("),
    ] {
        assert!(verify(&bad).is_err(), "accepted {bad}");
    }
    let renamed = source.replace(
        "proof selected: add(0, integer(n)) == 0 + 42 by {specialize external(0); omega};",
        "proof renamed: forall(j: integer) {add(j, integer(n)) == j + 42} by {exact external};",
    );
    assert!(verify(&renamed).is_ok());
}

#[test]
fn quantified_call_subjects_frame_sibling_fields_and_substitute_nested_binders() {
    let source = "type Pair struct {left: usize, right: usize} ideal fn add(a: integer, b: integer) -> integer {a + b} fn main() -> usize {let pair = Pair {left: 7, right: 8}; proof external: forall(i: integer) {add(i, integer(pair.left)) == i + 42} by {trustme}; pair.right = 9; proof selected: add(0, integer(pair.left)) == 0 + 42 by {specialize external(0); omega}; 42}";
    let (_, bundle) = prove(source).unwrap();
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("pair.right = 9", "pair.left = 9")).is_err());

    let nested = "ideal fn add(a: integer, b: integer) -> integer {a + b} fn main() -> usize {proof external: forall(i: integer) {forall(j: integer) {add(i, j) == 99}} by {trustme}; proof five: forall(k: integer) {add(5, k) == 99} by {specialize external(5); omega}; proof seven: add(5, 7) == 99 by {specialize five(7); omega}; 42}";
    let (_, bundle) = prove(nested).unwrap();
    assert_eq!(
        verify_with_certificate(nested, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&nested.replace("proof seven: add(5, 7)", "proof seven: add(6, 7)")).is_err());
}
