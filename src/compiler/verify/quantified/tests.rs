use super::*;
use crate::syntax::format::test_edit::SourceEdit;

#[test]
fn universal_premises_use_scoped_specialization_and_logical_cases() {
    for source in [
        "fn main() -> usize {proof restrict: (forall(i: integer) where(i >= 0) {i >= 5}) => (forall(j: integer) where(j >= 1) {j >= 5}) by {intro all; intro j; specialize all(j); omega}; 42}",
        "fn main() -> usize {proof select: (forall(i: integer) where(i >= 0) {i >= 5}) => 7 >= 5 by {intro all; specialize all(7); omega}; 42}",
        "fn main() -> usize {proof select: ((forall(i: integer) where(i >= 0) {i >= 5}) && 7 >= 0) => 7 >= 5 by {intro both; cases both with all, positive; specialize all(7); exact positive}; 42}",
        "fn main() -> usize {proof either: ((forall(i: integer) {i == 0}) || (forall(j: integer) {j == 1})) => ((forall(k: integer) {k == 1}) || (forall(k: integer) {k == 0})) by {intro either; cases either with zero | one; right; exact zero; left; exact one}; 42}",
    ] {
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
    }
}

#[test]
fn universal_premises_cannot_escape_scope_skip_domains_or_generalize_one_point() {
    for source in [
        "fn main() -> usize {proof select: (forall(i: integer) where(i >= 0) {i >= 5}) => -1 >= 5 by {intro all; specialize all(-1); omega}; 42}",
        "fn main() -> usize {proof select: (forall(i: integer) where(i >= 0) {i >= 5}) => 7 >= 5 by {intro all; specialize all(7); omega}; proof escaped: 7 >= 5 by {specialize all(7); omega}; 42}",
        "fn main() -> usize {proof bad: (forall(i: integer) where(i == 7) {i == 7}) => (forall(j: integer) {j == 7}) by {intro all; intro j; specialize all(j); omega}; 42}",
        "fn main() -> usize {proof bad: (forall(i: integer) where(i >= 0) {i >= 5}) => 7 == 0 by {intro all; omega}; 42}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn source_universals_introduce_specialize_execute_and_replay() {
    let source = include_str!("../../../../examples/universal.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let bytes = crate::compiler::native::emit(&program).unwrap();
    let erased = verify("fn main() -> usize {let index: usize = 7; 42}").unwrap();
    assert_eq!(bytes, crate::compiler::native::emit(&erased).unwrap());
}

#[test]
fn source_universals_track_free_parameters_and_nested_bindings() {
    for source in [
        "fn bounded(n: usize, k: usize) -> usize where(k < n) {proof range: forall(i: integer) where(0 <= i && i < integer(n)) {i <= integer(n) - 1} by {intro i; omega}; proof selected: integer(k) <= integer(n) - 1 by {specialize range(k); omega}; k} fn main() -> usize {bounded(10, 7)}",
        "fn main() -> usize {proof pair: forall(i: integer) {forall(j: integer) where(j >= 0) {i + j >= i}} by {intro a; intro b; omega}; proof five: forall(k: integer) where(k >= 0) {5 + k >= 5} by {specialize pair(5); omega}; proof seven: 5 + 7 >= 5 by {specialize five(7); omega}; 7}",
        "fn main() -> usize {let i: usize = 7; proof p: forall(i: integer) {forall(i: integer) {i == i}} by {intro a; intro b; omega}; proof outer_restored: i == 7; i}",
        "fn main() -> usize {let value: usize = 7; fact positive = integer(value) >= 0; proof p: forall(i: integer) where(i >= 0) {positive && i >= 0} by {intro i; constructor; omega; omega}; value}",
        "fn main() -> usize {proof vacuous: forall(i: integer) where(false) {i == 123} by {intro i; omega}; 7}",
    ] {
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "7");
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn source_universals_remain_sparse_and_follow_generic_and_module_scopes() {
    let small = "fn main() -> usize {proof p: forall(i: integer) where(0 <= i && i < 10) {i < 10} by {intro i; omega}; 7}";
    let huge = small.replace_evg("10", "1000000000");
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

    let generic = "module bounds {fn check<const N: usize>(x: usize) -> usize where(x < N) {proof p: forall(i: integer) where(0 <= i && i < integer(N)) {i <= integer(N) - 1} by {intro i; omega}; proof picked: integer(x) <= integer(N) - 1 by {specialize p(x); omega}; x}} fn main() -> usize {bounds::check::<10>(7)}";
    assert_eq!(verify(generic).unwrap().run().unwrap().to_string(), "7");
    let fields = "type Bounds struct {limit: usize} fn check(b: &Bounds, x: usize) -> usize where(x < b.limit) {proof p: forall(i: integer) where(0 <= i && i < integer(b.limit)) {i <= integer(b.limit) - 1} by {intro i; omega}; proof picked: integer(x) <= integer(b.limit) - 1 by {specialize p(x); omega}; x} fn main() -> usize {let b = Bounds {limit: 10}; check(&b, 7)}";
    let (program, bundle) = prove(fields).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "7");
    assert_eq!(
        verify_with_certificate(fields, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn source_universals_reject_single_index_proofs_wrong_instances_and_effects() {
    for (source, fragment) in [
        ("fn main() -> usize {proof bad: forall(i: integer) {i == 0} by {intro i; omega}; 0}", "cannot prove"),
        ("fn main() -> usize {proof p: forall(i: integer) where(i >= 0) {i >= 0} by {intro i; omega}; proof bad: -1 >= 0 by {specialize p(-1); omega}; 0}", "cannot prove"),
        ("fn main() -> usize {proof p: forall(i: integer) where(i >= 0) {i >= 0} by {intro i; omega}; proof bad: 1 == 0 by {specialize p(1); omega}; 0}", "different proposition"),
        ("ideal fn predicate(x: integer) -> bool {x >= 0} fn main() -> usize {fact bad = forall(i: integer) {predicate(i)}; 0}", "structured bound-dependent"),
        ("fn main() -> usize {let data: [usize; 2] = [7, 9]; fact bad = forall(i: integer) where(i >= 0 && i < 2) {data[i] == 7}; 0}", "structured bound-dependent"),
        ("fn main() -> usize {let bad = forall(i: integer) {i == i}; 0}", "proof-only"),
        ("fn main() -> usize {let n: usize = 1; fact bad = forall(i: integer) {n + 1 >= n}; 0}", "quantified arithmetic uses integer"),
        ("fn main() -> usize {fact bad = forall(i: integer) where(forall(j: integer) {true}) {true}; 0}", "unquantified scalar proposition"),
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains(fragment), "expected {fragment}: {error}");
    }
}

#[test]
fn admitted_universals_are_scoped_to_their_actual_subjects_and_revisions() {
    let before = "fn main() -> usize {let n: usize = 7; proof external: forall(i: integer) {integer(n) == 42} by {trustme}; proof selected: integer(n) == 42 by {specialize external(0); omega}; 0}";
    let (program, bundle) = prove(before).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        verify_with_certificate(before, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let stale = before.replace_evg("proof selected:", "n = 8; proof selected:");
    assert!(verify(&stale)
        .unwrap_err()
        .contains("earlier or unresolved state"));
    let wrong_subject = before.replace_evg(
        "proof selected: integer(n)",
        "let m: usize = 7; proof selected: integer(m)",
    );
    assert!(verify(&wrong_subject)
        .unwrap_err()
        .contains("different subject or state"));
    let renamed = before.replace_evg(
        "proof selected: integer(n) == 42 by {specialize external(0); omega};",
        "proof renamed: forall(j: integer) {integer(n) == 42} by {exact external};",
    );
    assert!(verify(&renamed).is_ok());
    let nested = "fn main() -> usize {proof p: forall(i: integer) {forall(j: integer) where(j >= 0) {i + j >= i}} by {trustme}; proof five: forall(k: integer) where(k >= 0) {5 + k >= 5} by {specialize p(5); omega}; proof seven: 5 + 7 >= 5 by {specialize five(7); omega}; 0}";
    let (program, bundle) = prove(nested).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        verify_with_certificate(nested, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let unrelated = "fn process(x: usize) where(x == 42) {} fn main() -> usize {proof unused: forall(i: integer) {false} by {trustme}; process(43); 0}";
    assert!(verify(unrelated).unwrap_err().contains("cannot prove"));
}
