use super::*;

#[test]
fn quantified_calls_prove_preconditions_over_their_domains() {
    for source in [
        "ideal fn successor(n: integer) -> integer where n >= 0 {n + 1} fn main() -> usize {proof _: forall(i: integer) where(i >= 0) {successor(i) >= 1} by {intro i; omega}; 42}",
        "ideal fn add(a: integer, b: integer) -> integer where a >= 0 && b >= 0 {a + b} fn main() -> usize {proof _: forall(i: integer) where(i >= 0) {forall(j: integer) where(j >= 0) {add(i, j) >= i}} by {intro i; intro j; omega}; 42}",
        "ideal fn positive(n: integer) -> bool {n >= 0} ideal fn needs(n: integer) -> integer where positive(n) {n} fn main() -> usize {proof _: forall(i: integer) where(positive(i)) {needs(i) == i} by {intro i; omega}; 42}",
        "ideal fn requires_false(n: integer) -> integer where false {n} fn main() -> usize {proof _: forall(i: integer) where(false) {requires_false(i) == 999} by {intro i; omega}; 42}",
        "ideal fn needs(n: integer) -> bool where n >= 0 {true} fn main() -> usize {proof _: forall(i: integer) where(i >= 0) {forall(j: integer) where(needs(i)) {j == j}} by {intro i; intro j; omega}; 42}",
        "ideal fn needs(n: integer) -> bool where n >= 0 {true} fn main() -> usize {proof _: forall(i: integer) where(needs(0)) {i == i} by {intro i; omega}; 42}",
        "ideal fn at_least(n: integer, floor: integer) -> integer where n >= floor {n} fn check(floor: usize) {proof _: forall(i: integer) where(i >= integer::from(floor)) {at_least(i, integer::from(floor)) >= integer::from(floor)} by {intro i; omega};} fn main() -> usize {check(7); 42}",
        "ideal fn needs(n: integer) -> integer where n >= 0 {n} fn check(n: usize) {proof _: forall(i: integer) {needs(integer(n)) + i >= i} by {intro i; omega};} fn main() -> usize {check(7); 42}",
        "ideal fn needs(n: integer) -> integer where n >= 0 {n} ideal fn nested(n: integer) -> integer where n >= 0 {needs(n)} fn main() -> usize {proof _: forall(i: integer) where(i >= 0) {nested(needs(i)) == i} by {intro i; omega}; 42}",
    ] {
        let (program, certificate) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &certificate).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn quantified_precondition_checks_remain_sparse_and_preserve_captured_revisions() {
    let source = "ideal fn bounded(n: integer, limit: integer) -> integer where n >= 0 && n < limit {n} fn main() -> usize {let limit: usize = 8; proof range: forall(i: integer) where(i >= 0 && i < integer(limit)) {bounded(i, integer(limit)) == i} by {intro i; omega}; 42}";
    let (small, small_bundle) = prove(source).unwrap();
    let large_source = source.replace("limit: usize = 8", "limit: usize = 1000000000");
    let (large, large_bundle) = prove(&large_source).unwrap();
    assert_eq!(small.obligations, large.obligations);
    assert_eq!(
        small_bundle.certificate_count(),
        large_bundle.certificate_count()
    );
    assert_eq!(
        verify_with_certificate(&large_source, &large_bundle)
            .unwrap()
            .proof_search_count(),
        0
    );

    let source = "ideal fn add(a: integer, b: integer) -> integer where a >= 0 && b >= 0 {a + b} fn main() -> usize {let n: usize = 7; proof external: forall(i: integer) where(i >= 0) {add(i, integer(n)) == i + 42} by {trustme}; proof selected: add(0, integer(n)) == 0 + 42 by {specialize external(0); omega}; 42}";
    assert!(verify(source).is_ok());
    assert!(verify(&source.replace("proof selected:", "n = 8; proof selected:")).is_err());
}

#[test]
fn quantified_call_preconditions_cannot_use_the_wrong_domain_or_prove_themselves() {
    for source in [
        "ideal fn needs(n: integer) -> integer where n >= 0 {n} fn main() {fact p = forall(i: integer) {needs(i) == i};}",
        "ideal fn needs(n: integer) -> integer where n > 0 {n} fn main() {fact p = forall(i: integer) where(i >= 0) {needs(i) == i};}",
        "ideal fn needs(n: integer) -> integer where n >= 0 {n} fn main() {proof _: forall(i: integer) {needs(i) == i} by {trustme};}",
        "ideal fn positive(n: integer) -> bool where n >= 0 {n >= 0} fn main() {fact p = forall(i: integer) where(positive(i)) {i >= 0};}",
        "ideal fn needs(n: integer) -> bool where n >= 0 {true} fn main() {fact p = forall(i: integer) where(i >= 0 && needs(i)) {i == i};}",
        "ideal fn needs(n: integer) -> integer where n >= 0 {n} fn main() {fact p = forall(i: integer) where(i >= 0) {forall(j: integer) {needs(j) == j}};}",
        "ideal fn needs(n: integer) -> bool where n >= 0 {true} fn main() {fact p = forall(i: integer) where(i >= 0) {forall(i: integer) where(needs(i)) {i == i}};}",
        "ideal fn needs(n: integer) -> bool where n >= 0 {true} fn main() {let n: usize = 0; fact p = forall(n: integer) {needs(n)};}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("precondition of quantified call") && error.contains("cannot prove"), "{error}\n{source}");
    }
}

#[test]
fn quantified_preconditions_ignore_trusted_posts_and_reject_opaque_computation() {
    for (source, fragment) in [
        ("ideal fn lie(n: integer) -> bool ensures result {false} proof {trustme} ideal fn needs(n: integer) -> integer where lie(n) {n} fn main() {fact p = forall(i: integer) {needs(i) == i};}", "cannot prove"),
        ("ideal fn positive(n: integer) -> bool {if n >= 0 {true} else {false}} ideal fn needs(n: integer) -> integer where positive(n) {n} fn main() {fact p = forall(i: integer) where(i >= 0) {needs(i) == i};}", "precondition of quantified call to needs did not reduce"),
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains(fragment), "{error}\n{source}");
    }
}

#[test]
fn definedness_reuse_cannot_import_a_sibling_branch_condition() {
    let source = "ideal fn needs(n: integer) -> integer where n >= 0 {n} fn check(n: isize) {if n >= 0 {fact valid = forall(i: integer) {needs(integer(n)) == integer(n)};} else {fact invalid = forall(i: integer) {needs(integer(n)) == integer(n)};}} fn main() {check(0);}";
    let error = verify(source).unwrap_err();
    assert!(
        error.contains("precondition of quantified call") && error.contains("cannot prove"),
        "{error}"
    );
}
