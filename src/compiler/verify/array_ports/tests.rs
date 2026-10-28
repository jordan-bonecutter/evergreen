use super::*;

pub(super) fn check(source: &str) {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn billion_element_reference_inputs_only_materialize_observed_ports() {
    for source in [
        "fn unused(refs: [&usize; 1000000000]) {}",
        "fn last(refs: &[&usize; 1000000000]) -> usize {*(*refs)[999999999]}",
        "fn same(refs: &[&usize; 1000000000]) -> bool ensures result {(*refs)[999999999] == (*refs)[999999999]}",
        "fn old_port(refs: &[&usize; 1000000000]) {ideal let saved = old((*refs)[999999999]); proof unchanged: saved == (*refs)[999999999];}",
        "fn choose(refs: &[&usize; 1000000000], flag: bool) -> usize {if flag {*(*refs)[999999999]} else {*(*refs)[999999999]}}",
        "fn observe_one_arm(refs: &[&usize; 1000000000], flag: bool) -> usize {let ignored = if flag {*(*refs)[999999999]} else {0}; *(*refs)[999999999]}",
        "fn observe_nested(refs: &[[&usize; 1000000000]; 1000000000], flag: bool) -> usize {let ignored = if flag {*(*refs)[999999999][999999999]} else {0}; *(*refs)[999999999][999999999]}",
        "type Positive struct {value: usize} where value > 0; fn observe_refined(refs: &[&Positive; 1000000000], flag: bool) -> usize {let ignored = if flag {(*(*refs)[999999999]).value} else {0}; (*(*refs)[999999999]).value}",
        "fn bump(refs: &[&usize; 1000000000]) where *(*refs)[999999999] < usize::MAX modifies((*refs)[999999999]) ensures *(*refs)[999999999] == old(*(*refs)[999999999]) + 1 {*(*refs)[999999999] = *(*refs)[999999999] + 1;}",
        "fn set(refs: &[&usize; 1000000000]) modifies((*refs)[999999999]) ensures *(*refs)[0] == old(*(*refs)[0]) {*(*refs)[999999999] = 42;}",
        "fn nested(refs: &[[&usize; 1000000000]; 1000000000]) -> usize {*(*refs)[999999999][999999999]}",
        "fn empty(input: [[[&usize; 0]; 1000000000]; 1000000000]) -> [[[&usize; 0]; 1000000000]; 1000000000] {input}",
        "type Positive struct {value: usize} where value > 0; fn choose(refs: &[&Positive; 1000000000], flag: bool) -> usize {if flag {(*(*refs)[999999999]).value} else {(*(*refs)[999999999]).value}}",
        "fn set(n: usize, refs: &[&usize; n]) where n > 0 modifies((*refs)[0]) ensures *(*refs)[0] == 42 {*(*refs)[0] = 42;}",
    ] {check(source);}
}

#[test]
fn deferred_reference_ports_preserve_actual_alias_checks() {
    let example = include_str!("../../../../examples/sparse_arrays.evg");
    check(example);
    assert_eq!(verify(example).unwrap().run().unwrap().to_string(), "42");
    let prefix = "fn set(refs: &[&usize; 2]) modifies((*refs)[1]) ensures *(*refs)[0] == old(*(*refs)[0]) {*(*refs)[1] = 42;}";
    let source = format!("{prefix} fn main() -> usize {{let a: usize = 7; let b: usize = 0; let refs = [&a, &b]; set(&refs); b}}");
    check(&source);
    assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42");
    let bad = source.replace("[&a, &b]", "[&a, &a]");
    assert!(verify(&bad).unwrap_err().contains("body recheck failed"));
    for invalid in [
        "fn bad(refs: &[&usize; 1000000000]) {*(*refs)[999999999] = 42;}",
        "fn bad(refs: &[&usize; 1000000000]) -> usize {*(*refs)[1000000000]}",
        "fn bad(refs: &[&usize; 1000000000]) -> &usize borrows((*refs)[0]) {(*refs)[999999999]}",
        "fn bad(input: &[&usize; 1000000000]) -> [&usize; 1000000000] borrows(result[0]: (*input)[0]) {[]}",
    ] {
        assert!(verify(invalid).is_err(), "accepted {invalid}");
    }
}

#[test]
fn admitted_element_proofs_expire_on_pointee_writes() {
    let prefix = "fn require42(n: usize) where n == 42 {} fn work(refs: &[&usize; 1000000000]) modifies((*refs)[999999999]) {let observed = *(*refs)[999999999]; proof assumed: *(*refs)[999999999] == 42 by {trustme}; require42(*(*refs)[999999999]);";
    let good = format!("{prefix} }}");
    let (program, bundle) = prove(&good).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        verify_with_certificate(&good, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let bad = format!("{prefix} *(*refs)[999999999] = 43; require42(*(*refs)[999999999]); }}");
    assert!(verify(&bad)
        .unwrap_err()
        .contains("precondition of require42"));
}
