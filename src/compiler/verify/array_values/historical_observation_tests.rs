use super::*;

fn replay(source: &str) -> (VerifiedProgram, usize) {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    (program, bundle.certificate_count())
}

const CHAIN: &str = "fn read(a: &[u8; 8], b: &[u8; 8], c: &[u8; 8], at: usize) -> u8
    where at < 8 &&
        (forall(i: integer) where (0 <= i && i < 8) {(*a)[i] == (*b)[i]}) &&
        (forall(i: integer) where (0 <= i && i < 8) {(*b)[i] == (*c)[i]}) &&
        (forall(i: integer) where (0 <= i && i < 8) {(*c)[i] == 7})
    ensures result == 7
{(*a)[at]}";

#[test]
fn unobserved_scalar_chains_compose_without_dense_storage() {
    let (small, small_certificates) = replay(CHAIN);
    let huge = CHAIN
        .replace("; 8]", "; 1000000000]")
        .replace("< 8", "< 1000000000");
    let (large, large_certificates) = replay(&huge);
    assert_eq!(small.obligations, large.obligations);
    assert_eq!(small_certificates, large_certificates);
    for bad in [
        CHAIN.replace("{(*c)[i] == 7}", "{(*c)[i] == (*a)[i]}"),
        CHAIN.replace("{(*b)[i] == (*c)[i]}", "{(*b)[i] == (*b)[i]}"),
        CHAIN.replace(
            "{(*b)[i] == (*c)[i]}",
            "{(*b)[i] == (*c)[i] || (*b)[i] == 9}",
        ),
        CHAIN
            .replace("{(*a)[at]}", "{(*a)[7]}")
            .replace("i < 8", "i < 7"),
    ] {
        let error = verify(&bad).unwrap_err();
        assert!(error.contains("cannot prove"), "{error}");
    }
}

#[test]
fn unobserved_record_leaves_keep_their_field_and_boolean_types() {
    let source = "type Pair struct {left: u8, right: u8, flag: bool}
    fn read(a: &[Pair; 8], b: &[Pair; 8], c: &[Pair; 8], at: usize) -> bool
        where at < 8 &&
            (forall(i: integer) where (0 <= i && i < 8) {same_value((*a)[i], (*b)[i])}) &&
            (forall(i: integer) where (0 <= i && i < 8) {(*b)[i].left == (*c)[i].right && (*b)[i].flag == (*c)[i].flag}) &&
            (forall(i: integer) where (0 <= i && i < 8) {(*c)[i].right == 7 && (*c)[i].flag == true})
        ensures result
    {(*a)[at].left == 7 && (*a)[at].flag}";
    replay(source);
    for bad in [
        source.replace("{(*a)[at].left", "{(*a)[at].right"),
        source.replace("(*c)[i].right == 7", "(*c)[i].left == 7"),
        source.replace("&& (*a)[at].flag}", "&& !(*a)[at].flag}"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn historical_copy_relations_survive_source_mutation_and_cleanup() {
    let source = "fn release(data: unique(u8, 8)) {}
    fn read(a: &[u8; 8]) -> u8
        where (forall(i: integer) where (0 <= i && i < 8) {(*a)[i] == 7})
        ensures result == 7
    {
        let b: unique(u8, 8) = alloc(8, 0);
        let c: unique(u8, 8) = alloc(8, 0);
        arrays::copy_range(a, &*b, 0, 8);
        arrays::copy_range(&*b, &*c, 0, 8);
        (*b)[0] = 9;
        release(b);
        (*c)[0]
    }
    fn main() -> u8 {let a: [u8; 8] = [7, 7, 7, 7, 7, 7, 7, 7]; read(&a)}";
    assert_eq!(replay(source).0.run().unwrap().to_string(), "7");
    for bad in [
        source.replace(
            "        arrays::copy_range(&*b",
            "        (*b)[0] = 9; arrays::copy_range(&*b",
        ),
        source.replace("        (*c)[0]", "        (*c)[0] = 9; (*c)[0]"),
        source.replace("        (*c)[0]", "        (*b)[0]"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn intermediate_observations_do_not_leak_branch_facts_or_admissions() {
    let source = "fn read(a: &[u8; 8], b: &[u8; 8], flag: bool)
        where
            (forall(i: integer) where (0 <= i && i < 8) {(*a)[i] == (*b)[i]}) &&
            (forall(i: integer) where (flag && 0 <= i && i < 8) {(*b)[i] == 7})
    {
        if flag {let first = (*a)[0]; proof _: first == 7;}
        if flag {let second = (*a)[0]; proof _: second == 7;}
    }";
    replay(source);
    assert!(verify(&source.replace("if flag {let second", "{let second")).is_err());
    let admitted = "fn read(a: &[u8; 8], b: &[u8; 8]) -> u8
        where (forall(i: integer) where (0 <= i && i < 8) {(*a)[i] == (*b)[i]})
        ensures result == 7
    {
        proof assumed: forall(i: integer) where (0 <= i && i < 8) {(*b)[i] == 7} by {trustme};
        (*a)[0]
    }";
    assert!(verify(admitted).is_err());
}

#[test]
fn repeated_relocation_preserves_whole_payloads_without_recreating_owners() {
    let source = include_str!("../../../../examples/repeated_relocation.evg");
    let (program, _) = replay(source);
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(
        events
            .iter()
            .filter(|event| event.as_str() == "drop Pair")
            .count(),
        1
    );
    let wrong = source.replace("x: 42", "x: 43");
    let error = verify(&wrong).unwrap_err();
    assert!(error.contains("cannot prove proof preserved"), "{error}");
}
