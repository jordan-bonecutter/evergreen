use super::*;

const RECORDS: &str = "
type Pair struct {left: u8, right: u8}
type Sample struct {pair: Pair, flag: bool}
impl Copy for Pair {}
impl Copy for Sample {}
";

fn replay(body: &str) -> VerifiedProgram {
    let source = format!("{RECORDS}{body}");
    let (program, bundle) = prove(&source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    program
}

fn reject(body: &str) {
    let source = format!("{RECORDS}{body}");
    assert!(verify(&source).is_err(), "{source}");
}

#[test]
fn source_field_contracts_support_ordinary_caller_reads() {
    let source = include_str!("../../../../examples/array_field_proofs.evg");
    let (program, bundle) = prove(source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn record_projection_congruence_keeps_each_field_and_index_distinct() {
    let source = "fn check(data: &[Sample; 8]) {
        proof _: forall(i: integer) where (0 <= i && i < 8) {
            forall(j: integer) where (j == i) {(*data)[i].pair.left == (*data)[j].pair.left}
        } by {intro i; intro j; omega};
    }";
    replay(source);
    reject(&source.replace("[j].pair.left", "[j].pair.right"));
    reject(&source.replace("j == i", "j == 7"));
    for domain in ["true", "0 <= i && i <= 8"] {
        for tactic in ["intro i; omega", "trustme"] {
            let source = format!("{RECORDS}fn check(data: &[Sample; 8]) {{proof _: forall(i: integer) where ({domain}) {{(*data)[i].pair.left == (*data)[i].pair.left}} by {{{tactic}}};}}");
            let error = verify(&source).unwrap_err();
            assert!(error.contains("quantified array index bounds"), "{error}");
        }
    }
}

#[test]
fn projected_read_bindings_capture_the_original_field_and_revision() {
    let source = "fn read(data: &[Sample; 8], at: usize) where at < 8 modifies(data) {
        let saved = (*data)[at].pair.left;
        proof _: forall(i: integer) where (i == integer(at)) {(*data)[i].pair.left == saved} by {intro i; omega};
        (*data)[at].pair.left = 42;
        proof _: forall(i: integer) where (i == integer(at)) {old(*data)[i].pair.left == saved} by {intro i; omega};
    }";
    replay(source);
    reject(&source.replace("old(*data)[i]", "(*data)[i]"));
    reject(&source.replace("[i].pair.left", "[i].pair.right"));
    reject(&source.replace("i == integer(at)", "0 <= i && i < 8"));
}

#[test]
fn projected_contracts_describe_numeric_and_boolean_reads() {
    let source = "fn read(data: &[Sample; 8], at: usize, a: bool, b: bool) -> bool
        where at < 8 && (forall(i: integer) where (0 <= i && i < 8) {(*data)[i].flag == (a && !b)})
        ensures result == (a && !b)
    {(*data)[at].flag}";
    replay(source);
    reject(&source.replace("ensures result ==", "ensures result !="));
    let numeric = "fn read(data: &[Sample; 8], at: usize) -> u8
        where at < 8 && (forall(i: integer) where (0 <= i && i < 8) {(*data)[i].pair.left == 7})
        ensures result == 7
    {(*data)[at].pair.left}";
    replay(numeric);
    reject(&numeric.replace("{(*data)[at].pair.left}", "{(*data)[at].pair.right}"));
    reject(
        &numeric
            .replace("ensures result == 7", "modifies(data) ensures result == 7")
            .replace(
                "{(*data)[at].pair.left}",
                "{(*data)[at].pair.left = 9; (*data)[at].pair.left}",
            ),
    );
}

#[test]
fn field_stores_preserve_siblings_and_the_unobserved_remainder() {
    let source = "fn set(data: &[Sample; 8], at: usize, value: u8) where at < 8 modifies(data) {
        (*data)[at].pair.left = value;
        proof _: forall(i: integer) where (i == integer(at)) {(*data)[i].pair.left == value} by {intro i; omega};
        proof _: forall(i: integer) where (0 <= i && i < 8) {(*data)[i].pair.right == old(*data)[i].pair.right} by {intro i; omega};
        proof _: forall(i: integer) where (0 <= i && i < 8 && i != integer(at)) {(*data)[i].pair.left == old(*data)[i].pair.left} by {intro i; omega};
    }";
    replay(source);
    reject(&source.replace(" && i != integer(at)", ""));
    reject(&source.replace("== value}", "== 0}"));
    let huge = source
        .replace("; 8]", "; 1000000000]")
        .replace("< 8", "< 1000000000");
    let small = format!("{RECORDS}{source}");
    let huge = format!("{RECORDS}{huge}");
    let (a, ca) = prove(&small).unwrap();
    let (b, cb) = prove(&huge).unwrap();
    assert_eq!(a.obligations, b.obligations);
    assert_eq!(ca.certificate_count(), cb.certificate_count());
    verify_with_certificate(&huge, &cb).unwrap();
}

#[test]
fn projected_equalities_preserve_privacy_and_scalar_types() {
    let inside = "module hidden {
        opaque type Secret struct {value: u8}
        fn check(data: &[Secret; 8]) {
            proof _: forall(i: integer) where (0 <= i && i < 8) {(*data)[i].value == (*data)[i].value} by {intro i; omega};
        }
    }";
    replay(inside);
    let outside = inside
        .replace("        fn check", "} fn check")
        .replace("&[Secret; 8]", "&[hidden::Secret; 8]");
    let outside = outside.trim_end().strip_suffix('}').unwrap();
    let error = verify(outside).unwrap_err();
    assert!(error.contains("opaque representation"), "{error}");
    for claim in [
        "(*data)[i].pair.left == (*data)[i].flag",
        "(*data)[i].pair.left == 256",
        "(*data)[i].pair == (*data)[i].pair",
        "(*data)[i].missing == 0",
    ] {
        reject(&format!("fn check(data: &[Sample; 8]) {{proof _: forall(i: integer) where (0 <= i && i < 8) {{{claim}}} by {{trustme}};}}"));
    }
}

#[test]
fn projected_histories_keep_literal_fill_and_branch_values() {
    let source = "fn check(flag: bool) {
        let data: unique(Sample, 8) = alloc(8, Sample {pair: Pair {left: 7, right: 9}, flag: true});
        proof _: forall(i: integer) where (0 <= i && i < 8) {(*data)[i].flag == true} by {intro i; omega};
        if flag {(*data)[0].pair.left = 42;} else {(*data)[1].pair.left = 43;}
        proof _: forall(i: integer) where (0 <= i && i < 8) {(*data)[i].pair.right == 9} by {intro i; omega};
        proof _: forall(i: integer) where (2 <= i && i < 8) {(*data)[i].pair.left == 7} by {intro i; omega};
    }
    fn main() -> usize {check(true); check(false); 42}";
    assert_eq!(replay(source).run().unwrap().to_string(), "42");
    reject(&source.replace("2 <= i", "0 <= i"));
    let literal = "fn main() -> usize {
        let data: [Pair; 2] = [Pair {left: 7, right: 9}, Pair {left: 42, right: 11}];
        proof _: forall(i: integer) where (i == 0) {data[i].left == 7} by {intro i; omega};
        proof _: forall(i: integer) where (i == 1) {data[i].right == 11} by {intro i; omega};
        42
    }";
    assert_eq!(replay(literal).run().unwrap().to_string(), "42");
    reject(&literal.replace("data[i].right", "data[i].left"));
}

#[test]
fn projected_observations_require_the_correct_plane_and_checked_proof() {
    let source = "fn compare(a: &[Sample; 8], b: &[Sample; 8], at: usize)
        where at < 8 && (forall(i: integer) where (0 <= i && i < 8) {(*a)[i].pair.left == (*b)[i].pair.right})
    {let first = (*a)[at].pair.left; let second = (*b)[at].pair.right; proof _: first == second;}";
    replay(source);
    replay(&source.replace(
        "let first = (*a)[at].pair.left; let second = (*b)[at].pair.right;",
        "let second = (*b)[at].pair.right; let first = (*a)[at].pair.left;",
    ));
    reject(&source.replace("(*b)[at].pair.right", "(*a)[at].pair.right"));
    reject(&source.replace("(*b)[at].pair.right", "(*b)[at].pair.left"));
    reject("fn read(data: &[Sample; 8]) -> u8 ensures result == 7 {
        proof lie: forall(i: integer) where (0 <= i && i < 8) {(*data)[i].pair.left == 7} by {trustme};
        (*data)[0].pair.left
    }");
}

#[test]
fn quantified_field_admissions_expire_with_their_array_revision() {
    let source = format!("{RECORDS}fn check(data: &[Sample; 8]) modifies(data) {{
        proof external: forall(i: integer) where (0 <= i && i < 8) {{(*data)[i].pair.left == 7}} by {{trustme}};
        proof again: forall(j: integer) where (0 <= j && j < 8) {{(*data)[j].pair.left == 7}} by {{exact external}};
    }}");
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    verify_with_certificate(&source, &bundle).unwrap();
    for field in ["left", "right"] {
        // The quantified claim currently observes the whole array revision.
        // Even a sibling write requires an explicit preservation proof.
        let changed = source.replace(
            "proof again:",
            &format!("(*data)[0].pair.{field} = 9; proof again:"),
        );
        let error = verify(&changed).unwrap_err();
        assert!(error.contains("earlier state"), "{error}");
    }
}

#[test]
fn captured_boolean_fills_survive_record_stores_and_branch_joins() {
    let source = include_str!("../../../../examples/boolean_record_history.evg");
    let (program, bundle) = prove(source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for bad in [
        source.replace(
            "(*data)[0].pair.left = 42;",
            "(*data)[0].pair.left = 42; (*data)[0].flag = !(a && !b);",
        ),
        source.replace(
            "(*data)[1].pair.left = 43;",
            "(*data)[1].pair.left = 43; (*data)[1].pair.right = 11;",
        ),
        source.replace("2 <= i", "0 <= i"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
    let huge = source
        .replace(", 8", ", 1000000000")
        .replace("alloc(8,", "alloc(1000000000,")
        .replace("< 8", "< 1000000000");
    let (large, large_bundle) = prove(&huge).unwrap();
    assert_eq!(program.obligations, large.obligations);
    assert_eq!(bundle.certificate_count(), large_bundle.certificate_count());
    verify_with_certificate(&huge, &large_bundle).unwrap();
}
