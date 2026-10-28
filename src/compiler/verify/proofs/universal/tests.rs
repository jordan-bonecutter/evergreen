use super::*;

fn replay(source: &str, admissions: usize) {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert_eq!(program.trusted_assumptions().len(), admissions);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn named_specializations_feed_cases_and_nested_universal_proofs() {
    for source in [
        "fn main() {proof all: forall(i: integer) where(i >= 0) {i >= 0} by {intro i; omega}; proof derived: 5 >= 0 && 5 + 1 >= 1 by {specialize all(5) as positive; omega; constructor; exact positive; omega};}",
        "fn main() {proof transport: (forall(i: integer) where(i >= 0) {i == 0 || i == 1}) => 7 <= 1 by {intro all; specialize all(7) as either; omega; cases either with zero | one; omega; omega};}",
        "fn main() {proof all: forall(i: integer) {forall(j: integer) {i + j == j + i}} by {intro i; intro j; omega}; proof symmetric: forall(k: integer) {5 + k == k + 5} by {intro k; specialize all(5) as first; omega; specialize first(k) as second; omega; exact second};}",
        "module bounds {fn check<const N: usize>(x: usize) -> usize where(x < N) {proof all: forall(i: integer) where(0 <= i && i < integer(N)) {i <= integer(N) - 1} by {intro i; omega}; proof picked: integer(x) <= integer(N) - 1 by {specialize all(x) as bound; omega; exact bound}; x}} fn main() -> usize {bounds::check::<10>(7)}",
    ] {replay(source, 0);}
}

#[test]
fn named_specializations_cannot_skip_domains_escape_scope_or_shadow_names() {
    for source in [
        "fn main() {proof all: forall(i: integer) where(i >= 0) {i >= 0} by {intro i; omega}; proof bad: -1 >= 0 by {specialize all(-1) as positive; omega; exact positive};}",
        "fn main() {proof all: forall(i: integer) where(i == 7) {i == 7} by {intro i; omega}; proof bad: forall(j: integer) {j == 7} by {intro j; specialize all(j) as chosen; omega; exact chosen};}",
        "fn main() {proof all: forall(i: integer) {i == i} by {intro i; omega}; proof used: 5 == 5 by {specialize all(5) as same; omega; exact same}; proof escaped: 5 == 5 by {exact same};}",
        "fn main() {proof all: forall(i: integer) {i == i} by {intro i; omega}; proof bad: 5 == 5 by {specialize all(5) as all; omega; exact all};}",
        "fn main() {proof all: forall(i: integer) {i == i} by {intro i; omega}; proof bad: forall(j: integer) {j == j} by {intro j; specialize all(j) as j; omega; exact j};}",
        "fn main() {fact declared = forall(i: integer) {i == i}; proof bad: 5 == 5 by {specialize declared(5) as same; omega; exact same};}",
    ] {assert!(verify(source).is_err(), "{source}");}
}

#[test]
fn named_specializations_keep_admitted_subjects_even_under_open_domains() {
    let source = "fn main() {
        let x: usize = 43; let y: usize = 43;
        proof external: forall(i: integer) where(i >= 0) {x == 42} by {trustme};
        proof used: forall(j: integer) where(j >= 0) {x == 42} by {
            intro j; specialize external(j) as selected; omega; exact selected
        };
    }";
    replay(source, 1);
    let wrong_subject = source.replace("where(j >= 0) {x == 42}", "where(j >= 0) {y == 42}");
    let error = verify(&wrong_subject).unwrap_err();
    assert!(
        error.contains("different proposition or an earlier state"),
        "{error}"
    );
    let changed = source.replace("proof used:", "x = 44; proof used:");
    assert!(verify(&changed)
        .unwrap_err()
        .contains("earlier or unresolved state"));
    let leaked = format!(
        "{} proof unrelated: y == 44; }}",
        source.trim_end().strip_suffix('}').unwrap()
    );
    let error = verify(&leaked).unwrap_err();
    assert!(error.contains("cannot prove"), "{error}");
}
