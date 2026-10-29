use super::*;

const TYPES: &str = "type Pair struct {x: usize, valid: bool} type Item struct {pair: Pair, tag: u8} impl Copy for Pair {} impl Copy for Item {}";

fn replay(body: &str) {
    let source = format!("{TYPES} {body}");
    let (program, bundle) = prove(&source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn structural_values_replay_without_runtime_equality_or_copy_permission() {
    replay(include_str!(
        "../../../../../examples/slot_value_contracts.evg"
    ));
    assert!(verify("fn wrong(slot: &(usize | shape(usize)), value: usize) where typeof(*slot) == shape(usize) {proof _: same_value(*slot, value);}").is_err());
    replay("fn duplicate(x: Item) -> Item ensures same_value(result, x) {x} fn main() {let item = Item {pair: Pair {x: 7, valid: true}, tag: 3}; let other = duplicate(item); proof _: same_value(item, other); proof _: other.pair.x == 7;}");
    replay("fn check(x: Item, y: Item) where same_value(x, y) ensures x.tag == y.tag && x.pair.x == y.pair.x && x.pair.valid == y.pair.valid {}");
    replay("fn check(x: Item) {proof _: same_value(x, x);}");
    replay("fn check(x: &Item) {proof _: same_value(x, x);}");
    let source = format!("{TYPES} fn check(x: Item) {{proof _: same_value(x, x);}}")
        .replace("impl Copy for Item {}", "");
    verify(&source).unwrap();
}

#[test]
fn structural_indexed_values_preserve_fields_and_bounds() {
    replay("fn check(data: &[Item; 8], at: usize, initial: Item) -> bool where at < 8 && (forall(i: integer) where(0 <= i && i < 8) {same_value((*data)[i], initial)}) ensures result {(*data)[at].tag == initial.tag && (*data)[at].pair.x == initial.pair.x && (*data)[at].pair.valid == initial.pair.valid}");
    replay("fn check(a: &[Item; 8], b: &[Item; 8]) {proof _: (forall(i: integer) where(0 <= i && i < 8) {same_value((*a)[i], (*b)[i])}) => (forall(j: integer) where(0 <= j && j < 8) {same_value((*b)[j], (*a)[j])}) by {intro all; intro j; omega};}");
    for body in [
        "fn check(x: Item, y: Item) {proof _: same_value(x, y);}",
        "fn check(x: Item, y: Item) where x.pair.x == y.pair.x && x.tag == y.tag {proof _: same_value(x, y);}",
        "fn check(data: &[Item; 8]) {proof _: forall(i: integer) {same_value((*data)[i], (*data)[i])};}",
        "fn check(x: Item) -> bool {same_value(x, x)}",
    ] {
        assert!(verify(&format!("{TYPES} {body}")).is_err(), "{body}");
    }
}

#[test]
fn structural_admissions_keep_subjects_and_revisions() {
    let source = format!("{TYPES} fn main() {{let x = Pair {{x: 1, valid: true}}; let y = Pair {{x: 2, valid: false}}; proof assumed: same_value(x, y) by {{trustme}}; proof used: same_value(x, y) by {{exact assumed}};}}");
    let (_, bundle) = prove(&source).unwrap();
    verify_with_certificate(&source, &bundle).unwrap();
    for bad in [
        source.replace("proof used:", "x.x = 3; proof used:"),
        source.replace("proof used: same_value(x, y)", "proof used: false"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn record_collection_contracts_execute_replay_and_remain_sparse() {
    let source = include_str!("../../../../../examples/record_collections.evg");
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
        source.replace("same_value(b[1], wanted)", "same_value(b[1], initial)"),
        source.replace("same_value(popped, wanted)", "same_value(popped, initial)"),
        source.replace("same_value(after, wanted)", "same_value(after, initial)"),
        source.replace(
            "let after = v.pop();",
            "*v.get(0) = initial; let after = v.pop();",
        ),
    ] {
        let error = verify(&bad).unwrap_err();
        assert!(error.contains("cannot prove"), "{error}");
    }
    let small = format!("{TYPES} fn copy(a: &[Item; 8], b: &[Item; 8]) modifies(b) {{arrays::copy_range(a, b, 0, 8);}}");
    let large = small
        .replace("; 8]", "; 1000000000]")
        .replace(", 0, 8)", ", 0, 1000000000)");
    let (small, a) = prove(&small).unwrap();
    let (large_program, b) = prove(&large).unwrap();
    assert_eq!(small.obligations, large_program.obligations);
    assert_eq!(a.certificate_count(), b.certificate_count());
    verify_with_certificate(&large, &b).unwrap();
}

#[test]
fn structural_equality_does_not_mint_authority_or_observe_invalid_storage() {
    for source in [
        "type Value struct {n: usize} fn main() {let a = Value {n: 7}; let b = a; proof _: same_value(a, b);}",
        "type Empty struct {} fn check(data: &[Empty; 0]) {proof _: forall(i: integer) where(i == 0) {same_value((*data)[i], (*data)[i])};}",
        "fn main() {proof _: same_value(usize::MAX + 1, usize::MAX + 1);}",
        "fn main() {proof _: same_value(true, 1);}",
    ] {
        assert!(verify(source).is_err(), "{source}");
    }
    replay("module hidden {opaque type Value struct {x: usize} fn make(x: usize) -> Value {Value {x: x}}} fn check(x: hidden::Value) {proof _: same_value(x, x);}");
    replay("type Empty struct {} fn check(data: &[Empty; 0]) {proof _: forall(i: integer) where(0 <= i && i < 0) {same_value((*data)[i], (*data)[i])} by {intro i; omega};}");
}

#[test]
fn owning_value_contracts_preserve_identity_without_copying_or_reviving_storage() {
    let source = include_str!("../../../../../examples/buffer_values.evg");
    let (program, certificate) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(
        events
            .iter()
            .filter(|event| event.as_str() == "drop Item")
            .count(),
        1
    );
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    verify("type Sized struct {cap: usize, data: unique(usize, cap)} impl Drop for Sized {fn drop({cap, data}) {}} fn identity(value: Sized) -> Sized ensures same_value(result, value) {value} fn main() -> usize {42}").unwrap();
    verify("fn identity(value: [unique(usize); 2]) -> [unique(usize); 2] ensures same_value(result, value) {value} fn main() -> usize {42}").unwrap();
    for bad in [
        "fn main() {let a = alloc(42); let b = alloc(42); proof _: same_value(a, b);}",
        "fn stale(owner: unique(usize)) {drop(owner); proof _: same_value(old(owner), old(owner));}",
        "fn duplicate(owner: unique(usize)) {proof _: same_value(owner, owner); let first = owner; let second = owner;}",
    ] {
        assert!(verify(bad).is_err(), "accepted {bad}");
    }
}

#[test]
fn union_value_equality_compares_only_matching_live_payloads() {
    replay("fn check(x: &(usize | bool), y: &(usize | bool)) where typeof(*x) == usize && typeof(*y) == usize {let a: usize = *x; let b: usize = *y; if a == b {proof _: same_value(*x, *y);}}");
    for bad in [
        "fn main() {let a: usize | bool = 7; let b: usize | bool = 8; proof _: same_value(a, b);}",
        "fn main() {let a: usize | bool = 1; let b: usize | bool = true; proof _: same_value(a, b);}",
    ] {
        assert!(verify(bad).is_err(), "accepted {bad}");
    }
}

#[test]
fn owning_array_frames_remain_sparse_and_do_not_preserve_the_changed_slot() {
    let source = include_str!("../../../../../examples/owning_array_frame.evg");
    let (program, certificate) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    let huge = source.replace('3', "1000000000");
    assert_eq!(verify(&huge).unwrap().obligations, program.obligations);
    let changed = source.replace("i < integer::from(length) - 1", "i < integer::from(length)");
    assert!(verify(&changed).is_err());
}

#[test]
fn range_specialization_checks_congruence_for_repeated_indices() {
    let source = r#"fn check(capacity: usize, a: &[unique(usize) | shape(unique(usize)); capacity], b: &[unique(usize) | shape(unique(usize)); capacity], index: usize)
where 0 < index && index <= capacity && (forall(i: integer) where (0 <= i && i < integer::from(capacity)) {same_value((*a)[i], (*b)[i])})
ensures forall(j: integer) where (0 <= j && j < integer::from(capacity) && j == integer::from(index) - 1) {same_value((*a)[integer::from(index) - 1], (*b)[j])}
{
proof before: forall(i: integer) where (0 <= i && i < integer::from(capacity)) {same_value((*a)[i], (*b)[i])} by {assumption};
proof after: forall(j: integer) where (0 <= j && j < integer::from(capacity) && j == integer::from(index) - 1) {same_value((*a)[integer::from(index) - 1], (*b)[j])} by {using before; intro prior; intro j; omega};
}
fn main() -> usize {42}
"#;
    let (_, certificate) = prove(source).unwrap();
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    let unrelated = source.replace(" && j == integer::from(index) - 1", "");
    assert!(verify(&unrelated).is_err());
}

#[test]
fn owning_buffer_growth_exposes_reference_free_payload_values() {
    let source = include_str!("../../../../../examples/buffer_record_values.evg");
    let (program, certificate) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(
        events
            .iter()
            .filter(|event| event.as_str() == "drop Item")
            .count(),
        2
    );
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    let wrong = source.replace("Item {tag: 42}", "Item {tag: 43}");
    let error = verify(&wrong).unwrap_err();
    assert!(error.contains("cannot prove proof preserved"), "{error}");
}
