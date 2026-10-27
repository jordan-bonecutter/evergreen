use super::*;

#[test]
fn boolean_matches_share_branch_proofs_effects_and_ownership_rules() {
    let source = include_str!("../../../examples/match.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    let wrong_member = source.replace("true => flag(value)", "true => word(value)");
    assert!(verify(&wrong_member)
        .unwrap_err()
        .contains("active raw union member"));
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let owning = include_str!("../../../examples/raw_union_owner_drop.evg").replace(
        "if present {discard_owner(data)} else {discard_empty(data)}",
        "match present {true => discard_owner(data), false => discard_empty(data)}",
    );
    let (program, bundle) = prove(&owning).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(
        events,
        ["drop MaybeOwner", "drop MaybeOwner", "drop Resource"]
    );
    assert_eq!(
        verify_with_certificate(&owning, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for source in [
        "fn main() -> usize {match false {false => 42, true => 1}}",
        "fn main() -> usize {match false {true => 1, _ => 42}}",
        "fn main() -> usize {match true {_ => 42}}",
        "fn main() -> usize {match true {true => {match false {false => 42, _ => 1}}, false => 1}}",
        "fn main() -> usize {let owner: plane(usize) = alloc(42); match true {true => drop(owner), false => drop(owner)} 42}",
        "fn main() {match true {true => {}, false => {}}}",
    ] {assert!(verify(source).is_ok(), "rejected {source}");}
}

#[test]
fn matching_rejects_missing_duplicate_unreachable_and_ill_typed_cases() {
    for source in [
        "fn main() {match true {true => ()}}",
        "fn main() {match true {}}",
        "fn main() {match true {true => (), true => (), false => ()}}",
        "fn main() {match true {_ => (), false => ()}}",
        "fn main() {match true {true => (), false => (), _ => ()}}",
        "fn main() {match 42 {true => (), false => ()}}",
        "fn main() {match true {1 => (), _ => ()}}",
        "fn main() -> usize {match true {true => 42, false => true}}",
        "fn main() {match true {true => {42;}, false => {()}}}",
        "fn main() -> usize {let owner: plane(usize) = alloc(42); match true {true => drop(owner), false => ()}; *owner}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}
