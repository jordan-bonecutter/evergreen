use super::*;

#[test]
fn match_blocks_preserve_results_and_clean_up_only_arm_locals() {
    let source = include_str!("../../../examples/match_blocks.evg");
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource", "drop Resource", "drop Resource"]);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for source in [
        "fn main() -> usize {let x: usize = 0; if true {let y: usize = 42; x = y;} x}",
        "fn main() -> usize {let x: usize = 0; if false {x = 1;} else if true {x = 42;} x}",
        "fn main() -> usize {let x = {let y: usize = 42; y}; x}",
        "fn main() -> usize {let owner: unique(usize) = alloc(42); let moved = match false {true => {let selected = owner; selected}, false => {let selected = owner; selected}}; *moved}",
        "fn main() -> usize {let owner: unique(usize) = {let local: unique(usize) = alloc(42); local}; *owner}",
        "type Guard struct {target: &usize} impl Drop for Guard {fn drop(self) modifies(self.target) ensures *self.target == 42 {*self.target = 42;}} fn main() -> usize {let owner = {let local: unique(usize) = alloc(7); let guard = Guard {target: &*local}; local}; *owner}",
        "type Resource struct {tag: usize} impl Drop for Resource {fn drop(self) {}} fn read(a: &Resource, b: usize) -> usize where b <= 35 && a.tag == 7 {a.tag + b} fn main() -> usize {read(&{let item = Resource {tag: 7}; item}, {let value: usize = 35; value})}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|e| panic!("{source}: {e}"));
        assert_eq!(program.run().unwrap().to_string(), "42", "{source}");
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
    assert!(verify("fn main() {match true {true => {42;}, false => {()}}}").is_ok());
}

#[test]
fn block_names_lifetimes_permissions_and_proofs_remain_scoped() {
    for source in [
        "fn main() -> usize {match true {true => {let x: usize = 42;}, false => {}}; x}",
        "fn main() -> usize {let p = {let local: usize = 42; &local}; *p}",
        "fn main() -> usize {let p = match true {true => {let local: usize = 42; &local}, false => {let local: usize = 42; &local}}; *p}",
        "fn main() -> usize {let x: usize = 0; {fact local = x == 0; proof established: local;} proof escaped: local; x}",
        "fn main() -> usize {let x: usize = 0; {proof local: x == 0;} proof escaped: x == 0 by {exact local}; x}",
        "fn bad(target: &usize) {match true {true => {*target = 42;}, false => {}}} fn main() {}",
        "fn main() -> usize {proof bad: {let x: usize = 42; x == 42}; 0}",
        "fn main() -> usize {let x: usize = 42; {let x: usize = 1; x}}",
        "fn main() -> usize {match true {true => {return 42;}, false => 0}}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn loops_nested_in_expression_blocks_cannot_claim_totality() {
    let source = "fn diverge() -> usize {match true {true => {while true invariant(true) {} 42}, false => 0}} fn main() -> usize {0}";
    let program = verify(source).unwrap();
    assert!(
        program
            .functions
            .iter()
            .find(|f| f.name == "diverge")
            .unwrap()
            .partial
    );
    let rejected = source.replace(
        "fn main() -> usize {0}",
        "fn main() -> usize {proof bad: diverge() == 42; 0}",
    );
    assert!(verify(&rejected).is_err());
    let recursive = "fn recur(n: usize) -> usize {match true {true => {let x = recur(n); x}, false => 0}} fn main() -> usize {0}";
    let program = verify(recursive).unwrap();
    assert!(
        program
            .functions
            .iter()
            .find(|f| f.name == "recur")
            .unwrap()
            .partial
    );
    assert!(verify(&recursive.replace(
        "fn main() -> usize {0}",
        "fn main() -> usize {proof bad: recur(0) == 0; 0}"
    ))
    .is_err());
}

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
        "fn main() -> usize {let owner: unique(usize) = alloc(42); match true {true => drop(owner), false => drop(owner)} 42}",
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
        "fn main() -> usize {let owner: unique(usize) = alloc(42); match true {true => drop(owner), false => ()}; *owner}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}
