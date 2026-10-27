use super::*;

#[test]
fn source_destructors_dispose_only_the_active_allocation_and_its_payload() {
    let source = include_str!("../../../../examples/raw_union_owner_drop.evg");
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(
        events,
        ["drop MaybeOwner", "drop MaybeOwner", "drop Resource"]
    );
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let incomplete = source.replace(
        "if present {discard_owner(data)} else {discard_empty(data)}",
        "()",
    );
    assert!(verify(&incomplete)
        .unwrap_err()
        .contains("cannot be dropped implicitly"));
    let allocating = source.replace(
        "fn discard_owner(value: unique(Resource)) {}",
        "fn discard_owner(value: unique(Resource)) {let extra: unique(usize) = alloc(0);}",
    );
    assert!(verify(&allocating)
        .unwrap_err()
        .contains("destructor calls require"));
    let false_flag = source.replace("present: true", "present: false");
    assert!(verify(&false_flag)
        .unwrap_err()
        .contains("invariant of MaybeOwner"));
    let suspended = "type Pair struct {a: usize, b: usize} where (fact balanced = a == b; balanced); fn dispose(value: unique(usize)) {} fn main() {let pair = Pair {a: 0, b: 0}; let owner: unique(usize) = alloc(42); update(pair) lifts balanced {dispose(owner);}}";
    assert!(verify(suspended)
        .unwrap_err()
        .contains("invariants are open"));
}

#[test]
fn conditional_owners_survive_calls_and_only_the_active_owner_is_released() {
    let source = include_str!("../../../../examples/raw_union_owner.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(
        verify(&source.replace("if full {consume(value)}", "if !full {consume(value)}")).is_err()
    );
}

#[test]
fn union_members_cannot_duplicate_owners_or_revive_freed_planes() {
    for source in [
        "fn bad(v: unique(usize) | shape(unique(usize))) -> usize {let p: unique(usize) = v; *p}",
        "fn main() {let p: unique(usize) = alloc(42); let v: unique(usize) | bool = p; let a: unique(usize) = v; let b: unique(usize) = v;}",
        "fn main() -> usize {let p: unique(usize) = alloc(42); let r = &*p; let v: unique(usize) | bool = p; let a: unique(usize) = v; drop(a); *r}",
        "fn bad(v: &(unique(usize) | bool)) -> usize where typeof(*v) == unique(usize) {let stolen: unique(usize) = *v; *stolen}",
        "fn drop_owner(v: unique(usize)) {drop(v);} fn keep(v: unique(usize)) {} fn bad(flag: bool, p: unique(usize)) {if flag {drop_owner(p)} else {()}; keep(p);}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn borrowed_union_dereferences_observe_the_existing_allocation_without_moving_it() {
    let source = "fn read(value: &(unique(usize) | shape(unique(usize)))) -> usize where typeof(*value) == unique(usize) {**value} fn consume(value: unique(usize)) {drop(value);} fn main() -> usize {let owner: unique(usize) = alloc(42); let data: unique(usize) | shape(unique(usize)) = owner; let n = read(&data); consume(data); n}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(
        verify(&source.replace("where typeof(*value) == unique(usize)", ""))
            .unwrap_err()
            .contains("active raw union member")
    );
    let bad_write = "fn bad(value: &(unique(usize) | bool)) where typeof(*value) == unique(usize) {**value = 42;}";
    assert!(verify(bad_write).unwrap_err().contains("effect contract"));
    let stale = source
        .replace("let n = read(&data);", "let view = &**(&data);")
        .replace("consume(data); n", "consume(data); *view");
    assert!(verify(&stale).unwrap_err().contains("never"));
}

#[test]
fn union_pointer_reads_track_the_pointee_revision_for_admitted_proofs() {
    let prefix = "fn require42(n: usize) where n == 42 {} fn dispose(value: unique(usize)) {drop(value);} fn main() -> usize {let owner: unique(usize) = alloc(43); let data: unique(usize) | shape(unique(usize)) = owner; let view = &data; proof assumed: **view == 42 by {trustme}; require42(**view);";
    let good = format!("{prefix} dispose(data); 42}}");
    let (program, bundle) = prove(&good).unwrap();
    assert_eq!(
        program.function_safety_assumptions("main").unwrap().count(),
        1
    );
    assert_eq!(
        verify_with_certificate(&good, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let bad = format!("{prefix} **view = 44; require42(**view); dispose(data); 42}}");
    assert!(verify(&bad)
        .unwrap_err()
        .contains("precondition of require42"));
}

#[test]
fn active_union_borrow_ports_check_reference_results_and_write_permissions() {
    let source = include_str!("../../../../examples/raw_union_borrow.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for invalid in [
        source.replace("modifies(&**value)", ""),
        source.replace("borrows(&**value)", "borrows(value)"),
        source.replace("let n = *before;", "dispose(data); let n = *before;"),
        "fn escaping(value: unique(usize) | bool) -> &usize where typeof(value) == unique(usize) borrows(&*value) {&*value}".into(),
    ] {
        assert!(verify(&invalid).is_err(), "accepted {invalid}");
    }
}

#[test]
fn checked_union_injection_and_extraction_use_active_member_evidence() {
    let source = "fn extract(value: usize | bool) -> usize where typeof(value) == usize {let number: usize = value; number} fn main() -> usize {extract(42)}";
    let (program, bundle) = prove(source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let bad = source.replace("extract(42)", "extract(true)");
    assert!(verify(&bad)
        .unwrap_err()
        .contains("precondition of extract"));
    let bad = "fn bad(value: usize | bool) -> usize {let number: usize = value; number}";
    assert!(verify(bad).unwrap_err().contains("active raw union member"));
    assert!(verify("fn bad() {let value: usize | bool = 42;}")
        .unwrap_err()
        .contains("cannot be dropped implicitly"));
}

#[test]
fn shapes_reserve_storage_without_a_live_value() {
    let source = "fn empty(value: shape(usize)) {} fn main() {let storage = shape(usize); proof uninitialized: typeof(storage) == shape(usize); empty(storage); proof consumed: typeof(storage) == shape(usize);}";
    assert!(verify(source).is_ok());
    assert!(verify(source).unwrap().run().is_ok());
    assert!(verify("fn main() {let storage = shape(usize); let wrong: usize = storage;}").is_err());
}

#[test]
fn a_source_flag_proves_an_optional_payloads_active_type() {
    let source = include_str!("../../../../examples/raw_union.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let bad = source.replace("present: true", "present: false");
    assert!(verify(&bad).unwrap_err().contains("invariant of MaybeWord"));
}

#[test]
fn inactive_member_refinements_cannot_erase_live_overflow_obligations() {
    for source in [
        "type Empty struct {} where false; fn bad(value: Empty | usize) -> usize where typeof(value) == usize {let n: usize = value; n + 1}",
        "type Empty struct {} where false; fn bad(flag: bool, n: usize) -> usize {let value: Empty | usize = if flag {n} else {n}; let live: usize = value; live + 1}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("no overflow"), "{error}");
    }
}

#[test]
fn an_explicit_source_flag_selects_members_across_a_conditional_join() {
    let source = "fn word(n: usize) -> usize {n} fn flag(b: bool) -> usize {if b {42} else {1}} fn choose(small: bool) -> usize {let value: usize | bool = if small {true} else {42}; if small {flag(value)} else {word(value)}} fn main() -> usize {choose(false)}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("if small {flag(value)}", "if !small {flag(value)}")).is_err());
}

#[test]
fn nominal_member_refinements_and_drop_follow_only_the_active_payload() {
    let refined = "type NonZero struct {data: usize} where data != 0; fn read(value: NonZero | usize) -> usize where (typeof(value) == NonZero) {let n: NonZero = value; n.data - 1} fn main() -> usize {read(NonZero {data: 43})}";
    assert_eq!(verify(refined).unwrap().run().unwrap().to_string(), "42");
    let resource = "type Resource struct {tag: usize} where tag == 7; impl Drop for Resource {fn drop(self) {proof valid: self.tag == 7;}} fn consume(r: Resource) -> usize {r.tag} fn word(n: usize) -> usize {n} fn choose(flag: bool) -> usize {let value: Resource | usize = if flag {Resource {tag: 7}} else {42}; if flag {consume(value)} else {word(value)}} fn main() -> usize {if choose(true) == 7 {42} else {1}}";
    let (program, bundle) = prove(resource).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
    assert_eq!(
        verify_with_certificate(resource, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let inactive = resource.replace("choose(true) == 7", "choose(false) == 42");
    assert!(verify(&inactive)
        .unwrap()
        .run_with_events()
        .unwrap()
        .1
        .is_empty());
    let reinterpret = "fn bad(value: usize | isize) -> isize where typeof(value) == usize {let n: isize = value; n}";
    assert!(verify(reinterpret)
        .unwrap_err()
        .contains("active raw union member"));
}

#[test]
fn type_observations_are_ideal_and_follow_consumption() {
    let source = "fn main() -> usize {let owner = alloc(42); drop(owner); proof gone: typeof(owner) == shape(unique(isize)); let storage = shape(&usize); proof shape_type: shape(&usize) == typeof(storage); let empty = shape(usize); proof no_value: typeof(empty) != usize; 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for bad in [
        "fn main() {let value = typeof(42);}",
        "fn main() {let storage = shape(nat);}",
        "fn main() {let storage = shape(shape(usize));}",
        "fn main() {let storage = shape(usize); let read: usize = storage;}",
    ] {
        assert!(verify(bad).is_err(), "{bad}");
    }
}

#[test]
fn borrowed_union_storage_and_array_members_preserve_their_types() {
    let borrowed = "fn view(value: &(usize | bool)) -> usize where typeof(*value) == usize {*value} fn main() -> usize {let value: usize | bool = 42; let n = view(&value); let consumed: usize = value; n}";
    assert_eq!(verify(borrowed).unwrap().run().unwrap().to_string(), "42");
    let array = "fn first(value: [u8; 2]) -> u8 {value[0]} fn main() -> u8 {let payload: [u8; 2] | bool = [42, 7]; first(payload)}";
    assert_eq!(verify(array).unwrap().run().unwrap().to_string(), "42");
    let shape = "module data {type Payload struct {value: usize} fn none() -> shape(Payload) {shape(Payload)}} fn main() -> usize {let reserved = data::none(); 42}";
    assert_eq!(verify(shape).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn admitted_member_evidence_expires_on_storage_replacement() {
    let good = "fn main() -> usize {let payload: usize | bool = true; proof assumed: typeof(payload) == usize by {trustme}; let n: usize = payload; 42}";
    let (program, bundle) = prove(good).unwrap();
    assert_eq!(
        program
            .function_safety_assumptions("main")
            .unwrap()
            .map(|a| a.goal.as_str())
            .collect::<Vec<_>>(),
        ["proof assumed"]
    );
    assert_eq!(
        verify_with_certificate(good, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    // The explicit assumption permits this interpretation in the compiler,
    // while the reference evaluator detects the admitted type mismatch.
    assert!(program
        .run()
        .unwrap_err()
        .contains("inactive raw union member"));
    let stale = "fn main() -> usize {let payload: usize | bool = true; proof assumed: typeof(payload) == usize by {trustme}; let old: bool = payload; payload = true; let n: usize = payload; 42}";
    assert!(verify(stale)
        .unwrap_err()
        .contains("active raw union member"));
}

#[test]
fn ideal_execution_cannot_erase_a_runtime_unions_consumption() {
    for source in [
        "fn main() {let value: usize | bool = 42; ideal let hidden = value; ideal let n: usize = hidden;}",
        "fn main() {let value: usize | bool = 42; let values: [usize | bool; 1] = [value]; ideal let hidden = values;}",
        "type Resource struct {} impl Drop for Resource {fn drop(self) {}} fn main() {let value: Resource | usize = Resource {}; ideal let hidden = value; ideal let r: Resource = hidden;}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("cannot consume runtime ownership"), "{error}");
    }
    let proof_data = "ideal fn word(n: usize) -> usize ensures result == n {let payload: usize | bool = n; let value: usize = payload; value} fn main() -> usize {ideal let n = word(42); proof checked: n == 42; 42}";
    // Pure ideal computation may own and eliminate its own union values.
    assert!(verify(proof_data).is_ok());
}

#[test]
fn enclosing_drop_eliminates_its_raw_union_with_source_code() {
    let source = include_str!("../../../../examples/raw_union_drop.evg");
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource", "drop Holder", "drop Holder"]);
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let incomplete = source.replace(
        "if present {discard_word(data)} else {discard_storage(data)}",
        "()",
    );
    assert!(verify(&incomplete)
        .unwrap_err()
        .contains("cannot be dropped implicitly"));
}

#[test]
fn exclusive_members_can_carry_the_same_owner_without_duplicating_it() {
    let source = include_str!("../../../../examples/raw_union_owner_paths.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let stale = source.replace(
        "*view = 42;",
        "let n = if flag {consume_left(data)} else {consume_right(data)}; *view = 42;",
    );
    assert!(verify(&stale).unwrap_err().contains("never"));
}
