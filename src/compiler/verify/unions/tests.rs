use super::*;

#[test]
fn raw_union_member_moves_leave_a_shape_in_existing_storage() {
    for source in [
        include_str!("../../../../examples/slot_extraction.evg"),
        "fn main() -> usize {let slot: unique(usize) | shape(unique(usize)) = alloc(42); let view = &slot; let value: unique(usize) = move(*view); proof empty: typeof(*view) == shape(unique(usize)); let retired: shape(unique(usize)) = slot; *value}",
        "type Slot struct {data: unique(usize) | shape(unique(usize)), tag: usize} fn main() -> usize {let slot = Slot {data: alloc(42), tag: 7}; let value: unique(usize) = slot.data; proof still_here: slot.tag == 7 && typeof(slot.data) == shape(unique(usize)); let Slot {data, tag} = slot; let retired: shape(unique(usize)) = data; *value}",
        "fn take<T>(slot: &(T | shape(T))) -> T where typeof(*slot) == T modifies(slot) ensures typeof(*slot) == shape(T) {move(*slot)} fn main() -> usize {let slot: usize | shape(usize) = 42; let view = &slot; let value = take::<usize>(view); proof empty: typeof(*view) == shape(usize); let retired: shape(usize) = slot; value}",
        "fn main() -> usize {let slot: usize | shape(usize) = 42; let view = &slot; let copied: usize = *view; proof still_initialized: typeof(*view) == usize; let value: usize = slot; copied + value - 42}",
        "fn main() -> usize {let owner: shared(usize) = alloc(42); let slot: shared(usize) | shape(shared(usize)) = owner; proof copied: owner_count(owner) == 2; let view = &slot; let value: shared(usize) = move(*view); let retired: shape(shared(usize)) = slot; leak(value); let final: unique(usize) = move(owner); *final}",
        "fn main() -> usize {let values = vec::Vec::<u8>::new(1); let header = &values; values = values.reallocate(2); if header.capacity() == 2 {42} else {1}}",
        "fn main() -> usize {let slot: unique(usize) | shape(unique(usize)) = alloc(42); let view = &slot; let payload = &**view; proof before: *payload == 42; let value: unique(usize) = *view; proof retained: *payload == 42 by {exact before}; let retired: shape(unique(usize)) = slot; *payload}",
        "type Slot struct {data: unique(usize) | shape(unique(usize)), tag: usize} fn main() -> usize {let slot = Slot {data: alloc(42), tag: 7}; proof before: slot.tag == 7; let value: unique(usize) = slot.data; proof retained: slot.tag == 7 by {exact before}; let Slot {data, tag} = slot; let retired: shape(unique(usize)) = data; *value}",
        "type Item struct {data: unique(usize)} impl Drop for Item {fn drop(self) {}} fn main() -> usize {let slot: Item | shape(Item) = Item {data: alloc(42)}; let view = &slot; let value: Item = *view; let retired: shape(Item) = slot; *value.data}",
        "fn select(slot: &(unique(usize) | shape(unique(usize))), count: &usize) -> &(unique(usize) | shape(unique(usize))) where *count == 0 modifies(count) borrows(slot) ensures *count == 1 {*count = 1; slot} fn main() -> usize {let slot: unique(usize) | shape(unique(usize)) = alloc(42); let count: usize = 0; let value: unique(usize) = *select(&slot, &count); let retired: shape(unique(usize)) = slot; if count == 1 {*value} else {1}}",
        "fn main() -> usize {let owner: shared(usize) = alloc(42); let slot: shared(usize) | shape(shared(usize)) = owner; let view = &slot; let copied: shared(usize) = *view; proof copies: owner_count(owner) == 3; leak(copied); let final_member: shared(usize) = slot; leak(final_member); let final: unique(usize) = move(owner); *final}",
        "type Handle struct {data: shared(usize)} impl Copy for Handle {} fn main() -> usize {let owner: shared(usize) = alloc(42); let handle = Handle {data: owner}; let slot: Handle | shape(Handle) = handle; let view = &slot; let copied: Handle = *view; proof copies: owner_count(owner) == 4; leak(copied); let taken: Handle = move(*view); let retired: shape(Handle) = slot; leak(taken); leak(handle); let final: unique(usize) = move(owner); *final}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn raw_union_extraction_requires_live_member_and_write_authority() {
    for (source, diagnostic) in [
        ("fn take(slot: &(unique(usize) | shape(unique(usize)))) -> unique(usize) where typeof(*slot) == unique(usize) {*slot} fn main() {}", "effect contract"),
        ("fn main() {let slot: unique(usize) | shape(unique(usize)) = alloc(42); let view = &slot; let first: unique(usize) = *view; let second: unique(usize) = *view; let retired: shape(unique(usize)) = slot;}", "active raw union member"),
        ("fn main() {let slot: unique(usize) | shape(unique(usize)) = alloc(42); let view = &slot; proof assumed: typeof(*view) == unique(usize) by {trustme}; let first: unique(usize) = *view; let second: unique(usize) = *view; let retired: shape(unique(usize)) = slot;}", "active raw union member"),
        ("fn main() -> usize {let slot: unique(usize) | shape(unique(usize)) = alloc(42); let view = &slot; let payload = &**view; let value: unique(usize) = *view; let retired: shape(unique(usize)) = slot; drop(value); *payload}", "type never"),
        ("type Holder struct {data: unique(usize)} fn main() {let holder = Holder {data: alloc(42)}; let alias: shared(usize) = holder.data;}", "partial-initialization tracking"),
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains(diagnostic), "{error}\n{source}");
    }
    let dependent = "type Slot struct {present: bool, data: unique(usize) | shape(unique(usize))} where present == (typeof(data) == unique(usize)); fn main() {let slot = Slot {present: true, data: alloc(42)}; let value: unique(usize) = slot.data; let Slot {present, data} = slot; let retired: shape(unique(usize)) = data;}";
    assert!(
        verify(dependent).is_err(),
        "extraction forgot its enclosing invariant"
    );
}

#[test]
fn moving_a_union_resource_runs_its_destructor_once() {
    let source = "type Item struct {data: unique(usize)} impl Drop for Item {fn drop(self) {}} fn main() -> usize {let slot: Item | shape(Item) = Item {data: alloc(42)}; let view = &slot; let value: Item = *view; let retired: shape(Item) = slot; *value.data}";
    let program = verify(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Item"]);
}

#[test]
fn conditional_union_extraction_consumes_only_the_selected_member() {
    let source = "fn choose(flag: bool) -> usize {let left: unique(usize) | shape(unique(usize)) = alloc(42); let right: unique(usize) | shape(unique(usize)) = alloc(7); let selected = if flag {&left} else {&right}; let value: unique(usize) = *selected; if flag {let empty: shape(unique(usize)) = left; let remaining: unique(usize) = right;} else {let remaining: unique(usize) = left; let empty: shape(unique(usize)) = right;}; *value} fn main() -> usize {choose(true) + choose(false) - 7}";
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn raw_union_shape_storage_can_be_initialized_without_cleanup() {
    for source in [
        include_str!("../../../../examples/slot_initialization.evg"),
        "fn main() -> usize {let slot: unique(usize) | shape(unique(usize)) = shape(unique(usize)); slot = alloc(42); let value: unique(usize) = slot; *value}",
        "type Slot struct {data: unique(usize) | shape(unique(usize))} fn main() -> usize {let slot = Slot {data: shape(unique(usize))}; slot.data = alloc(42); let Slot {data} = slot; let value: unique(usize) = data; *value}",
        "type Resource struct {tag: usize} impl Drop for Resource {fn drop(self) {}} fn main() -> usize {let slot: Resource | shape(Resource) = shape(Resource); slot = Resource {tag: 42}; let value: Resource = slot; value.tag}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn raw_union_initialization_requires_current_empty_storage() {
    for source in [
        "fn main() {let slot: unique(usize) | shape(unique(usize)) = alloc(7); slot = alloc(42);}",
        "fn init(slot: &(unique(usize) | shape(unique(usize))), value: unique(usize)) modifies(slot) {*slot = value;} fn main() {}",
        "fn main() {let slot: unique(usize) | shape(unique(usize)) = shape(unique(usize)); let view = &slot; proof was_empty: typeof(*view) == shape(unique(usize)); *view = alloc(7); *view = alloc(42);}",
        "fn fill(slot: &(unique(usize) | shape(unique(usize)))) -> unique(usize) where typeof(*slot) == shape(unique(usize)) modifies(slot) ensures typeof(*slot) == unique(usize) {*slot = alloc(7); alloc(42)} fn main() {let slot: unique(usize) | shape(unique(usize)) = shape(unique(usize)); let view = &slot; *view = fill(view);}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("raw union replacement requires a current uninitialized shape member"), "{error}");
    }
    let dependent = "type Slot struct {empty: bool, data: unique(usize) | shape(unique(usize))} where empty == (typeof(data) == shape(unique(usize))); fn main() {let slot = Slot {empty: true, data: shape(unique(usize))}; slot.data = alloc(42);}";
    assert!(
        verify(dependent).is_err(),
        "initialization forgot its enclosing invariant"
    );
    let missing_effect = "fn init(slot: &(unique(usize) | shape(unique(usize))), value: unique(usize)) where typeof(*slot) == shape(unique(usize)) {*slot = value;} fn main() {}";
    assert!(verify(missing_effect)
        .unwrap_err()
        .contains("effect contract"));
}

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
