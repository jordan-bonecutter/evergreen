//! Verifier acceptance, rejection, execution, and certificate regressions.

use super::*;

#[test]
fn result_borrows_are_anchored_in_surviving_returned_owners() {
    let source = include_str!("../../../examples/owned_result_views.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for source in [
        "type Out struct {owner: plane(usize), view: &usize} fn bad(r: &usize) -> Out borrows(view: &*result.owner) {Out {owner: alloc(42), view: r}}",
        "type Out struct {owner: plane(usize), view: &usize} fn bad() -> Out borrows(view: &*result.owner) {let other: plane(usize) = alloc(42); let view = &*other; Out {owner: alloc(42), view: view}}",
    ] {let error = verify(source).unwrap_err(); assert!(error.contains("returned reference field does not match"), "{error}");}
    for source in [
        "type Out struct {value: usize, view: &usize} fn bad(r: &usize) -> Out borrows(view: &result.value) {Out {value: 42, view: r}}",
        "type Out struct {owner: &plane(usize), view: &usize} fn bad(r: &plane(usize)) -> Out borrows(owner: r, view: &**result.owner) {Out {owner: r, view: &**r}}",
        "type Out struct {owner: plane(usize), view: &usize} fn bad(r: &usize) -> Out borrows(view: result.view) {Out {owner: alloc(42), view: r}}",
    ] {let error = verify(source).unwrap_err(); assert!(error.contains("result borrows") || error.contains("result anchors"), "{error}");}
    let library = "type Packet struct {owner: plane(usize), other: plane(usize), view: &usize} where(view == &*owner); fn wrong(p: Packet) -> Packet borrows(view: &*result.other) {p}";
    assert!(verify(library).is_ok()); // The independent-port configuration is impossible.
    let call = format!("{library} fn main() -> usize {{let owner: plane(usize) = alloc(42); let view = &*owner; let packet = Packet {{owner: owner, other: alloc(7), view: view}}; let returned = wrong(packet); *returned.view}}");
    let error = verify(&call).unwrap_err();
    assert!(
        error.contains("body recheck failed")
            && error.contains("returned reference field does not match"),
        "{error}"
    );
    let trusted_call = call.replace(
        "let returned = wrong(packet);",
        "proof cheat: false by {trustme}; let returned = wrong(packet);",
    );
    assert!(verify(&trusted_call)
        .unwrap_err()
        .contains("returned reference field does not match"));
    let trusted_body = "type Out struct {owner: plane(usize), view: &usize} fn bad(r: &usize) -> Out borrows(view: &*result.owner) {proof cheat: false by {trustme}; Out {owner: alloc(42), view: r}}";
    assert!(verify(trusted_body)
        .unwrap_err()
        .contains("returned reference field does not match"));
    let correct = call.replace(
        "borrows(view: &*result.other)",
        "borrows(view: &*result.owner)",
    );
    assert_eq!(verify(&correct).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn result_owned_alias_selection_is_checked_after_destructor_effects() {
    let source = "type Guard struct {target: &usize} impl Drop for Guard {fn drop(self) modifies(self.target) ensures(*self.target == 1) {*self.target = 1;}} type Indexed struct {owner: plane([usize; 2]), index: &usize, view: &usize} fn make(index: &usize) -> Indexed where(*index == 0) modifies(index) borrows(index: index, view: &(*result.owner)[*result.index]) {let owner: plane([usize; 2]) = alloc([7, 42]); let guard = Guard {target: index}; let view = &(*owner)[*index]; Indexed {owner: owner, index: index, view: view}} fn main() -> usize {let index: usize = 0; let packet = make(&index); *packet.view}";
    assert!(verify(source)
        .unwrap_err()
        .contains("returned reference field does not match"));
    let settled = source.replace(
        "let view = &(*owner)[*index];",
        "drop(guard); let view = &(*owner)[*index];",
    );
    let (program, bundle) = prove(&settled).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Guard"]);
    assert_eq!(
        verify_with_certificate(&settled, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn heap_record_updates_track_physical_planes_and_retained_requirements() {
    let source = include_str!("../../../examples/heap_updates.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let unclosed = source.replace(
        "ideal (*holder.allocation).owners = nat(*changed);",
        "proof only_count: *changed == 43;",
    );
    assert!(verify(&unclosed)
        .unwrap_err()
        .contains("invariant of ledgers::Ledger"));
    for argument in ["&*holder.allocation", "dormant"] {
        let observes = source.replace("ideal (*holder.allocation).owners = nat(*changed);", &format!("ideal let observed = ledgers::inspect({argument}); ideal (*holder.allocation).owners = nat(*changed);"));
        assert!(verify(&observes)
            .unwrap_err()
            .contains("invariant of ledgers::Ledger"));
    }
    let duplicate = source.replace(
        "update(*holder.allocation)",
        "update(*holder.allocation, *dormant)",
    );
    assert!(verify(&duplicate)
        .unwrap_err()
        .contains("duplicate update place"));
    let no_permission = source.replace("modifies(&(*ledger).count, &(*ledger).owners)", "");
    assert!(verify(&no_permission)
        .unwrap_err()
        .contains("matching modifies contract"));
    let pulse = include_str!("../../../examples/reject_heap_update_intermediate.evg");
    assert!(verify(pulse).unwrap_err().contains("invariant of Ledger"));
    let reverse_release = source.replace("ideal (*ledger).owners = (*ledger).owners - 1;\n            (*ledger).count = (*ledger).count - 1;", "(*ledger).count = (*ledger).count - 1; ideal (*ledger).owners = (*ledger).owners - 1;");
    assert!(verify(&reverse_release)
        .unwrap_err()
        .contains("invariant of ledgers::Ledger"));
    let pulse_bounds = source.replace(
        "{*slot = value; slot}",
        "{*slot = 101; *slot = value; slot}",
    );
    assert!(verify(&pulse_bounds)
        .unwrap_err()
        .contains("invariant of ledgers::Ledger"));
}

#[test]
fn dormant_heap_views_preserve_other_container_requirements() {
    let source = include_str!("../../../examples/heap_updates.evg");
    let views = source
        .replace(
            "type Holder",
            "type View struct {record: &ledgers::Ledger}\ntype Holder",
        )
        .replace(
            "let holder = Holder {allocation: owner};",
            "let holder = Holder {allocation: owner}; let tracked = View {record: dormant};",
        );
    assert_eq!(verify(&views).unwrap().run().unwrap().to_string(), "42");
    let guarded = views.replace(
        "type View struct {record: &ledgers::Ledger}",
        "type View struct {record: &ledgers::Ledger} where((*record).count <= 42);",
    );
    assert!(verify(&guarded).unwrap_err().contains("invariant of View"));
    let observer = views.replace("fn main()", "ideal fn inspect_view(v: &View) -> nat {ledgers::inspect((*v).record)} fn main()")
        .replace("ideal (*holder.allocation).owners = nat(*changed);", "ideal let invalid = inspect_view(&tracked); ideal (*holder.allocation).owners = nat(*changed);");
    assert!(verify(&observer)
        .unwrap_err()
        .contains("invariant of ledgers::Ledger"));
    let owner_view = source.replace("ideal fn inspect(ledger:", "ideal fn inspect_owner(owner: &plane(Ledger)) -> nat {(**owner).owners} ideal fn inspect(ledger:")
        .replace("let holder = Holder {allocation: owner};", "let holder = Holder {allocation: owner}; let owner_view = &holder.allocation;")
        .replace("ideal (*holder.allocation).owners = nat(*changed);", "ideal let invalid = ledgers::inspect_owner(owner_view); ideal (*holder.allocation).owners = nat(*changed);");
    assert!(verify(&owner_view)
        .unwrap_err()
        .contains("invariant of ledgers::Ledger"));
}

#[test]
fn explicit_ideal_borrowed_writes_reset_erasure_at_pointer_edges() {
    let source = "ideal fn set(r: &nat, n: nat) modifies(r) ensures(*r == n) {ideal *r = n;} fn main() -> usize {ideal let n: nat = 0; ideal let done = set(&n, 42); proof updated: n == 42; 42}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    for source in [
        "fn main() {let n: usize = 0; ideal let r = &n; ideal *r = 42;}",
        "ideal type State struct {count: &usize} fn main() {let n: usize = 0; ideal let state = State {count: &n}; ideal *state.count = 42;}",
        "type Item struct {n: usize} fn main() {let owner = alloc(Item {n: 0}); ideal (*owner).n = 42;}",
    ] {assert!(verify(source).unwrap_err().contains("ideal assignments cannot modify runtime storage"));}
}

#[test]
fn owned_planes_keep_identity_across_moves_and_cleanup_nested_payloads() {
    let source = include_str!("../../../examples/owned_planes.evg");
    let (program, bundle) = prove(source).unwrap();
    let (result, events) = program.run_with_events().unwrap();
    assert_eq!(result.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
    let overflow = source.replace("make(41)", "make(usize::MAX)");
    assert!(verify(&overflow)
        .unwrap_err()
        .contains("precondition of advance"));
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(program.trusted_assumptions().is_empty());
    let through_call = "fn write(owner: plane(usize), view: &usize) -> usize modifies(view) ensures(result == 42) {*view = 42; *view} fn main() -> usize {let owner: plane(usize) = alloc(41); let view = &*owner; write(owner, view); 42}";
    assert_eq!(
        verify(through_call).unwrap().run().unwrap().to_string(),
        "42"
    );
    let observed_after =
        through_call.replace("write(owner, view); 42", "write(owner, view); *view");
    assert!(verify(&observed_after).unwrap_err().contains("never"));
    let branches = "fn choose(owner: &plane(usize), flag: bool) -> usize modifies(&**owner) ensures(result == **owner && result >= 41 && result <= 42) {let done = if flag {set(owner, 42)} else {set(owner, 41)}; **owner}";
    let source = format!("fn set(owner: &plane(usize), n: usize) -> usize modifies(&**owner) ensures(**owner == n && result == n) {{**owner = n; n}} {branches} fn main() -> usize {{let p: plane(usize) = alloc(0); choose(&p, true)}}");
    assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn heap_ownership_rejects_dangling_duplicates_and_erased_effects() {
    for (source, diagnostic) in [
        (include_str!("../../../examples/reject_heap_use_after_free.evg"), "never"),
        (include_str!("../../../examples/reject_heap_duplicate_owner.evg"), "shape(T)"),
        (include_str!("../../../examples/reject_heap_borrow_write.evg"), "effect contract"),
        ("fn main() -> usize {let owner: plane(usize) = alloc(7); let view = &*owner; drop(owner); owner = alloc(42); *view}", "never"),
        ("fn bad(owner: plane(usize), view: &usize) -> &usize borrows(view) {view} fn main() -> usize {let owner: plane(usize) = alloc(42); let view = &*owner; *bad(owner, view)}", "never"),
        ("fn change(owner: plane(usize)) -> usize {*owner = 42; 42} fn main() -> usize ensures(result == 42) {let owner: plane(usize) = alloc(7); proof wrong: change(owner) == 42; *owner}", "proof calls must borrow heap owners"),
        ("fn make() -> plane(usize) {alloc(42)} fn main() {proof wrong: *make() == 42;}", "proof calls must borrow heap owners"),
        ("fn main() {ideal let owner = alloc(42);}", "allocation requires runtime"),
        ("fn bad(owner: plane(usize)) {ideal let stolen = owner;}", "cannot consume runtime ownership"),
        ("fn main() {let n: usize = 42; let owner = alloc(&n);}", "without borrowed references"),
        ("ideal fn bad(owner: &plane(usize)) modifies(&**owner) {**owner = 42;}", "ideal modifies must target proof storage"),
        ("fn main() {ideal let n: nat = 42; let owner = alloc(n);}", "ideal parameter"),
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
    }
}

#[test]
fn opaque_ideal_effect_regions_forward_and_recheck_aliases() {
    let credits = concat!(include_str!("../../../stdlib/credits/credits.evg"), "\u{1e}").replace("module credits;", "module credits;ideal fn issue(n: nat) -> Credit ensures(result.units == n) {Credit {units: n}}");
    let transfer = include_str!("../../../proofs/borrowed_credit_transfer.evg");
    let library = format!(
        "{credits} {} {transfer} {}",
        concat!(
            include_str!("../../../stdlib/borrow_credits/borrow_credits.evg"),
            "\u{1e}"
        ),
        include_str!("../../../proofs/borrowed_token_transfer.evg")
    );
    let source = format!("{library} fn main() -> usize {{let data: usize = 42; use_borrow_transfer(credits::issue(42), &data)}}");
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let pair = "ideal fn take_pair(a: &credits::Credit, b: &credits::Credit) -> credits::Split where(credits::units(a) >= 1 && credits::units(b) >= 1) modifies(a, b) ensures(credits::units(a) + 1 == old(credits::units(a)) && credits::units(b) + 1 == old(credits::units(b))) {credits::Split {left: credits::take(a, 1), right: credits::take(b, 1)}}";
    let separate = format!("{credits} {pair} fn main() -> usize {{ideal let a = credits::issue(1); ideal let b = credits::issue(1); ideal let parts = take_pair(&a, &b); proof empty: credits::units(&a) == 0 && credits::units(&b) == 0; 42}}");
    assert_eq!(verify(&separate).unwrap().run().unwrap().to_string(), "42");
    let alias = separate.replace("take_pair(&a, &b)", "take_pair(&a, &a)");
    let error = verify(&alias).unwrap_err();
    assert!(
        error.contains("body recheck failed") && error.contains("precondition of credits::take"),
        "{error}"
    );
    let hidden_reference =
        format!("{library} ideal fn bad(t: &borrow_credits::Token) modifies(t) {{}}");
    assert!(verify(&hidden_reference)
        .unwrap_err()
        .contains("modifies targets require"));
    assert!(verify("type Value struct {n: usize} fn observe(r: &Value) modifies(r) {}").is_ok());
    let runtime_owner = "type Owner struct {n: plane(usize)} fn bad(r: &Owner) modifies(r) {}";
    assert!(verify(runtime_owner)
        .unwrap_err()
        .contains("modifies targets require"));
}

#[test]
fn old_scalar_accessors_use_entry_storage_and_require_pure_total_calls() {
    let source = include_str!("../../../examples/old_accessors.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let wrong = source.replace("old(read(value)) == 41", "old(read(value)) == 42");
    assert!(verify(&wrong).unwrap_err().contains("postcondition"));
    let strengthened = source.replace(
        "-> usize ensures(result == *value)",
        "-> usize where(*value == 42) ensures(result == *value)",
    );
    assert!(verify(&strengthened)
        .unwrap_err()
        .contains("precondition of read"));
    for source in [
        "fn write(r: &usize) -> usize modifies(r) {*r = 42; 42} fn bad(r: &usize) {proof wrong: old(write(r)) == 42;}",
        "fn endless() -> usize {endless()} fn bad() {proof wrong: old(endless()) == 42;}",
        "fn identity(r: &usize) -> &usize borrows(r) {r} fn bad(r: &usize) {proof wrong: old(identity(r)) == r;}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("old snapshots require"), "{error}");
    }
}

#[test]
fn borrowed_credit_transfer_conserves_quantity_and_rejects_overdrafts() {
    let credits = concat!(
        include_str!("../../../stdlib/credits/credits.evg"),
        "\u{1e}"
    );
    let source = format!(
        "{credits}\n{}",
        include_str!("../../../proofs/borrowed_credit_transfer.evg")
    );
    let (program, bundle) = prove(&source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let overdraw = format!("{credits} ideal fn bad(c: credits::Credit) where(credits::units(&c) == 1) {{let first = credits::take(&c, 1); let second = credits::take(&c, 1);}}");
    assert!(verify(&overdraw)
        .unwrap_err()
        .contains("precondition of credits::take"));
    let forged = source.replace(
        "(*credit).units = (*credit).units - amount;",
        "(*credit).units = (*credit).units;",
    );
    assert!(verify(&forged).unwrap_err().contains("postcondition"));
    let private = format!("{credits} ideal fn bad(c: credits::Credit) {{(*(&c)).units = 100;}}");
    assert!(verify(&private).unwrap_err().contains("opaque"));
}

#[test]
fn ideal_borrow_writes_have_checked_erased_footprints() {
    let source = include_str!("../../../examples/ideal_borrow_writes.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let missing = source.replacen(
        "ideal fn forward_budget(state: &Budget, remaining: nat)\nmodifies(&(*state).remaining)",
        "ideal fn forward_budget(state: &Budget, remaining: nat)",
        1,
    );
    assert!(verify(&missing).unwrap_err().contains("matching modifies"));
    let bad_post = source.replace(
        "ensures(*state == expected)",
        "ensures(*state == expected + 1)",
    );
    assert!(verify(&bad_post).is_err());
    let retained = source.replace("synced);", "synced && expected >= 40);");
    assert!(verify(&retained).is_ok());
    let pulse = retained.replace("{*state = expected;}", "{*state = 0; *state = expected;}");
    assert!(verify(&pulse).unwrap_err().contains("invariant"));
}

#[test]
fn erased_pointer_values_never_authorize_erased_runtime_writes() {
    for source in [
        "ideal fn bad(r: &usize) modifies(r) {*r = 0;}",
        "ideal fn bad(ideal r: &usize) modifies(r) {*r = 0;}",
        "ideal type State struct {target: &usize} ideal fn bad(s: &State) modifies((*s).target) {*(*s).target = 0;}",
        "type State struct {ideal target: &usize} ideal fn bad(s: &State) modifies((*s).target) {*(*s).target = 0;}",
        "ideal type State struct {target: &usize} ideal fn bad(s: State) modifies(s.target) {*s.target = 0;}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("ideal modifies must target proof storage"), "{error}");
    }
    let source = "ideal fn set(r: &nat) -> nat modifies(r) ensures(*r == 0) {*r = 0; 0} fn main() {ideal let n: nat = 1; proof wrong: set(&n) == 0;}";
    let error = verify(source).unwrap_err();
    assert!(error.contains("forbidden in proof expressions"), "{error}");
}

#[test]
fn ideal_record_fields_move_and_erase_with_runtime_values() {
    let source = include_str!("../../../examples/ideal_fields.evg");
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop packets::Tagged", "drop packets::Resource"]);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(program.trusted_assumptions().is_empty());
    let layout =
        crate::compiler::layout::of(&Type::Named("packets::Packet".into()), &program.structs)
            .unwrap();
    assert_eq!(layout.size, 8);
    assert!(!layout.fields.contains_key("witness"));
    let empty =
        crate::compiler::layout::of(&Type::Named("packets::Empty".into()), &program.structs)
            .unwrap();
    assert_eq!(empty.size, 1);
    assert!(empty.fields.is_empty());
    let duplicate = source.replace(
        "let forwarded = packets::forward(packet);",
        "let forwarded = packets::forward(packet); let duplicate = packets::forward(packet);",
    );
    assert!(verify(&duplicate).is_err());
    let bad_proof = source.replace(
        "witness.expected == nat(value)",
        "witness.expected == nat(value) + 1",
    );
    assert!(verify(&bad_proof).is_err());
    let output = verify("type View struct {value: usize, ideal secret: nat} fn main() -> View {View {value: 42, secret: 123}}").unwrap().run().unwrap();
    let crate::interpreter::Value::Record(_, fields) = output else {
        panic!("expected runtime record")
    };
    assert_eq!(fields.len(), 1);
    assert_eq!(fields["value"].to_string(), "42");
}

#[test]
fn ideal_record_fields_cannot_leak_or_erase_runtime_effects() {
    for bad in [
        "type Cell struct {value: usize, ideal secret: usize} fn main() -> usize {let cell = Cell {value: 7, secret: 42}; cell.secret}",
        "type Cell struct {ideal secret: usize} fn main() -> usize {let cell = Cell {secret: 42}; let Cell {secret} = cell; secret}",
        "type Cell struct {ideal secret: usize} fn main() -> &usize {let cell = Cell {secret: 42}; &cell.secret}",
        "type Resource struct {} impl Drop for Resource {fn drop(self){}} type Bad struct {ideal owner: Resource} fn main() {}",
        "type Cell struct {value: usize, ideal secret: usize} fn write(n: &usize) -> usize modifies(n) {*n = 42; 42} fn main() {let n: usize = 0; let cell = Cell {value: 7, secret: write(&n)};}",
        "type Cell struct {value: usize, ideal secret: usize} fn main() {let cell = Cell {value: 7, secret: 42}; ideal cell.value = 42;}",
    ] {assert!(verify(bad).is_err(), "accepted {bad}");}
    let invariant = "type Cell struct {value: usize, ideal expected: usize} where(value == expected); fn main() {let cell = Cell {value: 7, expected: 7}; ideal cell.expected = 42;}";
    assert!(verify(invariant).unwrap_err().contains("invariant of Cell"));
}

#[test]
fn carried_ideal_credit_references_remain_in_the_alias_model() {
    let credits = concat!(include_str!("../../../stdlib/credits/credits.evg"), "\u{1e}").replace("module credits;", "module credits;ideal fn issue() -> Credit ensures(result.units == 42) {Credit {units: 42}}");
    let library = format!(
        "{credits} {} {}",
        concat!(
            include_str!("../../../stdlib/borrow_credits/borrow_credits.evg"),
            "\u{1e}"
        ),
        include_str!("../../../proofs/carried_borrow_credits.evg")
    );
    let source = format!("{library} fn main() -> usize {{let data: usize = 42; let carrier = carry(credits::issue(), &data); consume_carrier(carrier)}}");
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let wrong = format!("{library} fn separate(carrier: &Carrier) -> bool ensures((*carrier).target != borrow_credits::target(&(*carrier).token)) {{false}} fn main() -> bool {{let data: usize = 42; let carrier = carry(credits::issue(), &data); separate(&carrier)}}");
    assert!(verify(&wrong).unwrap_err().contains("body recheck failed"));
}

#[test]
fn ideal_assignments_and_update_locals_preserve_erasure_and_scope() {
    let source = include_str!("../../../examples/ideal_update_state.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(program.trusted_assumptions().is_empty());
    let wrong_copy = source.replace(
        "proof original: data[0] == 7;",
        "proof original: data[0] == 42;",
    );
    assert!(verify(&wrong_copy).is_err());
    let runtime_leak = source.replace(
        "count + updated + copied - 42",
        "count + expected + copied - 42",
    );
    assert!(verify(&runtime_leak).is_err());
    let escaped = source.replace("let updated: usize = 0;", "");
    assert!(verify(&escaped).is_err());
}

#[test]
fn ideal_assignments_cannot_write_runtime_storage_or_revive_owners() {
    for bad in [
        "fn main() -> usize {let value: usize = 7; ideal value = 42; value}",
        "fn main() -> usize {let data: [usize; 1] = [7]; ideal data[0] = 42; data[0]}",
        "type Cell struct {value: usize} fn main() {let cell = Cell {value: 7}; ideal cell.value = 42;}",
        "fn main() {let value: usize = 7; ideal let view = &value; ideal *view = 42;}",
        "ideal type Ticket struct {units: nat} ideal fn consume(ticket: Ticket) {} fn main() {ideal let ticket = Ticket {units: 1}; ideal let gone = consume(ticket); ideal ticket = old(ticket);}",
        "fn main() {ideal let value: nat = 1; proof original: value == 1; ideal value = 2; proof wrong: value == 1 by {exact original};}",
        "type Owner struct {value: usize} type Pair struct {a: usize, b: usize} where(fact same = a == b; same); fn main() {let owner = Owner {value: 7}; let pair = Pair {a: 1, b: 1}; update(pair) lifts same {ideal let Owner {value} = owner;}}",
        "fn change(value: &usize) -> usize modifies(value) ensures(*value == 42) {*value = 42; 0} fn main() {let value: usize = 7; ideal let data: [usize; 1] = [0]; ideal data[change(&value)] = 42;}",
        "type Pair struct {a: usize, b: usize} where(fact same = a == b; same); fn main() {let pair = Pair {a: 1, b: 1}; ideal let original: nat = 0; ideal let view = &original; update(pair) lifts same {ideal let local: nat = 1; ideal view = &local;} proof stale: *view == 1;}",
    ] {assert!(verify(bad).is_err(), "accepted {bad}");}
}

#[test]
fn move_only_credit_bookkeeping_can_be_replaced_inside_updates() {
    let library = format!(
        "{} {}",
        concat!(
            include_str!("../../../stdlib/credits/credits.evg"),
            "\u{1e}"
        ),
        concat!(
            include_str!("../../../stdlib/borrow_credits/borrow_credits.evg"),
            "\u{1e}"
        )
    );
    let client = include_str!("../../../proofs/borrow_credit_updates.evg");
    let source = format!("{library} {client}");
    let (program, bundle) = prove(&source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let wrong_order = client.replace(
        "ledger.owners = ledger.owners - 1;\n        *count = *count - 1;",
        "*count = *count - 1;\n        ledger.owners = ledger.owners - 1;",
    );
    assert!(verify(&format!("{library} {wrong_order}"))
        .unwrap_err()
        .contains("invariant of CountLedger"));
    let duplicate = client.replace(
        "ideal token = remaining;",
        "ideal token = remaining; ideal let duplicate = remaining;",
    );
    assert!(verify(&format!("{library} {duplicate}")).is_err());
    let stale = client
        .replace("let ledger =", "ideal let old_view = &token; let ledger =")
        .replace(
            "proof matches_count:",
            "proof stale: borrow_credits::units(old_view) == original; proof matches_count:",
        );
    assert!(verify(&format!("{library} {stale}"))
        .unwrap_err()
        .contains("never"));
}

#[test]
fn erased_borrow_resources_keep_identity_generation_and_cleanup() {
    let source = include_str!("../../../examples/ideal_borrow_resources.evg");
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(program.trusted_assumptions().is_empty());
    let wrong_target = source
        .replace("read(view, &resource.value)", "read(view, &other.value)")
        .replace(
            "ideal let view =",
            "let other = Resource {value: 42}; ideal let view =",
        );
    assert!(verify(&wrong_target)
        .unwrap_err()
        .contains("precondition of read"));
    let stale = source.replace(
        "read(view, &resource.value)",
        "drop(resource); resource = Resource {value: 42}; read(view, &resource.value)",
    );
    assert!(verify(&stale).unwrap_err().contains("never"));
    let duplicate = source.replace(
        "read(view, &resource.value)",
        "let first = read(view, &resource.value); read(view, &resource.value)",
    );
    assert!(verify(&duplicate).is_err());
    let owner = "type Resource struct {value: usize} impl Drop for Resource {fn drop(self){}} ideal fn observe(r: &Resource) -> &Resource borrows(r) {r} fn read(ideal proof_view: &Resource, r: &Resource) -> usize where(proof_view == r) ensures(result == (*r).value) {(*r).value} fn main() -> usize {let resource = Resource {value: 42}; read(observe(&resource), &resource)}";
    let (value, events) = verify(owner).unwrap().run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
}

#[test]
fn erased_borrows_cannot_supply_runtime_values_or_mutations() {
    for bad in [
        "fn leak(ideal r: &usize) -> usize {*r}",
        "fn leak(ideal r: &usize) -> &usize borrows(r) {r}",
        "fn write(ideal r: &usize) modifies(r) {*r = 0;}",
        "fn branch(ideal r: &usize) -> usize {if *r == 42 {42} else {0}}",
        "ideal fn write(r: &usize) {*r = 0;}",
        "ideal fn local(r: &usize) -> &usize borrows(r) {let n: usize = 42; &n}",
        "ideal fn swap(r: &usize, other: &usize) -> &usize borrows(r) {other}",
        "ideal fn forward(r: &usize) -> &usize {r}",
        "type Resource struct {} impl Drop for Resource {fn drop(self){}} ideal type Bad struct {owned: Resource} fn take(ideal bad: Bad) {}",
        "type Resource struct {} impl Drop for Resource {fn drop(self){}} ideal fn steal(r: &Resource) {drop(*r);}",
        "fn separate(ideal view: &usize, r: &usize) -> usize ensures(view != r) {*r} fn main() -> usize {let data: usize = 42; separate(&data, &data)}",
        "type Positive struct {value: usize} where(value > 0); fn overwrite(ideal view: &Positive, value: &usize) modifies(value) ensures(*value == 0 && (*view).value > 0) {*value = 0;} fn main() {let positive = Positive {value: 1}; overwrite(&positive, &positive.value);}",
    ] {assert!(verify(bad).is_err(), "accepted {bad}");}
}

#[test]
fn borrowed_credit_library_conserves_units_and_reference_targets() {
    let library = format!(
        "{} {}",
        concat!(
            include_str!("../../../stdlib/credits/credits.evg"),
            "\u{1e}"
        ),
        concat!(
            include_str!("../../../stdlib/borrow_credits/borrow_credits.evg"),
            "\u{1e}"
        )
    );
    let client = include_str!("../../../proofs/borrow_credits.evg");
    let source = format!("{library} {client}");
    let (program, bundle) = prove(&source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let duplicate = client.replace(
        "borrow_credits::join(left, right)",
        "borrow_credits::join(left, left)",
    );
    assert!(verify(&format!("{library} {duplicate}")).is_err());
    let wrong_units = library.replace(
        "units(&result.left) == amount",
        "units(&result.left) == amount + 1",
    );
    assert!(verify(&format!("{wrong_units} {client}")).is_err());
    let wrong_targets = "ideal fn wrong(a: credits::Credit, b: credits::Credit, x: &usize, y: &usize) -> borrow_credits::Token where(x != y) borrows(target: x) {let left = borrow_credits::bind(a, x); let right = borrow_credits::bind(b, y); borrow_credits::join(left, right)}";
    assert!(verify(&format!("{library} {wrong_targets}"))
        .unwrap_err()
        .contains("precondition of borrow_credits::join"));
    let forged = "ideal fn forge(target: &usize) -> borrow_credits::Token borrows(target: target) {borrow_credits::Token {budget: 42, target: target}}";
    assert!(verify(&format!("{library} {forged}"))
        .unwrap_err()
        .contains("opaque representation"));
}

#[test]
fn updates_accept_scalar_borrow_and_index_writes_without_repeating_lvalues() {
    let source = include_str!("../../../examples/update_borrow_writes.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(program.trusted_assumptions().is_empty());
    let no_grant = source.replace("modifies(count)", "");
    assert!(verify(&no_grant).unwrap_err().contains("effect contract"));
    let wrong = source.replace(
        "proof selected_once: visits == 1;",
        "proof selected_once: visits == 2;",
    );
    assert!(verify(&wrong).is_err());
    let overflow = source.replace("let visits: usize = 0;", "let visits: usize = usize::MAX;");
    assert!(verify(&overflow)
        .unwrap_err()
        .contains("precondition of select"));
}

#[test]
fn update_borrow_writes_keep_retained_and_unopened_invariants() {
    let source = include_str!("../../../examples/reject_update_borrow_write.evg");
    let line = source
        .lines()
        .position(|line| line.trim() == "*ledger.count = 0;")
        .unwrap()
        + 1;
    let error = verify(source).unwrap_err();
    assert!(error.starts_with(&format!("line {line}:")), "{error}");
    assert!(error.contains("invariant of Ledger"), "{error}");
    let indexed = source
        .replace("let count: usize = 41;", "let data: [usize; 1] = [41];")
        .replace("count: &count", "count: &data[0]")
        .replace("*ledger.count = 0;", "data[0] = 0;");
    assert!(verify(&indexed)
        .unwrap_err()
        .contains("invariant of Ledger"));
    let unopened = "type Pair struct {left: usize, right: usize} where(fact balanced = left == right; balanced); type Positive struct {value: usize} where(value > 0); fn main() {let pair = Pair {left: 7, right: 7}; let positive = Positive {value: 1}; let view = &positive.value; update(pair) lifts balanced {*view = 0;}}";
    assert!(verify(unopened)
        .unwrap_err()
        .contains("invariant of Positive"));
    let owning = "type Owner struct {value: usize} impl Drop for Owner {fn drop(self){}} type Pair struct {left: usize, right: usize} where(fact balanced = left == right; balanced); fn main() {let pair = Pair {left: 7, right: 7}; let owner = Owner {value: 1}; update(pair) lifts balanced {owner = owner;}}";
    assert!(verify(owning).unwrap_err().contains("only scalar writes"));
}

#[test]
fn self_observing_invariants_use_the_resulting_store() {
    let source = include_str!("../../../examples/self_observing_fields.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(program.trusted_assumptions().is_empty());
    let wrong = source.replace("view.pointer = &view.value;", "");
    assert!(verify(&wrong).unwrap_err().contains("invariant of Mirror"));
    let nested = "type Mirror struct {value: usize, pointer: &usize} where(*pointer == value); type Holder struct {entry: Mirror} fn main() -> usize ensures(result == 42) {let initial: usize = 7; let holder = Holder {entry: Mirror {value: 7, pointer: &initial}}; holder.entry.pointer = &holder.entry.value; holder.entry.value = 42; *holder.entry.pointer}";
    assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn self_observing_invalid_stores_fail_before_a_later_restore() {
    let source = include_str!("../../../examples/reject_self_observing_write.evg");
    let line = source
        .lines()
        .position(|line| line.trim() == "view.value = 0;")
        .unwrap()
        + 1;
    for source in [
        source.to_owned(),
        source.replace("view.value = 0;", "*view.pointer = 0;"),
    ] {
        let error = verify(&source).unwrap_err();
        assert!(error.starts_with(&format!("line {line}:")), "{error}");
        assert!(error.contains("invariant of PositiveView"), "{error}");
    }
    // An external pointee remains positive when the unrelated field changes.
    let separate = source.replace("view.pointer = &view.value;", "");
    assert_eq!(verify(&separate).unwrap().run().unwrap().to_string(), "7");
}

#[test]
fn scalar_write_helpers_work_inside_selective_updates() {
    let source = include_str!("../../../examples/update_calls.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(program.trusted_assumptions().is_empty());
    let proof_too_early = source.replace(
        "proof weak: ledger::zero_is_safe;",
        "proof weak: ledger::accurate;",
    );
    assert!(verify(&proof_too_early).is_err());
    assert!(verify(&source.replace("forward(&ledger.owners, *changed);", "")).is_err());
    let alias = source.replace("fn local()", "fn both(a: &usize, b: &usize) modifies(a, b) ensures(*a == 42 && *b == 42) {*a = 42; *b = 42;} fn local()")
        .replace("let changed = set(&ledger.count, 42);", "both(&ledger.count, &ledger.count); let changed = &ledger.count;");
    assert_eq!(verify(&alias).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn update_helper_postconditions_cannot_hide_unsafe_intermediate_writes() {
    let helpers = "fn pulse(slot: &usize) modifies(slot) ensures(*slot == 42) {*slot = 0; *slot = 42;} fn forward(slot: &usize) modifies(slot) ensures(*slot == 42) {pulse(slot);}";
    for field in ["count: usize", "count: &usize"] {
        let indirect = field.contains('&');
        let count = if indirect { "*count" } else { "count" };
        let initial = if indirect { "&storage" } else { "42" };
        let argument = if indirect {
            "ledger.count"
        } else {
            "&ledger.count"
        };
        for callee in ["pulse", "forward"] {
            let source = format!("type Ledger struct {{{field}, owners: usize}} where(fact accurate = {count} == owners; fact weak = {count} == 0 => owners == 0; accurate && weak); {helpers} fn main() {{let storage: usize = 42; let ledger = Ledger {{count: {initial}, owners: 42}}; update(ledger) lifts accurate {{{callee}({argument});}}}}");
            let error = verify(&source).unwrap_err();
            assert!(error.contains("invariant of Ledger"), "{error}\n{source}");
            assert!(error.contains("body recheck failed"), "{error}");
        }
    }
    let conditional = "type Ledger struct {count: usize, owners: usize} where(fact accurate = count == owners; fact weak = count == 0 => owners == 0; accurate && weak); fn pulse(slot: &usize) modifies(slot) ensures(*slot == 42) {*slot = 0; *slot = 42;} fn maybe(slot: &usize, flag: bool) where(*slot == 42) modifies(slot) ensures(*slot == 42) {let effect = if flag {pulse(slot)} else {()};} fn main() {let ledger = Ledger {count: 42, owners: 42}; update(ledger) lifts accurate {maybe(&ledger.count, false);}}";
    assert!(verify(conditional).is_ok());
    assert!(verify(
        &conditional.replace("maybe(&ledger.count, false)", "maybe(&ledger.count, true)")
    )
    .unwrap_err()
    .contains("invariant of Ledger"));
}

#[test]
fn update_calls_still_require_permissions_and_ownership_free_bodies() {
    let source = "type Pair struct {left: usize, right: usize} where(fact balanced = left == right; balanced); fn set(slot: &usize) modifies(slot) ensures(*slot == 42) {*slot = 42;} fn hidden(slot: &usize) {let pair = Pair {left: 7, right: 7}; update(pair) lifts balanced {set(slot);}}";
    assert!(verify(source)
        .unwrap_err()
        .contains("matching modifies contract"));
    // A dereference must not bypass effect checking of its inner call.
    let source = "type Resource struct {} impl Drop for Resource {fn drop(self) {}} type Pair struct {left: usize, right: usize} where(fact balanced = left == right; balanced); fn hidden(slot: &usize) -> &usize borrows(slot) {let resource = Resource {}; slot} fn main() {let pair = Pair {left: 7, right: 7}; update(pair) lifts balanced {pair.left = *hidden(&pair.left); pair.right = pair.left;}}";
    assert!(verify(source)
        .unwrap_err()
        .contains("invariant-independent effects"));
    let source = "type Pair struct {left: usize, right: usize} where(fact balanced = left == right; balanced); fn main() {let pair = Pair {left: 42, right: 42}; let owner: plane(usize) = alloc(42); update(pair) lifts balanced {let observed = *(if true {owner} else {owner});}}";
    assert!(verify(source)
        .unwrap_err()
        .contains("runtime ownership moves are forbidden"));
}

#[test]
fn conditional_record_array_borrows_preserve_fields_and_storage_identity() {
    let source = include_str!("../../../examples/record_array_borrows.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for wrong in [
        source.replace("else {&(*data)[1].left}", "else {&(*data)[1].right}"),
        source.replace("else {&(*data)[1]}", "else {&(*data)[2]}"),
        source.replace(
            "borrows(&(*data)[if flag {0} else {1}])",
            "borrows(&(*data)[0])",
        ),
        source.replace("    (*selected).left", "    drop(data); (*selected).left"),
        source.replace(
            "(*selected).right == (if flag {9} else {13})",
            "(*selected).right == 42",
        ),
    ] {
        assert!(verify(&wrong).is_err(), "accepted {wrong}");
    }
    let different_planes = "type Cell struct {value: usize} fn bad(flag: bool) {let a = Cell {value: 7}; let b = Cell {value: 9}; let selected = if flag {&a} else {&b};}";
    assert!(verify(different_planes).is_err());
    let owners = "type Cell struct {value: usize} fn bad(flag: bool) {let data: [Cell; 2] = [Cell {value: 7}, Cell {value: 9}]; let selected = if flag {&data[0]} else {&data[1]};}";
    assert!(verify(owners).is_ok()); // Borrowing never copies the move-only element.
    let dropping = owners.replace("fn bad", "impl Drop for Cell {fn drop(self) {}} fn bad");
    assert!(verify(&dropping).is_err());
    let refined = "type Positive struct {value: usize} where(value > 0); fn choose(data: &[Positive; 2], flag: bool) -> &Positive borrows(&(*data)[if flag {0} else {1}]) {if flag {&(*data)[0]} else {&(*data)[1]}} fn read(flag: bool) -> usize ensures(result == 42) {let data: [Positive; 2] = [Positive {value: 7}, Positive {value: 9}]; let selected = choose(&data, flag); data[0].value = 42; data[1].value = 42; proof typed: (*selected).value > 0; (*selected).value} fn main() -> usize {read(false)}";
    assert_eq!(verify(refined).unwrap().run().unwrap().to_string(), "42");
    let nested = "type Inner struct {value: usize} type Cell struct {inner: Inner} fn read(flag: bool) -> usize ensures(result == 42) {let data: [Cell; 2] = [Cell {inner: Inner {value: 7}}, Cell {inner: Inner {value: 9}}]; let selected = if flag {&data[0].inner.value} else {&data[1].inner.value}; *selected = 42; if flag {data[0].inner.value} else {data[1].inner.value}} fn main() -> usize {read(true)}";
    assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn record_array_histories_preserve_aliases_fields_and_replay() {
    let source = include_str!("../../../examples/record_array_history.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let nested = include_str!("../../../examples/record_array_values.evg");
    let (program, bundle) = prove(nested).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(nested, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for wrong in [
        source.replace("(*data)[index].left == 42", "(*data)[index].left == 43"),
        source.replace("old((*data)[index].right)", "42"),
        source.replace(
            "modifies(&(*data)[index].left)",
            "modifies(&(*data)[index].right)",
        ),
    ] {
        assert!(verify(&wrong).is_err(), "accepted {wrong}");
    }
    let replacement = "type Cell struct {value: usize} fn replace(data: [Cell; 2], i: usize) -> usize where(i < 2) ensures(result == 42) {let selected = &data[i].value; data = [Cell {value: 42}, Cell {value: 42}]; *selected} fn main() -> usize {replace([Cell {value: 7}, Cell {value: 9}], 1)}";
    assert_eq!(
        verify(replacement).unwrap().run().unwrap().to_string(),
        "42"
    );
}

#[test]
fn record_array_writes_must_preserve_element_invariants() {
    let definition = "type Positive struct {value: usize} where(value > 0);";
    let setter = "fn set(value: &usize) modifies(value) ensures(*value == 42) {*value = 42;}";
    let caller = "fn change(data: [Positive; 2], i: usize) -> usize where(i < 2) ensures(result == 42) {let chosen = &data[i].value; set(&data[i].value); *chosen} fn main() -> usize {change([Positive {value: 7}, Positive {value: 9}], 1)}";
    let valid = format!("{definition} {setter} {caller}");
    assert_eq!(verify(&valid).unwrap().run().unwrap().to_string(), "42");
    let wrong = valid.replace("42", "0");
    let error = verify(&wrong).unwrap_err();
    assert!(error.contains("invariant of Positive"), "{error}");
    let direct = format!("{definition} fn bad(data: &[Positive; 2], i: usize) where(i < 2) modifies(&(*data)[i].value) {{(*data)[i].value = 0;}}");
    let error = verify(&direct).unwrap_err();
    assert!(error.contains("invariant of Positive"), "{error}");
    // An invariant on a generated alias-merge candidate must not erase
    // exactly the branch on which the store would violate that invariant.
    let conditional = format!("{definition} fn bad(data: [Positive; 2], i: usize, j: usize) where(i < 2 && j < 2) {{let observed = &data[j].value; data[i].value = if i == j {{0}} else {{42}};}}");
    let error = verify(&conditional).unwrap_err();
    assert!(error.contains("invariant of Positive"), "{error}");
    let intermediate = "type Balanced struct {left: usize, right: usize} where(left == right); fn set(left: &usize, right: &usize) modifies(left, right) ensures(*left == 42 && *right == 42) {*left = 42; *right = 42;} fn change(data: [Balanced; 2], i: usize) -> usize where(i < 2) ensures(result == 42) {let selected = &data[i].left; set(&data[i].left, &data[i].right); *selected} fn main() -> usize {change([Balanced {left: 7, right: 7}, Balanced {left: 9, right: 9}], 1)}";
    let (program, bundle) = prove(intermediate).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(intermediate, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(
        verify(&intermediate.replace("ensures(result == 42)", "ensures(result == 43)")).is_err()
    );
}

#[test]
fn array_histories_frame_cells_first_read_after_writes_and_branches() {
    for source in [
        include_str!("../../../examples/array_frame_history.evg"),
        include_str!("../../../examples/array_branch_history.evg"),
    ] {
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
    }
    let symbolic = "fn write_at(data: &[usize; 2], i: usize, j: usize) -> usize where(i < 2 && j < 2) modifies(&(*data)[i]) ensures((i == j => result == 42) && (i != j => result == old((*data)[j]))) {(*data)[i] = 42; let first_read = if i == j {(*data)[j]} else {0}; (*data)[j]} fn main() -> usize {let data: [usize; 2] = [7, 9]; write_at(&data, 0, 1)}";
    let (program, bundle) = prove(symbolic).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "9");
    assert_eq!(
        verify_with_certificate(symbolic, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&symbolic.replace(
        "ensures((i == j => result == 42) && (i != j => result == old((*data)[j])))",
        "ensures(result == 42)"
    ))
    .is_err());
}

#[test]
fn array_history_cache_replays_conditions_in_each_branch() {
    let source = "fn write(data: &[usize; 2], i: usize) where(i < 2) modifies(&(*data)[i]) ensures((*data)[i] == 42) {(*data)[i] = 42;} fn check(data: [usize; 2], i: usize, j: usize) -> usize where(i < 2 && j < 2) ensures((i == j => result == 42) && (i != j => result == data[j])) {let effect = if i == j {write(&data, i)} else {()}; data[j]} fn main() -> usize {check([7, 9], 0, 1)}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "9");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let false_frame = source.replace(
        "ensures((i == j => result == 42) && (i != j => result == data[j]))",
        "ensures(result == 42)",
    );
    assert!(verify(&false_frame).is_err());
}

#[test]
fn array_history_expansion_stops_before_unbounded_recursion() {
    let source = format!(
        "fn read(data: &[usize; 2]) -> usize modifies(&(*data)[0]) {{{} (*data)[1]}}",
        "(*data)[0] = 42;".repeat(65)
    );
    let error = verify(&source).unwrap_err();
    assert!(error.contains("array history read depth limit"), "{error}");
    let boolean = "fn set(data: &[bool; 2]) modifies(&(*data)[0]) ensures((*data)[1] == old((*data)[1])) {(*data)[0] = false;} fn main() -> bool {let data: [bool; 2] = [true, true]; set(&data); data[1]}";
    assert_eq!(verify(boolean).unwrap().run().unwrap().to_string(), "true");
}

#[test]
fn conditional_contract_indices_and_entry_snapshots_replay() {
    for source in [
        include_str!("../../../examples/conditional_contracts.evg"),
        include_str!("../../../examples/old_selection.evg"),
    ] {
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
    }
    let variables = "fn at(data: &[usize; 2], flag: bool, i: usize, j: usize) -> &usize where(i < 2 && j < 2) borrows(&(*data)[if flag {i} else {j}]) {if flag {&(*data)[i]} else {&(*data)[j]}} fn main() -> usize ensures(result == 42) {let data: [usize; 2] = [7, 42]; *at(&data, false, 0, 1)}";
    assert_eq!(verify(variables).unwrap().run().unwrap().to_string(), "42");
    let numeric = "fn at(data: &[usize; 2], i: usize) -> &usize where(i < 2) borrows(&(*data)[if i == 0 {0} else {1}]) {&(*data)[i]} fn main() -> usize {let data: [usize; 2] = [7, 42]; *at(&data, 1)}";
    assert_eq!(verify(numeric).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn conditional_contract_indices_cannot_retarget_or_execute_effects() {
    for source in [
        "fn bad(data: &[usize; 2], flag: bool) -> &usize borrows(&(*data)[if flag {0} else {1}]) {flag = !flag; if flag {&(*data)[0]} else {&(*data)[1]}}",
        "fn bad(data: &[usize; 2], flag: bool) modifies(&(*data)[if flag {0} else {1}]) {flag = !flag; (*data)[if flag {0} else {1}] = 42;}",
        "fn bad(data: &[usize; 2], cursor: &usize) where(*cursor == 0) modifies(cursor, &(*data)[if *cursor == 0 {0} else {1}]) {*cursor = 1; (*data)[if *cursor == 0 {0} else {1}] = 42;}",
        "fn side(cursor: &usize) -> bool modifies(cursor) {*cursor = 0; true} fn bad(data: &[usize; 2], cursor: &usize) -> &usize borrows(&(*data)[if side(cursor) {0} else {1}]) {&(*data)[0]}",
        "fn bad(data: &[usize; 2], flag: bool) -> &usize borrows(&(*data)[if flag {0} else {2}]) {if flag {&(*data)[0]} else {&(*data)[1]}}",
        "fn bad(data: &[usize; 2], flag: bool) {proof wrong: old((*data)[if flag {0} else {1}]) == 42;}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
    let effectful_old = "fn side() -> bool {true} fn bad(data: &[usize; 2]) {proof wrong: old((*data)[if side() {0} else {1}]) == 42;}";
    assert!(verify(effectful_old).is_err());
}

#[test]
fn identity_sensitive_conditional_contracts_recheck_actual_aliases() {
    let correct = "fn at(data: &[usize; 2], a: &usize, b: &usize) -> &usize borrows(&(*data)[if a == b {0} else {1}]) {if a == b {&(*data)[0]} else {&(*data)[1]}} fn main() -> usize ensures(result == 42) {let data: [usize; 2] = [42, 7]; let n: usize = 0; *at(&data, &n, &n)}";
    let (program, bundle) = prove(correct).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(correct, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let incorrect = correct.replace(
        "{if a == b {&(*data)[0]} else {&(*data)[1]}}",
        "{&(*data)[1]}",
    );
    assert!(verify(&incorrect)
        .unwrap_err()
        .contains("body recheck failed"));
}

#[test]
fn conditional_array_references_preserve_origins_and_old_views() {
    for source in [
        include_str!("../../../examples/conditional_borrows.evg"),
        include_str!("../../../examples/conditional_drop.evg"),
    ] {
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
    }
    let replaced = "fn read(flag: bool, i: usize) -> usize where(i < 2) ensures(result == 42) {let data: [usize; 2] = [7, 9]; let observed = &data[i]; let selected = if flag {&data[0]} else {&data[1]}; data = [42, 42]; proof old_view: *observed == 42; *selected} fn main() -> usize {read(false, 0)}";
    assert_eq!(verify(replaced).unwrap().run().unwrap().to_string(), "42");
    let nested = "type Buffer struct {data: [usize; 2]} fn read(flag: bool) -> usize ensures(result == 42) {let buffer = Buffer {data: [7, 9]}; let selected = if flag {&buffer.data[0]} else {&buffer.data[1]}; *selected = 42; if flag {buffer.data[0]} else {buffer.data[1]}} fn main() -> usize {read(false)}";
    assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
    let rebound = "fn read(flag: bool) -> usize ensures(result == 42) {let data: [usize; 2] = [7, 9]; let selected = &data[0]; let indirect = &selected; selected = if flag {&data[0]} else {&data[1]}; **indirect = 42; if flag {data[0]} else {data[1]}} fn main() -> usize {read(true)}";
    assert_eq!(verify(rebound).unwrap().run().unwrap().to_string(), "42");
    let array = "fn choose(flag: bool) -> [usize; 2] ensures((flag => result[0] == 42) && (!flag => result[1] == 42)) {if flag {[42, 7]} else {[7, 42]}} fn main() -> usize ensures(result == 42) {let data = choose(false); data[1]}";
    assert_eq!(verify(array).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn conditional_references_cannot_change_origins_or_escape_generation_checks() {
    let source = include_str!("../../../examples/conditional_borrows.evg");
    assert!(verify(&source.replace("borrows(&(*data)[index])", "borrows(&(*data)[0])")).is_err());
    assert!(verify(&source.replace("data[1] = 42;", "drop(data); data = [7, 42];")).is_err());
    for source in [
        "fn bad(a: &usize, b: &usize, flag: bool) -> &usize borrows(a) {if flag {a} else {b}}",
        "fn bad(flag: bool) -> usize {let data: [usize; 2] = [7, 9]; let selected = if flag {&data[0]} else {&data[1]}; drop(data); *selected}",
        "fn bad(data: &[usize; 2], i: usize) -> &usize where(i < 2) borrows(&(*data)[i]) {i = 0; if i == 0 {&(*data)[0]} else {&(*data)[1]}}",
        "type Pair struct {a: usize, b: usize} fn bad(flag: bool) {let pair = Pair {a: 7, b: 9}; let selected = if flag {&pair.a} else {&pair.b};}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn reference_equality_checks_identity_and_symbolic_projections() {
    let source = include_str!("../../../examples/reference_identity.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let indexed = "fn same(a: &usize, b: &usize) -> bool ensures(result == (a == b)) {a == b} fn at(data: &[usize; 2], i: usize, j: usize) -> bool where(i < 2 && j < 2) ensures(result == (i == j)) {same(&(*data)[i], &(*data)[j])} fn main() -> usize ensures(result == 42) {let data: [usize; 2] = [7, 7]; proof equal: at(&data, 1, 1); proof distinct: !at(&data, 0, 1); if at(&data, 0, 0) {42} else {0}}";
    assert_eq!(verify(indexed).unwrap().run().unwrap().to_string(), "42");
    let ideal = "ideal fn same(a: &usize, b: &usize) -> bool ensures(result == (a == b)) {a == b} fn main() -> usize {let n: usize = 7; proof alias: same(&n, &n); 42}";
    assert_eq!(verify(ideal).unwrap().run().unwrap().to_string(), "42");
    let nominal = "type Empty struct {} fn main() -> usize {let a = Empty {}; let b = Empty {}; proof distinct: &a != &b; proof identity: &a == &a; 42}";
    assert_eq!(verify(nominal).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn readonly_contracts_cannot_assume_independent_reference_identity() {
    for source in [
        "fn separate(a: &usize, b: &usize) -> bool ensures(!result) {a == b} fn main() {let n: usize = 0; separate(&n, &n);}",
        "fn impossible(a: &usize, b: &usize) -> usize where(a == b) {proof lie: false; 42} fn main() -> usize {let n: usize = 0; impossible(&n, &n)}",
        "type Two struct {a: &usize, b: &usize} fn separate(view: Two) -> bool ensures(!result) {view.a == view.b} fn main() {let n: usize = 0; separate(Two {a: &n, b: &n});}",
        "type Container struct {value: usize, pointer: &usize} fn separate(c: &Container) -> bool ensures(!result) {(*c).pointer == &(*c).value} fn main() {let n: usize = 0; let c = Container {value: 7, pointer: &n}; c.pointer = &c.value; separate(&c);}",
    ] {
        assert!(verify(source).unwrap_err().contains("body recheck failed"), "accepted {source}");
    }
    let same_pre = "fn same(a: &usize, b: &usize) -> usize where(a == b) ensures(result == 42) {42} fn main() -> usize {let n: usize = 0; same(&n, &n)}";
    assert_eq!(verify(same_pre).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(
        &same_pre
            .replace("same(&n, &n)", "same(&n, &other)")
            .replace(
                "let n: usize = 0;",
                "let n: usize = 0; let other: usize = 0;"
            )
    )
    .is_err());
}

#[test]
fn reference_identity_cannot_observe_stale_storage_or_compare_different_types() {
    for source in [
        "fn main() {let n: usize = 0; let r = &n; drop(n); proof stale: r == r;}",
        "fn main() {let n: usize = 0; let r = &n; drop(n); n = 0; proof stale: r != &n;}",
        "fn bad(a: &usize, b: &usize) -> bool {a < b}",
        "fn bad(a: &usize, b: &isize) -> bool {a == b}",
        "fn bad(a: &usize, b: usize) -> bool {a == b}",
        "fn bad(a: &usize) {proof invalid: old(&a) == &a;}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn propositional_proof_scripts_check_rules_and_replay_without_search() {
    let source = include_str!("../../../examples/propositional_proofs.evg");
    let (program, bundle) = prove(source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for source in [
        "fn identity(a: bool) {proof same: a => a by {intro h; exact h}; proof expanded: !a || a by {exact same};}",
        "fn package(a: bool, b: bool) {proof rule: a => b => (a && b) by {intro ha; intro hb; constructor; exact ha; exact hb}; proof again: a => b => (a && b) by {intro ha; intro hb; apply rule; assumption; assumption};}",
        "fn scopes(a: bool, b: bool) {proof both: (a => a) && (b => b) by {constructor; intro h; exact h; intro h; exact h};}",
        "fn duplicate(a: bool, b: bool) {proof both: a => ((a || b) && (a || b)) by {intro h; constructor; left; exact h; left; assumption};}",
        "fn negate(a: bool) {proof law: !(a && !a) by {intro impossible; omega};}",
        "fn refute(a: bool) {proof impossible: !a => a => false by {intro negative; intro positive; apply negative; exact positive};}",
        "fn main() -> usize {proof identity: true => true by {intro h; exact h}; 42}",
    ] {assert!(verify(source).is_ok(), "rejected {source}");}
}

#[test]
fn proof_cases_check_both_branches_and_decompose_conjunctions() {
    let source = include_str!("../../../examples/proof_cases.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for source in [
        "fn absurd(a: bool) {proof explosion: false => a by {intro impossible; cases impossible};}",
        "fn same(a: bool, b: bool) {proof either: (a || b) => (a || b) by {intro h; cases h with part | part; left; exact part; right; exact part};}",
        "fn retain(a: bool, b: bool) {proof same: (a || b) => (a || b) by {intro h; cases h with first | second; exact h; exact h};}",
        "fn retain(a: bool, b: bool) {proof same: (a && b) => (a && b) by {intro h; cases h with first, second; exact h};}",
        "fn nested(a: bool, b: bool, c: bool) {proof grouped: (a || (b || c)) => ((a || b) || c) by {intro h; cases h with ha | rest; left; left; exact ha; cases rest with hb | hc; left; right; exact hb; right; exact hc};}",
    ] {assert!(verify(source).is_ok(), "rejected {source}");}
}

#[test]
fn proof_cases_cannot_leak_hypotheses_or_ignore_an_alternative() {
    for source in [
        "fn bad(a: bool, b: bool) {proof false_case: (a || b) => a by {intro h; cases h with first | second; exact first; exact second};}",
        "fn bad(a: bool, b: bool) {proof leaked: (a || b) => a by {intro h; cases h with first | second; exact first; exact first};}",
        "fn bad(a: bool, b: bool) {proof incomplete: (a || b) => (b || a) by {intro h; cases h with first | second; right; exact first};}",
        "fn bad(a: bool, b: bool) {proof wrong: (a || b) => a by {intro h; cases h with first, second; exact first};}",
        "fn bad(a: bool, b: bool) {proof wrong: (a && b) => a by {intro h; cases h with first | second; exact first; exact second};}",
        "fn bad(a: bool, b: bool) {proof wrong: (a && b) => a by {intro h; cases h with part, part; exact part};}",
        "fn bad(a: bool, b: bool) {proof wrong: (a && b) => a by {intro h; cases h with a, other; exact a};}",
        "fn bad(a: bool, b: bool) {proof wrong: (a && b) => a by {intro h; cases h with h, other; exact h};}",
        "fn bad(a: bool, b: bool) {fact h = a || b; proof raw: a || b by {cases h with first | second; left; exact first; right; exact second};}",
        "fn bad() {proof missing: true by {cases absent with first | second; omega; omega};}",
        "fn bad() {proof present: true; proof wrong: true by {cases present};}",
        "fn bad(a: bool, b: bool) {proof identity: (a || b) => (a || b) by {intro h; cases h};}",
        "fn bad() {proof malformed: true by {cases absent with first second; omega};}",
        "fn bad() {proof witness: (true && true) => true by {intro h; cases h with first, second; exact first}; proof escaped: true by {exact second};}",
        "fn bad(a: bool) {proof reflexive: (a && a) => a by {intro h; cases h with first, second; exact first}; proof leaked_path: a;}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn propositional_hypotheses_cannot_escape_or_prove_the_wrong_goal() {
    for source in [
        "fn bad(a: bool, b: bool) {proof wrong: a => b by {intro h; exact h};}",
        "fn bad(a: bool) {proof same: a => a by {intro h; exact h}; proof escaped: a by {exact h};}",
        "fn bad() {proof same: false => false by {intro h; exact h}; proof leaked: false;}",
        "fn bad(a: bool) {proof both: (a => a) && a by {constructor; intro h; exact h; exact h};}",
        "fn bad(a: bool) {fact rule = a => a; proof same: a => a by {apply rule};}",
        "fn bad(a: bool) {proof same: a => a by {intro h; exact h}; proof unfinished: a => a by {intro h; apply same};}",
        "fn bad(a: bool) {proof same: a => a by {intro a; exact a};}",
        "fn bad() {proof no_hypothesis: true by {assumption};}",
        "fn bad() {proof extra: true by {omega; omega};}",
        "fn bad() {proof wrong: true by {intro h; omega};}",
        "fn bad() {proof wrong: true by {constructor; omega; omega};}",
        "fn bad() {proof wrong: true by {left; omega};}",
        "fn bad() {proof wrong: true by {right; omega};}",
        "fn bad() {proof wrong: true by {apply missing};}",
        "fn bad() {proof wrong: true by {invent_proof};}",
        "fn bad() {proof mixed: true && true by {constructor; trustme; omega};}",
        "fn main() -> usize {let n: usize = 1; proof rule: n == 1 => n > 0; n = 0; proof stale: n > 0 by {apply rule; omega}; n}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
    let oversized = format!(
        "fn main() {{proof too_long: true by {{{}}};}}",
        "omega;".repeat(1025)
    );
    assert!(verify(&oversized)
        .unwrap_err()
        .contains("proof script limit"));
}

#[test]
fn overlapping_calls_reprove_bodies_contracts_and_return_aliases() {
    let source = include_str!("../../../examples/aliasing_calls.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace(
        "proof self_swap: value == 7;",
        "proof self_swap: value == 42;"
    ))
    .is_err());
    let arrays = "fn change(data: &[usize; 2], value: &usize) modifies(data) ensures((*data)[0] == old(*value)) {(*data)[0] = *value;} fn main() -> usize ensures(result == 42) {let data: [usize; 2] = [7, 42]; change(&data, &data[1]); data[0]}";
    assert_eq!(verify(arrays).unwrap().run().unwrap().to_string(), "42");
    let scope = "fn write(a: &usize, b: &usize) modifies(a) {proof saved: *b <= usize::MAX; *a = 42;} fn main() -> usize ensures(result == 42) {let n: usize = 7; proof saved: n == 7; write(&n, &n); n}";
    assert_eq!(verify(scope).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&scope.replace(
        "write(&n, &n); n",
        "write(&n, &n); proof stale: n == 7 by {exact saved}; n"
    ))
    .is_err());
    let private = "module hidden {opaque type View struct {a: &usize, b: &usize} fn set(view: View) modifies(view.a) {*view.a = 42;} fn write(a: &usize, b: &usize) -> usize modifies(a) {let view = View {a: a, b: b}; set(view); *b}} fn main() -> usize ensures(result == 42) {let n: usize = 7; hidden::write(&n, &n)}";
    assert_eq!(verify(private).unwrap().run().unwrap().to_string(), "42");
    let ordered = "fn sequence(first: &usize, second: &usize) modifies(first, second) {*first = 7; *second = 42;} fn main() -> usize ensures(result == 42) {let n: usize = 0; sequence(&n, &n); n}";
    assert_eq!(verify(ordered).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn overlapping_calls_do_not_assume_independent_posts_or_expand_permissions() {
    let library = "fn set(write: &usize, read: &usize) modifies(write) ensures(*write == 42 && *read == old(*read)) {*write = 42;}";
    let invalid = format!("{library} fn main() {{let n: usize = 7; set(&n, &n);}}");
    assert!(verify(&invalid)
        .unwrap_err()
        .contains("body recheck failed"));
    // The same contract can hold for a particular aliasing input.
    let valid = format!(
        "{library} fn main() -> usize ensures(result == 42) {{let n: usize = 42; set(&n, &n); n}}"
    );
    assert_eq!(verify(&valid).unwrap().run().unwrap().to_string(), "42");
    for caller in [
        "fn bad(a: &usize) {set(a, a);}",
        "fn bad(a: &usize) modifies(a) {proof call: set(a, a) == ();}",
    ] {
        assert!(verify(&format!("{library} {caller}")).is_err());
    }
    let invalidated = "type Positive struct {value: usize} where(value > 0); fn set(write: &usize, read: &usize) modifies(write) {*write = 0;} fn main() {let positive = Positive {value: 1}; set(&positive.value, &positive.value);}";
    assert!(verify(invalidated).is_err());
    let trusted = "fn set(write: &usize, read: &usize) modifies(write) ensures(*read == old(*read)) {*write = 42;} proof {trustme} fn main() -> usize ensures(result == 7) {let n: usize = 7; set(&n, &n); n}";
    let (program, bundle) = prove(trusted).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().len() >= 2);
    assert_eq!(
        verify_with_certificate(trusted, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn overlapping_body_rechecks_share_evaluation_limits() {
    let recursive = "fn spin(a: &usize, b: &usize) modifies(a, b) {spin(a, b);} fn main() {let value: usize = 0; spin(&value, &value);}";
    let error = verify(recursive).unwrap_err();
    assert!(error.contains("verification evaluation limit"), "{error}");
}

#[test]
fn aliased_count_handle_batch_cleanup_rechecks_each_remaining_owner() {
    let library = [
        include_str!("../../../stdlib/counter.evg"),
        include_str!("../../../proofs/count_handles.evg"),
    ]
    .join("\n");
    let source = format!(
        "{library} {}",
        include_str!("../../../examples/batch_count.evg")
    );
    let (program, bundle) = prove(&source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "0");
    assert_eq!(
        events,
        [
            "drop count_handles::Handle",
            "drop count_handles::Release",
            "drop count_handles::Handle",
            "drop count_handles::Release"
        ]
    );
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    // Numeric constructors alone can claim two handles over count=1. Their
    // combined release is rejected: after the first, the second is invalid.
    let bad = format!("{library} fn main() {{let count: usize = 1; let first = count_handles::create(&count); let second = count_handles::create(&count); count_handles::release_pair([first, second]);}}");
    assert!(verify(&bad).unwrap_err().contains("body recheck failed"));
}

#[test]
fn reference_returns_preserve_incoming_planes_and_reject_local_escapes() {
    let good = include_str!("../../../examples/borrow_returns.evg");
    assert_eq!(verify(good).unwrap().run().unwrap().to_string(), "42");
    for source in [
        "fn bad(r: &usize) -> &usize borrows(r) {let local = *r; &local}",
        "fn bad(a: &usize, b: &usize) -> &usize borrows(a) {b}",
        "fn bad(r: &usize) -> &&usize borrows(&r) {&r}",
        "fn bad(n: usize) -> &usize borrows(&n) {&n}",
        "fn bad(r: &usize) -> &usize {r}",
        "fn bad(r: &usize) -> usize borrows(r) {*r}",
        "fn bad(r: &usize) -> &usize borrows(if true {r} else {r}) {r}",
    ] {
        assert!(verify(source).is_err(), "{source}");
    }
    let stale = good.replace("    *r", "    drop(pair);\n    *r");
    assert!(verify(&stale).is_err());
    let replaced = good.replace(
        "    *r",
        "    drop(pair);\n    pair = Pair {left: 0, right: 42};\n    *r",
    );
    assert!(verify(&replaced).is_err());
    let array = "fn first(a: &[usize; 2]) -> &usize borrows(&(*a)[0]) {&(*a)[0]} fn main() -> usize {let a: [usize; 2] = [42, 7]; *first(&a)}";
    assert_eq!(verify(array).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn modifying_reference_returns_keep_the_entry_alias_and_replay() {
    let library = concat!(include_str!("../../../stdlib/arrays/array.evg"), "\u{1e}");
    let source = format!(
        "{library} {}",
        include_str!("../../../examples/write_borrows.evg")
    );
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    let replayed = verify_with_certificate(&source, &bundle).unwrap();
    assert_eq!(replayed.proof_search_count(), 0);
    assert_eq!(replayed.run().unwrap().to_string(), "42");
    let scalar = "fn increment(r: &usize) -> &usize where(*r < usize::MAX) modifies(r) borrows(r) ensures(*result == old(*r) + 1) {*r = *r + 1; r} fn main() -> usize ensures(result == 42) {let n: usize = 41; let original = &n; let updated = increment(&n); proof visible: *original == 42; *updated}";
    assert_eq!(verify(scalar).unwrap().run().unwrap().to_string(), "42");
    let frame = "fn set(a: &[usize; 2]) -> &usize modifies(&(*a)[0]) borrows(&(*a)[0]) ensures(*result == 42) {(*a)[0] = 42; &(*a)[0]} fn main() -> usize ensures(result == 49) {let a: [usize; 2] = [1, 7]; let r = set(&a); *r + a[1]}";
    assert_eq!(verify(frame).unwrap().run().unwrap().to_string(), "49");
    let parent = "type Pair struct {left: usize, right: usize} fn set(p: &Pair) -> &Pair modifies(&(*p).left) borrows(p) ensures((*result).left == 7) {(*p).left = 7; p} fn main() -> usize ensures(result == 42) {let p = Pair {left: 0, right: 42}; let q = set(&p); (*q).right}";
    assert_eq!(verify(parent).unwrap().run().unwrap().to_string(), "42");
    let invariant = "type Fixed struct {value: usize} where(value == 42); fn refresh(r: &Fixed) -> &Fixed modifies(&(*r).value) borrows(r) ensures((*r).value == 42 && (*result).value == 42) {(*r).value = 42; r} fn main() -> usize ensures(result == 42) {let fixed = Fixed {value: 42}; let refreshed = refresh(&fixed); (*refreshed).value}";
    assert_eq!(verify(invariant).unwrap().run().unwrap().to_string(), "42");
    let readonly = "fn set(a: &usize, b: &usize) -> &usize modifies(a) borrows(b) ensures(*a == 7 && *result == old(*b)) {*a = 7; b} fn main() -> usize ensures(result == 42) {let a: usize = 0; let b: usize = 42; *set(&a, &b)}";
    assert_eq!(verify(readonly).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn modifying_returns_cannot_change_aliases_or_bypass_write_permissions() {
    for source in [
        "fn bad(r: &usize) -> &usize modifies(r) borrows(r) {*r = 42; let local: usize = 42; &local}",
        "fn bad(r: &usize, other: &usize) -> &usize modifies(r) borrows(r) {*r = 42; other}",
        "fn bad(a: &[usize; 2], i: usize) -> &usize where(i == 0) modifies(&(*a)[i]) borrows(&(*a)[i]) {(*a)[i] = 42; i = 1; &(*a)[i]}",
        "fn bad(a: &[usize; 2]) -> &usize modifies(a) borrows(&(*a)[0]) {*a = [42]; &(*a)[0]}",
        "fn bad(r: &usize) -> &usize modifies(r) borrows(r) {drop(*r); r}",
        "ideal fn bad(r: &usize) -> &usize modifies(r) borrows(r) {r}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
    let parent = "type Pair struct {left: usize, right: usize} fn set(p: &Pair) -> &Pair modifies(&(*p).left) borrows(p) {(*p).left = 7; p} fn bad(p: &Pair) modifies(&(*p).left) {let wider = set(p); (*wider).right = 42;}";
    assert!(verify(parent).unwrap_err().contains("effect contract"));
    let overlaps = "fn set(a: &usize, b: &usize) -> &usize modifies(a) borrows(b) {*a = 7; b} fn main() -> usize {let n: usize = 42; *set(&n, &n)}";
    assert_eq!(verify(overlaps).unwrap().run().unwrap().to_string(), "7");
    let setter =
        "fn set(r: &usize) -> &usize modifies(r) borrows(r) ensures(*result == 42) {*r = 42; r}";
    for caller in [
        "fn bad(r: &usize) -> &usize borrows(r) {set(r)}",
        "fn bad(r: &usize) {proof cannot_erase_write: *set(r) == 42;}",
        "fn main() -> usize {let n: usize = 1; let r = set(&n); drop(n); *r}",
        "fn main() -> usize {let n: usize = 1; let r = set(&n); drop(n); n = 42; *r}",
        "fn main() -> usize ensures(result == 0) {let n: usize = 0; *set(&n)}",
    ] {
        assert!(
            verify(&format!("{setter} {caller}")).is_err(),
            "accepted {caller}"
        );
    }
}

#[test]
fn computed_place_contracts_capture_checked_entry_expressions() {
    let source = include_str!("../../../examples/computed_places.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    let replayed = verify_with_certificate(source, &bundle).unwrap();
    assert_eq!(replayed.proof_search_count(), 0);
    assert_eq!(replayed.run().unwrap().to_string(), "42");
    let cursor = "fn insert(data: &[usize; 3], cursor: &usize) -> &usize where(*cursor < 2) modifies(cursor, &(*data)[*cursor + 1]) borrows(&(*data)[*cursor + 1]) ensures(*result == 42 && *cursor == old(*cursor) + 1) {let selected = &(*data)[*cursor + 1]; *selected = 42; *cursor = *cursor + 1; selected} fn main() -> usize ensures(result == 42) {let data: [usize; 3] = [7, 8, 9]; let cursor: usize = 1; let selected = insert(&data, &cursor); proof cursor_changed: cursor == 2; *selected}";
    assert_eq!(verify(cursor).unwrap().run().unwrap().to_string(), "42");
    let math = "fn next(data: &[usize; 3], i: usize) -> &usize where(i < 2) borrows(&(*data)[integer(i) + 1]) {&(*data)[i + 1]} fn main() -> usize {let a: [usize; 3] = [7, 8, 42]; *next(&a, 1)}";
    assert_eq!(verify(math).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn computed_place_contracts_reject_overflow_bounds_and_retargeting() {
    for source in [
        "fn bad(a: &[usize; 2], i: usize) -> &usize where(i < 2) borrows(&(*a)[i + 1]) {&(*a)[i + 1]}",
        "fn bad(a: &[usize; 3], i: usize) -> &usize where(i == usize::MAX) borrows(&(*a)[i + 1]) {&(*a)[0]}",
        "fn bad(a: &[usize; 3], i: usize) -> &usize where(i < 2) borrows(&(*a)[i - 1]) {&(*a)[0]}",
        "fn bad(a: &[usize; 3], i: usize) -> &usize where(i == 0) borrows(&(*a)[i + 1]) {i = 1; &(*a)[i + 1]}",
        "fn bad(a: &[usize; 3], i: usize) where(i == 0) modifies(&(*a)[i + 1]) {i = 1; (*a)[i + 1] = 42;}",
        "fn bad(a: &[usize; 3], cursor: &usize) where(*cursor == 0) modifies(cursor, &(*a)[*cursor + 1]) {*cursor = 1; (*a)[*cursor + 1] = 42;}",
        "fn set(i: &usize) -> usize modifies(i) {*i = 0; 0} fn bad(a: &[usize; 3], i: &usize) -> &usize borrows(&(*a)[set(i)]) {&(*a)[0]}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn owning_return_records_preserve_aliases_extents_and_cleanup() {
    for source in [
        include_str!("../../../examples/owned_borrows.evg"),
        include_str!("../../../examples/borrowed_view.evg"),
    ] {
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        let replayed = verify_with_certificate(source, &bundle).unwrap();
        assert_eq!(replayed.proof_search_count(), 0);
        assert_eq!(replayed.run().unwrap().to_string(), "42");
    }
    let alias = "type Pair struct {left: &usize, right: &usize} fn pair(left: &usize, right: &usize) -> Pair borrows(left: left, right: right) {Pair {left: left, right: right}} fn main() -> usize ensures(result == 42) {let count: usize = 1; let view = pair(&count, &count); *view.left = 42; *view.right}";
    assert_eq!(verify(alias).unwrap().run().unwrap().to_string(), "42");
    let indexed = "type View struct {reference: &usize} fn at(data: &[usize; 3], i: usize) -> View where(i < 2) borrows(reference: &(*data)[i + 1]) {View {reference: &(*data)[1 + i]}} fn main() -> usize ensures(result == 17) {let data: [usize; 3] = [7, 42, 9]; let view = at(&data, 0); data[1] = 17; *view.reference}";
    assert_eq!(verify(indexed).unwrap().run().unwrap().to_string(), "17");
    assert!(verify(&indexed.replace("data[1] = 17;", "drop(data);")).is_err());
}

#[test]
fn owning_return_aliases_cannot_escape_local_storage_or_forge_origins() {
    let view = "type View struct {target: &usize}";
    for function in [
        "fn bad(target: &usize) -> View {View {target: target}}",
        "fn bad(a: &usize, b: &usize) -> View borrows(target: a) {View {target: b}}",
        "fn bad(target: &usize) -> View borrows(target: target) {let local: usize = 42; View {target: &local}}",
        "fn bad(value: usize) -> View borrows(target: &value) {View {target: &value}}",
        "fn bad(target: &usize) -> View borrows(missing: target) {View {target: target}}",
        "fn bad(target: &usize) -> View borrows(target: target, target: target) {View {target: target}}",
        "fn bad(a: &usize, b: &usize) -> View borrows(target: a) {proof cheat: false by {trustme}; View {target: b}}",
    ] {
        assert!(verify(&format!("{view} {function}")).is_err(), "accepted {function}");
    }
    let declarations = include_str!("../../../examples/owned_borrows.evg")
        .split("fn main")
        .next()
        .unwrap();
    let invalid = format!("{declarations} type PositiveView struct {{target: &usize}} where(*target > 0); fn bad(target: &usize) -> PositiveView where(*target > 0) modifies(target) borrows(target: target) {{let cleanup = StoreOnDrop {{target: target, value: 0}}; PositiveView {{target: target}}}}");
    assert!(verify(&invalid).is_err());
    let invalid_array = format!("{declarations} type PositiveView struct {{target: &usize}} where(*target > 0); fn bad(target: &usize) -> [PositiveView; 1] where(*target > 0) modifies(target) borrows(result[0].target: target) {{let cleanup = StoreOnDrop {{target: target, value: 0}}; [PositiveView {{target: target}}]}}");
    assert!(verify(&invalid_array).is_err());
    let broken = format!("{declarations} fn main() -> usize {{let count: usize = 0; let guard = make(&count, 42); drop(count); drop(guard); 0}}");
    assert!(verify(&broken).is_err());
}

#[test]
fn fixed_reference_array_inputs_have_stable_ports_and_frame_siblings() {
    let source = include_str!("../../../examples/reference_array_inputs.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let by_value = "fn set(refs: [&usize; 2]) modifies(refs[1]) ensures(*refs[1] == 42 && *refs[0] == old(*refs[0])) {*refs[1] = 42;} fn main() -> usize ensures(result == 42) {let a: usize = 7; let b: usize = 0; set([&a, &b]); proof framed: a == 7; b}";
    assert_eq!(verify(by_value).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&by_value.replace("set([&a, &b])", "set([&a, &a])"))
        .unwrap_err()
        .contains("overlaps"));
    let nested = "type Shelf struct {views: [[&usize; 1]; 2]} fn set(shelf: &Shelf) modifies((*shelf).views[1][0]) ensures(*(*shelf).views[1][0] == 42 && *(*shelf).views[0][0] == old(*(*shelf).views[0][0])) {*(*shelf).views[1][0] = 42;} fn main() -> usize ensures(result == 42) {let a: usize = 7; let b: usize = 0; let shelf = Shelf {views: [[&a], [&b]]}; set(&shelf); proof framed: a == 7; b}";
    assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn fixed_reference_array_inputs_cannot_hide_aliases_or_escape_origins() {
    let declarations = include_str!("../../../examples/reference_array_inputs.evg")
        .split("fn main")
        .next()
        .unwrap();
    let overlap = format!("{declarations} fn main() {{let n: usize = 0; let views: [View; 2] = [View {{target: &n}}, View {{target: &n}}]; set_second(&views, 42);}}");
    assert!(verify(&overlap).unwrap_err().contains("overlaps"));
    for source in [
        "fn hidden(refs: [&usize; 2]) {*refs[1] = 42;}",
        "fn bad(refs: [&usize; 2]) modifies(refs[1]) {refs = [refs[1], refs[0]]; *refs[1] = 42;}",
        "fn bad(refs: [&usize; 2]) -> &usize borrows(refs[0]) {refs[1]}",
        "fn bad(refs: [&usize; 2]) -> &&usize borrows(&refs[0]) {&refs[0]}",
        "fn bad(ideal n: nat, refs: [&usize; n]) modifies(refs[0]) {*refs[0] = 42;}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
    let invalidated = format!("{declarations} type Positive struct {{target: &usize}} where(*target > 0); fn main() {{let a: usize = 7; let b: usize = 1; let positive = Positive {{target: &b}}; let views: [View; 2] = [View {{target: &a}}, View {{target: &b}}]; set_second(&views, 0);}}");
    assert!(verify(&invalidated).is_err());
    let large = "fn oversized(refs: [&usize; 2049]) {}";
    assert!(verify(large)
        .unwrap_err()
        .contains("incoming reference array expansion"));
    let dangling = include_str!("../../../examples/reference_array_inputs.evg")
        .replace("set_second(&views, 42);", "drop(last); last = 42;");
    assert!(verify(&dangling).is_err());
}

#[test]
fn returned_reference_arrays_preserve_nested_origins_and_replay() {
    let source = include_str!("../../../examples/borrowed_array.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let owned = include_str!("../../../examples/borrowed_array_owners.evg");
    let (program, bundle) = prove(owned).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop DeferredStore", "drop DeferredStore"]);
    assert_eq!(
        verify_with_certificate(owned, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let nested = "type Views struct {items: [[&usize; 1]; 2]} fn views(a: &usize, b: &usize) -> Views borrows(items[0][0]: a, items[1][0]: b) {Views {items: [[a], [b]]}} fn main() -> usize ensures(result == 42) {let a: usize = 0; let b: usize = 1; let v = views(&a, &b); *v.items[1][0] = 42; b}";
    assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
    let elements = "type View struct {value: &usize} fn views(a: &usize, b: &usize) -> [View; 2] borrows(result[0].value: a, result[1].value: b) {[View {value: a}, View {value: b}]} fn main() -> usize ensures(result == 42) {let a: usize = 0; let b: usize = 1; let v = views(&a, &b); *v[1].value = 42; b}";
    assert_eq!(verify(elements).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("data[1] = 42;", "drop(data);")).is_err());
    assert!(verify(&source.replace("data[1] = 42;", "drop(data); data = [7, 42, 11];")).is_err());
}

#[test]
fn returned_reference_arrays_reject_missing_duplicate_and_forged_origins() {
    for source in [
        "fn bad(a: &usize) -> [&usize; 2] borrows(result[0]: a) {[a, a]}",
        "fn bad(a: &usize) -> [&usize; 1] borrows(result[0]: a, result[0]: a) {[a]}",
        "fn bad(a: &usize) -> [&usize; 1] borrows(result[1]: a) {[a]}",
        "fn bad(a: &usize, b: &usize) -> [&usize; 2] borrows(result[0]: a, result[1]: b) {[b, a]}",
        "fn bad(a: &usize) -> [&usize; 1] borrows(result[0]: a) {let local: usize = 42; [&local]}",
        "fn bad(a: &usize) -> [&usize; 1] borrows(result[0]: &a) {[a]}",
        "fn bad(a: &usize) -> [&usize; 1] borrows(result[0 + 0]: a) {[a]}",
        "fn bad(a: &usize) -> [&usize; 1] borrows(result[0]: a) {proof cheat: false by {trustme}; let local: usize = 42; [&local]}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
    let expansion = "fn bad(a: &usize) -> [[[&usize; 0]; 2048]; 2048] {}";
    assert!(verify(expansion)
        .unwrap_err()
        .contains("return alias expansion"));
}

#[test]
fn language_count_handle_constructors_clones_and_drops_compose() {
    let source = [
        include_str!("../../../stdlib/counter.evg"),
        include_str!("../../../proofs/count_handles.evg"),
        include_str!("../../../examples/clone_count.evg"),
    ]
    .join("\n");
    let (program, bundle) = prove(&source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "0");
    assert_eq!(
        events,
        [
            "drop count_handles::Handle",
            "drop count_handles::Release",
            "drop count_handles::Handle",
            "drop count_handles::Release"
        ]
    );
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace(
        "let incremented = counter_increment((*handle).release.count);",
        ""
    ))
    .is_err());
}

#[test]
fn later_call_arguments_cannot_invalidate_earlier_borrows() {
    let source = "type Owner struct {tag: usize} impl Drop for Owner {fn drop(self){}} fn read_then_consume(r: &usize, owner: Owner) -> usize {*r} fn main() -> usize {let owner = Owner {tag: 42}; read_then_consume(&owner.tag, owner)}";
    assert!(verify(source).is_err());
}

#[test]
fn expanding_value_copies_are_rejected_before_unbounded_materialization() {
    let mut arrays = "fn main() -> usize {let a0: [usize; 1] = [1];".to_owned();
    for i in 1..40 {
        arrays.push_str(&format!("let a{i} = [a{}, a{}];", i - 1, i - 1));
    }
    arrays.push_str("42}");
    let error = verify(&arrays).unwrap_err();
    assert!(error.contains("symbolic value"), "{error}");
    let mut formulas = "fn f(flag: bool) -> usize {let p0 = flag;".to_owned();
    for i in 1..40 {
        formulas.push_str(&format!("let p{i} = p{} && !p{};", i - 1, i - 1));
    }
    formulas.push_str("42}");
    let error = match verify(&formulas) {
        Err(error) => error,
        Ok(_) => panic!("expanded formulas must hit a checked work limit"),
    };
    assert!(error.contains("symbolic value"), "{error}");
    let mut snapshots = format!(
        "fn main() -> usize {{let a: [usize; 256] = [{}]; let r = &a;",
        vec!["1"; 256].join(",")
    );
    for _ in 0..512 {
        snapshots.push_str("if true {()} else {()};");
    }
    snapshots.push_str("42}");
    let error = match verify(&snapshots) {
        Err(error) => error,
        Ok(_) => panic!("branch snapshots must be charged"),
    };
    assert!(error.contains("work limit"), "{error}");
    let ordinary = "fn main() -> usize {let a: [usize; 2] = [7, 42]; let b = [a, a]; let c = [b, b]; c[1][0][1]}";
    assert_eq!(verify(ordinary).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn compact_type_graphs_and_fact_chains_have_checked_work_limits() {
    let mut source = "type Node0 struct {value: usize}\n".to_owned();
    for i in 1..20 {
        source.push_str(&format!(
            "type Node{i} struct {{left: Node{}, right: Node{}}}\n",
            i - 1,
            i - 1
        ));
    }
    source.push_str("fn main() -> usize {42}");
    assert!(verify(&source)
        .unwrap_err()
        .contains("type expansion limit"));
    let mut source = "fn main() -> usize {fact f0 = true;".to_owned();
    for i in 1..150 {
        source.push_str(&format!("fact f{i} = f{};", i - 1));
    }
    source.push_str("42}");
    assert!(verify(&source)
        .unwrap_err()
        .contains("verification evaluation limit"));
    assert!(verify("type Pair struct {left: usize, right: usize} fn main() -> usize {let p = Pair {left: 7, right: 42}; p.right}").is_ok());
}

#[test]
fn borrowed_temporaries_keep_their_drop_receiver_valid_until_scope_exit() {
    let declarations = "type Owner struct {tag: usize} where (tag == 7); impl Drop for Owner {fn drop(self){}} type Holder struct {reference: &usize, tag: usize} where (fact live = *reference == 7; live); impl Drop for Holder {fn drop(self){proof receiver_valid: self::live;}} fn consume(owner: Owner) -> usize ensures (result == 0) {0}";
    let bad = "fn main() -> usize {let owner = Owner {tag: 7}; let value = Holder {reference: &owner.tag, tag: 42}.tag + consume(owner); value}";
    assert!(verify(&format!("{declarations}\n{bad}"))
        .unwrap_err()
        .contains("implicit temporary cleanup"));
    let good = "fn main() -> usize ensures (result == 42) {let owner = Owner {tag: 7}; let value = Holder {reference: &owner.tag, tag: 42}.tag; drop(owner); value}";
    let (value, events) = verify(&format!("{declarations}\n{good}"))
        .unwrap()
        .run_with_events()
        .unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Holder", "drop Owner"]);
}

#[test]
fn array_read_facts_survive_contracts_and_branch_scope_changes() {
    let source = include_str!("../../../examples/array_contracts.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("{data}", "{[data[1], data[0]]}")).is_err());
    let branch = "fn select(data: [usize; 2], index: usize, flag: bool) -> usize where (index < 2) ensures (result == data[index]) {if flag {data[index]} else {data[index]}}";
    assert!(verify(branch).is_ok());
    let record = "type Positive struct {value: usize} where (value > 0); impl Copy for Positive {} fn select(data: [Positive; 1], flag: bool) -> Positive ensures (result.value == data[0].value) {if flag {data[0]} else {data[0]}} fn main() -> usize ensures (result == 42) {let input: [Positive; 1] = [Positive {value: 42}]; let answer = select(input, false); answer.value}";
    assert_eq!(verify(record).unwrap().run().unwrap().to_string(), "42");
    let nested = "fn read(data: [[usize; 2]; 1]) -> usize ensures (result == data[0][1]) {data[0][1]} fn main() -> usize ensures (result == 42) {let data: [[usize; 2]; 1] = [[7, 42]]; read(data)}";
    assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
    let false_fact = "type Item struct {value: usize} where (fact lie = 1 == 2; true); fn bad(data: [Item; 1]) -> usize ensures (result == 1) {let first = data[0]; let second = data[0]; 0}";
    assert!(verify(false_fact).is_err());
    let branch_fact = "fn bad(data: [usize; 1]) -> usize ensures (result == 0) {if data[0] == 0 {data[0]} else {data[0]}}";
    assert!(verify(branch_fact).is_err());
    let literal = "fn first(n: usize, data: [u8; n]) -> u8 where (n > 0) ensures (result == data[0]) {data[0]} fn main() -> u8 ensures (result == 7) {let n: usize = 1; first(2, [7, 42])}";
    assert_eq!(verify(literal).unwrap().run().unwrap().to_string(), "7");
    assert!(verify(&literal.replace("first(2, [7, 42])", "first(2, [7])")).is_err());
    assert!(verify(&literal.replace("first(2, [7, 42])", "first(2, [256, 42])")).is_err());
}

#[test]
fn field_assignment_cannot_resurrect_siblings_consumed_by_its_rhs() {
    let declarations = "type Left struct {} impl Drop for Left {fn drop(self){}} type Right struct {} impl Drop for Right {fn drop(self){}} type Pair struct {left: Left, right: Right} fn take(pair: Pair) -> Left {let Pair {left, right} = pair; left}";
    let bad = "fn main() -> usize {let pair = Pair {left: Left {}, right: Right {}}; pair.left = take(pair); 0}";
    assert!(verify(&format!("{declarations}\n{bad}"))
        .unwrap_err()
        .contains("field assignment cannot restore shape"));
    let good = "fn main() -> usize {let pair = Pair {left: Left {}, right: Right {}}; pair = Pair {left: take(pair), right: Right {}}; 0}";
    let (_, events) = verify(&format!("{declarations}\n{good}"))
        .unwrap()
        .run_with_events()
        .unwrap();
    assert_eq!(events, ["drop Right", "drop Left", "drop Right"]);
    let explicit_move = "type Plain struct {left: usize, right: usize} fn take(p: Plain) -> usize {p.left} fn main() -> usize {let p = Plain {left: 1, right: 2}; p.left = take(move(p)); p.left}";
    assert!(verify(explicit_move).is_err());
}

#[test]
fn ideal_parameters_are_checked_and_erased_without_runtime_access() {
    let source = include_str!("../../../examples/ideal_parameters.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("countdown(5, 5)", "countdown(5, 6)")).is_err());
    assert!(verify(&source.replace(
        "checked_value(42, expected_answer())",
        "checked_value(41, expected_answer())"
    ))
    .is_err());
    for body in [
        "n",
        "let x = n; x",
        "let r = &n; *r",
        "n = 1; 0",
        "if n > 0 {1} else {0}",
        "move(n)",
    ] {
        assert!(
            verify(&format!("fn bad(ideal n: usize) -> usize {{{body}}}")).is_err(),
            "{body}"
        );
    }
    let interleaved = "fn sum(ideal a: nat, x: usize, ideal b: nat, y: usize) -> usize where (x <= 10 && y <= 10 && a == nat(x) && b == nat(y)) ensures (nat(result) == a + b) {x + y} fn main() -> usize ensures (result == 3) {sum(1, 1, 2, 2)}";
    assert_eq!(verify(interleaved).unwrap().run().unwrap().to_string(), "3");
    let only_ideal = "fn answer(ideal expected: nat) -> usize where (expected == 42) ensures (nat(result) == expected) {42} fn main() -> usize {answer(42)}";
    assert_eq!(verify(only_ideal).unwrap().run().unwrap().to_string(), "42");
    let move_only = "ideal type Ticket struct {tag: nat} fn bad(ideal t: Ticket) -> usize {0}";
    assert!(verify(move_only).is_ok());
    let effect = "fn write(r: &usize) -> usize modifies(r) ensures (result == 1) {*r = 1; 1} fn metadata(ideal n: nat) -> usize {0} fn main() -> usize {let x: usize = 0; metadata(nat(write(&x)))}";
    assert!(verify(effect).unwrap_err().contains("modifying calls"));
    let declarations = source.split("fn main()").next().unwrap();
    let update = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn main() -> usize ensures (result == 42) {let p = Pair {left: 0, right: 0}; update(p) lifts balanced {p.left = checked_value(42, expected_answer()); p.right = p.left;} p.right}";
    assert_eq!(
        verify(&format!("{declarations}\n{update}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
}

#[test]
fn evergreen_counter_library_checks_boundaries_and_refines_rc_counts() {
    let library = include_str!("../../../stdlib/counter.evg");
    for initial in [0u64, 1, u64::MAX - 1, u64::MAX] {
        let expected = initial.saturating_add(1);
        let success = initial < u64::MAX;
        let source = format!("{library}\nfn main() -> usize ensures (result == {expected}) {{let count: usize = {initial}; let success = counter_try_increment(&count); proof flag: success == {success}; count}}");
        assert_eq!(
            verify(&source).unwrap().run().unwrap().to_string(),
            expected.to_string()
        );
        if initial > 0 {
            let expected = initial - 1;
            let zero = expected == 0;
            let source = format!("{library}\nfn main() -> usize ensures (result == {expected}) {{let count: usize = {initial}; let zero = counter_decrement(&count); proof flag: zero == {zero}; count}}");
            assert_eq!(
                verify(&source).unwrap().run().unwrap().to_string(),
                expected.to_string()
            );
        }
    }
    for bad in [
        include_str!("../../../examples/reject_counter_underflow.evg"),
        include_str!("../../../examples/reject_counter_overflow.evg"),
    ] {
        assert!(verify(&format!("{library}\n{bad}")).is_err());
    }
    let source = [
        include_str!("../../../proofs/rc_protocol.evg"),
        library,
        include_str!("../../../proofs/rc_count_refinement.evg"),
    ]
    .join("\n");
    assert!(verify(&source).is_ok());
    let executed = format!(
        "{source}\n{}",
        include_str!("../../../examples/rc_count.evg")
    );
    let program = verify(&executed).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(program.run().unwrap().to_string(), "0");
    let alternative = source.replace(
        "let success = counter_increment(count);",
        "let success = counter_try_increment(count);",
    );
    assert!(verify(&alternative).is_ok());
    let broken = source.replace("*count = *count - 1;", "*count = *count;");
    assert!(verify(&broken).is_err());
}

#[test]
fn symbolic_array_reads_are_versioned_after_writes() {
    let prefix = "fn increment(r: &usize) where (*r < usize::MAX) modifies(r) ensures (*r == old(*r) + 1) {*r = *r + 1;}";
    for mutation in [
        "let r = &a[0]; *r = 1;",
        "increment(&a[0]);",
        "let x = if true {increment(&a[0])} else {()};",
    ] {
        let source = format!("{prefix} fn unchanged(i: usize) -> bool where (i < 1) ensures (result) {{let a: [usize; 1] = [0]; let before = a[i]; {mutation} a[i] == before}}");
        assert!(
            verify(&source).is_err(),
            "stale array read survived {mutation}"
        );
    }
    let unchanged = "fn unchanged(i: usize) -> bool where (i < 1) ensures (result) {let a: [usize; 1] = [0]; let before = a[i]; a[i] == before}";
    assert!(verify(unchanged).is_ok());
    let copy = "fn unchanged(i: usize) -> bool where (i < 1) ensures (result) {let a: [usize; 1] = [0]; let snapshot = a; let before = snapshot[i]; let r = &a[0]; *r = 1; snapshot[i] == before}";
    assert!(verify(copy).is_ok());
    let alias = "fn bad(i: usize) -> bool where (i < 1) ensures (result) {let n: usize = 0; let a: [&usize; 1] = [&n]; let before = *a[i]; n = 1; *a[i] == before}";
    assert!(verify(alias).unwrap_err().contains("alias contract"));
    let concrete = "fn main() -> usize ensures (result == 1) {let n: usize = 0; let a: [&usize; 1] = [&n]; n = 1; *a[0]}";
    assert_eq!(verify(concrete).unwrap().run().unwrap().to_string(), "1");
}

#[test]
fn conditional_stores_join_effects_without_leaking_branch_assumptions() {
    let source = include_str!("../../../examples/conditional_writes.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace(
        "maybe_increment(alias, false)",
        "maybe_increment(alias, true)"
    ))
    .is_err());
    assert!(
        verify(&source.replace("*alias + counters.right", "*alias + counters.right + 1")).is_err()
    );
    let declarations = source.split("type Counters").next().unwrap();
    let invalid = "fn bad(r: &usize, flag: bool) where (*r < usize::MAX) modifies(r) ensures (*r == old(*r) + 1) {if flag {increment(r)} else {()}}";
    assert!(verify(&format!("{declarations}\n{invalid}")).is_err());
    let array = "fn main() -> usize ensures (result == 41) {let a: [usize; 2] = [40, 7]; let alias = &a[0]; let x = if false {()} else {increment(alias)}; proof frame: a[1] == 7; *alias}";
    assert_eq!(
        verify(&format!("{declarations}\n{array}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "41"
    );
    let nested = "fn main() -> usize ensures (result == 2) {let n: usize = 0; let x = if true {if false {()} else {increment(&n)}} else {()}; increment(&n); n}";
    assert_eq!(
        verify(&format!("{declarations}\n{nested}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "2"
    );
}

#[test]
fn branches_must_agree_on_consumed_ownership() {
    let declarations = "type Token struct {tag: usize} fn consume(t: Token) -> usize ensures (result == t.tag) {t.tag}";
    let valid = "fn main() -> usize ensures (result == 7) {let t = Token {tag: 7}; if true {consume(t)} else {consume(t)}}";
    assert_eq!(
        verify(&format!("{declarations}\n{valid}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "7"
    );
    let invalid =
        "fn main() -> usize {let t = Token {tag: 7}; let x = if true {consume(t)} else {0}; t.tag}";
    assert!(verify(&format!("{declarations}\n{invalid}")).is_err());
    let invalid = valid.replace(
        "if true {consume(t)} else {consume(t)}",
        "let x = if true {consume(t)} else {consume(t)}; t.tag",
    );
    assert!(verify(&format!("{declarations}\n{invalid}")).is_err());
}

#[test]
fn ideal_bindings_are_erased_and_keep_move_only_ownership() {
    let source = include_str!("../../../examples/ideal_bindings.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    for body in [
        "ideal let n: usize = 42; n",
        "ideal let n: usize = 1; if n == 1 {42} else {0}",
        "ideal let n: usize = 1; let r = &n; *r",
        "ideal let n: usize = 1; n = 2; 42",
        "ideal let n = false; proof unsound: n; 42",
        "ideal let n: usize = usize::MAX + 1; 42",
    ] {
        assert!(
            verify(&format!("fn main() -> usize {{{body}}}")).is_err(),
            "{body}"
        );
    }
    let library = concat!(
        include_str!("../../../stdlib/credits/credits.evg"),
        "\u{1e}"
    );
    let client = include_str!("../../../proofs/ideal_credit_bindings.evg");
    assert!(verify(&format!("{library} {client}")).is_ok());
    assert!(verify(&format!(
        "{library} {}",
        client.replace("spend_credit(right, value)", "spend_credit(left, value)")
    ))
    .is_err());
    assert!(verify(&format!(
        "{library} {}",
        client.replace(
            "ideal let credits::Split {left, right} = parts;",
            "let credits::Split {left, right} = parts;"
        )
    ))
    .is_err());
    let bad =
        "fn steal(ideal c: credits::Credit) -> usize {ideal let credits::Credit {units} = c; 42}";
    assert!(verify(&format!("{library} {bad}")).is_err());
    let observer = "type Resource struct {tag: usize} where(tag == 42); impl Drop for Resource {fn drop(self){}} ideal fn observe(r: &Resource) -> nat ensures(result == nat((*r).tag)) {nat((*r).tag)} fn main() -> usize {let r = Resource {tag: 42}; ideal let saved = observe(&r); proof correct: saved == 42; r.tag}";
    let (value, events) = verify(observer).unwrap().run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
    assert!(verify(&observer.replace("observe(&r)", "drop(r)")).is_err());
}

#[test]
fn erased_move_only_resources_move_without_runtime_values_or_effects() {
    let source = include_str!("../../../examples/erased_resources.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let declarations = source.split("fn main").next().unwrap();
    for bad in [
        "fn duplicate(ideal t: tickets::Ticket) -> usize {let a = consume(t, 0); consume(t, 42)}",
        "fn restore(ideal t: tickets::Ticket) -> usize {let a = consume(t, 0); consume(old(t), 42)}",
        "fn leak(ideal t: tickets::Ticket) -> usize {t}",
        "fn branch(ideal t: tickets::Ticket) -> usize {if t.tag == 1 {42} else {0}}",
    ] {assert!(verify(&format!("{declarations} {bad}")).is_err(), "{bad}");}
    let proof_view = "ideal fn inspect(t: tickets::Ticket) -> nat {1} fn caller(ideal t: tickets::Ticket) -> usize {proof stable: inspect(t) == inspect(t); consume(t, 42)}";
    // A missing postcondition cannot prove equality of arbitrary summaries.
    assert!(verify(&format!("{declarations} {proof_view}")).is_err());
    let proof_view = proof_view.replace("-> nat {1}", "-> nat ensures(result == 1) {1}");
    assert!(verify(&format!("{declarations} {proof_view}")).is_ok());
    let old_scalar = "fn answer(ideal expected: nat) -> usize where(expected == 42) ensures(result == 42) {42} fn caller(n: usize) -> usize where(n == 42) ensures(result == 42) {n = 0; answer(nat(old(n)))} fn main() -> usize {caller(42)}";
    assert_eq!(verify(old_scalar).unwrap().run().unwrap().to_string(), "42");
    let library = concat!(
        include_str!("../../../stdlib/credits/credits.evg"),
        "\u{1e}"
    );
    let bridge = "fn spend(ideal credit: credits::Credit, value: usize) -> usize ensures(result == value) {value} fn forward(ideal credit: credits::Credit, value: usize) -> usize ensures(result == value) {spend(credit, value)}";
    assert!(verify(&format!("{library} {bridge}")).is_ok());
    let borrow =
        "ideal type WithRef struct {r: &usize} fn ignore(ideal resource: WithRef) -> usize {0}";
    assert!(verify(borrow).is_ok());
    let resource = "type Resource struct {} impl Drop for Resource {fn drop(self){}}";
    for bad in [
        "ideal fn consume_resource(resource: Resource) -> nat {1}",
        "ideal fn make_resource() -> Resource {Resource {}}",
        "ideal fn make_hidden() -> nat {let r = Resource {}; 1}",
        "fn metadata(ideal u: ()) -> usize {0} fn main() -> usize {let r = Resource {}; metadata(drop(r))}",
        "fn metadata(ideal n: usize) -> usize {0} fn main() -> usize {let n: usize = 42; metadata(move(n))}",
    ] {assert!(verify(&format!("{resource} {bad}")).is_err(), "{bad}");}
}

#[test]
fn opaque_module_representations_are_checked_without_client_privileges() {
    let source = include_str!("../../../examples/opaque_values.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let declarations = source.split("fn main").next().unwrap();
    for body in [
        "let p = permits::Permit {tag: 42}; 42",
        "let p = permits::issue(); p.tag",
        "let p = permits::issue(); p.tag = 42; 42",
        "let p = permits::issue(); let r = &p.tag; *r",
        "let p = permits::issue(); let permits::Permit {tag} = p; tag",
        "let p = permits::issue(); let x = permits::read(&p); p.tag",
        "let p = permits::issue(); proof hidden: p.tag == 42; 42",
    ] {
        let error = verify(&format!("{declarations} fn main() -> usize {{{body}}}")).unwrap_err();
        assert!(error.contains("opaque representation"), "{error}: {body}");
    }
    assert!(verify(&format!(
        "{declarations} module permits {{fn forge() -> Permit {{Permit {{tag: 42}}}}}}"
    ))
    .is_err());
    assert!(verify(&format!("{declarations} module other {{fn forge() -> permits::Permit {{permits::Permit {{tag: 42}}}}}}" )).is_err());
    assert!(verify(&format!(
        "{declarations} impl Drop for permits::Permit {{fn drop(self){{}}}}"
    ))
    .unwrap_err()
    .contains("defining module"));
    let self_fact = source.replace("tag == 42", "self.tag == 42");
    assert_eq!(verify(&self_fact).unwrap().run().unwrap().to_string(), "42");
    let wrap = "type Wrapper struct {p: permits::Permit} where (p::valid); fn main() -> usize {let wrapper = Wrapper {p: permits::issue()}; permits::read(&wrapper.p)}";
    assert_eq!(
        verify(&format!("{declarations} {wrap}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
    assert!(verify(&format!(
        "{declarations} {}",
        wrap.replace("p::valid", "p.tag == 42")
    ))
    .is_err());
}

#[test]
fn opaque_move_only_credits_can_be_rearranged_but_not_forged_or_duplicated() {
    let library = concat!(
        include_str!("../../../stdlib/credits/credits.evg"),
        "\u{1e}"
    );
    assert!(verify(&format!(
        "{library} {}",
        include_str!("../../../proofs/opaque_credits.evg")
    ))
    .is_ok());
    for client in [
        "ideal fn forge() -> credits::Credit {credits::Credit {units: 7}}",
        "ideal fn steal(c: credits::Credit) -> nat {c.units}",
        "ideal fn duplicate(c: credits::Credit) -> credits::Split {credits::Split {left: c, right: c}}",
        "ideal fn extract(c: credits::Credit) -> nat {let credits::Credit {units} = c; units}",
        "ideal fn forge(c: credits::Credit) -> credits::Credit {credits::join(credits::Credit {units: 7}, c)}",
        "ideal fn mint(c: credits::Credit) -> credits::Credit {c.units = 7; c}",
        "ideal fn copy(c: &credits::Credit) -> credits::Credit {*c}",
    ] {assert!(verify(&format!("{library} {client}")).is_err(), "{client}");}
}

#[test]
fn dynamic_array_projections_preserve_aliasing_and_prove_disjointness() {
    let source = include_str!("../../../examples/indexed_borrows.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert_eq!(
        verify(
            &source
                .replace("may_alias(data, 1, 1)", "may_alias(data, 0, 1)")
                .replace(
                    "ensures (result == 42) {\n    let data",
                    "ensures (result == 1) {\n    let data"
                )
        )
        .unwrap()
        .run()
        .unwrap()
        .to_string(),
        "1"
    );
    let definitions = source.split("fn may_alias").next().unwrap();
    let equal_reads = "fn same(data: [usize; 2], i: usize, j: usize) -> usize where (i < 2 && j < 2 && i == j) ensures(result == 0) {data[i] - data[j]}";
    assert!(verify(equal_reads).is_ok());
    let fake = "fn bad(data: [usize; 2], i: usize, j: usize) -> usize where (i < 2 && j < 2) ensures(result == 42) {let a = &data[i]; let b = &data[j]; set_42(a); *b}";
    assert!(verify(&format!("{definitions} {fake}")).is_err());
    let fake = "fn bad(data: [usize; 2], i: usize) -> usize where(i < 2) ensures(result == data[i]) {let r = &data[i]; set_42(r); *r}";
    assert!(verify(&format!("{definitions} {fake}")).is_err());
    let contract = "fn same(data: &[usize; 2], i: usize, j: usize) -> &usize where(i < 2 && j < 2 && i == j) borrows(&(*data)[i]) {&(*data)[j]}";
    assert!(verify(contract).is_ok());
    assert!(verify(&contract.replace(" && i == j", "")).is_err());
    let snapshot = "fn snapshot(data: [usize; 2], i: usize) -> usize where(i == 0) ensures(result == 42) {let r = &data[i]; i = 1; set_42(r); data[0]} fn main() -> usize {let data: [usize; 2] = [7, 1]; snapshot(data, 0)}";
    assert_eq!(
        verify(&format!("{definitions} {snapshot}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
    let swap = include_str!("../../../stdlib/swap.evg");
    let wrapper = "fn dynamic_swap(data: [usize; 2], i: usize, j: usize) -> usize where(i < 2 && j < 2 && i != j) ensures(result == data[j]) {swap_usize(&data[i], &data[j]); data[i]} fn main() -> usize ensures(result == 42) {dynamic_swap([7, 42], 0, 1)}";
    assert_eq!(
        verify(&format!("{swap} {wrapper}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
    assert_eq!(
        verify(&format!("{swap} {}", wrapper.replace(" && i != j", "")))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
    let no_bound =
        "fn bad(data: &[usize; 2], i: usize) -> &usize borrows(&(*data)[i]) {&(*data)[i]}";
    assert!(verify(no_bound).is_err());
    let signed = "fn bad(data: &[usize; 2], i: isize) -> &usize where(i < 2) borrows(&(*data)[i]) {&(*data)[i]}";
    assert!(verify(signed).is_err());
}

#[test]
fn implication_and_unlifted_weaker_invariants_check_each_store() {
    let source = include_str!("../../../examples/weak_invariant.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let bad = source.replace("ledger.count = 42;", "ledger.count = 0;");
    assert!(verify(&bad).is_err());
    let bad = source.replace(
        "ledger::reference_count_is_0_implies_no_owners;",
        "ledger::reference_count_is_accurate;",
    );
    assert!(verify(&bad).is_err());
    let release = "fn release() -> usize {let ledger = Ledger {count: 1, owners: 1}; update(ledger) lifts reference_count_is_accurate {ledger.owners = 0; proof still_safe: ledger::reference_count_is_0_implies_no_owners; ledger.count = 0;} ledger.count}";
    assert!(verify(&format!(
        "{} {release}",
        source.split("fn main").next().unwrap()
    ))
    .is_ok());
    for a in [false, true] {
        for b in [false, true] {
            let program = verify(&format!(
                "fn main() -> bool ensures(result == {}) {{{a} => {b}}}",
                !a || b
            ))
            .unwrap();
            assert_eq!(program.run().unwrap().to_string(), (!a || b).to_string());
        }
    }
    // Implication binds below || and associates to the right.
    assert_eq!(
        verify("fn main() -> bool ensures(result == true) {false => true => false}")
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "true"
    );
    assert!(verify("fn bad() -> bool ensures(result == true) {true => false}").is_err());
    assert!(verify("fn bad() -> bool {1 => true}").is_err());
}

#[test]
fn opaque_array_borrows_share_cells_bounds_and_branch_state() {
    let source = include_str!("../../../examples/array_borrows.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let declarations = source.split("fn main").next().unwrap();
    let branch = "fn choose(data: &[usize; 2], flag: bool) -> usize ensures(result == (*data)[0]) {if flag {*first(2, data)} else {(*data)[0]}} fn main() -> usize ensures(result == 42) {let data: [usize; 2] = [42, 7]; choose(&data, true)}";
    assert_eq!(
        verify(&format!("{declarations} {branch}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
    for bad in [
        source.replace("where (n > 0)", ""),
        source.replace("    *right\n}", "    drop(data);\n    *right\n}"),
        source.replace("first(2, &data)", "first(0, &data)"),
    ] {
        assert!(verify(&bad).is_err());
    }
    let frame = "fn set(r: &usize) modifies(r) ensures(*r == 42) {*r = 42;} fn change(data: [usize; 2], flag: bool) -> usize ensures(result == data[1]) {let r = &data[0]; let before = data[1]; let x = if flag {set(r)} else {()}; data[1]} fn main() -> usize ensures(result == 42) {change([7, 42], true)}";
    assert_eq!(verify(frame).unwrap().run().unwrap().to_string(), "42");
    let bad = "fn local(data: [usize; 1]) -> &usize borrows(&data[0]) {&data[0]}";
    assert!(verify(bad).is_err());
    let fake = "fn bad(data: &[usize; 2]) -> usize ensures(result == 0) {if *first(2, data) == 0 {*first(2, data)} else {*first(2, data)}}";
    assert!(verify(&format!("{declarations} {fake}")).is_err());
}

#[test]
fn projected_effects_frame_siblings_and_preserve_array_views() {
    let helper = "fn set(data: &[usize; 2], i: usize) where(i < 2) modifies(&(*data)[i]) ensures((*data)[i] == 42) {(*data)[i] = 42;}";
    let source = format!("{helper} fn main() -> usize ensures(result == 49) {{let a: [usize; 2] = [1, 7]; set(&a, 0); a[0] + a[1]}}");
    assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "49");
    let bad = helper.replace("(*data)[i] = 42", "(*data)[1] = 42");
    assert!(verify(&bad).is_err());
    let source = "fn read(i: usize) -> usize where(i < 2) ensures(result == 42) {let a: [usize; 2] = [1, 7]; let r = &a[i]; a = [42, 42]; *r} fn main() -> usize {read(1)}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn scalar_array_regions_preserve_aliases_and_replay_without_search() {
    let library = concat!(include_str!("../../../stdlib/arrays/array.evg"), "\u{1e}");
    let source = format!(
        "{library} {}",
        include_str!("../../../examples/array_updates.evg")
    );
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    let replayed = verify_with_certificate(&source, &bundle).unwrap();
    assert_eq!(replayed.proof_search_count(), 0);
    assert_eq!(replayed.run().unwrap().to_string(), "42");

    // Both a constant cell and a symbolic cell retain their storage paths
    // when the call summary replaces known contents with an opaque array.
    let caller = "fn check(i: usize) -> usize where(i < 2) ensures(result == 42) {let a: [usize; 2] = [7, 9]; let constant = &a[0]; let dynamic = &a[i]; arrays::replace_pair(&a, 42, 42); proof constant_live: *constant == 42; *dynamic} fn main() -> usize {check(1)}";
    assert_eq!(
        verify(&format!("{library} {caller}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
    let nested = "fn read(i: usize) -> usize where(i < 2) ensures(result == 42) {let a: [[usize; 2]; 1] = [[7, 9]]; let r = &a[0][i]; a = [[42, 42]]; *r} fn main() -> usize {read(1)}";
    assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
    let sibling = "type WithTag struct {data: [usize; 2], tag: usize} fn read(i: usize) -> usize where(i < 2) ensures(result == 42) {let p = WithTag {data: [42, 42], tag: 7}; let r = &p.data[i]; p.tag = 9; *r} fn main() -> usize {read(1)}";
    assert_eq!(verify(sibling).unwrap().run().unwrap().to_string(), "42");
    let caller = "type WithTag struct {data: [usize; 2], tag: usize} fn main() -> usize ensures(result == 42) {let p = WithTag {data: [7, 9], tag: 42}; arrays::replace_pair(&p.data, 1, 2); p.tag}";
    assert_eq!(
        verify(&format!("{library} {caller}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
}

#[test]
fn array_effects_do_not_gain_permissions_or_keep_old_contents() {
    let library = concat!(include_str!("../../../stdlib/arrays/array.evg"), "\u{1e}");
    for caller in [
        // A projected grant cannot authorize an entire-array write.
        "fn bad(a: &[usize; 2]) modifies(&(*a)[0]) {arrays::replace_pair(a, 1, 2);}",
        // Writes follow entry indices even if the index variable is rebound.
        "fn bad(a: &[usize; 2], i: usize) where(i == 0) modifies(&(*a)[i]) {i = 1; (*a)[i] = 42;}",
        // Broad regions forget all contents outside the checked postcondition.
        "fn change(a: &[usize; 2]) modifies(a) {(*a)[1] = 9;} fn main() -> usize ensures(result == 42) {let a: [usize; 2] = [42, 7]; change(&a); a[0]}",
        // Rechecking aliases cannot justify a false unchanged-cell claim.
        "fn change(a: &[usize; 2], r: &usize) modifies(a) ensures(*r == old(*r)) {(*a)[0] = 0;} fn main() {let a: [usize; 2] = [42, 7]; change(&a, &a[0]);}",
        // A whole-array grant does not authorize writes to another parameter.
        "fn bad(a: &[usize; 2], b: &usize) modifies(a) {*b = 42;}",
        // Reference-containing elements require separate ownership semantics.
        "fn bad(a: &[&usize; 2]) modifies(a) {}",
    ] {
        assert!(verify(&format!("{library} {caller}")).is_err(), "accepted {caller}");
    }
}

#[test]
fn reference_field_effects_and_borrows_replay_and_preserve_origin_paths() {
    let source = include_str!("../../../examples/reference_fields.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    let replayed = verify_with_certificate(source, &bundle).unwrap();
    assert_eq!(replayed.proof_search_count(), 0);
    assert_eq!(replayed.run().unwrap().to_string(), "42");
    let declarations = source.split("fn main").next().unwrap();
    let slot = "type Container struct {pointer: &usize, value: usize} fn main() -> usize ensures(result == 42) {let backing: usize = 1; let c = Container {pointer: &backing, value: 41}; c.pointer = &c.value; increment_indirect(&c.pointer); c.value}";
    assert_eq!(
        verify(&format!("{declarations} {slot}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
    let array = "type BufferView struct {data: &[usize; 3]} fn set(view: BufferView, index: usize) -> &usize where(index < 2) modifies(&(*view.data)[index]) borrows(&(*view.data)[index]) ensures(*result == 42) {(*view.data)[index] = 42; &(*view.data)[index]} fn main() -> usize ensures(result == 42) {let data: [usize; 3] = [7, 9, 42]; let untouched = &data[2]; let changed = set(BufferView {data: &data}, 1); proof frame: *untouched == 42; *changed}";
    assert_eq!(verify(array).unwrap().run().unwrap().to_string(), "42");
    let aliases = "type Two struct {left: &usize, right: &usize} fn first(view: Two) -> &usize borrows(view.left) {view.left} fn main() -> usize {let n: usize = 42; *first(Two {left: &n, right: &n})}";
    assert_eq!(verify(aliases).unwrap().run().unwrap().to_string(), "42");
    let normalized = "type View struct {count: &usize} fn set(view: View) modifies(view.count, *(&view.count)) ensures(*view.count == 42) {*view.count = 42;} fn main() -> usize {let n: usize = 0; set(View {count: &n}); n}";
    assert_eq!(verify(normalized).unwrap().run().unwrap().to_string(), "42");
    let private = "module counters {opaque type View struct {count: &usize} fn add(view: View) -> &usize where(*view.count < usize::MAX) modifies(view.count) borrows(view.count) ensures(*result == old(*view.count) + 1) {*view.count = *view.count + 1; view.count} fn bump(count: &usize) -> &usize where(*count < usize::MAX) modifies(count) borrows(count) ensures(*result == old(*count) + 1) {add(View {count: count})}} fn main() -> usize {let n: usize = 41; *counters::bump(&n)}";
    assert_eq!(verify(private).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn reference_field_calls_reject_hidden_aliases_between_independent_views() {
    let pair = "type Two struct {left: &usize, right: &usize} fn set(view: Two) modifies(view.left) ensures(*view.left == 42 && *view.right == old(*view.right)) {*view.left = 42;}";
    let both = "type Two struct {left: &usize, right: &usize} fn set(view: Two) modifies(view.left, view.right) ensures(*view.left == 1 && *view.right == 2) {*view.left = 1; *view.right = 2;}";
    for library in [pair, both] {
        let source = format!("{library} fn main() -> usize {{let n: usize = 7; set(Two {{left: &n, right: &n}}); n}}");
        assert!(verify(&source).unwrap_err().contains("overlaps"));
    }
    let container = "type Container struct {pointer: &usize, value: usize} fn set(c: &Container) modifies((*c).pointer) ensures(*(*c).pointer == 42 && (*c).value == old((*c).value)) {*(*c).pointer = 42;} fn main() -> usize {let backing: usize = 1; let c = Container {pointer: &backing, value: 7}; c.pointer = &c.value; set(&c); c.value}";
    assert!(verify(container).unwrap_err().contains("overlaps"));
    let source = "type View struct {count: &usize} fn set(view: View, other: &usize) modifies(view.count) {*view.count = 42;} fn main() {let n: usize = 7; set(View {count: &n}, &n);}";
    assert!(verify(source).is_ok());
    let source = "type View struct {count: &usize} fn set(view: View) modifies(view.count) {*view.count = 42;} fn missing(view: View) {set(view);}";
    assert!(verify(source)
        .unwrap_err()
        .contains("matching modifies contract"));
}

#[test]
fn modified_input_views_preserve_types_even_after_parameter_rebinding() {
    let guard = "type Guard struct {count: &usize} where(*count > 0); fn zero(count: &usize) modifies(count) ensures(*count == 0) {*count = 0;}";
    for body in [
        "*(*view).count = 0;",
        "zero((*view).count);",
        "let target = (*view).count; let safe: usize = 7; let replacement = Guard {count: &safe}; view = &replacement; zero(target);",
    ] {
        let source = format!("{guard} fn bad(view: &Guard) modifies((*view).count) {{{body}}}");
        assert!(verify(&source).is_err(), "accepted {body}");
    }
    // Known pointee types are implicit preservation contracts, even without
    // a numeric postcondition. Caller-only enclosing types are not assumed.
    let preserved = format!("{guard} fn reset(view: &Guard) modifies((*view).count) {{*(*view).count = 1;}} fn wrapper(view: &Guard) modifies((*view).count) ensures(*(*view).count > 0) {{reset(view);}} fn main() -> usize {{let count: usize = 42; let view = Guard {{count: &count}}; wrapper(&view); count}}");
    assert_eq!(verify(&preserved).unwrap().run().unwrap().to_string(), "1");
    let enclosing = "type NonZero struct {value: usize} where(value > 0); fn zero(value: &usize) modifies(value) ensures(*value == 0) {*value = 0;} fn bad(view: &NonZero) modifies(&(*view).value) {zero(&(*view).value);}";
    assert!(verify(enclosing).is_err());
    let unused = "fn zero(value: &usize) modifies(value) ensures(*value == 0) {*value = 0;} fn main() -> usize {let old: usize = 7; let unused = &old; drop(old); let value: usize = 1; zero(&value); value}";
    assert_eq!(verify(unused).unwrap().run().unwrap().to_string(), "0");
    let dangling_array = "fn main() -> usize {let owner: usize = 7; let pointers: [&usize; 1] = [&owner]; drop(owner); 42}";
    assert!(verify(dangling_array).is_err());
    let closed_array = dangling_array.replace("drop(owner);", "drop(pointers); drop(owner);");
    assert_eq!(
        verify(&closed_array).unwrap().run().unwrap().to_string(),
        "42"
    );
}

#[test]
fn multiple_scalar_writes_check_disjoint_or_actual_alias_storage() {
    let library = include_str!("../../../stdlib/swap.evg");
    let source = format!(
        "{library}\n{}",
        include_str!("../../../examples/disjoint_writes.evg")
    );
    assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42");
    for body in [
        "let n: usize = 1; swap_usize(&n, &n); n",
        "let n: usize = 1; let r = &n; swap_usize(&n, r); n",
        "let a: [usize; 2] = [1, 2]; swap_usize(&a[0], &a[0]); a[0]",
    ] {
        assert_eq!(
            verify(&format!("{library} fn main() -> usize {{{body}}}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "1"
        );
    }
    for body in [
        "let a: [usize; 2] = [7, 42]; swap_usize(&a[0], &a[1]); a[0]",
        "let a: usize = usize::MAX; let b: usize = 42; swap_usize(&a, &b); a",
        "let p = Equal {left: 42, right: 42}; swap_usize(&p.left, &p.right); p.right",
    ] {
        let source = format!("{library} type Equal struct {{left: usize, right: usize}} where(left == right); fn main() -> usize ensures(result == 42) {{{body}}}");
        assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42");
    }
    let copy = "fn copy(to: &usize, from: &usize) modifies(to) ensures(*to == old(*from) && *from == old(*from)) {*to = *from;}";
    assert_eq!(
        verify(&format!(
            "{copy} fn main() -> usize {{let n: usize = 42; copy(&n, &n); n}}"
        ))
        .unwrap()
        .run()
        .unwrap()
        .to_string(),
        "42"
    );
    assert!(verify(&format!("{copy} fn main() -> usize ensures(result == 42) {{let a: usize = 0; let b: usize = 42; copy(&a, &b); a}}")).is_ok());
    assert!(verify("fn duplicate(r: &usize) modifies(r, r) ensures(*r == 0) {*r = 0;}").is_ok());
    assert!(verify("fn missing(r: &usize) modifies(no_such_param) {*r = 0;}").is_err());
}

#[test]
fn scalar_write_contracts_update_aliases_and_frame_other_fields() {
    let source = include_str!("../../../examples/write_contracts.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("modifies(r)", "")).is_err());
    assert!(verify(&source.replace("where (*r < usize::MAX)", "")).is_err());
    assert!(verify(&source.replace("old(*r) + 2", "old(*r) + 3")).is_err());
    let declarations = source.split("type Counters").next().unwrap();
    for body in [
        "fn wrapper(r: &usize) {increment(r);}",
        "fn wrapper(r: &usize, other: &usize) modifies(r) {*other = 1;}",
        "fn main() -> usize {let n: usize = 0; proof p: old(n) == 0; n}",
        "fn main() -> usize {let n: usize = 0; proof p: n == 0; increment(&n); proof stale: n == 0 by {exact p}; n}",
        "type Balanced struct {left: usize, right: usize} where (left == right); fn main() -> usize {let p = Balanced {left: 0, right: 0}; increment(&p.left); p.left}",
    ] {
        assert!(verify(&format!("{declarations}\n{body}")).is_err(), "{body}");
    }
    let bounded = "type Bounded struct {value: usize} where (value <= 10); fn main() -> usize ensures (result == 10) {let p = Bounded {value: 9}; increment(&p.value); p.value}";
    assert_eq!(
        verify(&format!("{declarations}\n{bounded}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "10"
    );
    let runtime_old = "fn f(n: usize) -> usize {old(n)}";
    assert!(verify(runtime_old).is_err());
    let proof_effect = "fn main() -> usize {let n: usize = 0; proof p: increment(&n) == 0; n}";
    assert!(verify(&format!("{declarations}\n{proof_effect}")).is_err());
}

#[test]
fn compound_old_snapshots_freeze_entry_storage_and_pointer_targets() {
    let source = include_str!("../../../examples/old_places.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    let replayed = verify_with_certificate(source, &bundle).unwrap();
    assert_eq!(replayed.proof_search_count(), 0);
    assert_eq!(replayed.run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("old((*pair).left) + 1", "old((*pair).left) + 2")).is_err());
    let guarded = "ideal fn observed(data: &[usize; 2], i: usize) -> nat ensures(result == if i < 2 {nat(old((*data)[i]))} else {0}) {if i < 2 {nat(old((*data)[i]))} else {0}} fn main() -> usize {let data: [usize; 2] = [7, 42]; ideal let valid = observed(&data, 1); ideal let outside = observed(&data, usize::MAX); proof values: valid == 42 && outside == 0; 42}";
    assert_eq!(verify(guarded).unwrap().run().unwrap().to_string(), "42");
    let entry = "fn main() -> usize where(old(1 + 1) == 2) {42}";
    assert_eq!(verify(entry).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&entry.replace("== 2", "== 3"))
        .unwrap()
        .run()
        .is_err());
}

#[test]
fn entry_snapshot_work_includes_consumed_plane_slots() {
    let mut source = "fn observe(n: usize) where(n < usize::MAX) ensures(old(n + 1) == n + 1) {} fn main() -> usize {".to_owned();
    for i in 0..640 {
        source.push_str(&format!("let value{i}: usize = 1; drop(value{i});"));
    }
    for _ in 0..448 {
        source.push_str("observe(0);");
    }
    source.push_str("42}");
    let error = verify(&source).unwrap_err();
    assert!(error.contains("symbolic value work limit"), "{error}");
}

#[test]
fn compound_old_snapshots_do_not_capture_locals_effects_or_new_ownership() {
    let ownership = "ideal type Token struct {units: nat} ideal type Bundle struct {token: Token} ideal fn consume(t: Token) -> nat {t.units} fn bad(ideal bundle: Bundle) {ideal let Bundle {token} = bundle; ideal let used = consume(token); ideal let again = consume(old(bundle.token));}";
    assert!(verify(ownership)
        .unwrap_err()
        .contains("old ownership snapshots"));
    for source in [
        "fn bad(n: usize) {let local: usize = 1; proof missing: old(local + n) == 1;}",
        "ideal fn bad(data: &[usize; 2], i: usize) -> nat {nat(old((*data)[i]))}",

        "fn change(r: &usize) -> usize modifies(r) {*r = 0; 0} fn bad(r: &usize) {proof effect: old(change(r)) == 0;}",
        "fn bad(n: usize) -> usize {old(n + 1)}",
        "fn bad(n: usize) where(n == usize::MAX) {proof overflow: old(n + 1) > n;}",

    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn boolean_write_contracts_use_entry_snapshots() {
    let source = "fn flip(r: &bool) -> () modifies(r) ensures (*r == !old(*r)) {*r = !*r;} fn main() -> bool ensures (result == true) {let value = false; flip(&value); value == (1 < 2)}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "true");
    assert!(
        verify(&source.replace("ensures (*r == !old(*r))", "ensures (*r == old(*r))")).is_err()
    );
}

#[test]
fn complete_patterns_transfer_each_field_without_partial_moves() {
    let source = include_str!("../../../examples/destructure.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    for replacement in [
        "Pair {left: first}",
        "Pair {left: first, left: second}",
        "Pair {left: first, right: first}",
        "Pair {unknown: first, right: second}",
        "Permit {left: first, right: second}",
    ] {
        assert!(verify(&source.replace("Pair {left: first, right: second}", replacement)).is_err());
    }
    assert!(verify(&source.replace("let a = consume(first);", "let a = pair.left.tag;")).is_err());
    assert!(
        verify(&source.replace("let b = consume(second);", "let b = consume(first);")).is_err()
    );
    let destructor = "type Guard struct {tag: usize} impl Drop for Guard {fn drop(self) {}} fn main() -> usize {let g = Guard {tag: 7}; let Guard {tag} = g; tag}";
    assert!(verify(destructor).unwrap_err().contains("bypass"));
    let ideal = "ideal type Ticket struct {tag: nat} ideal type Pair struct {left: Ticket, right: Ticket} ideal fn split() -> nat {let pair = Pair {left: Ticket {tag: 2}, right: Ticket {tag: 3}}; let Pair {left, right} = pair; left.tag + right.tag}";
    assert!(verify(ideal).is_ok());
    let credits = include_str!("../../../proofs/move_only_credits.evg");
    assert!(verify(credits).is_ok());
    let duplicate = format!(
        "{credits}\n{}",
        include_str!("../../../proofs/reject_duplicate_credit.evg")
    );
    assert!(verify(&duplicate).unwrap_err().contains("shape(T)"));
}

#[test]
fn move_only_values_move_without_requiring_a_destructor() {
    let source = include_str!("../../../examples/move_values.evg");
    let program = verify(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.drops.is_empty());
    for body in [
        "let p = Permit {tag: 1}; let q = p; p.tag",
        "let p = Permit {tag: 1}; let q = transfer(p); consume(p)",
        "let e = Envelope {permit: Permit {tag: 1}}; let q = e; e.permit.tag",
        "let a = [Permit {tag: 1}]; let b = a; a[0].tag",
        "let p = Permit {tag: 1}; drop(p); p.tag",
    ] {
        let declarations = source.split("fn main()").next().unwrap();
        assert!(
            verify(&format!("{declarations} fn main() -> usize {{{body}}}")).is_err(),
            "{body}"
        );
    }
    let duplicate = "ideal type Ticket struct {tag: nat} ideal fn forward(t: Ticket) -> Ticket {t} ideal fn duplicate() -> nat {let t = Ticket {tag: 7}; let u = forward(t); let v = forward(t); 0}";
    assert!(verify(duplicate).is_err());
    assert!(verify("affine fn main() -> usize {0}").is_err());
    assert!(verify("ideal affine fn main() -> nat {0}").is_err());
}

#[test]
fn conditional_records_preserve_branch_relations_and_nested_types() {
    let source = include_str!("../../../examples/conditional_records.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace(
        "Pair {chosen: Checked {value: 42}",
        "Pair {chosen: Checked {value: 0}"
    ))
    .is_err());
    assert!(verify(&source.replace("choose(true,", "choose(false,")).is_err());
    let source = "fn noop(flag: bool) -> () {if flag {()} else {()}} fn main() -> usize {let x = noop(false); 42}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn trusted_function_contracts_remain_audited_at_callers() {
    let source = "fn external() -> usize ensures (result == 99) {0} proof {trustme} fn main() -> usize ensures (result == 99) {external()}";
    let program = verify(source).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert!(program.trusted_assumptions()[0].goal.contains("external"));
    // Erased assumptions can lie about runtime behavior, so the audit must
    // survive even when downstream obligations use only checked arithmetic.
    assert_eq!(program.run().unwrap().to_string(), "0");
    assert!(verify(&source.replace("trustme", "omega")).is_err());
}

#[test]
fn checks_contracts_and_bounds_internally() {
    let p = verify(include_str!("../../../examples/contracts.evg")).unwrap();
    assert!(p.obligations >= 3);
    for source in [
        include_str!("../../../examples/reject_bounds.evg"),
        include_str!("../../../examples/reject_contract.evg"),
    ] {
        assert!(verify(source).is_err());
    }
}

#[test]
fn composes_calls_and_checks_preconditions() {
    let prefix = "fn inc(n: usize) -> usize where (n < 10) ensures (result == n + 1) { n + 1 } ";
    assert!(verify(&format!(
        "{prefix} fn main() -> usize ensures (result == 5) {{ inc(4) }}"
    ))
    .is_ok());
    assert!(verify(&format!("{prefix} fn main() -> usize {{ inc(10) }}")).is_err());
}

#[test]
fn verifies_both_branches_and_natural_subtraction() {
    verify(
        "ideal fn abs(n: integer) -> integer ensures (result >= 0) { if n >= 0 { n } else { -n } }",
    )
    .unwrap();
    verify("ideal fn sub(n: nat) -> nat ensures (result <= n) { n - 1 }").unwrap();
    assert!(verify(
        "fn bad(n: isize) -> isize ensures (result >= 0) { if n >= 0 { n } else { n } }"
    )
    .is_err());
}

#[test]
fn facts_are_proved_before_use() {
    assert!(verify("fn bad(n: usize) -> usize { proof lie: n < 0; n }").is_err());
    assert!(verify("fn bad() -> usize { proof h: true by { exact missing }; 0 }").is_err());
    assert!(verify("fn bad() -> usize { result }").is_err());
}

#[test]
fn arrays_and_types_are_checked() {
    verify("fn main() -> usize ensures (result == 20) { let a: [usize; 2] = [10, 20]; a[1] }")
        .unwrap();
    for s in [
        "fn f() -> usize { let a: [usize; 2] = [1]; 0 }",
        "fn f() -> usize { let a: [usize; 1] = [1]; a[1] }",
        "fn f() -> usize { -1 }",
        "fn f() -> bool { 1 }",
    ] {
        assert!(verify(s).is_err(), "{s}");
    }
}

#[test]
fn compound_logic_and_contradictory_preconditions() {
    verify("fn f(n: usize) -> usize where (n < 3 || n > 10) ensures (result != 5) { n }").unwrap();
    verify("fn f(n: usize) -> usize where (n < 0) ensures (result > 100) { n }").unwrap();
}

#[test]
fn struct_invariants_and_atomic_replacement() {
    let prefix = "type Buffer struct { len: usize, cap: usize } where (len <= cap); ";
    let valid = format!("{prefix} fn main() -> usize {{ let b = Buffer {{ len: 1, cap: 2 }}; b = Buffer {{ len: b.len + 2, cap: b.cap + 2 }}; b.len }}");
    assert_eq!(verify(&valid).unwrap().run().unwrap().to_string(), "3");
    for body in [
        "let b = Buffer {len: 3, cap: 2}; b.len",
        "let b = Buffer {len: 1, cap: 2}; b.len = 3; b.len",
        "let b = Buffer {len: 1}; b.len",
        "let b = Buffer {len: 1, cap: 2, extra: 0}; b.len",
    ] {
        assert!(
            verify(&format!("{prefix} fn main() -> usize {{ {body} }}")).is_err(),
            "{body}"
        );
    }
}

#[test]
fn dependent_struct_fields_and_nested_invariants() {
    let s = "type Storage struct { len: usize, data: [isize; len] } type Outer struct { storage: Storage } fn main() -> isize { let s = Storage {len: 2, data: [10, 20]}; let o = Outer {storage: s}; o.storage.data[1] }";
    assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "20");
    assert!(verify("type Storage struct {len: usize, data: [isize; len]} fn main() -> usize {let s = Storage {len: 2, data: [1, 2]}; s.len = 3; 0}").is_err());
    assert!(verify("type Inner struct {x: usize} where (x > 0); type Outer struct {inner: Inner} fn main() -> usize {let o = Outer {inner: Inner {x: 1}}; o.inner.x = 0; 0}").is_err());
}

#[test]
fn contracts_capture_entry_parameters() {
    assert!(verify("fn bad(n: usize) -> usize ensures (result == n) { n = 0; n }").is_err());
    let s = "fn reset(n: usize) -> usize ensures (result == 0) { n = 0; n } fn main() -> usize ensures (result == 0) {reset(10)}";
    assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "0");
}

#[test]
fn aliased_references_share_scalar_updates() {
    let s = "fn read(r: &usize) -> usize ensures (result == *r) { *r } fn main() -> usize ensures (result == 7) { let x: usize = 1; let a = &x; let b = &x; *a = 7; read(b) }";
    assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "7");
    let s = "fn main() -> usize ensures (result == 11) { let data: [usize; 2] = [1, 2]; let a = &data[0]; let b = &data[1]; *a = 9; *b = 11; *b }";
    assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "11");
}

#[test]
fn stale_references_are_compile_errors() {
    for body in [
        "let x: usize = 1; let r = &x; drop(x); *r",
        "let x: usize = 1; let r = &x; let y = move(x); *r",
        "let a: [usize; 1] = [1]; let r = &a[0]; drop(a); *r",
        "let x: usize = 1; let r = &x; drop(x); x = 2; *r",
        "let x: usize = 1; let y = move(x); x",
    ] {
        assert!(
            verify(&format!("fn main() -> usize {{ {body} }}")).is_err(),
            "{body}"
        );
    }
    let s = "fn main() -> usize { let x: usize = 1; let y = move(x); x = 2; x + y }";
    assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "3");
    let fixed = "fn main() -> usize ensures (result == 3) { let a: [usize; 2] = [1, 2]; let r = &a[0]; a = [3, 4]; *r }";
    assert_eq!(verify(fixed).unwrap().run().unwrap().to_string(), "3");
}

#[test]
fn reference_updates_recheck_invariants_and_cannot_escape() {
    let prefix = "type Small struct {n: usize} where (n < 4); ";
    assert!(verify(&format!(
        "{prefix} fn main() -> usize {{let x = Small {{n: 1}}; let r = &x.n; *r = 9; x.n }}"
    ))
    .is_err());
    assert!(verify("fn escape() -> &usize {let x: usize = 1; &x}").is_err());
    assert!(verify("fn write(r: &usize) -> () { *r = 1; () }").is_err());
    assert!(verify("fn f(n: usize) -> usize ensures (result == move(n)) { n }").is_err());
}

#[test]
fn runtime_divergence_is_inferred_and_cannot_become_proof_evidence() {
    let source = include_str!("../../../examples/partial_recursion.evg");
    let program = verify(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        program
            .potentially_diverging_functions()
            .collect::<Vec<_>>(),
        ["countdown", "main"]
    );
    assert!(program.trusted_assumptions().is_empty());
    let spin = "fn spin() -> usize ensures(false) {spin()}";
    assert!(verify(spin).is_ok());
    let chain = "fn first() -> usize ensures(false) {first()} fn second() -> usize ensures(false) {first()} fn third() -> usize ensures(false) {second()}";
    assert_eq!(
        verify(chain)
            .unwrap()
            .potentially_diverging_functions()
            .count(),
        3
    );
    let measured = "fn relay(n: usize) -> usize decreases(n) {spin()}";
    assert_eq!(
        verify(&format!("{spin} {measured}"))
            .unwrap()
            .potentially_diverging_functions()
            .count(),
        2
    );
    assert!(verify(include_str!("../../../examples/reject_divergent_proof.evg")).is_err());
    for observer in [
        "ideal fn unsound() -> nat {nat(spin())}",
        "fn unsound() -> usize {proof lie: spin() == 0; 0}",
        "fn unsound() -> usize {ideal let lie = spin(); 0}",
        "fn unsound() -> usize where(spin() == 0) {0}",
    ] {
        let error = verify(&format!("{spin} {observer}")).unwrap_err();
        assert!(error.contains("potentially divergent"), "{error}");
    }
    assert!(verify("ideal fn spin() -> nat {spin()}").is_err());
    assert!(verify("fn lie() -> usize ensures(false) {0}").is_err());
    assert!(
        verify("fn lie(n: usize) -> usize ensures(false) {if n == 0 {0} else {lie(n - 1)}}")
            .is_err()
    );
    let namespaced = "fn spin() -> usize ensures(result == 42) {42} module looping {fn spin() -> usize ensures(false) {spin()}} ideal fn observe() -> nat ensures(result == 42) {nat(spin())}";
    assert_eq!(
        verify(namespaced)
            .unwrap()
            .potentially_diverging_functions()
            .collect::<Vec<_>>(),
        ["looping::spin"]
    );
    assert!(verify(&format!(
        "{namespaced} ideal fn bad() -> nat {{nat(looping::spin())}}"
    ))
    .is_err());
    assert!(verify("fn unsafe_loop(n: usize) -> usize {unsafe_loop(n + 1)}").is_err());
    let run =
        verify("fn spin() -> usize ensures(false) {spin()} fn main() -> usize {spin()}").unwrap();
    assert!(run.run().unwrap_err().contains("execution"));
    // A proved decreasing, pure runtime function is usable as ideal data.
    let total = "fn count(n: usize) -> usize ensures(result == n) decreases(n) {if n == 0 {0} else {count(n - 1) + 1}} fn main() -> usize ensures(result == 42) {ideal let expected = nat(count(42)); proof established: expected == 42; 42}";
    let program = verify(total).unwrap();
    assert_eq!(program.potentially_diverging_functions().count(), 0);
    let checked_pop = "fn main() -> usize ensures(result == 42) {let v = vec::new(2); vec::push(&v, 7); vec::push(&v, 42); vec::pop(&v)}";
    assert_eq!(
        verify(checked_pop).unwrap().run().unwrap().to_string(),
        "42"
    );
    assert_eq!(program.run().unwrap().to_string(), "42");
}

#[test]
fn verifies_well_founded_recursion() {
    let s = "fn countdown(n: usize) -> usize ensures (result == n) decreases (n) { if n == 0 { 0 } else { countdown(n - 1) + 1 } } fn main() -> usize ensures (result == 12) { countdown(12) }";
    assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "12");
    for body in [
        "loop(n)",
        "loop(n + 1)",
        "if n == 0 { loop(n) } else { loop(n - 1) }",
    ] {
        assert!(
            verify(&format!(
                "fn loop(n: usize) -> usize decreases (n) {{ {body} }}"
            ))
            .is_err(),
            "{body}"
        );
    }
    assert!(verify("fn bad(n: usize) -> usize ensures (bad(n) == 0) decreases (n) {0}").is_err());
}

#[test]
fn machine_overflow_requires_a_proof() {
    assert!(verify("fn increment(n: usize) -> usize { n + 1 }").is_err());
    let p = "fn increment(n: usize) -> usize where (n < usize::MAX) ensures (result == n + 1) { n + 1 } fn main() -> usize ensures (result == usize::MAX) { increment(usize::MAX - 1) }";
    assert_eq!(
        verify(p).unwrap().run().unwrap().to_string(),
        u64::MAX.to_string()
    );
    for s in [
        "fn main() -> usize {usize::MAX + 1}",
        "fn main() -> u8 {256}",
        "fn main() -> u8 {0 - 1}",
        "fn abs(n: isize) -> isize {if n >= 0 {n} else {-n}}",
        "fn main() -> i8 {-129}",
        "fn main() -> i8 {-i8::MIN}",
    ] {
        assert!(verify(s).is_err(), "{s}");
    }
    assert_eq!(
        verify("fn main() -> i8 {-128}")
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "-128"
    );
}

#[test]
fn signed_array_indices_also_need_lower_bounds() {
    assert!(
        verify("fn at(n: usize, a: [isize; n], i: isize) -> isize where (i < 5) {a[i]}").is_err()
    );
    verify("fn at(a: [isize; 5], i: isize) -> isize where (i >= 0 && i < 5) {a[i]}").unwrap();
}

#[test]
fn explicit_updates_restore_invariants_and_ordinary_writes_preserve_them() {
    let s = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn read(p: &Pair) -> usize {*p.left} fn main() -> usize {let p = Pair {left: 1, right: 1}; update(p) lifts balanced {p.left = 2; p.right = p.left;} p.right}";
    // Field projection binds tighter than dereference.
    let s = s.replace("*p.left", "(*p).left");
    assert_eq!(verify(&s).unwrap().run().unwrap().to_string(), "2");
    let s = "type Storage struct {len: usize, data: [usize; len]} fn main() -> usize {let s = Storage {len: 1, data: [10]}; s = Storage {len: 2, data: [10, 20]}; s.data[1]}";
    assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "20");
}

#[test]
fn incomplete_states_cannot_be_observed_as_the_refined_type() {
    let prefix = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn read(p: &Pair) -> usize {(*p).left} ";
    for body in [
        "let p = Pair {left: 1, right: 1}; let r = &p; p.left = 2; read(r)",
        "let p = Pair {left: 1, right: 1}; p.left = 2; let r = &p; p.right = 2; 0",
        "let p = Pair {left: 1, right: 1}; p.left = 2; drop(p); 0",
    ] {
        assert!(
            verify(&format!("{prefix} fn main() -> usize {{ {body} }}")).is_err(),
            "{body}"
        );
    }
    let body = "let p = Pair {left: 1, right: 1}; let r = &p; update(p) lifts balanced {p.left = 2; p.right = 2;} read(r)";
    assert_eq!(
        verify(&format!("{prefix} fn main() -> usize {{ {body} }}"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "2"
    );
}

#[test]
fn library_rc_protocol_is_verified_without_compiler_special_cases() {
    let source = include_str!("../../../proofs/rc_protocol.evg");
    assert!(verify(source).unwrap().obligations >= 50);
    assert!(verify(&source.replace("RcProtocol", "OrdinaryUserState")).is_ok());
    assert!(verify(include_str!("../../../proofs/reject_rc_unbalanced.evg")).is_err());
    let double_publish = format!("{source}\nideal fn duplicate_credit(s: RcProtocol) -> RcProtocol where (s.credits == 1) {{publish(publish(s))}}");
    assert!(verify(&double_publish)
        .unwrap_err()
        .contains("precondition of publish"));
}

#[test]
fn updates_enforce_visibility_cleanup_and_restoration_boundaries() {
    let prefix = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn observe(p: &Pair) -> usize {(*p).left} ";
    for update in [
        "update(p) lifts balanced {p.left = 2;}",
        "update(p) lifts balanced {p.left = observe(r); p.right = 2;}",
        "update(p) lifts balanced {p.left = *r; p.right = 2;}",
        "update(p) lifts balanced {p.left = drop(p); p.right = 2;}",
        "update(p) lifts balanced {p.left = move(p); p.right = 2;}",
        "update(p) lifts balanced {p.left = &p; p.right = 2;}",
        "update(p) lifts balanced {q.left = 2; q.right = 2;}",
        "update(p, p) lifts balanced {p.left = 2; p.right = 2;}",
        "update(p) lifts balanced {p = Pair {left: 2, right: 2};}",
        "update(p) lifts balanced {p.left = usize::MAX + 1; p.right = 2;}",
    ] {
        let source = format!("{prefix} fn main() -> usize {{let p = Pair {{left: 1, right: 1}}; let q = Pair {{left: 1, right: 1}}; let r = &p; {update} p.left}}");
        assert!(verify(&source).is_err(), "accepted {update}");
    }
}

#[test]
fn updates_preserve_untouched_owned_fields() {
    let source = "type Resource struct {tag: usize} where (tag == 7); type Pair struct {left: usize, right: usize, resource: Resource} where (fact balanced = left == right; balanced); fn main() -> usize {let p = Pair {left: 1, right: 1, resource: Resource {tag: 7}}; update(p) lifts balanced {p.left = 2; p.right = 2;} p.resource.tag}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "7");
    let replace = source.replace(
        "p.left = 2; p.right = 2;",
        "p.resource = Resource {tag: 7};",
    );
    assert!(verify(&replace).is_err());
    assert!(verify("type NonZero struct {value: usize} where (value != 0); fn main() -> usize {let x = NonZero {value: 1}; x.value = 0; 0}").is_err());
}

#[test]
fn borrowed_invariants_are_checked_through_record_fields() {
    let source = "type Positive struct {n: usize} where (n > 0); type Holder struct {p: &Positive} fn read(h: Holder) -> usize ensures (result > 0) {(*h.p).n} fn main() -> usize {let p = Positive {n: 1}; let h = Holder {p: &p}; p.n = 0; let result = read(h); p.n = 1; result}";
    assert!(verify(source).is_err());
}

#[test]
fn dropped_or_moved_owners_have_shape_type() {
    let prefix = "type Resource struct {tag: usize} where (tag == 7); impl Drop for Resource {fn drop(self){}} ";
    for body in [
        "let a = Resource {tag: 7}; let b = a; a.tag",
        "let a = Resource {tag: 7}; drop(a); a.tag",
        "let a = Resource {tag: 7}; drop(a); drop(a); 0",
        "let a = Resource {tag: 7}; let r = &a; let b = a; (*r).tag",
    ] {
        assert!(
            verify(&format!("{prefix} fn main() -> usize {{ {body} }}")).is_err(),
            "{body}"
        );
    }
}

#[test]
fn destructors_are_proved_and_effects_require_explicit_support() {
    for body in [
        "proof impossible: self.tag == 8;",
        "drop(self);",
        "let duplicate = self;",
        "let new = Resource {tag: 7};",
    ] {
        let source = format!("type Resource struct {{tag: usize}} where (tag == 7); impl Drop for Resource {{fn drop(self) {{ {body} }} }} fn main() -> usize {{0}}");
        assert!(verify(&source).is_err(), "{body}");
    }
}

#[test]
fn destructors_use_checked_scalar_helpers_without_gaining_external_effects() {
    let source = format!(
        "{} {}",
        include_str!("../../../stdlib/counter.evg"),
        include_str!("../../../examples/drop_helpers.evg")
    );
    let (program, bundle) = prove(&source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
    let replayed = verify_with_certificate(&source, &bundle).unwrap();
    assert_eq!(replayed.proof_search_count(), 0);
    assert_eq!(replayed.run().unwrap().to_string(), "42");
    let swaps = format!("{} type Pair struct {{left: usize, right: usize}} impl Drop for Pair {{fn drop(self) {{let left = self.left; let right = self.right; swap_usize(&self.left, &self.right); proof swapped: self.left == right && self.right == left;}}}} fn main() -> usize {{let pair = Pair {{left: 1, right: 2}}; 42}}", include_str!("../../../stdlib/swap.evg"));
    assert_eq!(verify(&swaps).unwrap().run().unwrap().to_string(), "42");
    let returned = "fn reset(r: &usize) -> &usize modifies(r) borrows(r) ensures(*result == 0) {*r = 0; r} type Resource struct {value: usize} impl Drop for Resource {fn drop(self){let r = reset(&self.value); proof updated: *r == 0 && self.value == 0;}} fn main() -> usize {let r = Resource {value: 42}; 42}";
    assert_eq!(verify(returned).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn destructor_helper_summaries_reject_hidden_cleanup_divergence_and_external_writes() {
    for (source, expected) in [
        ("type Resource struct {} fn hidden() -> usize {let another = Resource {}; 0} impl Drop for Resource {fn drop(self){let n = hidden();}}", "mutually recursive"),
        ("type Resource struct {} fn hidden() -> usize {let another = Resource {}; 0} fn wrapper() -> usize {hidden()} impl Drop for Resource {fn drop(self){let n = wrapper();}}", "mutually recursive"),
        ("fn forever() -> usize {forever()} type Resource struct {} impl Drop for Resource {fn drop(self){let n = forever();}}", "ownership-free"),
        ("type Leaf struct {} impl Drop for Leaf {fn drop(self){}} fn hidden() -> usize {let leaf = Leaf {}; 0} type Resource struct {} impl Drop for Resource {fn drop(self){let n = hidden();}}", "ownership-free"),
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains(expected), "{error}: {source}");
    }
    let library = include_str!("../../../stdlib/counter.evg");
    for body in [
        "let zero = counter_decrement(self.target);",
        "*self.target = 0;",
    ] {
        let source = format!("{library} type Resource struct {{target: &usize}} where(*target > 0); impl Drop for Resource {{fn drop(self){{{body}}}}}");
        let error = verify(&source).unwrap_err();
        assert!(
            error.contains("effect contract") || error.contains("modifies contract"),
            "{error}"
        );
    }
    let broken = format!("{library} type Resource struct {{value: usize}} where(value == 1); impl Drop for Resource {{fn drop(self){{let zero = counter_decrement(&self.value);}}}}");
    assert!(verify(&broken).is_err());
}

#[test]
fn destructor_effects_cover_explicit_scope_temporary_and_replacement_cleanup() {
    let example = include_str!("../../../examples/drop_effects.evg");
    let (program, bundle) = prove(example).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    let replayed = verify_with_certificate(example, &bundle).unwrap();
    assert_eq!(replayed.proof_search_count(), 0);
    let declarations = example.split("fn main").next().unwrap();
    for body in [
        "let count: usize = 0; let guard = StoreOnDrop {target: &count, value: 42}; drop(guard); count",
        "let count: usize = 0; StoreOnDrop {target: &count, value: 42}; count",
        "let count: usize = 0; let saved = StoreOnDrop {target: &count, value: 42}.value; proof saved_value: saved == 42; count",
        "let count: usize = 0; let guard = StoreOnDrop {target: &count, value: 7}; guard = StoreOnDrop {target: &count, value: 42}; proof old_dropped: count == 7; drop(guard); count",
        "let count: usize = 0; let guards: [StoreOnDrop; 2] = [StoreOnDrop {target: &count, value: 7}, StoreOnDrop {target: &count, value: 42}]; drop(guards); count",
    ] {
        let source = format!("{declarations} fn main() -> usize ensures(result == 42) {{{body}}}");
        assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42", "{body}");
    }
    let reverse = format!("{declarations} fn main() -> usize ensures(result == 7) {{let count: usize = 0; let sum = StoreOnDrop {{target: &count, value: 7}}.value + StoreOnDrop {{target: &count, value: 42}}.value; proof snapshot: sum == 49; count}}");
    assert_eq!(verify(&reverse).unwrap().run().unwrap().to_string(), "7");
}

#[test]
fn parent_cleanup_uses_final_child_fields_and_declared_effects() {
    let source = include_str!("../../../examples/drop_children.evg");
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Parent", "drop Child"]);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("modifies(self.child.target)", "")).is_err());
    let declarations = include_str!("../../../examples/drop_effects.evg")
        .split("fn main")
        .next()
        .unwrap();
    let invalidated_sibling = format!("{declarations} type Positive struct {{target: &usize}} where(*target > 0); impl Drop for Positive {{fn drop(self){{let previous = *self.target - 1;}}}} type Siblings struct {{first: StoreOnDrop, last: Positive}} fn main() -> usize {{let count: usize = 1; let siblings = Siblings {{first: StoreOnDrop {{target: &count, value: 0}}, last: Positive {{target: &count}}}}; drop(siblings); 42}}");
    assert!(verify(&invalidated_sibling).is_err());

    assert!(verify(&source.replace(
        "ensures (*self.child.target == 42)",
        "ensures (*self.child.target == self.child.tag)"
    ))
    .is_err());
}

#[test]
fn parent_is_consumed_before_count_releasing_field_cleanup() {
    let source = format!(
        "{} {}",
        include_str!("../../../stdlib/counter.evg"),
        include_str!("../../../examples/drop_count.evg")
    );
    let (program, bundle) = prove(&source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "0");
    assert_eq!(events, ["drop Counted", "drop ReleaseCount"]);
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let direct = format!("{} type Counted struct {{count: &usize}} where(*count > 0); impl Drop for Counted {{fn drop(self) modifies(self.count) {{let zero = counter_decrement(self.count);}}}}", include_str!("../../../stdlib/counter.evg"));
    assert!(verify(&direct).is_err());
}

#[test]
fn implicit_cleanup_cannot_hide_writes_or_keep_stale_proofs() {
    let declarations = include_str!("../../../examples/drop_effects.evg")
        .split("fn main")
        .next()
        .unwrap();
    for caller in [
        "fn hidden(target: &usize) {let guard = StoreOnDrop {target: target, value: 42};}",
        "fn hidden(guard: StoreOnDrop) {}",
        "fn hidden(target: &usize) {StoreOnDrop {target: target, value: 42};}",
        "fn hidden(target: &usize) {let value = StoreOnDrop {target: target, value: 42}.value;}",
    ] {
        let error = verify(&format!("{declarations} {caller}")).unwrap_err();
        assert!(error.contains("matching modifies contract"), "{error}");
    }
    let stale = format!("{declarations} fn main() -> usize {{let count: usize = 0; proof before: count == 0; StoreOnDrop {{target: &count, value: 42}}; proof after: count == 0 by {{exact before}}; count}}");
    assert!(verify(&stale).is_err());
    let wrong = format!("{declarations} fn main() -> usize ensures(result == 0) {{let count: usize = 0; StoreOnDrop {{target: &count, value: 42}}; count}}");
    assert!(verify(&wrong).is_err());
    let alias = "type Pair struct {write: &usize, read: &usize} impl Drop for Pair {fn drop(self) modifies(self.write) {*self.write = 42;}} fn main() {let count: usize = 0; let pair = Pair {write: &count, read: &count}; drop(pair);}";
    assert!(verify(alias).is_ok());
    let opaque = format!("{declarations} fn consume_array(guards: [StoreOnDrop; 2]) {{}}");
    let error = verify(&opaque).unwrap_err();
    assert!(error.contains("matching modifies contract"), "{error}");
    let opaque =
        format!("{declarations} fn consume_array(ideal n: nat, guards: [StoreOnDrop; n]) {{}}");
    let error = verify(&opaque).unwrap_err();
    assert!(error.contains("opaque arrays"), "{error}");
    let empty = format!("{declarations} fn empty(guards: [StoreOnDrop; 0]) {{}} fn main() -> usize {{let guards: [StoreOnDrop; 0] = []; empty(guards); 42}}");
    assert_eq!(verify(&empty).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn cleanup_cannot_observe_a_borrow_of_an_already_dropped_plane() {
    let source = "type Borrower struct {p: &usize} impl Drop for Borrower {fn drop(self){}} fn main() -> usize {let first: usize = 1; let h = Borrower {p: &first}; let later: usize = 2; h.p = &later; 0}";
    assert!(verify(source).is_err());
    let source = "type Borrower struct {p: &usize} impl Drop for Borrower {fn drop(self){}} fn main() -> usize {let first: usize = 1; let h = Borrower {p: &first}; 0}";
    assert!(verify(source).is_ok());
}

#[test]
fn independent_calls_and_scalar_borrows_are_allowed_inside_updates() {
    let source = include_str!("../../../examples/update_helpers.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let missing_restore = source.replace("pair.right = read(view);", "pair.right = 0;");
    assert!(verify(&missing_restore).is_err());
    let escape = source.replace("    pair.right\n}", "    read(view)\n}");
    assert!(verify(&escape).is_err());
    let prefix = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn equal(a: usize, b: usize) -> usize where (a == b) ensures (result == a) {a} ";
    let source = format!("{prefix} fn main() -> usize {{let p = Pair {{left: 1, right: 1}}; update(p) lifts balanced {{p.left = 2; p.right = equal(p.left, p.right);}} p.right}}");
    assert!(verify(&source).is_err());
}

#[test]
fn calls_with_unproven_effects_cannot_observe_open_invariants() {
    let source = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn observe(p: &Pair) -> usize {(*p).left} fn main() -> usize {let p = Pair {left: 1, right: 1}; update(p) lifts balanced {p.left = 2; p.right = observe(&p);} p.right}";
    assert!(verify(source).is_err());
    let source = "type Resource struct {} impl Drop for Resource {fn drop(self){}} type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn cleanup(value: usize) -> usize {let r = Resource {}; value} fn main() -> usize {let p = Pair {left: 1, right: 1}; update(p) lifts balanced {p.left = cleanup(p.left); p.right = p.left;} p.right}";
    assert!(verify(source).is_err());
}

#[test]
fn fact_definitions_are_not_proofs_or_assumptions() {
    let source = include_str!("../../../examples/named_facts.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(include_str!("../../../examples/reject_false_proof.evg")).is_err());
    assert!(
        verify("fn main() -> usize {fact false_claim = 1 == 2; proof exploit: 2 == 3; 0}").is_err()
    );
    assert!(verify("fn main() -> usize {fact true_claim = 1 == 1; proof p: true_claim by {exact true_claim}; 0}").is_err());
    assert!(verify("fn main() -> usize {fact p = 1 == 1; if p {1} else {0}}").is_err());
}

#[test]
fn exact_uses_the_named_proof_of_the_current_proposition() {
    let source = "fn identity(n: usize) -> usize ensures (result == n) {proof positive: n >= 0; n} proof {exact positive}";
    assert!(verify(source).is_err()); // True goal, but this is the wrong witness.
    let source = "fn main() -> usize {let x: usize = 1; fact p = x == 1; proof old: p; x = 2; proof stale: p by {exact old}; x}";
    assert!(verify(source).is_err());
    let source = "fn main() -> usize {let x: usize = 1; fact p = x == 1; proof old: p; x = 2; proof stale: p; x}";
    assert!(verify(source).is_err());
}

#[test]
fn caller_facts_cannot_redefine_struct_invariants() {
    let source = "type Checked struct {valid: bool} where (valid); fn main() -> usize {fact valid = true; let c = Checked {valid: false}; 0}";
    assert!(verify(source).is_err());
    let source = "type Checked struct {valid: bool} where (valid); fn main() -> usize {fact valid = false; let c = Checked {valid: true}; 0}";
    assert!(verify(source).is_ok());
}

#[test]
fn mathematical_values_and_ideal_records_cannot_leak_into_runtime_storage() {
    for source in [
        "fn main() -> nat {0}",
        "fn main() -> usize {let n: nat = 0; 0}",
        "type Bad struct {n: integer} fn main() -> usize {0}",
        "ideal type Model struct {n: nat} fn main() -> usize {let m = Model {n: 0}; 0}",
        "ideal fn answer() -> usize {42} fn main() -> usize {answer()}",
        "fn main() -> usize {let n = nat(42); 0}",
    ] {
        assert!(verify(source).is_err(), "{source}");
    }
    let source = "ideal fn main() -> nat {1 + 2}";
    assert!(verify(source).is_ok());
    assert!(verify(source).unwrap().run().is_err());
}

#[test]
fn proof_views_and_ideal_contracts_are_erased_before_execution() {
    let source = "ideal fn positive(n: nat) -> bool where (n > 0) ensures (result) {true} fn main() -> usize where (positive(nat(1))) {let value: usize = 42; proof p: nat(value) >= 0; value}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let source = "fn main() -> usize {let value = 42; proof bounded: value <= isize::MAX; 0}";
    assert!(verify(source).is_ok());
}

#[test]
fn lifted_requirements_are_named_and_selective() {
    let source = include_str!("../../../examples/selective_update.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let bounded_violation = source.replace(
        "pair.left = 42;",
        "pair.left = 101; pair.right = 101; pair.left = 42;",
    );
    assert!(verify(&bounded_violation).is_err());
    assert!(
        verify(&bounded_violation.replace("lifts balanced", "lifts balanced, bounded")).is_ok()
    );
    assert!(verify(&source.replace("lifts balanced", "lifts bounded")).is_err());
    assert!(verify(&source.replace("lifts balanced", "lifts unknown")).is_err());
    assert!(verify(&source.replace("lifts balanced", "lifts unused_false_claim")).is_err());
    assert!(verify(&source.replace("lifts balanced", "lifts Pair::balanced")).is_ok());
    assert!(verify(&source.replace("lifts balanced", "lifts balanced, balanced")).is_err());
    assert!(verify(&source.replace("lifts balanced", "")).is_err());
}

#[test]
fn named_type_facts_do_not_add_unproven_assumptions() {
    let source = "type State struct {n: usize} where (fact claim = n == 0; true); fn main() -> usize {let s = State {n: 1}; fact false_statement = s::claim; 0}";
    assert!(verify(source).is_ok());
    assert!(verify(&source.replace(
        "fact false_statement = s::claim;",
        "proof invalid: s::claim;"
    ))
    .is_err());
    let source = "type Checked struct {valid: bool} where (fact required = valid; required); fn main() -> usize {fact required = true; let s = Checked {valid: false}; 0}";
    assert!(verify(source).is_err());
}

#[test]
fn rc_and_arc_share_a_lifting_free_ideal_count_protocol() {
    let protocol = include_str!("../../../proofs/rc_protocol.evg");
    assert!(!protocol.contains("lifts"));
    let model = format!(
        "{protocol}\n{}",
        include_str!("../../../proofs/arc_interleavings.evg")
    );
    assert!(verify(&model).is_ok());
    let stale = format!(
        "{protocol}\n{}",
        include_str!("../../../proofs/reject_arc_stale_check.evg")
    );
    assert!(verify(&stale)
        .unwrap_err()
        .contains("precondition of reserve"));
}

#[test]
fn cleanup_can_write_live_owned_heap_and_pending_return_allocations() {
    let source = include_str!("../../../examples/owned_return_cleanup.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let owned_receiver = include_str!("../../../examples/owned_destructor_cleanup.evg");
    assert_eq!(
        verify(owned_receiver).unwrap().run().unwrap().to_string(),
        "42"
    );
    let after_free =
        owned_receiver.replace("drop(guard);", "drop(guard); proof stale: *target == 42;");
    assert!(verify(&after_free).is_err());
    let declarations = source.split("fn finish()").next().unwrap();
    let local = format!("{declarations} fn main() -> usize {{let owner: plane(usize) = alloc(7); let guard = Guard {{target: &*owner, value: 42}}; drop(guard); *owner}}");
    assert_eq!(verify(&local).unwrap().run().unwrap().to_string(), "42");
    let borrowed = format!("{declarations} fn finish(owner: &plane(usize)) -> usize {{let guard = Guard {{target: &**owner, value: 42}}; 42}} fn main() -> usize {{let owner: plane(usize) = alloc(7); finish(&owner)}}");
    assert!(verify(&borrowed).unwrap_err().contains("modifies"));
    let invalid_payload = format!("{declarations} type Positive struct {{value: usize}} where(value > 0); fn finish() -> plane(Positive) {{let owner: plane(Positive) = alloc(Positive {{value: 7}}); let guard = Guard {{target: &(*owner).value, value: 0}}; owner}} fn main() -> usize {{let owner = finish(); (*owner).value}}");
    assert!(verify(&invalid_payload).is_err());
    let stale = "type Guard struct {slot: &plane(usize)} impl Drop for Guard {fn drop(self) {fact readable = **self.slot == 7;}} fn finish() -> plane(usize) {let owner: plane(usize) = alloc(7); let guard = Guard {slot: &owner}; owner} fn main() -> usize {let owner = finish(); *owner}";
    assert!(verify(stale).is_err());
}

#[test]
fn owned_word_vectors_check_capacity_and_reference_lifetimes() {
    let source = include_str!("../../../examples/vec.evg");
    let (program, bundle) = prove(source).unwrap();
    let copy = program
        .functions
        .iter()
        .find(|f| f.name == "vec::copy_prefix")
        .unwrap();
    assert!(!crate::compiler::effects::recursive(copy));
    assert!(!copy.partial);
    assert_eq!(program.potentially_diverging_functions().count(), 0);
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for source in [
        "fn main() -> usize {let v = vec::new(0); vec::push(&v, 1); 0}",
        "fn main() -> usize {let v = vec::new(2); vec::pop(&v)}",
        "fn main() -> usize {let v = vec::new(2); *vec::get(&v, 0)}",
        "fn main() -> usize {let v = vec::new(1); vec::push(&v, 42); let p = vec::get(&v, 0); v = vec::reallocate(&v, 2); *p}",
        "fn main() -> usize {let v = vec::new(2); vec::push(&v, 42); v = vec::reallocate(&v, 0); 0}",
        "fn main() -> usize {let v = vec::new(usize::MAX); 0}",
    ] {
        assert!(verify(source).is_err(), "accepted invalid vector operation: {source}");
    }
    let source = "type Buffer struct {cap: usize, data: plane(usize, cap)} fn main() -> usize {let cap: usize = 7; let data: plane(usize, 2) = alloc(2, 42); let buffer = Buffer {cap: 2, data: data}; (*buffer.data)[1]}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("Buffer {cap: 2", "Buffer {cap: 3")).is_err());
}

#[test]
fn owned_dependent_parameters_resolve_in_the_callee_scope() {
    let source = "fn consume(count: usize, owner: plane(usize, count)) -> usize where(count > 0) {(*owner)[0]} fn main() -> usize {let count: usize = 7; let owner: plane(usize, 2) = alloc(2, 42); consume(2, owner)}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("consume(2, owner)", "consume(3, owner)")).is_err());
    let forward = source
        .replace(
            "count: usize, owner: plane(usize, count)",
            "owner: plane(usize, count), count: usize",
        )
        .replace("consume(2, owner)", "consume(owner, 2)");
    assert_eq!(verify(&forward).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn field_autoderef_uses_the_existing_ownership_and_effect_checks() {
    let source = include_str!("../../../examples/field_access.evg");
    let (program, bundle) = prove(source).unwrap();
    let explicit = source
        .replace("person.age", "(*person).age")
        .replace("reference.age", "(**reference).age");
    assert_eq!(
        crate::compiler::native::emit(&program).unwrap(),
        crate::compiler::native::emit(&verify(&explicit).unwrap()).unwrap()
    );
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("modifies(&person.age)", "")).is_err());
    assert!(
        verify(&source.replace("    reference.age", "    drop(person); reference.age")).is_err()
    );
    assert!(verify("type Person struct {age: usize} fn main() -> usize {let p = alloc(Person {age: 42}); let moved = p; p.age}").is_err());
    assert!(verify("fn main() -> usize {let v = vec::new(2); let r = &v; r.len}").is_err());
    let nested = "type Inner struct {value: usize} type Outer struct {inner: plane(Inner)} fn main() -> usize {let outer = alloc(Outer {inner: alloc(Inner {value: 42})}); let a = &outer; let b = &a; b.inner.value}";
    assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
    let field_borrow = "type Item struct {value: usize} fn read(x: &Item) -> &usize borrows(&x.value) {*&x.value; &x.value} fn main() -> usize {let x = alloc(Item {value: 42}); *read(&*x)}";
    assert_eq!(
        verify(field_borrow).unwrap().run().unwrap().to_string(),
        "42"
    );
}

#[test]
fn scalar_construction_checks_representation_and_preserves_proofs() {
    let source = include_str!("../../../examples/scalar_types.evg");
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
        source.replace("size: 1, align: 1", "size: 2, align: 1"),
        source.replace("align: 1", "align: 0"),
        source.replace("repr::Little", "repr::Big"),
        source.replace("bits: 8", "bits: 7"),
        source.replace("repr::TwosComplement", "repr::Binary"),
        source.replace("size: 1", "size: 1 + 0"),
        source.replace("add(Octet(40), Octet(2))", "add(Octet(255), Octet(2))"),
    ] {
        assert!(
            verify(&bad).is_err(),
            "accepted invalid scalar declaration or arithmetic: {bad}"
        );
    }
    let scalar = source.split("type SignedOctet").next().unwrap();
    assert!(verify(&format!(
        "{scalar} fn Octet() -> usize {{42}} fn main() -> usize {{Octet()}}"
    ))
    .is_err());
    assert!(verify("type FakePointer = make_type(size: 8, align: 8, represents: repr::Pointer {bits: 64, endian: repr::Little}); fn main() -> usize {42}").is_err());
    let module = format!("module words; {source}");
    let main = "fn main() -> u8 {words::add(words::Octet(40), words::Octet(2))}";
    let units = syntax::join_source_units(&[module, main.into()]).unwrap();
    assert_eq!(verify(&units).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn package_declarations_are_scheduled_by_dependencies_not_file_order() {
    let source = syntax::join_source_units(&[
        "module library; type Outer struct {inner: Inner} fn answer() -> usize ensures(result == 42) {helper(Outer {inner: Inner {value: 42}})}".into(),
        "module library; type Inner struct {value: usize} fn helper(value: Outer) -> usize ensures(result == value.inner.value) {value.inner.value}".into(),
        "module main; fn main() -> usize ensures(result == 42) {library::answer()}".into(),
    ]).unwrap();
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for bad in [
        "module bad; fn a() -> usize {b()} fn b() -> usize {a()}",
        "module bad; type A struct {other: B} type B struct {other: A} fn main() {}",
    ] {
        assert!(verify(bad).unwrap_err().contains("mutually recursive"));
    }
    assert!(verify("fn earlier() -> usize {later()} fn later() -> usize {42}").is_ok());
    let recursive = "module counting; fn countdown(n: usize) -> usize ensures(result == n) decreases(n) {if n == 0 {0} else {countdown(n - 1) + 1}}";
    let source = syntax::join_source_units(&[
        recursive.into(),
        "fn main() -> usize {counting::countdown(42)}".into(),
    ])
    .unwrap();
    assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn unresolved_source_imports_cannot_silently_be_ignored() {
    assert!(verify("import absent; fn main() -> usize {42}")
        .unwrap_err()
        .contains("unresolved import absent"));
    let program = verify("import vec; fn main() -> usize {let value = vec::new(1); vec::push(&value, 42); vec::pop(&value)}").unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
}

#[test]
fn destructors_can_decompose_only_their_complete_receiver() {
    let source = include_str!("../../../examples/drop_receiver_pattern.evg");
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource", "drop Child"]);
    let explicit = source.replace(
        "proof local_owner_is_valid: *data == 42;",
        "proof local_owner_is_valid: *data == 42; let moved = data; drop(child); drop(moved);",
    );
    let (value, events) = verify(&explicit).unwrap().run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource", "drop Child"]);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for bad in [
        source.replace("modifies(self.child.finished)", ""),
        source.replace(
            "let Resource {data, child} = self;",
            "let Resource {data} = self;",
        ),
        source.replace(
            "let Resource {data, child} = self;",
            "let Resource {data, child} = self; proof invalid: *self.data == 42;",
        ),
        source.replace(
            "let Resource {data, child} = self;",
            "let Resource {data, child} = self; let Resource {data: again, child: another} = self;",
        ),
        source.replace("drop(resource);", "let Resource {data, child} = resource;"),
        source
            .replace(
                "let payload = &*self.data;",
                "let payload = &*self.data; let old_slot = &self.data;",
            )
            .replace(
                "proof local_owner_is_valid: *data == 42;",
                "proof local_owner_is_valid: **old_slot == 42;",
            ),
        source.replace(
            "drop(resource);",
            "let old_payload = &*resource.data; drop(resource); proof invalid: *old_payload == 42;",
        ),
    ] {
        assert!(
            verify(&bad).is_err(),
            "accepted invalid destructor decomposition: {bad}"
        );
    }
}

#[test]
fn records_move_by_default_and_copy_requires_a_checked_explicit_impl() {
    let source = include_str!("../../../examples/copy_and_move.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let moved = source.replace(
        "    let moved = person;",
        "    let moved = person; proof stale: person.age == 28;",
    );
    assert!(verify(&moved).is_err());
    assert!(verify(&source.replace("impl Copy for Point {}", "")).is_err());
    let borrowed = "type Item struct {value: usize} fn value(item: &Item) -> usize ensures(result == item.value) {item.value} fn main() -> usize ensures(result == 42) {let item = Item {value: 21}; let a = value(&item); let b = item.value; a + b}";
    assert_eq!(verify(borrowed).unwrap().run().unwrap().to_string(), "42");
    for bad in [
        "type Owner struct {data: plane(usize)} impl Copy for Owner {} fn main() {}",
        "type Resource struct {value: usize} impl Copy for Resource {} impl Drop for Resource {fn drop(self) {}} fn main() {}",
        "type Inner struct {value: usize} type Outer struct {inner: Inner} impl Copy for Outer {} fn main() {}",
        "type Item struct {value: usize} impl Copy for Item {} impl Copy for Item {} fn main() {}",
        "module items {type Item struct {value: usize}} impl Copy for items::Item {} fn main() {}",
        "fn main() -> usize {let source: plane(usize) = alloc(42); let moved = source; *source}",
        "type Item struct {value: usize} fn consume(item: Item) {} fn main() {let item = Item {value: 42}; consume(item); consume(item);}",
        "type Item struct {value: usize} fn main() {let items: [Item; 0] = []; let moved = items; let again = items;}",
    ] { assert!(verify(bad).is_err(), "accepted invalid Copy or move: {bad}"); }
}

#[test]
fn methods_apply_implicit_self_and_the_normal_move_effect_and_borrow_rules() {
    let source = include_str!("../../../examples/methods.evg");
    let reordered = "type Person struct {age: usize} fn main() -> usize {let p = Person::new(42); p.read()} impl Person {method read() -> usize {self.age} fn new(age: usize) -> Self {Self {age: age}}}";
    assert_eq!(verify(reordered).unwrap().run().unwrap().to_string(), "42");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(
        verify(&source.replace("person.into_age()", "person.into_age(); person.age()")).is_err()
    );
    assert!(verify(&source.replace("modifies(&self.age)", "")).is_err());
    assert!(verify(&source.replace(
        "person.into_age()",
        "let reference = &person; reference.into_age()"
    ))
    .is_err());
    assert!(
        verify(&source.replace("person.birthday();", "person.missing();"))
            .unwrap_err()
            .contains("unknown method missing")
    );
    assert!(verify("method foo() {}").is_err());
    assert!(verify("type Item struct {} impl Item {method foo(self) {}}").is_err());
    assert!(verify("module items {type Item struct {value: usize}} impl items::Item {method& read() -> usize {self.value}} fn main() {}").is_err());
    let copy = "type Point struct {value: usize} impl Copy for Point {} impl Point {method read() -> usize ensures(result == self.value) {self.value}} fn main() -> usize ensures(result == 42) {let p = Point {value: 21}; p.read() + p.read()}";
    assert_eq!(verify(copy).unwrap().run().unwrap().to_string(), "42");
    let borrow = "type Item struct {value: usize} impl Item {method& view() -> &usize borrows(&self.value) {&self.value}} fn main() -> usize {let item = Item {value: 42}; let pointer = &item; *pointer.view()}";
    assert_eq!(verify(borrow).unwrap().run().unwrap().to_string(), "42");
    let stale = borrow.replace(
        "*pointer.view()",
        "let view = pointer.view(); drop(item); *view",
    );
    assert!(verify(&stale).is_err());
    let namespace = syntax::join_source_units(&[
        format!("module people; {source}"),
        "fn main() -> usize {let p = people::Person::new(42); p.into_age()}".into(),
    ])
    .unwrap();
    assert_eq!(verify(&namespace).unwrap().run().unwrap().to_string(), "42");
    let destructor = "type Resource struct {done: &bool} impl Drop for Resource {method drop() modifies(self.done) ensures(*self.done) {*self.done = true;}} fn main() -> usize {let done = false; let resource = Resource {done: &done}; drop(resource); if done {42} else {0}}";
    assert_eq!(verify(destructor).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn consuming_an_owning_method_preserves_payload_borrows_until_the_new_owner_drops() {
    let source = include_str!("../../../examples/owned_method_transfer.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("    *borrowed", "    drop(data); *borrowed")).is_err());
    assert!(verify(&source.replace("    *borrowed", "    values.length()")).is_err());
    let header = source
        .replace(
            "    let data = values.into_data();",
            "    let header = &values; let data = values.into_data();",
        )
        .replace("    *borrowed", "    header.length()");
    assert!(verify(&header).is_err());
}

#[test]
fn borrowed_record_methods_have_checked_effects_inside_updates_and_drop() {
    let source = include_str!("../../../examples/update_methods.evg");
    let (program, certificate) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    // Lifting an invariant does not permit a call that assumes that invariant.
    let invalid = "type Pair struct {left: usize, right: usize} where(fact balanced = left == right; balanced); impl Pair {method& read() -> usize {self.left}} fn main() {let pair = Pair {left: 7, right: 7}; update(pair) lifts balanced {pair.left = 42; let observed = pair.read(); pair.right = 42;}}";
    assert!(verify(invalid).is_err());
    // A reference receiver still needs a declared write footprint.
    assert!(verify(&source.replace("modifies(&self.value)", "")).is_err());
    // Reading a valid, borrowed receiver does not recursively run its Drop.
    let destructor = "type Resource struct {value: usize} impl Resource {method& read() -> usize ensures(result == self.value) {self.value}} impl Drop for Resource {method drop() {let observed = self.read(); proof checked: observed == self.value;}} fn main() -> usize {let resource = Resource {value: 42}; drop(resource); 42}";
    let (value, events) = verify(destructor).unwrap().run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
    // Place projections must inspect effects hidden in an index expression.
    let hidden = "type Resource struct {} impl Drop for Resource {method drop() {}} fn hidden() -> usize ensures(result == 0) {let resource = Resource {}; 0} type Data struct {items: array(usize, 1)} fn read(data: &Data) -> usize {data.items[hidden()]} impl Drop for Data {method drop() {let observed = read(&self);}}";
    let error = verify(hidden).unwrap_err();
    assert!(error.contains("ownership-free"), "{error}");
}

#[test]
fn borrowed_temporary_methods_keep_statement_lifetimes_and_cleanup() {
    let source = include_str!("../../../examples/temporary_methods.evg");
    let (program, certificate) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Item"]);
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    let declarations = source.split("fn main()").next().unwrap();
    let within = format!("{declarations} fn main() -> usize {{let dropped = false; *Item::new(&dropped).view() + 1}}");
    assert_eq!(verify(&within).unwrap().run().unwrap().to_string(), "42");
    for body in [
        "let dropped = false; let view = Item::new(&dropped).view(); *view",
        "let dropped = false; let view = &Item::new(&dropped).value; *view",
        "let dropped = false; let view = Item::new(&dropped).view(); proof stale: view == view; 42",
    ] {
        let error = verify(&format!("{declarations} fn main() -> usize {{{body}}}")).unwrap_err();
        assert!(error.contains("never"), "{error}");
    }
    let conditional = format!("{declarations} fn choose(flag: bool) -> usize {{let dropped = false; let value = (if flag {{Item::new(&dropped)}} else {{Item {{value: 41, dropped: &dropped}}}}).read(); if dropped {{value + 1}} else {{0}}}} fn main() -> usize {{choose(false)}}");
    assert_eq!(
        verify(&conditional).unwrap().run().unwrap().to_string(),
        "42"
    );
    // Even a Copy value without Drop owns its temporary storage lifetime.
    let copy = "type Point struct {value: usize} impl Copy for Point {} impl Point {fn new() -> Self {Self {value: 42}} method& view() -> &usize borrows(&self.value) {&self.value}} fn main() -> usize {let view = Point::new().view(); *view}";
    assert!(verify(copy).is_err());
    let once = format!("{declarations} fn make(count: &usize, dropped: &bool) -> Item where(*count < usize::MAX) modifies(count) borrows(dropped: dropped) ensures(*count == old(*count) + 1 && result.value == 41 && result.dropped == dropped) {{*count = *count + 1; Item::new(dropped)}} fn main() -> usize {{let count: usize = 0; let dropped = false; let value = make(&count, &dropped).read(); if count == 1 && dropped {{value + 1}} else {{0}}}}");
    let (value, events) = verify(&once).unwrap().run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Item"]);
}

#[test]
fn struct_where_clauses_accept_unparenthesized_self_projections() {
    let declaration = "type NonZero struct {data: usize} where self.data != 0;";
    assert!(verify(&format!("{declaration} fn main() -> usize {{0}}")).is_ok());
    let good = format!("{declaration} fn main() -> usize {{let n = NonZero {{data: 42}}; n.data}}");
    assert_eq!(verify(&good).unwrap().run().unwrap().to_string(), "42");
    for body in [
        "let n = NonZero {data: 0}; 0",
        "let n = NonZero {data: 42}; n.data = 0; 0",
        "let n = NonZero {data: 42}; let p = &n.data; *p = 0; 0",
    ] {
        assert!(
            verify(&format!("{declaration} fn main() -> usize {{{body}}}")).is_err(),
            "{body}"
        );
    }
}

#[test]
fn dependent_runtime_lengths_are_inferred_from_actual_array_types() {
    let functions = "fn first(length: usize, data: linear_plane(usize, length)) -> usize where length > 0 {(*data)[0]} fn same(length: usize, a: linear_plane(usize, length), b: linear_plane(usize, length)) -> usize where length > 0 {(*a)[0]}";
    let source = format!(
        "{functions} fn main() -> usize {{let data: array(usize, 2) = [42, 7]; first(&data)}}"
    );
    let (program, certificate) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    let dynamic = format!("{functions} fn forward(n: usize, data: linear_plane(usize, n)) -> usize where n > 0 {{first(data)}} fn main() -> usize {{let data: array(usize, 2) = [42, 7]; forward(&data)}}");
    assert_eq!(verify(&dynamic).unwrap().run().unwrap().to_string(), "42");
    let mismatch = format!("{functions} fn main() -> usize {{let a: array(usize, 1) = [21]; let b: array(usize, 2) = [21, 0]; same(&a, &b)}}");
    assert!(verify(&mismatch).is_err());
    let constructor = "type NonZero struct {data: usize} where self.data != 0; impl NonZero {fn new(x: usize) -> Self where x != 0 {return Self {data: x}}} fn main() -> usize {let x = NonZero::new(1); 0}";
    assert!(verify(constructor).is_ok());
    assert!(verify(&constructor.replace("new(1)", "new(0)"))
        .unwrap_err()
        .contains("precondition of NonZero::new"));
}

#[test]
fn nonzero_addition_uses_mathematical_bounds_for_machine_arithmetic() {
    let source = include_str!("../../../examples/nonzero.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("new(10)", "new(0)")).is_err());
}

#[test]
fn ideal_integer_spelling_and_named_constructor_proofs() {
    let source = include_str!("../../../examples/nonzero_proof.evg");
    assert!(verify(source).is_ok());
    assert!(verify("ideal fn identity(n: integer) -> integer {n}").is_ok());
    assert!(verify("ideal fn identity(n: int) -> int {n}").is_err());
    assert!(verify("fn main() -> integer {0}").is_err());
    assert!(verify("fn main() -> usize {integer(0)}").is_err());
}

#[test]
fn return_provenance_errors_explain_the_required_surviving_planes() {
    let local = "fn foo() -> &usize {let x: usize = 0; &x} fn main() -> usize {0}";
    let error = verify(local).unwrap_err();
    assert!(error.contains("local plane"), "{error}");
    assert!(error.contains("local storage ends"), "{error}");
    let missing = "fn foo(x: &usize) -> &usize {x}";
    let error = verify(missing).unwrap_err();
    assert!(
        error.contains("surviving planes") && error.contains("borrows contract"),
        "{error}"
    );
    let extra = "fn foo(x: &usize) -> usize borrows(x) {*x}";
    assert!(verify(extra)
        .unwrap_err()
        .contains("return type contains no references"));
    let good = "fn foo(x: &usize) -> &usize borrows(x) {x} fn main() -> usize {let x: usize = 42; *foo(&x)}";
    assert_eq!(verify(good).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn anonymous_proofs_check_goals_without_named_witnesses() {
    let source = include_str!("../../../examples/anonymous_proofs.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("x = x + 42", "x = x + 43")).is_err());
    let failed_claim = "fn process(x: usize) where x == 42 {} fn main() -> usize {let x: usize = 43; process(x); proof _: x == 42 by {trustme}; 0}";
    assert!(verify(failed_claim)
        .unwrap_err()
        .contains("precondition of process"));
    let stale = "fn process(x: usize) where x == 42 {} fn test(x: usize) {fact known = x == 42; proof assume: known by {trustme}; x = x + 1; process(x);} fn main() {}";
    assert!(verify(stale)
        .unwrap_err()
        .contains("precondition of process"));
    let named = "fn main() -> usize {proof saved: true; proof true by {exact saved}; 42}";
    assert_eq!(verify(named).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn returned_reference_fields_keep_independent_plane_provenance() {
    let source = include_str!("../../../examples/borrowed_fields.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for invalid in [
        source.replace("borrows(data: data, data2: data2)", "borrows(data: data)"),
        source.replace(
            "Self {data: data, data2: data2}",
            "Self {data: data2, data2: data}",
        ),
        source.replace("Self {data: data, data2: data2}", "Self {data: data}"),
        source.replace("    *data2", "    *data"),
        source.replace("    drop(first);", "    drop(second);"),
    ] {
        assert!(verify(&invalid).is_err(), "{invalid}");
    }
    // Multiple fields may share one origin; both contracts are checked.
    let shared = source
        .replace("foo(&*first, &*second)", "foo(&*second, &*second)")
        .replace("bar.data == &*first", "bar.data == &*second");
    assert_eq!(verify(&shared).unwrap().run().unwrap().to_string(), "42");
}
#[test]
fn union_borrowed_storage_waits_for_conditional_provenance() {
    for source in [
        "fn consume(value: &usize | bool) {}",
        "type View struct {value: &usize} fn consume(value: View | bool) {}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("conditional borrow footprints"), "{error}");
    }
}
