use super::*;
use crate::syntax::format::test_edit::SourceEdit;

fn replay(source: &str, expected: &str) {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(program.run().unwrap().to_string(), expected);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn returned_nominal_ranges_survive_binding_and_cleanup_but_not_storage_changes() {
    let source = include_str!("../../../../examples/buffer_reallocation.evg");
    replay(source, "42");
    for bad in [
        source.replace_evg("grown.get(1)", "grown.get(2)"),
        source.replace_evg(
            "let view = grown.get(1);",
            "grown.len = 3; let view = grown.get(1);",
        ),
        source.replace_evg(
            "let view = grown.get(1);",
            "let stolen: unique(usize) = move((*grown.data)[0]); let view = grown.get(1);",
        ),
        source.replace_evg("drop(grown);", "drop(grown); let stale = **view;"),
        source.replace_evg("len: len, data: grown", "len: len + 1, data: grown"),
    ] {
        assert!(verify(&bad).is_err(), "accepted {bad}");
    }
}

#[test]
fn fact_and_proof_names_have_lexical_variable_scope() {
    let source = "fn main() -> usize {let x: usize = 42; fact expected = x == 42; proof outer: expected; {proof inner: expected by {exact outer}; proof _: expected by {exact inner};}; proof _: expected by {exact outer}; x}";
    replay(source, "42");
    let escaped = source.replace(
        "}; proof _: expected by {exact outer};",
        "}; proof _: expected by {exact inner};",
    );
    assert!(verify(&escaped).is_err());
    for source in [
        "fn callee() {proof _: true by {exact caller_proof};} fn main() {proof caller_proof: true; callee();}",
        "type Resource struct {} impl Drop for Resource {fn drop(self) {proof _: true by {exact caller_proof};}} fn main() {proof caller_proof: true; let value = Resource {};}",
        "fn main() {{fact local = true; proof witness: local;}; proof _: local;}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn actual_owned_and_aliased_reads_inherit_checked_storage_candidates() {
    let source = "fn read(data: unique(usize, 4)) -> usize {(*data)[2]}
        fn main() -> usize {let data: unique(usize, 4) = alloc(4, 0);
            arrays::fill_range(&*data, 0, 4, 42);
            let observed = read(data); proof _: observed == 42; observed}";
    replay(source, "42");
    let borrowed = "fn read(a: &[usize; 4], b: &[usize; 4]) -> usize {(*b)[2]}
        fn main() -> usize {let data: [usize; 4] = [0, 0, 0, 0];
            arrays::fill_range(&data, 0, 4, 42);
            let observed = read(&data, &data); proof _: observed == 42; observed}";
    replay(borrowed, "42");
    // The actual write invalidates the caller's range, including reads through
    // the aliased input. Returning the new value must not retain the old one.
    let changed = borrowed.replace(
        "-> usize {(*b)[2]}",
        "-> usize modifies(a) {(*a)[2] = 7; (*b)[2]}",
    );
    assert!(verify(&changed).is_err());
    replay(
        &changed.replace("proof _: observed == 42;", "proof _: observed == 7;"),
        "7",
    );
    let admitted = source.replace(
        "arrays::fill_range(&*data, 0, 4, 42);",
        "proof assumed: forall(i: integer) where(0 <= i && i < 4) {(*data)[i] == 42} by {trustme};",
    );
    assert!(verify(&admitted).is_err());
}

#[test]
fn actual_reads_respect_branch_guards_and_do_not_export_inner_call_results() {
    let source = "fn read(data: unique(usize, 4)) -> usize {(*data)[2]}
        fn check(flag: bool) {
            let data: unique(usize, 4) = alloc(4, 0);
            if flag {arrays::fill_range(&*data, 0, 4, 42);} else {};
            if flag {let observed = read(data); proof _: observed == 42;} else {};
        } fn main() -> usize {check(true); check(false); 42}";
    replay(source, "42");
    assert!(verify(&source.replace("if flag {let observed", "if !flag {let observed")).is_err());
    let unrelated = "fn promised() -> usize ensures forall(i: integer) where(0 <= i && i < 4) {i < integer(result)} {42}
        fn owner_call(data: unique(usize, 4)) -> usize {let ignored = promised(); 0}
        fn main() {let data: unique(usize, 4) = alloc(4, 0); let observed = owner_call(data);
            proof _: forall(i: integer) where(0 <= i && i < 4) {i < integer(observed)} by {intro i; omega};}";
    assert!(verify(unrelated).is_err());
}

#[test]
fn isolated_heap_computations_use_checked_contracts_without_replaying_allocations() {
    let source = include_str!("../../../../examples/vec_local_storage.evg");
    replay(source, "42");
    // A caller receives the advertised contract, not the local body's concrete
    // result. Removing the promise cannot leave the result known to be 42.
    let unpromised = source.replace_evg("ensures result == 42", "");
    assert!(verify(&unpromised).is_err());
    let false_promise = source.replace_evg("ensures result == 42", "ensures result == 43");
    assert!(verify(&false_promise).is_err());
}
