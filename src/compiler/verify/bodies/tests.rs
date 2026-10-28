use super::*;

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
