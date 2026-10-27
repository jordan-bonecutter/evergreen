use super::*;

#[test]
fn source_rc_automatic_drop_preserves_the_counter_and_payload_plane() {
    let source = include_str!("../../../../examples/rc_drop.evg");
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
fn resource_case_continuations_preserve_lifetimes_moves_and_returned_claims() {
    for source in [
        "fn release(value: owner(usize), count: usize) where nat(count) == owners(value) {if count == 1 {let unique = recover_owner(value); drop(unique);} else {release_owner(value);}} fn forward(value: owner(usize), count: usize) where nat(count) == owners(value) {release(value, count);} fn main() -> usize {let unique: plane(usize) = alloc(42); let first = share_owner(unique); let second = duplicate_owner(&first); let view = &*first; forward(second, 2); let answer = *view; forward(first, 1); answer}",
        "fn duplicate(value: &owner(usize), flag: bool) -> owner(usize) {if flag {duplicate_owner(value)} else {duplicate_owner(value)}} fn main() -> usize {let unique: plane(usize) = alloc(42); let first = share_owner(unique); let second = duplicate(&first, false); release_owner(second); *first}",
        "fn consume(value: owner(usize), flag: bool) where owners(value) == 1 {if flag {drop(value);} else {}} fn main() -> usize {let unique: plane(usize) = alloc(7); consume(share_owner(unique), false); 42}",
        "fn consume(value: owner(usize), flag: bool) -> usize where owners(value) == 1 {let view = &*value; if flag {drop(value);} else {} if flag {42} else {*view}} fn main() -> usize {let unique: plane(usize) = alloc(42); consume(share_owner(unique), false)}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn resource_case_proofs_do_not_authorize_dangling_reads_or_copied_claims() {
    for source in [
        "fn release(value: owner(usize), count: usize) -> usize where nat(count) == owners(value) {let view = &*value; if count == 1 {let unique = recover_owner(value); drop(unique);} else {release_owner(value);} *view}",
        "fn consume(value: owner(usize), flag: bool) -> usize where owners(value) == 1 {let view = &*value; if flag {drop(value);} else {} *view}",
        "fn main() -> usize {let first = rc::new(42); let second = first.clone(); let view = first.value(); drop(first); drop(second); *view}",
        "fn main() -> usize {let first = rc::new(42); let second = first.clone(); let handle = &first; drop(first); handle.strong_count()}",
        "fn duplicate(value: &owner(usize), flag: bool) -> owner(usize) {let copy = if flag {duplicate_owner(value)} else {duplicate_owner(value)}; let another = copy; copy}",
        "fn bad(value: owner(usize), count: usize) -> usize where nat(count) == owners(value) {let view = &*value; proof assumed: count > 1 by {trustme}; if count == 1 {let unique = recover_owner(value); drop(unique);} else {release_owner(value);} *view}",
        "fn bad(value: owner(usize), flag: bool) -> usize where owners(value) == 1 {let view = &*value; if flag {drop(value);} else {} flag = false; if flag {42} else {*view}}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn resource_case_replays_preserve_conditional_types() {
    let prefix = "fn bad(value: owner(usize), count: usize, flag: bool) where nat(count) == owners(value) {if count == 1 {let unique = recover_owner(value); drop(unique);} else {release_owner(value);}";
    for expression in [
        "if flag {42} else {false}",
        "if count == 1 {42} else {false}",
        "if flag {alloc([1])} else {alloc([1, 2])}",
    ] {
        let source = format!("{prefix} let inconsistent = {expression};}}");
        let error = verify(&source).unwrap_err();
        assert!(error.contains("same result type"), "{error}");
    }
}

#[test]
fn source_rc_array_cleanup_and_returned_owners_keep_live_counts() {
    for source in [
        "fn main() -> usize {let first = rc::new(42); let group = [first.clone(), first.clone()]; proof three: first.strong_count() == 3; drop(group); proof sole: first.strong_count() == 1; if first.strong_count() == 1 {*first.value()} else {1}}",
        "fn replace(value: rc::Rc) -> rc::Rc where value.strong_count() < usize::MAX {let next = value.clone(); next} fn main() -> usize {let first = rc::new(42); let view = first.value(); let second = replace(first); proof sole: second.strong_count() == 1; if second.strong_count() == 1 {*view} else {1}}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn resource_case_tree_work_is_charged_across_all_replayed_prefixes() {
    let flags = (0..16)
        .map(|i| format!(", flag{i}: bool"))
        .collect::<String>();
    let branches = (0..16)
        .map(|i| format!("if flag{i} {{}} else {{}};"))
        .collect::<String>();
    let source = format!("fn bounded(value: owner(usize), count: usize{flags}) where nat(count) == owners(value) {{if count == 1 {{let unique = recover_owner(value); drop(unique);}} else {{release_owner(value);}} {branches}}}");
    let error = verify(&source).unwrap_err();
    assert!(
        error.contains("work limit") || error.contains("evaluation limit"),
        "{error}"
    );
}

#[test]
fn resource_case_admissions_follow_only_the_selected_actual_continuation() {
    let source = "fn needs(x: usize) where x == 42 {} fn release(value: owner(usize), count: usize, x: usize) where nat(count) == owners(value) {if count == 1 {let unique = recover_owner(value); drop(unique); proof allowed: x == 42 by {trustme}; needs(x);} else {release_owner(value);}} fn clean() -> usize {let unique: plane(usize) = alloc(42); let first = share_owner(unique); let second = duplicate_owner(&first); release(second, 2, 43); *first} fn main() -> usize {clean()}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(
        program
            .function_safety_assumptions("release")
            .unwrap()
            .count(),
        1
    );
    for name in ["clean", "main"] {
        assert_eq!(
            program.function_safety_assumptions(name).unwrap().count(),
            0
        );
    }
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}
