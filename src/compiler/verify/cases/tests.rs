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
        "fn release(value: shared(usize), count: usize) where nat(count) == owner_count(value) {if count == 1 {let unique: unique(usize) = move(value); drop(unique);} else {leak(value);}} fn forward(value: shared(usize), count: usize) where nat(count) == owner_count(value) {release(move(value), count);} fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let second = first; let view = &*first; forward(move(second), 2); let answer = *view; forward(move(first), 1); answer}",
        "fn duplicate(value: &shared(usize), flag: bool) -> shared(usize) {if flag {*value} else {*value}} fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let second = duplicate(&first, false); leak(second); *first}",
        "fn consume(value: shared(usize), flag: bool) where owner_count(value) == 1 {if flag {let final: unique(usize) = move(value); drop(final);} else {}} fn main() -> usize {let unique: unique(usize) = alloc(7); consume(unique, false); 42}",
        "fn consume(value: shared(usize), flag: bool) -> usize where owner_count(value) == 1 {let view = &*value; if flag {let final: unique(usize) = move(value); drop(final);} else {} if flag {42} else {*view}} fn main() -> usize {let unique: unique(usize) = alloc(42); consume(unique, false)}",
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
        "fn release(value: shared(usize), count: usize) -> usize where nat(count) == owner_count(value) {let view = &*value; if count == 1 {let unique: unique(usize) = move(value); drop(unique);} else {leak(value);} *view}",
        "fn consume(value: shared(usize), flag: bool) -> usize where owner_count(value) == 1 {let view = &*value; if flag {let final: unique(usize) = move(value); drop(final);} else {} *view}",
        "fn main() -> usize {let first = rc::new(42); let second = first.clone(); let view = first.value(); drop(first); drop(second); *view}",
        "fn main() -> usize {let first = rc::new(42); let second = first.clone(); let handle = &first; drop(first); handle.strong_count()}",
        "fn duplicate(value: &shared(usize), flag: bool) -> shared(usize) {let copy = if flag {*value} else {*value}; let another = move(copy); copy}",
        "fn bad(value: shared(usize), count: usize) -> usize where nat(count) == owner_count(value) {let view = &*value; proof assumed: count > 1 by {trustme}; if count == 1 {let unique: unique(usize) = move(value); drop(unique);} else {leak(value);} *view}",
        "fn bad(value: shared(usize), flag: bool) -> usize where owner_count(value) == 1 {let view = &*value; if flag {let final: unique(usize) = move(value); drop(final);} else {} flag = false; if flag {42} else {*view}}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn resource_case_replays_preserve_conditional_types() {
    let prefix = "fn bad(value: shared(usize), count: usize, flag: bool) where nat(count) == owner_count(value) {if count == 1 {let unique: unique(usize) = move(value); drop(unique);} else {leak(value);}";
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
    let source = format!("fn bounded(value: shared(usize), count: usize{flags}) where nat(count) == owner_count(value) {{if count == 1 {{let unique: unique(usize) = move(value); drop(unique);}} else {{leak(value);}} {branches}}}");
    let error = verify(&source).unwrap_err();
    assert!(
        error.contains("work limit") || error.contains("evaluation limit"),
        "{error}"
    );
}

#[test]
fn resource_case_admissions_follow_only_the_selected_actual_continuation() {
    let source = "fn needs(x: usize) where x == 42 {} fn release(value: shared(usize), count: usize, x: usize) where nat(count) == owner_count(value) {if count == 1 {let unique: unique(usize) = move(value); drop(unique); proof allowed: x == 42 by {trustme}; needs(x);} else {leak(value);}} fn clean() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let second = first; release(move(second), 2, 43); *first} fn main() -> usize {clean()}";
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
