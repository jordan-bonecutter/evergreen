use super::*;

fn check(source: &str, expected: &str) {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert_eq!(program.run().unwrap().to_string(), expected);
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn selected_references_read_the_original_plane_after_value_changes() {
    check("fn read_selected(a: &usize, b: &usize, flag: bool) -> usize ensures result == (if flag {*a} else {*b}) {let selected = if flag {a} else {b}; *selected} fn main() -> usize ensures result == 42 {let a: usize = 7; let b: usize = 42; read_selected(&a, &b, false)}", "42");
    check("fn main() -> usize ensures result == 42 {let a: usize = 7; let b: usize = 42; let selected = if a > b {&a} else {&b}; a = 100; *selected}", "42");
    check("fn read(value: &usize) -> usize ensures result == *value {*value} fn choose(a: &usize, b: &usize, flag: bool) -> usize ensures result == (if flag {*a} else {*b}) {let selected = if flag {a} else {b}; read(selected)} fn main() -> usize ensures result == 42 {let a: usize = 7; let b: usize = 42; choose(&a, &b, false)}", "42");
}

#[test]
fn selected_reference_identity_matches_its_guarded_origins() {
    check("fn identity(a: &usize, b: &usize, flag: bool) -> bool ensures result {let selected = if flag {a} else {b}; if flag {selected == a} else {selected == b}} fn main() -> bool {let a: usize = 7; let b: usize = 42; identity(&a, &b, false)}", "true");
    check("type Pair struct {a: usize, b: usize} fn read(flag: bool) -> usize {let pair = Pair {a: 7, b: 42}; let selected = if flag {&pair.a} else {&pair.b}; *selected} fn main() -> usize {read(false)}", "42");
}

#[test]
fn conditional_borrow_contracts_capture_the_entry_selection() {
    check(
        include_str!("../../../../examples/conditional_planes.evg"),
        "42",
    );
    check("fn choose(flag: &bool, a: &usize, b: &usize) -> &usize modifies(flag) borrows(a) when *flag else borrows(b) ensures *flag == !old(*flag) {let selected = *flag; *flag = !*flag; if selected {a} else {b}} fn main() -> usize ensures result == 42 {let flag = true; let a: usize = 42; let b: usize = 7; let selected = choose(&flag, &a, &b); proof changed: !flag; *selected}", "42");
    check("type Pair struct {left: usize, right: usize} fn max(a: &usize, b: &usize) -> &usize borrows(a) when *a >= *b else borrows(b) {if *a >= *b {a} else {b}} fn main() -> usize {let pair = Pair {left: 7, right: 42}; *max(&pair.left, &pair.right)}", "42");
    check("type Views struct {first: &usize, second: &usize} fn views(a: &usize, b: &usize, left: bool, right: bool) -> Views borrows(first: if left {a} else {b}, second: if right {a} else {b}) {Views {first: if left {a} else {b}, second: if right {a} else {b}}} fn main() -> usize {let a: usize = 7; let b: usize = 42; let selected = views(&a, &b, false, true); *selected.first + *selected.second - 7}", "42");
    check("fn set(value: &usize) modifies(value) ensures *value == 42 {*value = 42;} fn main() -> usize ensures result == 42 {let a: usize = 7; let b: usize = 0; let selected = if false {&a} else {&b}; set(selected); b}", "42");
}

#[test]
fn conditional_borrows_reject_wrong_origins_even_with_admissions() {
    for body in [
        "if *a >= *b {b} else {a}",
        "let local: usize = 42; if *a >= *b {&local} else {b}",
        "proof cheat: false by {trustme}; if *a >= *b {b} else {a}",
    ] {
        let source = format!("fn wrong(a: &usize, b: &usize) -> &usize borrows(a) when *a >= *b else borrows(b) {{{body}}}");
        assert!(verify(&source).is_err(), "accepted {source}");
    }
}

#[test]
fn selected_value_admissions_stay_in_the_selected_data_flow() {
    let prefix = "fn needs42(n: usize) where n == 42 {} fn work(a: &usize, b: &usize, flag: bool) modifies(a, b) {let selected = if flag {a} else {b}; proof assumed: *selected == 42 by {trustme}; needs42(*selected);";
    let good = format!("{prefix} }}");
    let (program, bundle) = prove(&good).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        verify_with_certificate(&good, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for suffix in [
        "*a = 43; *b = 43; needs42(*selected);",
        "let opposite = if flag {b} else {a}; needs42(*opposite);",
    ] {
        let bad = format!("{prefix} {suffix} }}");
        assert!(verify(&bad).is_err(), "accepted {bad}");
    }
    let bad = "fn needs42(n: usize) where n == 42 {} fn wrong(flag: bool) {let a: usize = 43; let b: usize = 43; let selected = if flag {&a} else {&b}; proof assumed: *selected == 42 by {trustme}; if flag {needs42(b)} else {needs42(a)};}";
    assert!(verify(bad).is_err());
    let partial = format!("{prefix} *a = 42; needs42(*selected); }}");
    let (program, bundle) = prove(&partial).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        verify_with_certificate(&partial, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn conditional_reference_liveness_follows_the_selected_generation() {
    check("fn choose(flag: bool) -> usize {let a: plane(usize) = alloc(7); let b: plane(usize) = alloc(42); let selected = if flag {&*a} else {&*b}; drop(a); if flag {0} else {*selected}} fn main() -> usize {choose(false)}", "42");
    for proof in ["", "proof wrong: !flag by {trustme};"] {
        let source = format!("fn wrong(flag: bool) -> usize {{let a: plane(usize) = alloc(7); let b: plane(usize) = alloc(42); let selected = if flag {{&*a}} else {{&*b}}; drop(a); let replacement: plane(usize) = alloc(99); {proof} *selected}}");
        let error = verify(&source).unwrap_err();
        assert!(error.contains("never"), "{error}\n{source}");
    }
}
