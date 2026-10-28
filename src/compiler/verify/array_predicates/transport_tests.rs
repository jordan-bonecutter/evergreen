use super::*;

#[test]
fn current_call_ranges_can_be_restricted_without_losing_their_dependencies() {
    let source = "fn copy(a: &[u8; 8], b: &[u8; 8]) modifies(b) {
        arrays::copy_range(a, b, 0, 8);
        proof selected: forall(i: integer) where(2 <= i && i < 5) {(*b)[i] == old(*a)[i]} by {intro i; omega};
    }";
    let (program, bundle) = prove(source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for bad in [
        source.replace("proof selected:", "(*b)[3] = 42; proof selected:"),
        source.replace("(*b)[i] == old(*a)[i]", "(*b)[i] == 42"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
    let admitted = "fn check(a: &[u8; 8]) {proof given: forall(i: integer) where(0 <= i && i < 8) {(*a)[i] == 42} by {trustme}; proof selected: forall(i: integer) where(2 <= i && i < 5) {(*a)[i] == 42} by {intro i; omega};}";
    assert!(verify(admitted).is_err());
}

#[test]
fn joined_ranges_require_the_original_branch_and_revision() {
    let source = "fn fill_when(data: &[u8; 4], flag: bool) modifies(data) {
        if flag {arrays::fill_range(data, 0, 4, 7);} else {};
        if flag {
            proof selected: forall(i: integer) where(0 <= i && i < 4) {(*data)[i] == 7} by {intro i; omega};
            proof _: (*data)[2] == 7;
        } else {};
    }";
    let (program, bundle) = prove(source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for bad in [
        source.replace("if flag {\n", "if !flag {\n"),
        source.replace("if flag {\n", "(*data)[1] = 8; if flag {\n"),
        source.replace("if flag {\n", "flag = !flag; if flag {\n"),
        source.replace("arrays::fill_range(data, 0, 4, 7);", "proof assume: forall(i: integer) where(0 <= i && i < 4) {(*data)[i] == 7} by {trustme};"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
    let nested = source
        .replace("flag: bool)", "flag: bool, outer: bool)")
        .replace(
            "if flag {arrays::fill_range(data, 0, 4, 7);} else {};",
            "if outer {if flag {arrays::fill_range(data, 0, 4, 7);} else {};} else {};",
        )
        .replace("if flag {\n", "if outer && flag {\n");
    let (_, bundle) = prove(&nested).unwrap();
    verify_with_certificate(&nested, &bundle).unwrap();
}

#[test]
fn conditional_range_contracts_require_a_checked_case_and_current_storage() {
    let source = "fn fill_when(data: &[u8; 4], flag: bool) modifies(data)
        ensures (if flag {forall(i: integer) where(0 <= i && i < 4) {(*data)[i] == 7}} else {true}) {
        if flag {arrays::fill_range(data, 0, 4, 7);} else {};
    }
    fn check(data: &[u8; 4]) modifies(data) {
        fill_when(data, true);
        proof _: (*data)[2] == 7;
    }";
    let (program, bundle) = prove(source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for bad in [
        source.replace("fill_when(data, true)", "fill_when(data, false)"),
        source.replace(
            "proof _: (*data)[2] == 7;",
            "(*data)[2] = 8; proof _: (*data)[2] == 7;",
        ),
        source.replace("proof _: (*data)[2] == 7;", "proof _: (*data)[2] == 8;"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}
