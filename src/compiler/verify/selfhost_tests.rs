use super::*;

#[test]
fn evergreen_lexer_checks_spans_progress_and_replays_without_search() {
    let source = syntax::join_source_units(&[
        include_str!("../../../selfhost/lexer/lexer.evg").to_owned(),
        include_str!("../../../selfhost/main.evg").replace("import lexer;", ""),
    ])
    .unwrap();
    let (program, bundle) = prove(&source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}
