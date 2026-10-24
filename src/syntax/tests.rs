//! Parser acceptance, rejection, and syntax-depth regressions.

use super::*;

#[test]
fn module_scopes_are_closed_and_names_are_qualified_once() {
    let program = parse("module a {opaque type Item struct {n: usize} fn get() -> Item {Item {n: 42}}} fn main() -> usize {let item: a::Item = a::get(); 42}").unwrap();
    assert_eq!(program.structs[0].name, "a::Item");
    assert!(program.structs[0].opaque);
    assert_eq!(program.functions[0].name, "a::get");
    assert!(
        matches!(&program.functions[0].result.kind, Kind::Record(name, _) if name == "a::Item")
    );
    for source in [
        "module a {module b {fn f() -> usize {0}}}",
        "module a {fn f() -> usize {0}} module a {fn g() -> usize {0}}",
        "module a {fn f() -> usize {0}",
        "opaque type Item struct {} fn main() -> usize {0}",
        "module usize {fn f() -> usize {0}}",
    ] {
        assert!(parse(source).is_err(), "{source}");
    }
    assert!(parse(&format!("fn {}() -> usize {{0}}", "x".repeat(257))).is_err());
}

#[test]
fn parses_calls_branches_and_arrays() {
    let f = parse("fn main() -> nat { let a: [nat; 2] = [1, 2]; if true { f(a[0]) } else { 3 } }")
        .unwrap();
    assert!(matches!(f.functions[0].result.kind, Kind::If(..)));
}

#[test]
fn rejects_flat_chains_before_the_expression_tree_can_overflow() {
    for expression in [
        std::iter::repeat_n("1", 300)
            .collect::<Vec<_>>()
            .join(" + "),
        format!("x{}", ".field".repeat(300)),
        format!("x{}", "[0]".repeat(300)),
        format!("x{}", "::known".repeat(300)),
    ] {
        let error = parse(&format!("fn main() -> usize {{{expression}}}")).unwrap_err();
        assert!(error.contains("expression tree depth limit"), "{error}");
    }
    assert!(parse(&format!(
        "fn main() -> usize {{{}}}",
        std::iter::repeat_n("1", 32).collect::<Vec<_>>().join(" + ")
    ))
    .is_ok());
}

#[test]
fn rejects_truncated_proofs_and_deep_syntax() {
    assert!(parse("fn f() -> nat { 1 } proof {").is_err());
    let s = format!(
        "fn f() -> nat {{ {}1{} }}",
        "(".repeat(200),
        ")".repeat(200)
    );
    assert!(parse(&s).is_err());
}
