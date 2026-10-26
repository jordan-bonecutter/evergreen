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

#[test]
fn inline_array_and_runtime_plane_spellings_are_distinct() {
    let source = "fn first(n: usize, data: linear_plane(u8, n), fixed: array(u16, 2)) -> u8 where(n > 0) {(*data)[0]} fn main() -> u8 {let data: array(u8, 1) = [42]; first(1, &data, [7, 9])}";
    let parsed = parse(source).unwrap();
    assert!(
        matches!(&parsed.functions[0].params[1].1, Type::Ref(inner) if matches!(inner.as_ref(), Type::Array(..)))
    );
    assert!(
        parse("fn bad(n: usize, data: array(u8, n)) {} fn main() {}")
            .unwrap_err()
            .contains("compile-time extent")
    );
    assert!(parse("fn main() {let owner: plane(u8, 3) = alloc(3, 0);}").is_ok());
}

#[test]
fn file_modules_do_not_require_wrapper_indentation() {
    let program = parse("module sample; opaque type Item struct {value: usize} fn value(item: &Item) -> usize {item.value}").unwrap();
    assert_eq!(program.functions[0].name, "sample::value");
    assert_eq!(program.structs[0].name, "sample::Item");
    assert!(parse("module sample; fn f() {} }").is_err());
    assert!(parse("fn f() {} module sample; fn g() {}").is_err());
    assert!(parse("module sample; module other; fn f() {}").is_err());
}

#[test]
fn source_units_share_module_names_without_leaking_file_scope() {
    let source = join_source_units(&[
        "module sample; type Item struct {value: usize} fn first() -> usize {42}".into(),
        "module sample; fn second() -> usize {first()}".into(),
        "fn main() -> usize {sample::second()}".into(),
    ])
    .unwrap();
    let program = parse(&source).unwrap();
    assert_eq!(program.functions[1].name, "sample::second");
    assert_eq!(program.functions[2].name, "main");
    assert!(
        matches!(&program.functions[1].result.kind, Kind::Call(name, _) if name == "sample::first")
    );
    assert!(join_source_units(&["fn main() {}\u{1e}".into()]).is_err());
}

#[test]
fn imports_are_explicit_package_dependencies_before_declarations() {
    let program = parse("module demo; import vec; fn answer() -> usize {42}").unwrap();
    assert!(program.imports.contains("vec"));
    for bad in [
        "module demo; import vec; import vec; fn answer() {}",
        "module demo; fn answer() {} import vec;",
        "import vec; module demo; fn answer() {}",
    ] {
        assert!(
            parse(bad).is_err(),
            "accepted invalid import placement: {bad}"
        );
    }
}
