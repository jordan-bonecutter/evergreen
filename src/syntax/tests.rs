//! Parser acceptance, rejection, and syntax-depth regressions.

use super::*;

#[test]
fn strings_decode_to_utf8_bytes_and_keep_following_source_lines() {
    let source = "fn main() {let text = \"λ🦀\\n\\r\\t\\0\\\\\\\"\\x41\\u{1F980}\";}";
    let program = parse(source).unwrap();
    let Statement::Let { value, .. } = &program.functions[0].body[0] else {
        panic!("missing string binding");
    };
    assert_eq!(
        value.kind,
        Kind::Bytes("λ🦀\n\r\t\0\\\"A🦀".as_bytes().to_vec())
    );
    let multiline = parse("fn main() {let text = \"one\ntwo\";\n42}").unwrap();
    assert_eq!(multiline.functions[0].result.line, 3);
    let quoted_syntax =
        parse("fn main() {let text = \"// not a comment: module a { }\";}").unwrap();
    assert_eq!(quoted_syntax.functions.len(), 1);
}

#[test]
fn invalid_string_escapes_cannot_create_non_utf8_literals() {
    for literal in [
        r#""\x80""#,
        r#""\xFF""#,
        r#""\xG0""#,
        r#""\x0""#,
        r#""\u{}""#,
        r#""\u{D800}""#,
        r#""\u{110000}""#,
        r#""\u{1234567}""#,
        r#""\u1234""#,
        r#""\z""#,
        "\"unterminated",
        "\"escape\\",
    ] {
        let source = format!("fn main() {{let text = {literal};}}");
        let error = parse(&source).unwrap_err();
        assert!(error.contains("line 1:"), "{error}");
    }
}

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
    assert!(parse("fn main() {let owner: unique(u8, 3) = alloc(3, 0);}").is_ok());
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

#[test]
fn mistaken_refined_alias_reports_the_supported_alternative() {
    let error = parse("type NonZero = usize where self != 0; fn main() -> usize {0}").unwrap_err();
    assert!(error.contains("type aliases are not supported"), "{error}");
    assert!(error.contains("struct with a where clause"), "{error}");
}
#[test]
fn nested_while_statements_have_a_parser_depth_limit() {
    let source = format!(
        "fn main() {{{}{}}}",
        "while false invariant(true) {".repeat(129),
        "}".repeat(129)
    );
    assert!(super::parse(&source).unwrap_err().contains("nesting limit"));
}
#[test]
fn raw_union_types_flatten_members_and_bind_reference_prefixes() {
    let program = parse("module data {type Payload struct {value: u8} type Slot struct {a: Payload | shape(Payload), b: &usize | bool, c: &(usize | bool), d: u8 | (u16 | u32)}}").unwrap();
    let slot = &program.structs[1];
    let Type::Union(members) = &slot.fields[0].1 else {
        panic!("missing union")
    };
    assert_eq!(members[0], Type::Named("data::Payload".into()));
    assert_eq!(
        members[1],
        Type::Shape(Box::new(Type::Named("data::Payload".into())))
    );
    assert!(
        matches!(&slot.fields[1].1, Type::Union(members) if matches!(&members[0], Type::Ref(_)))
    );
    assert!(
        matches!(&slot.fields[2].1, Type::Ref(inner) if matches!(inner.as_ref(), Type::Union(members) if members.len() == 2))
    );
    assert!(matches!(&slot.fields[3].1, Type::Union(members) if members.len() == 3));
    for bad in [
        "type Bad struct {data: shape(shape(usize))}",
        "type Bad struct {data: usize |}",
    ] {
        assert!(parse(bad).is_err());
    }
}
