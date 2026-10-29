use super::super::*;
use crate::shared::diagnostics::SourceOrigin;

#[test]
fn equality_diagnostics_hide_the_pair_of_internal_inequalities() {
    let value = Linear::variable("value");
    let equal = Formula::Ge(value.clone()).and(Formula::Ge(value.scale(-1).unwrap()));
    assert_eq!(super::obligation(&equal, &BTreeMap::new()), "value == 0");
    assert_eq!(
        super::obligation(&Formula::Not(Box::new(equal)), &BTreeMap::new()),
        "value != 0"
    );
    let bounded =
        Formula::Ge(value.clone()).and(Formula::Ge(Linear::number(10).sub(&value).unwrap()));
    assert_eq!(
        super::obligation(&bounded, &BTreeMap::new()),
        "(value >= 0 && value <= 10)"
    );

    let source = "type NonZero struct {data: usize} where data != 0; impl NonZero {fn new(x: usize) -> Self where x != 0 {return NonZero {data: x};}} fn main() -> usize {let my_nonzero = NonZero::new(usize::MAX + 1); 0}";
    let error = verify_diagnostic(source).unwrap_err();
    assert_eq!(error.requirement.unwrap().text, "(x != 0)");
    let obligation = error.obligation.unwrap();
    assert_eq!(obligation, "unknown usize != 0");
    assert!(!obligation.contains("&&"), "{obligation}");
    verify(&source.replace("usize::MAX + 1", "usize::MAX")).unwrap();
}

#[test]
fn typed_unknowns_keep_distinct_values_distinguishable() {
    let first = Linear::variable("evg_1");
    let second = Linear::variable("evg_2");
    let goal = equal(&first, &second).unwrap();
    let ty = Ty::Machine(syntax::MachineInt::parse("u8").unwrap());
    let types = BTreeMap::from([("evg_1".into(), ty.clone()), ("evg_2".into(), ty)]);
    assert_eq!(
        super::obligation(&goal, &types),
        "unknown u8 #1 - unknown u8 #2 == 0"
    );
    assert_eq!(
        super::obligation(&Formula::Ge(first), &types),
        "unknown u8 >= 0"
    );
}

#[test]
fn unknown_machine_bounds_are_printed_as_source_comparisons() {
    let source = "fn increment(n: usize) -> usize where n < usize::MAX ensures result == n + 1 {n + 1} fn main() -> usize {increment(usize::MAX + 1)}";
    let error = verify_diagnostic(source).unwrap_err();
    assert_eq!(
        error.obligation.as_deref(),
        Some("unknown usize < usize::MAX")
    );
    assert_eq!(
        error.source_obligation.as_deref(),
        Some("((usize::MAX + 1) < usize::MAX)")
    );
    assert_eq!(error.requirement.unwrap().text, "(n < usize::MAX)");
}

#[test]
fn source_obligations_preserve_proof_syntax_and_substitute_arguments_simultaneously() {
    let source = "fn require(a: usize, b: usize) where a < b {} fn main() {let b: usize = 42; require(b, 1);}";
    let error = verify_diagnostic(source).unwrap_err();
    assert_eq!(error.source_obligation.as_deref(), Some("(b < 1)"));
    let error = verify_diagnostic("fn main() {let x: usize = 42; proof _: x == 7;}").unwrap_err();
    assert_eq!(error.source_obligation.as_deref(), Some("(x == 7)"));
    let error = verify_diagnostic("fn main() {not_declared();}").unwrap_err();
    assert!(error.source_obligation.is_none());
}

#[test]
fn generic_invariant_failures_retain_callsite_definition_and_obligation() {
    let source = syntax::join_source_units(&[
        "type MyPair<T> struct {data: [T; 2]} where self.data[0] < self.data[1];".into(),
        "fn main() {\n    let pair = MyPair::<usize> {data: [2, 1]};\n}".into(),
    ])
    .unwrap();
    let error = verify_diagnostic(&source).unwrap_err();
    assert_eq!(error.origin, SourceOrigin::Input(1));
    assert_eq!(error.line, Some(2));
    let requirement = error.requirement.unwrap();
    assert_eq!(requirement.kind, "invariant");
    assert_eq!(requirement.origin, SourceOrigin::Input(0));
    assert_eq!(requirement.line, 1);
    assert!(
        requirement.text.contains("self.data[0] < self.data[1]"),
        "{}",
        requirement.text
    );
    assert!(error.obligation.is_some());
}

#[test]
fn callee_preconditions_keep_the_callsite_and_the_declared_requirement() {
    let source = syntax::join_source_units(&[
        "fn require_positive(n: usize) where n > 0 {}".into(),
        "fn main() {\n    require_positive(0);\n}".into(),
    ])
    .unwrap();
    let error = verify_diagnostic(&source).unwrap_err();
    assert_eq!(error.origin, SourceOrigin::Input(1));
    assert_eq!(error.line, Some(2));
    let requirement = error.requirement.unwrap();
    assert_eq!(requirement.kind, "precondition");
    assert_eq!(requirement.origin, SourceOrigin::Input(0));
    assert_eq!(requirement.text, "(n > 0)");
    assert_eq!(error.obligation.as_deref(), Some("-1 >= 0"));
}

#[test]
fn diagnostics_do_not_survive_into_an_unrelated_error_or_verification() {
    let source = "fn good() {proof _: false || true;} fn main() {no_such_function();}";
    let error = verify_diagnostic(source).unwrap_err();
    assert!(error.message.contains("unknown function"));
    assert!(error.obligation.is_none());
    assert!(error.requirement.is_none());
    assert!(verify_diagnostic("fn main() -> usize {42}").is_ok());
    let error = verify_diagnostic("fn main() {missing();}").unwrap_err();
    assert!(error.message.contains("unknown function"));
    assert!(error.obligation.is_none());
}

#[test]
fn diagnostic_rendering_is_bounded_and_preserves_pointer_projection_precedence() {
    use crate::syntax::{Expr, Kind};
    let pointer = Expr {
        kind: Kind::Unary(
            "*".into(),
            Box::new(Expr {
                kind: Kind::Name("data".into()),
                line: 1,
            }),
        ),
        line: 1,
    };
    let indexed = Expr {
        kind: Kind::Index(
            Box::new(pointer),
            Box::new(Expr {
                kind: Kind::Number(0),
                line: 1,
            }),
        ),
        line: 1,
    };
    assert_eq!(syntax::display::expression(&indexed), "(*data)[0]");
    let value = Expr {
        kind: Kind::Array(
            (0..10000)
                .map(|n| Expr {
                    kind: Kind::Number(n),
                    line: 1,
                })
                .collect(),
        ),
        line: 1,
    };
    let rendered = syntax::display::expression(&value);
    assert!(rendered.len() < 100);
    assert!(rendered.contains('…'));
}
