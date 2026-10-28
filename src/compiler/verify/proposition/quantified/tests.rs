use super::*;

fn ge(name: &str) -> Formula {
    Formula::Ge(Linear::variable(name))
}

fn forall(name: &str, domain: Formula, body: Formula) -> Formula {
    Formula::Forall {
        variable: name.into(),
        domain: Box::new(domain),
        body: Box::new(body),
    }
}

#[test]
fn free_variables_respect_nested_shadowing_and_sibling_scopes() {
    let formula = forall(
        "i",
        ge("n"),
        forall("i", ge("i"), ge("i")).and(ge("i")).and(ge("outer")),
    )
    .and(ge("i"));
    assert_eq!(
        formula.free_variables().unwrap(),
        BTreeSet::from(["n".into(), "outer".into(), "i".into(),])
    );
    assert!(forall("i", ge("i"), ge("i"))
        .free_variables()
        .unwrap()
        .is_empty());
}

#[test]
fn substitution_preserves_bound_names_and_rejects_capture() {
    let formula = forall("j", ge("j"), ge("i").and(ge("j")));
    assert_eq!(
        formula.substitute("i", &Linear::number(4)).unwrap(),
        forall("j", ge("j"), Formula::Ge(Linear::number(4)).and(ge("j")))
    );
    assert_eq!(
        formula.substitute("j", &Linear::number(9)).unwrap(),
        formula
    );
    assert!(formula
        .substitute("i", &Linear::variable("j"))
        .unwrap_err()
        .contains("capture"));
}

#[test]
fn substitution_checks_coefficient_and_constant_overflow() {
    let formula = Formula::Ge(Linear::variable("i").scale(2).unwrap());
    for term in [
        Linear::number(i128::MAX),
        Linear::variable("j").scale(i128::MAX).unwrap(),
    ] {
        assert!(formula
            .substitute("i", &term)
            .unwrap_err()
            .contains("overflow"));
    }
    let formula = Formula::Ge(
        Linear::variable("i")
            .add(&Linear::number(i128::MAX))
            .unwrap(),
    );
    assert!(formula.substitute("i", &Linear::number(1)).is_err());
}

#[test]
fn substitution_charges_repeated_expansion_before_materializing_it() {
    let mut formula = ge("i");
    for _ in 0..10 {
        // Keep equal children rather than simplifying them with Formula::and.
        formula = Formula::And(Box::new(formula.clone()), Box::new(formula));
    }
    let replacement = Linear {
        constant: 0,
        terms: (0..512).map(|i| (format!("v{i}"), 1)).collect(),
    };
    assert!(formula
        .substitute("i", &replacement)
        .unwrap_err()
        .contains("work limit"));
}

#[test]
fn quantified_names_depth_and_storage_are_bounded() {
    for name in [String::new(), "i".repeat(257)] {
        assert!(forall(&name, Formula::True, Formula::True)
            .storage_weight()
            .is_err());
    }
    let mut deep = Formula::True;
    for _ in 0..128 {
        deep = forall("i", Formula::True, deep);
    }
    assert!(deep.storage_weight().is_err());
    assert!(deep.free_variables().is_err());
    assert!(deep.substitute("i", &Linear::number(0)).is_err());
}
