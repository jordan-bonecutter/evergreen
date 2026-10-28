use super::*;

fn predicate(symbol: &str, arguments: Vec<Linear>) -> Formula {
    Formula::Predicate {
        symbol: symbol.into(),
        arguments,
    }
}

#[test]
fn predicate_substitution_and_free_variables_follow_every_argument() {
    let input = predicate(
        "read/v1",
        vec![
            Linear::variable("i").scale(2).unwrap(),
            Linear::variable("outer"),
        ],
    );
    let expected = predicate(
        "read/v1",
        vec![Linear::number(14), Linear::variable("outer")],
    );
    assert_eq!(input.substitute("i", &Linear::number(7)).unwrap(), expected);
    let formula = Formula::Forall {
        variable: "i".into(),
        domain: Box::new(Formula::True),
        body: Box::new(input),
    };
    assert_eq!(
        formula.free_variables().unwrap(),
        BTreeSet::from(["outer".into()])
    );
    let renamed = Formula::Forall {
        variable: "j".into(),
        domain: Box::new(Formula::True),
        body: Box::new(predicate(
            "read/v1",
            vec![
                Linear::variable("j").scale(2).unwrap(),
                Linear::variable("outer"),
            ],
        )),
    };
    assert!(formula.alpha_equal(&renamed));
    assert!(!formula.alpha_equal(&predicate("read/v1", vec![Linear::variable("i")])));
}

#[test]
fn predicate_encoding_keeps_symbols_arity_argument_order_and_values_distinct() {
    let formulas = [
        predicate("read/v1", vec![]),
        predicate("read/v1", vec![Linear::number(1)]),
        predicate("read/v2", vec![Linear::number(1)]),
        predicate("read/v1", vec![Linear::number(2)]),
        predicate("read/v1", vec![Linear::number(1), Linear::number(2)]),
        predicate("read/v1", vec![Linear::number(2), Linear::number(1)]),
    ];
    let encoded = formulas
        .iter()
        .map(|p| {
            let mut bytes = Vec::new();
            p.encode(&mut bytes);
            bytes
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(encoded.len(), formulas.len());
}

#[test]
fn predicate_storage_and_substitution_are_bounded_before_expansion() {
    assert!(predicate("", vec![]).storage_weight().is_err());
    assert!(predicate(&"s".repeat(MAX_VALUE_WORK), vec![])
        .storage_weight()
        .is_err());
    assert!(predicate("wide", vec![Linear::number(0); MAX_VALUE_WORK])
        .storage_weight()
        .is_err());
    let input = predicate("read", vec![Linear::variable("i"); 1024]);
    let replacement = Linear {
        constant: 0,
        terms: (0..512).map(|i| (format!("v{i}"), 1)).collect(),
    };
    assert!(input
        .substitute("i", &replacement)
        .unwrap_err()
        .contains("work limit"));
    let input = predicate("read", vec![Linear::variable("i").scale(2).unwrap()]);
    assert!(input
        .substitute("i", &Linear::number(i128::MAX))
        .unwrap_err()
        .contains("overflow"));
}
