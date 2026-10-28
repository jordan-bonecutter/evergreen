use super::*;

fn atom(symbol: &str, arguments: Vec<Linear>) -> Formula {
    Formula::Predicate {
        symbol: symbol.into(),
        arguments,
    }
}

#[test]
fn unfolding_is_a_closed_definition_and_not_a_proof_of_its_predicate() {
    let mut graph = Evidence::default();
    let definition = graph
        .define_predicate(
            "positive".into(),
            vec!["x".into()],
            Formula::Ge(Linear::variable("x")),
        )
        .unwrap();
    let predicate = atom("positive", vec![Linear::number(-1)]);
    let body = Formula::Ge(Linear::number(-1));
    for reverse in [false, true] {
        let (a, b) = if reverse {
            (body.clone(), predicate.clone())
        } else {
            (predicate.clone(), body.clone())
        };
        let law = graph
            .derive(
                Formula::Implies(Box::new(a), Box::new(b)),
                Rule::UnfoldPredicate {
                    definition,
                    reverse,
                },
            )
            .unwrap();
        graph.check_closed(law).unwrap();
        assert!(graph.admissions(law).admissions.is_empty());
        assert!(graph.admissions(law).complete);
    }
    for (goal, rule) in [
        (
            predicate.clone(),
            Rule::UnfoldPredicate {
                definition,
                reverse: true,
            },
        ),
        (
            Formula::Implies(Box::new(Formula::True), Box::new(predicate)),
            Rule::UnfoldPredicate {
                definition,
                reverse: true,
            },
        ),
        (
            Formula::Implies(
                Box::new(atom("other", vec![Linear::number(0)])),
                Box::new(Formula::True),
            ),
            Rule::UnfoldPredicate {
                definition,
                reverse: false,
            },
        ),
        (
            Formula::Implies(Box::new(atom("positive", vec![])), Box::new(Formula::True)),
            Rule::UnfoldPredicate {
                definition,
                reverse: false,
            },
        ),
        (
            Formula::True,
            Rule::UnfoldPredicate {
                definition: DefinitionId(usize::MAX),
                reverse: false,
            },
        ),
    ] {
        let before = (
            graph.nodes.len(),
            graph.edges,
            graph.storage_weight,
            graph.rule_work,
        );
        assert!(graph.derive(goal, rule).is_err());
        assert_eq!(
            before,
            (
                graph.nodes.len(),
                graph.edges,
                graph.storage_weight,
                graph.rule_work
            )
        );
    }
}

#[test]
fn definitions_are_closed_immutable_and_acyclic() {
    let mut graph = Evidence::default();
    graph
        .define_predicate(
            "base".into(),
            vec!["x".into()],
            Formula::Ge(Linear::variable("x")),
        )
        .unwrap();
    let first = graph.definitions.entries.len();
    for (symbol, params, body) in [
        ("base", vec!["x".into()], Formula::False),
        (
            "capture",
            vec!["x".into()],
            Formula::Ge(Linear::variable("unlisted")),
        ),
        ("duplicate", vec!["x".into(), "x".into()], Formula::True),
        ("invalid", vec![String::new()], Formula::True),
        ("self", vec![], atom("self", vec![])),
        ("future", vec![], atom("not-yet-defined", vec![])),
        ("wrong", vec![], atom("base", vec![])),
    ] {
        let weight = graph.storage_weight;
        assert!(graph.define_predicate(symbol.into(), params, body).is_err());
        assert_eq!(graph.definitions.entries.len(), first);
        assert_eq!(graph.storage_weight, weight);
    }
    let next = graph
        .define_predicate(
            "next".into(),
            vec!["y".into()],
            atom("base", vec![Linear::variable("y")]),
        )
        .unwrap();
    let unfolded = graph
        .predicate_definition(
            next,
            &atom("next", vec![Linear::number(42)]),
            &mut 0,
            MAX_INFERENCE_WORK,
        )
        .unwrap();
    assert_eq!(unfolded, atom("base", vec![Linear::number(42)]));
}

#[test]
fn simultaneous_arguments_are_not_rewritten_through_each_other() {
    let mut graph = Evidence::default();
    let row = Linear::variable("x").add(&Linear::variable("y")).unwrap();
    let definition = graph
        .define_predicate("sum".into(), vec!["x".into(), "y".into()], Formula::Ge(row))
        .unwrap();
    let result = graph
        .predicate_definition(
            definition,
            &atom("sum", vec![Linear::variable("y"), Linear::number(3)]),
            &mut 0,
            MAX_INFERENCE_WORK,
        )
        .unwrap();
    assert_eq!(
        result,
        Formula::Ge(Linear::variable("y").add(&Linear::number(3)).unwrap())
    );
}

#[test]
fn definition_storage_expansion_and_capture_fail_closed() {
    let mut graph = Evidence::default();
    let definition = graph
        .define_predicate(
            "scaled".into(),
            vec!["x".into()],
            Formula::Ge(Linear::variable("x").scale(2).unwrap()),
        )
        .unwrap();
    assert!(graph
        .predicate_definition(
            definition,
            &atom("scaled", vec![Linear::number(i128::MAX)]),
            &mut 0,
            MAX_INFERENCE_WORK
        )
        .is_err());
    assert!(graph
        .predicate_definition(
            definition,
            &atom("scaled", vec![Linear::number(1)]),
            &mut MAX_INFERENCE_WORK.saturating_sub(1),
            MAX_INFERENCE_WORK
        )
        .is_err());
    let quantifier = Formula::Forall {
        variable: "y".into(),
        domain: Box::new(Formula::True),
        body: Box::new(Formula::Ge(Linear::variable("x"))),
    };
    let definition = graph
        .define_predicate("binder".into(), vec!["x".into()], quantifier)
        .unwrap();
    assert!(graph
        .predicate_definition(
            definition,
            &atom("binder", vec![Linear::variable("y")]),
            &mut 0,
            MAX_INFERENCE_WORK
        )
        .unwrap_err()
        .contains("capture"));
    graph.storage_weight = MAX_VALUE_WORK;
    assert!(graph
        .define_predicate("too-much".into(), vec![], Formula::True)
        .is_err());
}
