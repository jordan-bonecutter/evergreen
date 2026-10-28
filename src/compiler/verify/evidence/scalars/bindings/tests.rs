use super::*;

fn atom(index: &str, value: &str) -> Formula {
    Formula::Predicate {
        symbol: "read_value".into(),
        arguments: vec![Linear::variable(index), Linear::variable(value)],
    }
}

fn fixture(graph: &mut Evidence) -> BindingId {
    let mut terms = Terms::new().unwrap();
    let work = &mut Work::new(1000);
    let index = terms.variable("index", work).unwrap();
    let value = terms.variable("value", work).unwrap();
    let read = terms.application("contents", &[index], work).unwrap();
    graph
        .define_scalar_equality(
            "read_value".into(),
            vec!["index".into(), "value".into()],
            Arc::new(terms),
            read,
            value,
        )
        .unwrap();
    let mut terms = Terms::new().unwrap();
    let index = terms.variable("at", work).unwrap();
    let read = terms.application("contents", &[index], work).unwrap();
    graph
        .define_scalar_binding("observed".into(), terms, read)
        .unwrap()
}

#[test]
fn scalar_bindings_check_both_sides_and_cannot_be_redeclared() {
    let mut graph = Evidence::default();
    let binding = fixture(&mut graph);
    let node = graph
        .derive(atom("at", "observed"), Rule::ScalarBinding(binding))
        .unwrap();
    graph.check_closed(node).unwrap();
    assert!(graph.admissions(node).admissions.is_empty());
    for goal in [atom("other", "observed"), atom("at", "other")] {
        assert!(graph.derive(goal, Rule::ScalarBinding(binding)).is_err());
    }
    assert!(graph
        .derive(
            atom("at", "observed"),
            Rule::ScalarBinding(BindingId(usize::MAX))
        )
        .is_err());
    for name in ["observed", "at"] {
        let mut terms = Terms::new().unwrap();
        let zero = terms.number(0, &mut Work::new(100)).unwrap();
        assert!(graph
            .define_scalar_binding(name.into(), terms, zero)
            .is_err());
    }
    let mut terms = Terms::new().unwrap();
    let recursive = terms.variable("recursive", &mut Work::new(100)).unwrap();
    assert!(graph
        .define_scalar_binding("recursive".into(), terms, recursive)
        .is_err());
}

#[test]
fn scalar_bindings_do_not_generalize_their_fixed_inputs() {
    let mut graph = Evidence::default();
    let binding = fixture(&mut graph);
    let body = graph
        .derive(atom("at", "observed"), Rule::ScalarBinding(binding))
        .unwrap();
    let (hypothesis, _) = graph.hypothesis(Formula::True).unwrap();
    for (variable, claim) in [("at", atom("i", "observed")), ("observed", atom("at", "i"))] {
        let goal = Formula::Forall {
            variable: "i".into(),
            domain: Box::new(Formula::True),
            body: Box::new(claim),
        };
        assert!(graph
            .derive(
                goal,
                Rule::ForallIntro {
                    hypothesis,
                    body,
                    eigenvariable: variable.into()
                }
            )
            .is_err());
    }
    let independent = Formula::Forall {
        variable: "i".into(),
        domain: Box::new(Formula::True),
        body: Box::new(atom("at", "observed")),
    };
    graph
        .derive(
            independent,
            Rule::ForallIntro {
                hypothesis,
                body,
                eigenvariable: "fresh".into(),
            },
        )
        .unwrap();
}

#[test]
fn transporting_a_read_retains_the_index_proof_dependencies() {
    let mut graph = Evidence::default();
    let binding = fixture(&mut graph);
    let source = graph
        .derive(atom("at", "observed"), Rule::ScalarBinding(binding))
        .unwrap();
    let (h, index) = graph
        .hypothesis(equal(&Linear::variable("at"), &Linear::variable("other")).unwrap())
        .unwrap();
    let value = graph
        .arithmetic(
            equal(&Linear::variable("observed"), &Linear::variable("observed")).unwrap(),
            paths::Support::default(),
        )
        .unwrap();
    let result = graph
        .derive(
            atom("other", "observed"),
            Rule::PredicateCongruence {
                source,
                equalities: vec![index, value],
            },
        )
        .unwrap();
    assert_eq!(graph.nodes[result.0].hypotheses, BTreeSet::from([h]));
    assert!(graph.check_closed(result).is_err());
    let admitted = graph
        .admit(equal(&Linear::variable("at"), &Linear::variable("other")).unwrap())
        .unwrap();
    let result = graph
        .derive(
            atom("other", "observed"),
            Rule::PredicateCongruence {
                source,
                equalities: vec![admitted, value],
            },
        )
        .unwrap();
    assert_eq!(
        graph.admissions(result).admissions,
        BTreeSet::from([admitted])
    );
}
