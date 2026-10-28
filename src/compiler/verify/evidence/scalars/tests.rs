use super::*;

fn atom(name: &str, arguments: Vec<Linear>) -> Formula {
    Formula::Predicate {
        symbol: name.into(),
        arguments,
    }
}

fn fixtures(graph: &mut Evidence) {
    let mut terms = Terms::new().unwrap();
    let work = &mut Work::new(10_000);
    let x = terms.variable("x", work).unwrap();
    let y = terms.variable("y", work).unwrap();
    let fx = terms.application("contents_v0", &[x], work).unwrap();
    let fy = terms.application("contents_v0", &[y], work).unwrap();
    let other = terms.application("contents_v1", &[y], work).unwrap();
    let gfx = terms.application("outer", &[fx], work).unwrap();
    let gfy = terms.application("outer", &[fy], work).unwrap();
    let pair_xy = terms.application("pair", &[x, y], work).unwrap();
    let pair_yx = terms.application("pair", &[y, x], work).unwrap();
    let terms = Arc::new(terms);
    for (symbol, left, right) in [
        ("scalar_eq", x, y),
        ("read_eq", fx, fy),
        ("different_versions", fx, other),
        ("nested_eq", gfx, gfy),
        ("pair_eq", pair_xy, pair_yx),
    ] {
        graph
            .define_scalar_equality(
                symbol.into(),
                vec!["x".into(), "y".into()],
                Arc::clone(&terms),
                left,
                right,
            )
            .unwrap();
    }
}

#[test]
fn scalar_congruence_preserves_hypotheses_and_admission_dependencies() {
    let mut graph = Evidence::default();
    fixtures(&mut graph);
    let args = vec![Linear::variable("before"), Linear::variable("after")];
    let (h, premise) = graph
        .hypothesis(equal(&args[0], &args[1]).unwrap())
        .unwrap();
    let read = graph
        .derive(
            atom("read_eq", args.clone()),
            Rule::ScalarCongruence {
                equalities: vec![premise],
            },
        )
        .unwrap();
    assert_eq!(graph.nodes[read.0].hypotheses, BTreeSet::from([h]));
    assert!(graph.check_closed(read).is_err());
    let nested = graph
        .derive(
            atom("nested_eq", args.clone()),
            Rule::ScalarCongruence {
                equalities: vec![read],
            },
        )
        .unwrap();
    assert_eq!(graph.nodes[nested.0].hypotheses, BTreeSet::from([h]));
    assert!(graph.admissions(nested).admissions.is_empty());

    let admitted = graph.admit(atom("scalar_eq", args.clone())).unwrap();
    graph.admit(Formula::False).unwrap(); // Unrelated admissions must not spread.
    let read = graph
        .derive(
            atom("read_eq", args.clone()),
            Rule::ScalarCongruence {
                equalities: vec![admitted],
            },
        )
        .unwrap();
    let nested = graph
        .derive(
            atom("nested_eq", args),
            Rule::ScalarCongruence {
                equalities: vec![read],
            },
        )
        .unwrap();
    assert_eq!(
        graph.admissions(nested).admissions,
        BTreeSet::from([admitted])
    );
    assert!(graph.check_closed(nested).is_ok());
}

#[test]
fn scalar_rules_reject_wrong_functions_arguments_arities_and_missing_proofs() {
    let mut graph = Evidence::default();
    fixtures(&mut graph);
    let args = vec![Linear::variable("a"), Linear::variable("b")];
    let (_, eq) = graph.hypothesis(atom("scalar_eq", args.clone())).unwrap();
    let (_, reverse) = graph
        .hypothesis(atom("scalar_eq", vec![args[1].clone(), args[0].clone()]))
        .unwrap();
    graph
        .derive(
            atom("pair_eq", args.clone()),
            Rule::ScalarCongruence {
                equalities: vec![eq, reverse],
            },
        )
        .unwrap();
    for (goal, rule) in [
        (atom("read_eq", args.clone()), Rule::ScalarReflexivity),
        (
            atom("different_versions", args.clone()),
            Rule::ScalarCongruence {
                equalities: vec![eq],
            },
        ),
        (
            atom("read_eq", args.clone()),
            Rule::ScalarCongruence { equalities: vec![] },
        ),
        (
            atom("read_eq", args.clone()),
            Rule::ScalarCongruence {
                equalities: vec![reverse],
            },
        ),
        (
            atom("read_eq", vec![Linear::number(0), Linear::number(1)]),
            Rule::ScalarCongruence {
                equalities: vec![eq],
            },
        ),
        (
            atom("pair_eq", args.clone()),
            Rule::ScalarCongruence {
                equalities: vec![reverse, eq],
            },
        ),
        (
            atom("read_eq", vec![args[0].clone()]),
            Rule::ScalarReflexivity,
        ),
        (atom("unregistered", args.clone()), Rule::ScalarReflexivity),
        (
            atom("read_eq", args),
            Rule::ScalarCongruence {
                equalities: vec![NodeId(usize::MAX)],
            },
        ),
    ] {
        let before = (graph.nodes.len(), graph.edges, graph.rule_work);
        assert!(graph.derive(goal, rule).is_err());
        assert_eq!(before, (graph.nodes.len(), graph.edges, graph.rule_work));
    }
}

#[test]
fn scalar_equalities_use_existing_quantifier_substitution_without_hidden_free_variables() {
    let mut graph = Evidence::default();
    fixtures(&mut graph);
    let body = atom(
        "read_eq",
        vec![Linear::variable("i"), Linear::variable("i")],
    );
    let theorem = Formula::Forall {
        variable: "i".into(),
        domain: Box::new(Formula::True),
        body: Box::new(body.clone()),
    };
    let eigen = Linear::variable("fresh");
    let (hypothesis, _) = graph.hypothesis(Formula::True).unwrap();
    let proof = graph
        .derive(
            body.substitute("i", &eigen).unwrap(),
            Rule::ScalarReflexivity,
        )
        .unwrap();
    let universal = graph
        .derive(
            theorem,
            Rule::ForallIntro {
                hypothesis,
                body: proof,
                eigenvariable: "fresh".into(),
            },
        )
        .unwrap();
    let domain = graph
        .arithmetic(Formula::True, paths::Support::default())
        .unwrap();
    let seven = graph
        .derive(
            atom("read_eq", vec![Linear::number(7), Linear::number(7)]),
            Rule::ForallElim {
                theorem: universal,
                domain,
                term: Linear::number(7),
            },
        )
        .unwrap();
    assert!(graph.check_closed(seven).is_ok());
    assert!(graph.admissions(seven).admissions.is_empty());

    let args = vec![eigen, Linear::number(0)];
    let admitted = graph.admit(atom("scalar_eq", args.clone())).unwrap();
    let conditional = graph
        .derive(
            atom("read_eq", args),
            Rule::ScalarCongruence {
                equalities: vec![admitted],
            },
        )
        .unwrap();
    let (hypothesis, _) = graph.hypothesis(Formula::True).unwrap();
    let invalid = Formula::Forall {
        variable: "i".into(),
        domain: Box::new(Formula::True),
        body: Box::new(atom(
            "read_eq",
            vec![Linear::variable("i"), Linear::number(0)],
        )),
    };
    assert!(graph
        .derive(
            invalid,
            Rule::ForallIntro {
                hypothesis,
                body: conditional,
                eigenvariable: "fresh".into(),
            }
        )
        .is_err());

    let mut terms = Terms::new().unwrap();
    let work = &mut Work::new(1000);
    let hidden = terms.variable("hidden", work).unwrap();
    let read = terms.application("read", &[hidden], work).unwrap();
    assert!(graph
        .define_scalar_equality("hidden".into(), vec![], Arc::new(terms), read, read)
        .unwrap_err()
        .contains("every free variable"));
}

#[test]
fn scalar_instantiation_is_simultaneous_and_definition_symbols_cannot_be_replaced() {
    let mut graph = Evidence::default();
    fixtures(&mut graph);
    let y = Linear::variable("y");
    let seven = Linear::number(7);
    let goal = atom("read_eq", vec![y.clone(), seven.clone()]);
    assert!(graph.derive(goal.clone(), Rule::ScalarReflexivity).is_err());
    let (_, premise) = graph.hypothesis(equal(&y, &seven).unwrap()).unwrap();
    graph
        .derive(
            goal,
            Rule::ScalarCongruence {
                equalities: vec![premise],
            },
        )
        .unwrap();

    let mut terms = Terms::new().unwrap();
    let zero = terms.number(0, &mut Work::new(10)).unwrap();
    let before = graph.storage_weight;
    assert!(graph
        .define_scalar_equality("read_eq".into(), vec![], Arc::new(terms), zero, zero)
        .is_err());
    assert_eq!(before, graph.storage_weight);
    assert!(graph
        .derive(
            atom("read_eq", vec![Linear::number(1), Linear::number(2)]),
            Rule::ScalarReflexivity
        )
        .is_err());
}
