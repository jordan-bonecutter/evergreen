use super::*;

fn predicate(symbol: &str, arguments: Vec<Linear>) -> Formula {
    Formula::Predicate {
        symbol: symbol.into(),
        arguments,
    }
}

fn forall(domain: Formula, body: Formula) -> Formula {
    Formula::Forall {
        variable: "i".into(),
        domain: Box::new(domain),
        body: Box::new(body),
    }
}

#[test]
fn universal_specialization_substitutes_the_index_inside_predicate_arguments() {
    let mut graph = Evidence::default();
    let body = predicate("array-version-1/member-0", vec![Linear::variable("i")]);
    let (domain, hypothesis) = graph
        .hypothesis(predicate(
            "array-version-1/member-0",
            vec![Linear::variable("k")],
        ))
        .unwrap();
    let theorem = graph
        .derive(
            forall(body.clone(), body),
            Rule::ForallIntro {
                hypothesis: domain,
                body: hypothesis,
                eigenvariable: "k".into(),
            },
        )
        .unwrap();
    graph.check_closed(theorem).unwrap();
    let cell = predicate("array-version-1/member-0", vec![Linear::number(7)]);
    let (domain, premise) = graph.hypothesis(cell.clone()).unwrap();
    let instance = graph
        .derive(
            cell.clone(),
            Rule::ForallElim {
                theorem,
                domain: premise,
                term: Linear::number(7),
            },
        )
        .unwrap();
    assert!(graph.check_closed(instance).is_err());
    let closed = graph
        .derive(
            Formula::Implies(Box::new(cell.clone()), Box::new(cell)),
            Rule::ImpIntro {
                hypothesis: domain,
                body: instance,
            },
        )
        .unwrap();
    graph.check_closed(closed).unwrap();
    assert!(graph.admissions(closed).admissions.is_empty());
}

#[test]
fn predicate_assumptions_about_one_index_cannot_be_generalized() {
    let mut graph = Evidence::default();
    let (domain, _) = graph.hypothesis(Formula::True).unwrap();
    let body = graph
        .admit(predicate("selector", vec![Linear::variable("k")]))
        .unwrap();
    let count = graph.nodes.len();
    assert!(graph
        .derive(
            forall(
                Formula::True,
                predicate("selector", vec![Linear::variable("i")])
            ),
            Rule::ForallIntro {
                hypothesis: domain,
                body,
                eigenvariable: "k".into(),
            }
        )
        .is_err());
    assert_eq!(graph.nodes.len(), count);
}

#[test]
fn predicate_congruence_requires_each_argument_equality_and_preserves_scope() {
    let mut graph = Evidence::default();
    let from = Linear::variable("old_index");
    let to = Linear::variable("new_index");
    let claim = predicate("selector/version-1", vec![from.clone(), Linear::number(3)]);
    let source = graph.admit(claim).unwrap();
    let (h, eq) = graph.hypothesis(equal(&from, &to).unwrap()).unwrap();
    let unchanged = graph
        .arithmetic(
            equal(&Linear::number(3), &Linear::number(3)).unwrap(),
            paths::Support::default(),
        )
        .unwrap();
    let goal = predicate("selector/version-1", vec![to, Linear::number(3)]);
    let result = graph
        .derive(
            goal.clone(),
            Rule::PredicateCongruence {
                source,
                equalities: vec![eq, unchanged],
            },
        )
        .unwrap();
    assert_eq!(graph.nodes[result.0].hypotheses, BTreeSet::from([h]));
    assert_eq!(
        graph.admissions(result).admissions,
        BTreeSet::from([source])
    );
    assert!(graph.check_closed(result).is_err());
    for (goal, rule) in [
        (
            goal.clone(),
            Rule::PredicateCongruence {
                source,
                equalities: vec![unchanged, eq],
            },
        ),
        (
            goal.clone(),
            Rule::PredicateCongruence {
                source,
                equalities: vec![eq],
            },
        ),
        (
            predicate(
                "selector/version-2",
                vec![Linear::variable("new_index"), Linear::number(3)],
            ),
            Rule::PredicateCongruence {
                source,
                equalities: vec![eq, unchanged],
            },
        ),
        (
            goal.clone(),
            Rule::PredicateCongruence {
                source: unchanged,
                equalities: vec![eq, unchanged],
            },
        ),
        (
            goal,
            Rule::PredicateCongruence {
                source,
                equalities: vec![eq, NodeId(usize::MAX)],
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
fn predicate_atoms_cannot_enter_arithmetic_as_unchecked_boolean_variables() {
    let claim = predicate("selector", vec![Linear::variable("i")]);
    for negated in [false, true] {
        assert!(extend_from(
            &paths::Paths::unit(),
            &claim,
            negated,
            paths::Origin::Unresolved,
            &mut Session::search(),
            &mut 0
        )
        .unwrap_err()
        .contains("logical proof rules"));
    }
}
