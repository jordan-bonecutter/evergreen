use super::*;

fn nonnegative(name: &str) -> Formula {
    Formula::Ge(Linear::variable(name))
}

fn range(name: &str) -> Formula {
    Formula::And(
        Box::new(nonnegative(name)),
        Box::new(Formula::Ge(
            Linear::number(9).sub(&Linear::variable(name)).unwrap(),
        )),
    )
}

fn forall(domain: Formula, body: Formula) -> Formula {
    Formula::Forall {
        variable: "i".into(),
        domain: Box::new(domain),
        body: Box::new(body),
    }
}

fn introduce(hypothesis: HypothesisId, body: NodeId) -> Rule {
    Rule::ForallIntro {
        hypothesis,
        body,
        eigenvariable: "k".into(),
    }
}

fn reject_without_mutation(graph: &mut Evidence, goal: Formula, rule: Rule) {
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

#[test]
fn bounded_universal_introduction_and_specialization_are_closed_and_checked() {
    let mut graph = Evidence::default();
    let (h, domain) = graph.hypothesis(range("k")).unwrap();
    let body = graph
        .derive(nonnegative("k"), Rule::AndLeft(domain))
        .unwrap();
    let theorem = graph
        .derive(forall(range("i"), nonnegative("i")), introduce(h, body))
        .unwrap();
    graph.check_closed(theorem).unwrap();
    assert!(graph.admissions(theorem).admissions.is_empty());
    assert!(graph.admissions(theorem).complete);

    let term = Linear::number(5);
    let bounds = range("i").substitute("i", &term).unwrap();
    let domain = graph.arithmetic(bounds, paths::Support::default()).unwrap();
    let specialized = graph
        .derive(
            Formula::Ge(term.clone()),
            Rule::ForallElim {
                theorem,
                domain,
                term,
            },
        )
        .unwrap();
    graph.check_closed(specialized).unwrap();
    assert!(graph.admissions(specialized).complete);
}

#[test]
fn universal_rules_reject_wrong_domains_binders_and_instances() {
    let mut graph = Evidence::default();
    let (h, domain) = graph.hypothesis(range("k")).unwrap();
    let body = graph
        .derive(nonnegative("k"), Rule::AndLeft(domain))
        .unwrap();
    let goal = forall(range("i"), nonnegative("i"));
    let theorem = graph.derive(goal.clone(), introduce(h, body)).unwrap();
    let wrong_domain = graph.admit(Formula::True).unwrap();
    let (wrong_h, _) = graph.hypothesis(Formula::True).unwrap();
    let good_domain = graph
        .admit(range("i").substitute("i", &Linear::number(5)).unwrap())
        .unwrap();
    for (claim, rule) in [
        (goal.clone(), introduce(wrong_h, body)),
        (
            goal.clone(),
            introduce(HypothesisId { node: wrong_domain }, body),
        ),
        (goal.clone(), introduce(h, domain)),
        (
            goal,
            introduce(
                HypothesisId {
                    node: NodeId(usize::MAX),
                },
                body,
            ),
        ),
        (
            Formula::True,
            Rule::ForallElim {
                theorem,
                domain: good_domain,
                term: Linear::number(5),
            },
        ),
        (
            Formula::Ge(Linear::number(5)),
            Rule::ForallElim {
                theorem,
                domain: wrong_domain,
                term: Linear::number(5),
            },
        ),
        (
            Formula::True,
            Rule::ForallElim {
                theorem: wrong_domain,
                domain: wrong_domain,
                term: Linear::number(5),
            },
        ),
    ] {
        reject_without_mutation(&mut graph, claim, rule);
    }
}

#[test]
fn universal_introduction_rejects_open_or_admitted_eigenvariable_assumptions() {
    let goal = forall(Formula::True, nonnegative("i"));
    let mut graph = Evidence::default();
    let (h, _) = graph.hypothesis(Formula::True).unwrap();
    let (_, open) = graph.hypothesis(nonnegative("k")).unwrap();
    let admitted = graph.admit(nonnegative("k")).unwrap();
    for body in [open, admitted] {
        reject_without_mutation(&mut graph, goal.clone(), introduce(h, body));
    }
    // The eigenvariable also cannot already be a free parameter in the goal.
    let (h, domain) = graph.hypothesis(nonnegative("k")).unwrap();
    reject_without_mutation(
        &mut graph,
        forall(nonnegative("i"), nonnegative("k")),
        introduce(h, domain),
    );
}

#[test]
fn used_unresolved_arithmetic_rows_block_generalization_but_unused_rows_do_not() {
    let mut graph = Evidence::default();
    let (h, _) = graph.hypothesis(Formula::True).unwrap();
    let path = paths::Path::from(vec![Linear::variable("k"), Linear::variable("unrelated")]);
    let mut support = paths::Support::default();
    support.add_rows(&path, &[0]);
    assert_eq!(support.context_variables, BTreeSet::from(["k".into()]));
    let body = graph.arithmetic(nonnegative("k"), support).unwrap();
    reject_without_mutation(
        &mut graph,
        forall(Formula::True, nonnegative("i")),
        introduce(h, body),
    );

    let mut support = paths::Support::default();
    support.add_rows(&path, &[1]);
    let body = graph.arithmetic(nonnegative("unrelated"), support).unwrap();
    let theorem = graph
        .derive(
            forall(Formula::True, nonnegative("unrelated")),
            introduce(h, body),
        )
        .unwrap();
    graph.check_closed(theorem).unwrap();
    // Generalization preserves the unresolved source; it does not certify that source.
    assert!(!graph.admissions(theorem).complete);
}

#[test]
fn inner_discharged_hypotheses_and_unused_admissions_do_not_prevent_generalization() {
    let mut graph = Evidence::default();
    let _unused = graph.admit(nonnegative("k")).unwrap();
    let (domain, _) = graph.hypothesis(Formula::True).unwrap();
    let (inner, premise) = graph.hypothesis(nonnegative("k")).unwrap();
    let body = graph
        .derive(
            Formula::Implies(Box::new(nonnegative("k")), Box::new(nonnegative("k"))),
            Rule::ImpIntro {
                hypothesis: inner,
                body: premise,
            },
        )
        .unwrap();
    let theorem = graph
        .derive(
            forall(
                Formula::True,
                Formula::Implies(Box::new(nonnegative("i")), Box::new(nonnegative("i"))),
            ),
            introduce(domain, body),
        )
        .unwrap();
    graph.check_closed(theorem).unwrap();
    assert!(graph.admissions(theorem).admissions.is_empty());
}

#[test]
fn untraced_contracts_and_imported_trust_cannot_claim_eigenvariable_freshness() {
    let mut graph = Evidence::default();
    let (h, _) = graph.hypothesis(Formula::True).unwrap();
    let contract = graph.contract(nonnegative("k"), vec![]).unwrap();
    reject_without_mutation(
        &mut graph,
        forall(Formula::True, nonnegative("i")),
        introduce(h, contract),
    );
    let pending = graph
        .reference(vec![], Some(summaries::Aspect::Safety))
        .unwrap();
    let body = graph
        .arithmetic(
            nonnegative("k"),
            paths::Support {
                parents: BTreeSet::from([pending]),
                ..paths::Support::default()
            },
        )
        .unwrap();
    reject_without_mutation(
        &mut graph,
        forall(Formula::True, nonnegative("i")),
        introduce(h, body),
    );
    let mut session = Session::search();
    let trust = session
        .trust(&[], b"external source", 1, "boundary")
        .unwrap();
    let imported = graph.import_trust(trust).unwrap();
    let body = graph
        .arithmetic(
            nonnegative("k"),
            paths::Support {
                parents: BTreeSet::from([imported]),
                ..paths::Support::default()
            },
        )
        .unwrap();
    reject_without_mutation(
        &mut graph,
        forall(Formula::True, nonnegative("i")),
        introduce(h, body),
    );
}

#[test]
fn applied_contracts_expose_claim_control_and_precondition_inputs() {
    let mut graph = Evidence::default();
    let (h, domain) = graph.hypothesis(range("k")).unwrap();
    let original = forall(range("i"), nonnegative("i"));
    let checked = graph
        .applied_contract(original, vec![], &Formula::True)
        .unwrap();
    let selected = graph
        .derive(
            nonnegative("k"),
            Rule::ForallElim {
                theorem: checked,
                domain,
                term: Linear::variable("k"),
            },
        )
        .unwrap();
    graph
        .derive(forall(range("i"), nonnegative("i")), introduce(h, selected))
        .unwrap();

    let captured = graph
        .applied_contract(nonnegative("k"), vec![], &Formula::True)
        .unwrap();
    reject_without_mutation(
        &mut graph,
        forall(range("i"), nonnegative("i")),
        introduce(h, captured),
    );
    let controlled = graph
        .applied_contract(Formula::False, vec![], &nonnegative("k"))
        .unwrap();
    reject_without_mutation(
        &mut graph,
        forall(range("i"), Formula::False),
        introduce(h, controlled),
    );
    let premise = graph
        .arithmetic(
            Formula::True,
            paths::Support {
                unresolved: true,
                context_variables: BTreeSet::from(["k".into()]),
                ..Default::default()
            },
        )
        .unwrap();
    let dependent = graph
        .applied_contract(Formula::False, vec![premise], &Formula::True)
        .unwrap();
    reject_without_mutation(
        &mut graph,
        forall(range("i"), Formula::False),
        introduce(h, dependent),
    );
    let opaque = graph.contract(Formula::True, vec![]).unwrap();
    let unresolved = graph
        .applied_contract(Formula::False, vec![opaque], &Formula::True)
        .unwrap();
    reject_without_mutation(
        &mut graph,
        forall(range("i"), Formula::False),
        introduce(h, unresolved),
    );
}

#[test]
fn specialization_terms_are_charged_even_when_the_body_does_not_use_them() {
    let mut graph = Evidence::default();
    let theorem = graph.admit(forall(Formula::True, Formula::True)).unwrap();
    let domain = graph.admit(Formula::True).unwrap();
    reject_without_mutation(
        &mut graph,
        Formula::True,
        Rule::ForallElim {
            theorem,
            domain,
            term: Linear::variable("x".repeat(MAX_VALUE_WORK)),
        },
    );
}

#[test]
fn repeated_freshness_checks_respect_the_aggregate_inference_budget() {
    let mut graph = Evidence::default();
    let (h, domain) = graph.hypothesis(range("k")).unwrap();
    let body = graph
        .derive(nonnegative("k"), Rule::AndLeft(domain))
        .unwrap();
    graph.rule_work = MAX_INFERENCE_WORK - 1;
    reject_without_mutation(
        &mut graph,
        forall(range("i"), nonnegative("i")),
        introduce(h, body),
    );
}
