use super::*;

fn atom(name: &str) -> Formula {
    Formula::Ge(Linear::variable(name))
}

fn implies(a: Formula, b: Formula) -> Formula {
    Formula::Implies(Box::new(a), Box::new(b))
}

#[test]
fn logical_rules_reject_wrong_connectives_premises_and_conclusions() {
    let mut graph = Evidence::default();
    let p = atom("p");
    let q = atom("q");
    let pp = graph.admit(p.clone()).unwrap();
    let pq = graph.admit(q.clone()).unwrap();
    let both = Formula::And(Box::new(p.clone()), Box::new(q.clone()));
    let conjunction = graph.derive(both.clone(), Rule::AndIntro(pp, pq)).unwrap();
    let either = Formula::Or(Box::new(p.clone()), Box::new(q.clone()));
    let implication = graph.admit(implies(p.clone(), q.clone())).unwrap();
    for (goal, rule) in [
        (both, Rule::AndIntro(pq, pp)),
        (q.clone(), Rule::AndLeft(conjunction)),
        (p.clone(), Rule::AndRight(conjunction)),
        (q.clone(), Rule::AndLeft(pp)),
        (either.clone(), Rule::OrLeft(pq)),
        (either, Rule::OrRight(pp)),
        (q.clone(), Rule::Reuse(pp)),
        (q.clone(), Rule::FalseElim(pp)),
        (
            q.clone(),
            Rule::ImpElim {
                theorem: implication,
                argument: pq,
            },
        ),
        (
            p.clone(),
            Rule::ImpElim {
                theorem: implication,
                argument: pp,
            },
        ),
        (
            q.clone(),
            Rule::ImpElim {
                theorem: pp,
                argument: pp,
            },
        ),
        (p, Rule::Reuse(NodeId(graph.nodes.len() + 10))),
    ] {
        let count = graph.nodes.len();
        let edges = graph.edges;
        let work = graph.rule_work;
        assert!(graph.derive(goal, rule).is_err());
        assert_eq!(graph.nodes.len(), count);
        assert_eq!(graph.edges, edges);
        assert_eq!(graph.rule_work, work);
    }
}

#[test]
fn implication_discharges_only_its_declared_hypothesis() {
    let mut graph = Evidence::default();
    let p = atom("p");
    let q = atom("q");
    let (h, hp) = graph.hypothesis(p.clone()).unwrap();
    let (other, hq) = graph.hypothesis(q.clone()).unwrap();
    assert!(graph.check_closed(hp).is_err());
    let identity = graph
        .derive(
            implies(p.clone(), p.clone()),
            Rule::ImpIntro {
                hypothesis: h,
                body: hp,
            },
        )
        .unwrap();
    graph.check_closed(identity).unwrap();

    let dependent = graph
        .derive(
            implies(p.clone(), q.clone()),
            Rule::ImpIntro {
                hypothesis: h,
                body: hq,
            },
        )
        .unwrap();
    assert_eq!(graph.nodes[dependent.0].hypotheses, BTreeSet::from([other]));
    assert!(graph.check_closed(dependent).is_err());
    let closed = graph
        .derive(
            implies(q.clone(), implies(p.clone(), q.clone())),
            Rule::ImpIntro {
                hypothesis: other,
                body: dependent,
            },
        )
        .unwrap();
    graph.check_closed(closed).unwrap();
    assert!(graph
        .derive(
            implies(q, p.clone()),
            Rule::ImpIntro {
                hypothesis: h,
                body: hp
            }
        )
        .is_err());
    let ordinary_proof = graph.admit(p.clone()).unwrap();
    assert!(graph
        .derive(
            implies(p.clone(), p),
            Rule::ImpIntro {
                hypothesis: HypothesisId {
                    node: ordinary_proof
                },
                body: hp
            }
        )
        .is_err());
}

#[test]
fn case_split_checks_both_branches_and_prevents_cross_branch_assumptions() {
    let mut graph = Evidence::default();
    let p = atom("p");
    let q = atom("q");
    let either = Formula::Or(Box::new(p.clone()), Box::new(q.clone()));
    let source = graph.admit(either.clone()).unwrap();
    let (lh, left) = graph.hypothesis(p.clone()).unwrap();
    let (rh, right) = graph.hypothesis(q.clone()).unwrap();
    let left_goal = graph.derive(either.clone(), Rule::OrLeft(left)).unwrap();
    let right_goal = graph.derive(either.clone(), Rule::OrRight(right)).unwrap();
    let split = |left, right| Rule::OrElim {
        source,
        left_hypothesis: lh,
        left,
        right_hypothesis: rh,
        right,
    };
    let closed = graph
        .derive(either.clone(), split(left_goal, right_goal))
        .unwrap();
    graph.check_closed(closed).unwrap();
    assert_eq!(
        graph.admissions(closed).admissions,
        BTreeSet::from([source])
    );

    // The left branch cannot provide evidence in the right branch, even when
    // it proves the exact requested conclusion.
    assert!(graph.derive(p.clone(), split(left, left)).is_err());
    assert!(graph
        .derive(either.clone(), split(left_goal, left_goal))
        .is_err());
    assert!(graph
        .derive(
            either.clone(),
            Rule::OrElim {
                source: left_goal,
                left_hypothesis: lh,
                left: left_goal,
                right_hypothesis: rh,
                right: right_goal
            }
        )
        .is_err());
    assert!(graph
        .derive(
            either,
            Rule::OrElim {
                source,
                left_hypothesis: lh,
                left: left_goal,
                right_hypothesis: lh,
                right: right_goal
            }
        )
        .is_err());
}

#[test]
fn arithmetic_imports_preserve_scope_and_open_evidence_cannot_be_published() {
    let mut graph = Evidence::default();
    let p = atom("p");
    let (h, hypothesis) = graph.hypothesis(p.clone()).unwrap();
    let arithmetic = graph
        .arithmetic(
            p.clone(),
            paths::Support {
                parents: BTreeSet::from([hypothesis]),
                unresolved: false,
            },
        )
        .unwrap();
    assert!(graph.check_closed(arithmetic).is_err());
    let snapshot = subjects::Snapshot::default();
    assert!(graph.record_subjects(arithmetic, snapshot).is_err());
    assert!(graph.subjects(arithmetic).is_none());
    let closed = graph
        .derive(
            implies(p.clone(), p),
            Rule::ImpIntro {
                hypothesis: h,
                body: arithmetic,
            },
        )
        .unwrap();
    graph.check_closed(closed).unwrap();
}

#[test]
fn negation_uses_the_same_scoped_implication_rules() {
    let mut graph = Evidence::default();
    let p = atom("p");
    let negation = Formula::Not(Box::new(p.clone()));
    let not_p = graph.admit(negation.clone()).unwrap();
    let (h, hp) = graph.hypothesis(p).unwrap();
    let contradiction = graph
        .derive(
            Formula::False,
            Rule::ImpElim {
                theorem: not_p,
                argument: hp,
            },
        )
        .unwrap();
    let arbitrary = graph
        .derive(atom("arbitrary"), Rule::FalseElim(contradiction))
        .unwrap();
    assert!(graph.check_closed(arbitrary).is_err());
    let closed = graph
        .derive(
            negation,
            Rule::ImpIntro {
                hypothesis: h,
                body: contradiction,
            },
        )
        .unwrap();
    graph.check_closed(closed).unwrap();
    assert_eq!(graph.admissions(closed).admissions, BTreeSet::from([not_p]));
}

#[test]
fn accepted_inferences_have_no_counterexample_in_two_atom_truth_tables() {
    fn truth(p: &Formula, assignment: u8) -> bool {
        match p {
            Formula::True => true,
            Formula::False => false,
            Formula::Ge(row) => match row.terms.keys().next().unwrap().as_str() {
                "p" => assignment & 1 != 0,
                "q" => assignment & 2 != 0,
                _ => panic!("unexpected truth-table atom"),
            },
            Formula::And(a, b) => truth(a, assignment) && truth(b, assignment),
            Formula::Or(a, b) => truth(a, assignment) || truth(b, assignment),
            Formula::Not(a) => !truth(a, assignment),
            Formula::Implies(a, b) => !truth(a, assignment) || truth(b, assignment),
        }
    }
    let p = atom("p");
    let q = atom("q");
    let formulas = [
        Formula::True,
        Formula::False,
        p.clone(),
        q.clone(),
        Formula::And(Box::new(p.clone()), Box::new(q.clone())),
        Formula::Or(Box::new(p.clone()), Box::new(q.clone())),
        implies(p.clone(), q),
        Formula::Not(Box::new(p)),
    ];
    // Enumerate candidate rules, including malformed ones; accepted candidates
    // must preserve truth for every valuation satisfying the imported premises.
    for a in &formulas {
        for b in &formulas {
            let mut graph = Evidence::default();
            let pa = graph.admit(a.clone()).unwrap();
            let pb = graph.admit(b.clone()).unwrap();
            for goal in &formulas {
                for rule in [
                    Rule::Reuse(pa),
                    Rule::AndLeft(pa),
                    Rule::AndRight(pa),
                    Rule::OrLeft(pa),
                    Rule::OrRight(pa),
                    Rule::FalseElim(pa),
                    Rule::AndIntro(pa, pb),
                    Rule::ImpElim {
                        theorem: pa,
                        argument: pb,
                    },
                ] {
                    if graph.derive(goal.clone(), rule).is_ok() {
                        for valuation in 0..4 {
                            assert!(
                                !truth(a, valuation)
                                    || !truth(b, valuation)
                                    || truth(goal, valuation)
                            );
                        }
                    }
                }
            }
        }
    }
}
