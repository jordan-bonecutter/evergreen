use super::*;

fn with_context<T>(session: &mut Session, check: impl FnOnce(&mut Context<'_>) -> T) -> T {
    let functions = BTreeMap::new();
    let structs = BTreeMap::new();
    let names = BTreeSet::new();
    let declarations = Declarations {
        target: crate::compiler::TargetKind::X86_64,
        functions: &functions,
        summaries: &BTreeMap::new(),
        structs: &structs,
        drops: &names,
        destructors: &functions,
        helpers: &names,
        cleanup_helpers: &names,
    };
    check(&mut Context::new(declarations, session))
}

fn script(ctx: &mut Context<'_>, goal: &Formula, steps: &[&str]) -> evidence::NodeId {
    let steps = steps
        .iter()
        .map(|step| (*step).to_owned())
        .collect::<Vec<_>>();
    ctx.proof_script(goal, "evidence test", 1, &steps).unwrap()
}

#[test]
fn logical_lookup_skips_unrelated_predicates_without_losing_admissions() {
    with_context(&mut Session::search(), |ctx| {
        let atom = |symbol: String| Formula::Predicate {
            symbol,
            arguments: vec![Linear::variable("index")],
        };
        // Deliberately large unrelated witnesses should cost a candidate
        // lookup, not repeated normalization of their complete formulas.
        for i in 0..64 {
            let mut claim = atom(format!("unrelated_{i}")).and(atom("shared".into()));
            for j in 0..16 {
                claim = claim.and(atom(format!("unused_{i}_{j}")));
            }
            let (_, node) = ctx.proof.evidence.hypothesis(claim).unwrap();
            ctx.proof.witnesses.insert(format!("unused_{i}"), node);
        }
        let goal = atom("wanted".into()).and(atom("shared".into()));
        let wanted = ctx.proof.evidence.admit(goal.clone()).unwrap();
        ctx.proof.witnesses.insert("wanted".into(), wanted);
        let before = ctx.work.value_work;
        assert_eq!(ctx.logical_assumption(&goal, None).unwrap(), Some(wanted));
        assert!(ctx.work.value_work - before < 512);
        assert!(ctx.proof.evidence.has_admissions(wanted));
        assert!(ctx
            .logical_assumption(&atom("absent".into()), None)
            .unwrap()
            .is_none());

        // Selector specialization must reject irrelevant open premises before
        // cloning their full bodies, just as exact logical lookup does.
        let before = ctx.work.value_work;
        assert!(ctx
            .prove_indexed_predicate(&atom("absent".into()), None, "missing selector", 1)
            .unwrap()
            .is_none());
        assert!(ctx.work.value_work - before < 512);

        // Normalization can erase an atom. Filter on the normalized goal so
        // a checked True remains usable for `irrelevant || true`.
        let truth = script(ctx, &Formula::True, &["omega"]);
        ctx.proof.witnesses.insert("truth".into(), truth);
        let erased = Formula::Or(Box::new(atom("erased".into())), Box::new(Formula::True));
        assert_eq!(ctx.logical_assumption(&erased, None).unwrap(), Some(truth));
    });
}

#[test]
fn tactics_track_only_the_admissions_they_use_and_replay_the_same_graph() {
    fn check(session: &mut Session) -> evidence::AdmissionDependencies {
        with_context(session, |ctx| {
            let unused = script(ctx, &Formula::False, &["trustme"]);
            ctx.proof.witnesses.insert("unused".into(), unused);
            let premise = Formula::Ge(Linear::variable("premise"));
            let conclusion = Formula::Ge(Linear::variable("conclusion"));
            let implication =
                Formula::Implies(Box::new(premise.clone()), Box::new(conclusion.clone()));
            let theorem = script(ctx, &implication, &["trustme"]);
            ctx.proof.witnesses.insert("theorem".into(), theorem);
            let premise_node = script(ctx, &premise, &["trustme"]);
            ctx.proof.witnesses.insert("premise".into(), premise_node);
            let root = script(ctx, &conclusion, &["apply theorem", "exact premise"]);
            let dependencies = ctx.proof.evidence.admissions(root);
            assert!(dependencies.complete);
            assert_eq!(
                dependencies.admissions,
                BTreeSet::from([theorem, premise_node])
            );
            assert!(!dependencies.admissions.contains(&unused));
            dependencies
        })
    }
    let mut recording = Session::recording();
    let expected = check(&mut recording);
    recording.finish().unwrap();
    let bundle = recording.bundle("proof graph replay").unwrap();
    let mut replay = Session::replay(&bundle);
    assert_eq!(check(&mut replay), expected);
    replay.finish().unwrap();
    assert_eq!(replay.search_count(), 0);
}

#[test]
fn arithmetic_edges_use_checked_row_support_on_search_and_replay() {
    fn check(session: &mut Session) -> evidence::AdmissionDependencies {
        with_context(session, |ctx| {
            let x = Linear::variable("x");
            let used_claim = Formula::Ge(x.clone());
            let unused_claim = Formula::Ge(Linear::variable("unrelated"));
            let used = script(ctx, &used_claim, &["trustme"]);
            let unused = script(ctx, &unused_claim, &["trustme"]);
            ctx.assume_from(&used_claim, paths::Origin::Evidence(used))
                .unwrap();
            ctx.assume_from(&unused_claim, paths::Origin::Evidence(unused))
                .unwrap();
            let goal = Formula::Ge(x.add(&Linear::number(1)).unwrap());
            let root = script(ctx, &goal, &["omega"]);
            let dependencies = ctx.proof.evidence.admissions(root);
            assert_eq!(dependencies.admissions, BTreeSet::from([used]));
            // Every used row here has an explicit origin; the unrelated
            // admission is available but is not a premise of the result.
            assert!(dependencies.complete);
            dependencies
        })
    }
    let mut recording = Session::recording();
    let expected = check(&mut recording);
    recording.finish().unwrap();
    let bundle = recording.bundle("arithmetic proof graph replay").unwrap();
    let mut replay = Session::replay(&bundle);
    assert_eq!(check(&mut replay), expected);
    replay.finish().unwrap();
    assert_eq!(replay.search_count(), 0);
}

#[test]
fn constant_false_context_retains_its_admission_dependency() {
    with_context(&mut Session::search(), |ctx| {
        let source = script(ctx, &Formula::False, &["trustme"]);
        ctx.assume_from(&Formula::False, paths::Origin::Evidence(source))
            .unwrap();
        assert!(ctx.proof.paths.is_empty());
        let goal = Formula::Ge(Linear::variable("arbitrary"));
        let root = script(ctx, &goal, &["omega"]);
        let dependencies = ctx.proof.evidence.admissions(root);
        assert_eq!(dependencies.admissions, BTreeSet::from([source]));
        assert!(dependencies.complete);
        // True needs no false premise, even in this inconsistent context.
        let truth = script(ctx, &Formula::True, &["omega"]);
        let truth_dependencies = ctx.proof.evidence.admissions(truth);
        assert!(truth_dependencies.admissions.is_empty());
        assert!(truth_dependencies.complete);
    });
}

#[test]
fn cases_keeps_source_dependency_after_local_hypotheses_leave_scope() {
    with_context(&mut Session::search(), |ctx| {
        let proposition = Formula::Ge(Linear::variable("p"));
        let conjunction = Formula::And(Box::new(proposition.clone()), Box::new(Formula::True));
        let source = script(ctx, &conjunction, &["trustme"]);
        ctx.proof.witnesses.insert("source".into(), source);
        let result = script(ctx, &proposition, &["cases source with p , q", "exact p"]);
        assert!(!ctx.proof.witnesses.contains_key("p"));
        assert!(!ctx.proof.witnesses.contains_key("q"));
        assert_eq!(
            ctx.proof.evidence.admissions(result).admissions,
            BTreeSet::from([source])
        );
    });
}

#[test]
fn closing_a_local_false_hypothesis_does_not_poison_the_outer_context() {
    with_context(&mut Session::search(), |ctx| {
        let baseline = ctx.proof.paths.clone();
        let arbitrary = Formula::Ge(Linear::variable("arbitrary"));
        let goal = Formula::Implies(Box::new(Formula::False), Box::new(arbitrary.clone()));
        let result = script(ctx, &goal, &["intro impossible", "omega"]);
        assert!(ctx.proof.evidence.admissions(result).admissions.is_empty());
        assert_eq!(ctx.proof.paths, baseline);
        assert!(!ctx.proof.witnesses.contains_key("impossible"));
        assert!(ctx
            .proof_script(&arbitrary, "outside hypothesis", 1, &["omega".into()])
            .is_err());
    });
}

#[test]
fn opaque_conclusions_from_local_contradictions_discharge_only_local_hypotheses() {
    with_context(&mut Session::search(), |ctx| {
        let predicate = Formula::Predicate {
            symbol: "unknown".into(),
            arguments: vec![Linear::number(7)],
        };
        let before = ctx.proof.paths.clone();
        let goal = Formula::Implies(Box::new(Formula::False), Box::new(predicate.clone()));
        let root = script(ctx, &goal, &["intro impossible", "omega"]);
        ctx.proof.evidence.check_closed(root).unwrap();
        assert!(ctx.proof.evidence.admissions(root).admissions.is_empty());
        assert_eq!(ctx.proof.paths, before);
        assert!(ctx.proof.witnesses.is_empty());
        assert!(ctx
            .proof_script(&predicate, "outside hypothesis", 1, &["omega".into()])
            .is_err());
    });
}

#[test]
fn introduction_preserves_claim_and_does_not_admit_its_hypothesis() {
    with_context(&mut Session::search(), |ctx| {
        let premise = Formula::Ge(Linear::variable("p"));
        let goal = Formula::Implies(Box::new(premise.clone()), Box::new(premise));
        let root = script(ctx, &goal, &["intro h", "exact h"]);
        assert_eq!(ctx.proof.evidence.claim(root).unwrap(), &goal);
        let dependencies = ctx.proof.evidence.admissions(root);
        assert!(dependencies.complete);
        assert!(dependencies.admissions.is_empty());
        assert!(!ctx.proof.witnesses.contains_key("h"));
    });
}

#[test]
fn predicate_hypotheses_stay_logical_and_disappear_on_success_or_error() {
    with_context(&mut Session::search(), |ctx| {
        let predicate = Formula::Predicate {
            symbol: "observation".into(),
            arguments: vec![Linear::variable("value")],
        };
        let goal = Formula::Implies(Box::new(predicate.clone()), Box::new(predicate));
        let before = ctx.proof.paths.clone();
        let root = script(ctx, &goal, &["intro p", "exact p"]);
        ctx.proof.evidence.check_closed(root).unwrap();
        assert!(ctx.proof.evidence.admissions(root).admissions.is_empty());
        assert_eq!(ctx.proof.paths, before);
        assert!(ctx.proof.witnesses.is_empty());

        assert!(ctx
            .proof_script(
                &goal,
                "bad local proof",
                1,
                &["intro p".into(), "exact absent".into()],
            )
            .is_err());
        assert_eq!(ctx.proof.paths, before);
        assert!(ctx.proof.witnesses.is_empty());
    });
}

#[test]
fn nested_case_hypotheses_are_discharged_on_search_and_replay() {
    fn check(session: &mut Session) {
        with_context(session, |ctx| {
            let p = Formula::Ge(Linear::variable("p"));
            let q = Formula::Ge(Linear::variable("q"));
            let goal = Formula::Implies(
                Box::new(Formula::Or(Box::new(p.clone()), Box::new(q.clone()))),
                Box::new(Formula::Or(Box::new(q), Box::new(p))),
            );
            let root = script(
                ctx,
                &goal,
                &[
                    "intro either",
                    "cases either with p | q",
                    "right",
                    "exact p",
                    "left",
                    "exact q",
                ],
            );
            ctx.proof.evidence.check_closed(root).unwrap();
            assert!(ctx.proof.witnesses.is_empty());
            assert_eq!(ctx.proof.paths, paths::Paths::unit());
            assert!(ctx.proof.evidence.admissions(root).admissions.is_empty());
        });
    }
    let mut recording = Session::recording();
    check(&mut recording);
    recording.finish().unwrap();
    let bundle = recording.bundle("scoped logical rules").unwrap();
    let mut replay = Session::replay(&bundle);
    check(&mut replay);
    replay.finish().unwrap();
    assert_eq!(replay.search_count(), 0);
}

#[test]
fn unused_conjunction_evidence_does_not_taint_an_independent_proof() {
    with_context(&mut Session::search(), |ctx| {
        let p = Formula::Ge(Linear::variable("p"));
        let pair = Formula::And(Box::new(p.clone()), Box::new(p));
        let source = script(ctx, &pair, &["trustme"]);
        ctx.proof.witnesses.insert("source".into(), source);
        let root = script(ctx, &Formula::True, &["cases source with p , q", "omega"]);
        assert!(ctx.proof.evidence.admissions(root).admissions.is_empty());
        ctx.proof.evidence.check_closed(root).unwrap();
    });
}

#[test]
fn using_checked_evidence_requires_a_proved_implication_and_current_admissions() {
    let source = "fn positive(x: usize) -> usize where x > 0 {
        proof premise: x > 0 by {omega};
        proof bound: x >= 1 by {using premise; intro prior; omega};
        x
    }
    fn main() -> usize {positive(42)}";
    let (program, certificate) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("x >= 1", "x >= 2")).is_err());
    assert!(verify(&source.replace("proof bound:", "x = 0; proof bound:")).is_err());
    let fact = source.replace("proof premise: x > 0 by {omega};", "fact premise = x > 0;");
    assert!(verify(&fact)
        .unwrap_err()
        .contains("requires a checked proof"));
    let stale = "fn main() -> usize {
        let x: usize = 7;
        proof before: x == 7 by {trustme};
        x = 8;
        proof after: x == 8 by {using before; intro prior; omega};
        42
    }";
    assert!(verify(stale)
        .unwrap_err()
        .contains("earlier or unresolved state"));
}
