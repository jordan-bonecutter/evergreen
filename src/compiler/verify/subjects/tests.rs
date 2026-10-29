//! State-subject capture and invalidation regressions.

use super::*;

fn value(n: i128) -> Symbol {
    Symbol::Number(Ty::Nat, Linear::number(n))
}
fn snapshot(stamp: Stamp) -> Snapshot {
    Snapshot {
        reads: BTreeSet::from([stamp]),
        past: BTreeMap::new(),
        values: BTreeMap::new(),
        complete: true,
        key: Some(ClaimKey::Read(stamp)),
    }
}

#[test]
fn saved_quantified_scalars_track_free_parameters_but_not_bound_indices() {
    let formula = Formula::Forall {
        variable: "index".into(),
        domain: Box::new(Formula::Ge(Linear::variable("length"))),
        body: Box::new(Formula::Ge(Linear::variable("index"))),
    };
    let saved =
        Snapshot::saved_scalar(state::WorldId::default(), None, &Symbol::Bool(formula)).unwrap();
    assert!(saved.complete);
    assert_eq!(
        saved.values[&state::WorldId::default()],
        BTreeSet::from(["length".into()])
    );

    let invalid = Formula::Forall {
        variable: String::new(),
        domain: Box::new(Formula::True),
        body: Box::new(Formula::True),
    };
    let saved =
        Snapshot::saved_scalar(state::WorldId::default(), None, &Symbol::Bool(invalid)).unwrap();
    assert!(!saved.complete);
    assert!(saved.key.is_none());
}

#[test]
fn quantified_subject_instantiation_preserves_inner_binders_and_bounds_copy_work() {
    let key = ClaimKey::Forall(
        Box::new(ClaimKey::Bool(true)),
        Box::new(ClaimKey::Forall(
            Box::new(ClaimKey::Bound(0)),
            Box::new(ClaimKey::Binary(
                "==".into(),
                Box::new(ClaimKey::Bound(1)),
                Box::new(ClaimKey::Bound(0)),
            )),
        )),
    );
    let source = Snapshot::from_key(key);
    let argument = Snapshot::from_key(ClaimKey::Number(7));
    let (_, body) = source.universal_parts(&argument, &mut 0).unwrap().unwrap();
    assert_eq!(
        body.key,
        Some(ClaimKey::Forall(
            Box::new(ClaimKey::Bound(0)),
            Box::new(ClaimKey::Binary(
                "==".into(),
                Box::new(ClaimKey::Number(7)),
                Box::new(ClaimKey::Bound(0))
            ))
        ))
    );
    let mut work = MAX_VALUE_WORK;
    assert!(source
        .universal_parts(&argument, &mut work)
        .unwrap_err()
        .contains("work limit"));
    let captured = Snapshot::from_key(ClaimKey::Bound(0));
    assert!(source
        .universal_parts(&captured, &mut 0)
        .unwrap_err()
        .contains("unscoped bound"));
    assert!(source
        .universal_parts(&Snapshot::default(), &mut 0)
        .unwrap()
        .is_none());
}

fn with_source(source: &str, check: impl FnOnce(&mut Context<'_>, &[Statement])) {
    let parsed = syntax::parse(source).unwrap();
    let structs = parsed
        .structs
        .into_iter()
        .map(|record| (record.name.clone(), record))
        .collect();
    let functions: BTreeMap<String, Function> = parsed
        .functions
        .iter()
        .filter(|f| f.name != "main")
        .cloned()
        .map(|f| (f.name.clone(), f))
        .collect();
    // These fixtures intentionally bypass declaration verification; supply
    // explicit empty summaries only for their admission-free helper bodies.
    let summaries = functions
        .keys()
        .map(|name: &String| (name.clone(), summaries::Summary::default()))
        .collect();
    let names = BTreeSet::new();
    let main = parsed.functions.iter().find(|f| f.name == "main").unwrap();
    let declarations = Declarations {
        target: crate::compiler::TargetKind::X86_64,
        functions: &functions,
        summaries: &summaries,
        structs: &structs,
        drops: &names,
        destructors: &functions,
        helpers: &names,
        cleanup_helpers: &names,
    };
    let mut session = Session::search();
    check(&mut Context::new(declarations, &mut session), &main.body);
}

fn named_snapshot(ctx: &Context<'_>, name: &str) -> Snapshot {
    let node = ctx.proof.witnesses[name];
    ctx.proof.evidence.subjects(node).unwrap().clone()
}

#[test]
fn constant_folding_keeps_subjects_and_same_value_assignment_expires_them() {
    let source = "fn main() -> usize {let x: usize = 43; fact is_42 = x == 42; proof admitted: is_42 by {trustme}; x = x; 0}";
    with_source(source, |ctx, body| {
        for statement in &body[..3] {
            ctx.statement(statement).unwrap();
        }
        let node = ctx.proof.witnesses["admitted"];
        assert_eq!(
            ctx.proof.evidence.claim(node).unwrap(),
            &equal(&Linear::number(43), &Linear::number(42)).unwrap()
        );
        let snapshot = named_snapshot(ctx, "admitted");
        assert_eq!(snapshot.reads.len(), 1);
        assert!(ctx
            .proof
            .subjects
            .current(&snapshot, &ctx.storage.memory)
            .unwrap());
        let fact = ctx.proof.facts["is_42"].clone();
        assert_eq!(snapshot.key, ctx.claim_subjects(&fact).unwrap().key);
        ctx.statement(&body[3]).unwrap();
        assert!(!ctx
            .proof
            .subjects
            .current(&snapshot, &ctx.storage.memory)
            .unwrap());
        let fact = ctx.proof.facts["is_42"].clone();
        let current = ctx.claim_subjects(&fact).unwrap();
        assert_ne!(snapshot.key, current.key);
    });
}

#[test]
fn collapsed_arithmetic_does_not_merge_subjects_or_statement_shapes() {
    let source = "fn main() -> usize {let x: usize = 43; let y: usize = 43; proof a: x == 42 by {trustme}; proof b: y == 42 by {trustme}; proof c: x == 0 by {trustme}; 0}";
    with_source(source, |ctx, body| {
        for statement in body {
            ctx.statement(statement).unwrap();
        }
        let a = named_snapshot(ctx, "a");
        let b = named_snapshot(ctx, "b");
        let c = named_snapshot(ctx, "c");
        assert_eq!(
            ctx.proof.evidence.claim(ctx.proof.witnesses["a"]).unwrap(),
            ctx.proof.evidence.claim(ctx.proof.witnesses["b"]).unwrap()
        );
        assert_ne!(a.key, b.key);
        assert_eq!(a.reads, c.reads);
        assert_ne!(a.key, c.key);
    });
}

#[test]
fn call_capture_is_incomplete_and_does_not_evaluate_the_call() {
    let source =
        "fn main() -> usize {let x: usize = 43; proof p: missing(x) == 42 by {trustme}; 0}";
    with_source(source, |ctx, body| {
        ctx.statement(&body[0]).unwrap();
        let Statement::Proof { proposition, .. } = &body[1] else {
            unreachable!()
        };
        let evaluations = ctx.work.eval_steps;
        let snapshot = ctx.claim_subjects(proposition).unwrap();
        assert!(!snapshot.complete);
        assert!(snapshot.key.is_none());
        assert_eq!(snapshot.reads.len(), 1);
        assert_eq!(ctx.work.eval_steps, evaluations);
    });
}

#[test]
fn real_field_assignment_preserves_the_other_fields_subject() {
    let source = "type Pair struct {left: usize, right: usize} fn main() -> usize {let pair = Pair {left: 43, right: 5}; proof a: pair.left == 42 by {trustme}; proof b: pair.right == 42 by {trustme}; pair.left = 43; 0}";
    with_source(source, |ctx, body| {
        for statement in &body[..3] {
            ctx.statement(statement).unwrap();
        }
        let left = named_snapshot(ctx, "a");
        let right = named_snapshot(ctx, "b");
        ctx.statement(&body[3]).unwrap();
        assert!(!ctx
            .proof
            .subjects
            .current(&left, &ctx.storage.memory)
            .unwrap());
        assert!(ctx
            .proof
            .subjects
            .current(&right, &ctx.storage.memory)
            .unwrap());
    });
}

#[test]
fn writing_through_an_alias_expires_the_referents_subject() {
    let source = "fn main() -> usize {let x: usize = 43; let alias = &x; proof a: x == 42 by {trustme}; *alias = 43; 0}";
    with_source(source, |ctx, body| {
        for statement in &body[..3] {
            ctx.statement(statement).unwrap();
        }
        let original = named_snapshot(ctx, "a");
        ctx.statement(&body[3]).unwrap();
        assert!(!ctx
            .proof
            .subjects
            .current(&original, &ctx.storage.memory)
            .unwrap());
    });
}

#[test]
fn moving_an_owner_slot_preserves_the_payload_subject_until_drop() {
    let source = "fn main() -> usize {let owner: unique(usize) = alloc(43); proof a: *owner == 42 by {trustme}; let moved = owner; drop(moved); 0}";
    with_source(source, |ctx, body| {
        for statement in &body[..2] {
            ctx.statement(statement).unwrap();
        }
        let payload = named_snapshot(ctx, "a");
        ctx.statement(&body[2]).unwrap();
        assert!(ctx
            .proof
            .subjects
            .current(&payload, &ctx.storage.memory)
            .unwrap());
        ctx.statement(&body[3]).unwrap();
        assert!(!ctx
            .proof
            .subjects
            .current(&payload, &ctx.storage.memory)
            .unwrap());
    });
}

#[test]
fn helper_effect_contracts_advance_the_actual_callers_subject() {
    let source = "fn change(value: &usize) modifies(value) {*value = 43;} fn main() -> usize {let x: usize = 43; proof a: x == 42 by {trustme}; change(&x); 0}";
    with_source(source, |ctx, body| {
        for statement in &body[..2] {
            ctx.statement(statement).unwrap();
        }
        let original = named_snapshot(ctx, "a");
        ctx.statement(&body[2]).unwrap();
        assert!(!ctx
            .proof
            .subjects
            .current(&original, &ctx.storage.memory)
            .unwrap());
    });
}

#[test]
fn aliases_share_epochs_but_sibling_fields_do_not() {
    let mut memory = Memory::default();
    let plane = memory.allocate(value(0)).unwrap();
    let first = memory.borrow(plane).unwrap();
    let alias = memory.borrow(plane).unwrap();
    let mut subjects = Subjects::default();
    let left = vec![Projection::Field("left".into())];
    let right = vec![Projection::Field("right".into())];
    let old_left = snapshot(subjects.observe(&memory, first, left.clone()).unwrap());
    let old_right = snapshot(subjects.observe(&memory, first, right).unwrap());
    assert_eq!(
        subjects.observe(&memory, alias, left.clone()).unwrap(),
        *old_left.reads.iter().next().unwrap()
    );
    subjects.write(plane, &left).unwrap();
    assert!(!subjects.current(&old_left, &memory).unwrap());
    assert!(subjects.current(&old_right, &memory).unwrap());
    subjects.write(plane, &[]).unwrap();
    assert!(!subjects.current(&old_right, &memory).unwrap());
}

#[test]
fn same_value_writes_and_restored_branch_allocations_cannot_revive_claims() {
    let mut memory = Memory::default();
    let baseline = memory.snapshot();
    let plane = memory.allocate(value(42)).unwrap();
    let reference = memory.borrow(plane).unwrap();
    let mut subjects = Subjects::default();
    let old = snapshot(subjects.observe(&memory, reference, vec![]).unwrap());
    subjects.write(plane, &[]).unwrap();
    memory.write(plane, value(42), false).unwrap();
    assert!(!subjects.current(&old, &memory).unwrap());
    let new = snapshot(subjects.observe(&memory, reference, vec![]).unwrap());
    memory = baseline;
    let reused = memory.allocate(value(42)).unwrap();
    assert_ne!(plane, reused);
    assert!(memory.read(reference).is_err());
    subjects.write(reused, &[]).unwrap();
    assert!(!subjects.current(&new, &memory).unwrap());
}

#[test]
fn generation_changes_invalidate_even_unchanged_contents() {
    let mut memory = Memory::default();
    let plane = memory.allocate(value(42)).unwrap();
    let mut subjects = Subjects::default();
    let stamp = subjects
        .observe(&memory, memory.borrow(plane).unwrap(), vec![])
        .unwrap();
    memory.take(plane).unwrap();
    memory.write(plane, value(42), false).unwrap();
    assert!(!subjects.current(&snapshot(stamp), &memory).unwrap());
}

#[test]
fn unknown_indices_overlap_and_distinct_constant_indices_do_not() {
    let index = |n| vec![Projection::Index(Linear::number(n))];
    assert!(!overlap(&index(0), &index(1)));
    assert!(overlap(
        &index(0),
        &[Projection::Index(Linear::variable("i"))]
    ));
    assert!(overlap(&[], &index(1)));
}

#[test]
fn deferred_admissions_leave_paths_unchanged_and_only_used_claims_become_edges() {
    let source = "fn needs(parameter: usize) where parameter == 42 {} fn main() -> usize {let x: usize = 43; proof unused: false by {trustme}; proof needed: x == 42 by {trustme}; needs(x); 0}";
    with_source(source, |ctx, body| {
        ctx.statement(&body[0]).unwrap();
        let paths = ctx.proof.paths.clone();
        ctx.statement(&body[1]).unwrap();
        ctx.statement(&body[2]).unwrap();
        assert_eq!(ctx.proof.paths, paths);
        let unused = ctx.proof.witnesses["unused"];
        let needed = ctx.proof.witnesses["needed"];
        ctx.statement(&body[3]).unwrap();
        assert_eq!(ctx.proof.paths, paths);
        let dependencies = ctx
            .proof
            .uses
            .iter()
            .flat_map(|&node| ctx.proof.evidence.admissions(node).admissions)
            .collect::<BTreeSet<_>>();
        assert_eq!(dependencies, BTreeSet::from([needed]));
        assert!(!dependencies.contains(&unused));
    });
}

#[test]
fn independently_provable_operations_do_not_acquire_available_admissions() {
    let source = "fn needs(parameter: usize) where parameter == 42 {} fn main() -> usize {let x: usize = 42; proof unnecessary: x == 42 by {trustme}; needs(x); 0}";
    with_source(source, |ctx, body| {
        for statement in body {
            ctx.statement(statement).unwrap();
        }
        assert!(ctx.proof.uses.iter().all(|&node| ctx
            .proof
            .evidence
            .admissions(node)
            .admissions
            .is_empty()));
    });
}

#[test]
fn immutable_plane_roots_preserve_independent_branch_versions() {
    let mut memory = Memory::default();
    let plane = memory.allocate(value(0)).unwrap();
    let reference = memory.borrow(plane).unwrap();
    let mut subjects = Subjects::default();
    subjects.write(plane, &[]).unwrap();
    let left = vec![Projection::Field("left".into())];
    let right = vec![Projection::Field("right".into())];
    let old_left = snapshot(subjects.observe(&memory, reference, left.clone()).unwrap());
    let old_right = snapshot(subjects.observe(&memory, reference, right.clone()).unwrap());
    let base = subjects.snapshot();
    subjects.write(plane, &left).unwrap();
    let a = subjects.snapshot();
    subjects.restore(base.clone());
    assert!(subjects.current(&old_left, &memory).unwrap());
    assert!(subjects.current(&old_right, &memory).unwrap());
    subjects.write(plane, &right).unwrap();
    let b = subjects.snapshot();
    assert!(subjects.current(&old_left, &memory).unwrap());
    assert!(!subjects.current(&old_right, &memory).unwrap());
    subjects.merge(&base, &a, &b, &Formula::True).unwrap();
    assert!(!subjects.current(&old_left, &memory).unwrap());
    assert!(!subjects.current(&old_right, &memory).unwrap());
    subjects.restore(a);
    assert!(!subjects.current(&old_left, &memory).unwrap());
    assert!(subjects.current(&old_right, &memory).unwrap());
    subjects.restore(base);
    assert!(subjects.current(&old_left, &memory).unwrap());
}

#[test]
fn observing_a_region_in_one_branch_does_not_change_the_other_branch() {
    let mut memory = Memory::default();
    let plane = memory.allocate(value(0)).unwrap();
    let reference = memory.borrow(plane).unwrap();
    let mut subjects = Subjects::default();
    subjects.write(plane, &[]).unwrap();
    let base = subjects.snapshot();
    subjects.write(plane, &[]).unwrap();
    let changed = subjects.observe(&memory, reference, vec![]).unwrap();
    let branch = subjects.snapshot();
    subjects.restore(base);
    let unchanged = subjects.observe(&memory, reference, vec![]).unwrap();
    assert_ne!(changed, unchanged);
    assert!(!subjects.current(&snapshot(changed), &memory).unwrap());
    assert!(subjects.current(&snapshot(unchanged), &memory).unwrap());
    subjects.restore(branch);
    assert!(subjects.current(&snapshot(changed), &memory).unwrap());
    assert!(!subjects.current(&snapshot(unchanged), &memory).unwrap());
}

#[test]
fn branch_availability_preserves_siblings_but_not_writes_or_new_generations() {
    let mut memory = Memory::default();
    let plane = memory.allocate(value(0)).unwrap();
    let reference = memory.borrow(plane).unwrap();
    let mut subjects = Subjects::default();
    let left = vec![Projection::Field("left".into())];
    let right = vec![Projection::Field("right".into())];
    let base = subjects.snapshot();
    subjects.write(plane, &left).unwrap();
    let claim = snapshot(subjects.observe(&memory, reference, left.clone()).unwrap());
    let branch = subjects.snapshot();
    let guard = Formula::Ge(Linear::variable("flag"));
    subjects.merge(&base, &branch, &base, &guard).unwrap();
    assert!(!subjects.current(&claim, &memory).unwrap());
    assert_eq!(
        subjects.branch_availability(&claim, &memory).unwrap(),
        guard
    );
    subjects.write(plane, &right).unwrap();
    assert_eq!(
        subjects.branch_availability(&claim, &memory).unwrap(),
        guard
    );
    let before = subjects.snapshot();
    subjects.write(plane, &left).unwrap();
    assert_eq!(
        subjects.branch_availability(&claim, &memory).unwrap(),
        Formula::False
    );
    subjects.restore(before);
    memory.take(plane).unwrap();
    memory.write(plane, value(0), false).unwrap();
    assert_eq!(
        subjects.branch_availability(&claim, &memory).unwrap(),
        Formula::False
    );
}

#[test]
fn statement_snapshots_preserve_old_facts_without_making_them_current() {
    let source = "fn main() -> usize {let x: usize = 43; proof p: x == 42 by {trustme}; x = x; 0}";
    with_source(source, |ctx, body| {
        for statement in body {
            ctx.statement(statement).unwrap();
        }
        assert_eq!(ctx.proof.states.len(), body.len());
        let node = ctx.proof.witnesses["p"];
        let claim = named_snapshot(ctx, "p");
        let stamp = *claim.reads.iter().next().unwrap();
        let plane = ctx.proof.subjects.entries[stamp.subject].plane;
        assert_eq!(
            ctx.proof
                .subjects
                .history
                .region(
                    ctx.proof.states[1].version(plane),
                    stamp.subject,
                    &ctx.proof.subjects.entries[stamp.subject].path
                )
                .unwrap(),
            stamp.revision
        );
        assert_ne!(
            ctx.proof
                .subjects
                .history
                .region(
                    ctx.proof.states[2].version(plane),
                    stamp.subject,
                    &ctx.proof.subjects.entries[stamp.subject].path
                )
                .unwrap(),
            stamp.revision
        );
        assert!(ctx.proof.states[1]
            .candidates(&BTreeSet::from([plane]))
            .contains(&node));
        assert!(!ctx
            .proof
            .subjects
            .current(&claim, &ctx.storage.memory)
            .unwrap());
    });
}

#[test]
fn evaluating_old_helpers_cannot_mutate_the_live_planes_fact_state() {
    let source = "fn identity(value: usize) -> usize where &value == &value ensures result == value {value} fn main() -> usize {let x: usize = 43; proof live: x == 42 by {trustme}; 0}";
    with_source(source, |ctx, body| {
        let ty = Ty::Machine(MachineInt::parse("usize").unwrap());
        let input = ctx
            .allocate_symbol(Symbol::Number(ty.clone(), Linear::number(7)))
            .unwrap();
        let reference = ctx.storage.memory.borrow(input).unwrap();
        ctx.locals.values.insert(
            "input".into(),
            Symbol::Ref(Box::new(ty.clone()), reference, vec![]),
        );
        let mut function = syntax::parse("fn point(input: &usize) -> usize {0}")
            .unwrap()
            .functions
            .remove(0);
        function.entry_memory = true;
        ctx.execution.current = Some("point".into());
        ctx.capture_old(&function).unwrap();
        for statement in body {
            ctx.statement(statement).unwrap();
        }
        let live = named_snapshot(ctx, "live");
        assert!(ctx
            .proof
            .subjects
            .current(&live, &ctx.storage.memory)
            .unwrap());
        let expression = Expr {
            line: 1,
            kind: Kind::Call(
                "identity".into(),
                vec![Expr {
                    line: 1,
                    kind: Kind::Unary(
                        "*".into(),
                        Box::new(Expr {
                            line: 1,
                            kind: Kind::Name("input".into()),
                        }),
                    ),
                }],
            ),
        };
        ctx.old_expression(&expression, Some(&ty)).unwrap();
        assert!(ctx
            .proof
            .subjects
            .current(&live, &ctx.storage.memory)
            .unwrap());
    });
}

#[test]
fn old_pointee_uses_the_saved_world_while_dereferencing_an_old_pointer_is_live() {
    let source = "fn main() -> usize {let x: usize = 7; let pointer = &x; 0}";
    with_source(source, |ctx, body| {
        for statement in body {
            ctx.statement(statement).unwrap();
        }
        let checkpoint = syntax::parse("fn checkpoint(pointer: &usize) {}")
            .unwrap()
            .functions
            .remove(0);
        ctx.capture_old(&checkpoint).unwrap();
        let pointer = Expr {
            kind: Kind::Name("pointer".into()),
            line: 1,
        };
        let dereference = Expr {
            kind: Kind::Unary("*".into(), Box::new(pointer.clone())),
            line: 1,
        };
        let old_value = Expr {
            kind: Kind::Call("old".into(), vec![dereference.clone()]),
            line: 1,
        };
        let old_pointer = Expr {
            kind: Kind::Call("old".into(), vec![pointer]),
            line: 1,
        };
        let live_value = Expr {
            kind: Kind::Unary("*".into(), Box::new(old_pointer)),
            line: 1,
        };
        let historical = ctx.claim_subjects(&old_value).unwrap();
        let live = ctx.claim_subjects(&live_value).unwrap();
        assert!(historical.complete && historical.reads.is_empty());
        assert_eq!(historical.past.len(), 1);
        assert_eq!(live.reads.len(), 1);
        ctx.assign_starting_owners(
            &dereference,
            &Expr {
                kind: Kind::Number(8),
                line: 1,
            },
            &[],
        )
        .unwrap();
        assert!(ctx
            .proof
            .subjects
            .current(&historical, &ctx.storage.memory)
            .unwrap());
        assert!(!ctx
            .proof
            .subjects
            .current(&live, &ctx.storage.memory)
            .unwrap());
        let stamp = *historical
            .past
            .values()
            .next()
            .unwrap()
            .iter()
            .next()
            .unwrap();
        assert!(ctx
            .proof
            .subjects
            .historical(&snapshot(stamp), ctx.entry.world)
            .unwrap());
        assert!(!ctx
            .proof
            .subjects
            .current(&snapshot(stamp), &ctx.storage.memory)
            .unwrap());
    });
}

#[test]
fn complex_old_subjects_resolve_saved_storage_without_changing_live_revisions() {
    with_source(
        "fn main() {let data: [usize; 2] = [7, 9]; let pointer = &data;}",
        |ctx, body| {
            for statement in body {
                ctx.statement(statement).unwrap();
            }
            let mut function = syntax::parse("fn checkpoint(pointer: &[usize; 2]) -> usize ensures result == old((*pointer)[0]) {0}")
            .unwrap().functions.remove(0);
            function.entry_memory = true;
            ctx.capture_old(&function).unwrap();
            let Kind::Binary(_, _, old) = &function.post.as_ref().unwrap().kind else {
                panic!()
            };
            let Kind::Call(_, args) = &old.kind else {
                panic!()
            };
            let place = &args[0];
            let before = ctx.claim_subjects(place).unwrap();
            let historical = ctx.claim_subjects(old).unwrap();
            assert!(historical.complete);
            assert!(historical.reads.is_empty());
            assert_eq!(historical.past.len(), 1);
            ctx.assign_starting_owners(
                place,
                &Expr {
                    kind: Kind::Number(42),
                    line: 1,
                },
                &[],
            )
            .unwrap();
            let live = ctx.claim_subjects(place).unwrap();
            assert_ne!(before.key, live.key);
            let again = ctx.claim_subjects(old).unwrap();
            assert_eq!(again.key, historical.key);
            assert!(ctx
                .proof
                .subjects
                .current(&live, &ctx.storage.memory)
                .unwrap());
            assert!(!ctx
                .proof
                .subjects
                .current(&before, &ctx.storage.memory)
                .unwrap());
            assert_eq!(
                ctx.old_expression(place, None).unwrap().number().unwrap(),
                Linear::number(7)
            );
        },
    );
}

#[test]
fn conditional_admissions_depend_on_the_condition_and_both_value_footprints() {
    let source = "fn main() {let flag = true; let a: usize = 1; let b: usize = 2; proof assumed: if flag {a == 42} else {b == 42} by {trustme}; proof reused: if flag {a == 42} else {b == 42} by {exact assumed};}";
    let (_, bundle) = prove(source).unwrap();
    verify_with_certificate(source, &bundle).unwrap();
    for change in ["flag = false;", "a = 2;", "b = 3;"] {
        let stale = source.replace("proof reused:", &format!("{change} proof reused:"));
        assert!(verify(&stale).is_err(), "{stale}");
    }
}
