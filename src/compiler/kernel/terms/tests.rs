use super::*;
use crate::compiler::kernel::{check, solve};
use std::collections::BTreeSet;

#[test]
fn applications_preserve_versions_indices_and_argument_order() {
    let mut terms = Terms::new().unwrap();
    let work = &mut Work::new(10_000);
    let i = terms.variable("i", work).unwrap();
    let j = terms.variable("j", work).unwrap();
    let first = terms.application("contents_v0", &[i, j], work).unwrap();
    assert_eq!(
        first,
        terms.application("contents_v0", &[i, j], work).unwrap()
    );
    assert_ne!(
        first,
        terms.application("contents_v0", &[j, i], work).unwrap()
    );
    assert_ne!(
        first,
        terms.application("contents_v1", &[i, j], work).unwrap()
    );
    assert_ne!(first, terms.variable("contents_v0(i,j)", work).unwrap());
    let constraints = [
        terms.affine(first, work).unwrap(),
        terms
            .affine(first, work)
            .unwrap()
            .scale(-1)
            .unwrap()
            .add(&Affine::number(-1))
            .unwrap(),
    ];
    let certificate = solve(&constraints).unwrap();
    check(&constraints, &certificate).unwrap();
    let changed = terms.application("contents_v1", &[i, j], work).unwrap();
    let wrong_version = [
        constraints[0].clone(),
        terms
            .affine(changed, work)
            .unwrap()
            .scale(-1)
            .unwrap()
            .add(&Affine::number(-1))
            .unwrap(),
    ];
    assert!(check(&wrong_version, &certificate).is_err());
    assert!(solve(&wrong_version).is_err());
    let changed = terms.application("contents_v0", &[i, i], work).unwrap();
    let wrong_index = [
        constraints[0].clone(),
        terms
            .affine(changed, work)
            .unwrap()
            .scale(-1)
            .unwrap()
            .add(&Affine::number(-1))
            .unwrap(),
    ];
    assert!(check(&wrong_index, &certificate).is_err());
    assert!(solve(&wrong_index).is_err());
}

#[test]
fn substitution_traverses_application_arguments_and_keeps_old_terms_immutable() {
    let mut terms = Terms::new().unwrap();
    let work = &mut Work::new(10_000);
    let i = terms.variable("i", work).unwrap();
    let n = terms.variable("n", work).unwrap();
    let one = terms.number(1, work).unwrap();
    let plus_one = terms.add(i, one, work).unwrap();
    let read = terms.application("contents_v0", &[plus_one], work).unwrap();
    let root = terms.application("predicate", &[read, n], work).unwrap();
    let original_commitment = terms.commitment(root, work).unwrap();
    assert_eq!(
        terms.free_variables(root, work).unwrap(),
        BTreeSet::from(["i".into(), "n".into()])
    );
    let seven = terms.number(7, work).unwrap();
    let rewritten = terms
        .substitute(root, &BTreeMap::from([("i".into(), seven)]), work)
        .unwrap();
    let eight = terms.number(8, work).unwrap();
    let expected_read = terms.application("contents_v0", &[eight], work).unwrap();
    let expected = terms
        .application("predicate", &[expected_read, n], work)
        .unwrap();
    assert_eq!(rewritten, expected);
    assert_ne!(
        original_commitment,
        terms.commitment(rewritten, work).unwrap()
    );
    assert_eq!(original_commitment, terms.commitment(root, work).unwrap());
    assert_eq!(
        terms.free_variables(rewritten, work).unwrap(),
        BTreeSet::from(["n".into()])
    );
    assert_eq!(
        terms.free_variables(root, work).unwrap(),
        BTreeSet::from(["i".into(), "n".into()])
    );
    assert_eq!(
        terms.substitute(root, &BTreeMap::new(), work).unwrap(),
        root
    );
}

#[test]
fn simultaneous_substitution_does_not_rewrite_inserted_arguments() {
    let mut terms = Terms::new().unwrap();
    let work = &mut Work::new(10_000);
    let x = terms.variable("x", work).unwrap();
    let y = terms.variable("y", work).unwrap();
    let seven = terms.number(7, work).unwrap();
    let root = terms.application("pair", &[x, y], work).unwrap();
    let rewritten = terms
        .substitute(
            root,
            &BTreeMap::from([("x".into(), y), ("y".into(), seven)]),
            work,
        )
        .unwrap();
    assert_eq!(
        rewritten,
        terms.application("pair", &[y, seven], work).unwrap()
    );
    let both_seven = terms.application("pair", &[seven, seven], work).unwrap();
    assert_ne!(rewritten, both_seven);
}

#[test]
fn normalized_argument_arithmetic_preserves_application_identity() {
    let mut terms = Terms::new().unwrap();
    let work = &mut Work::new(10_000);
    let x = terms.variable("x", work).unwrap();
    let one = terms.number(1, work).unwrap();
    let left = terms.add(x, one, work).unwrap();
    let right = terms.add(one, x, work).unwrap();
    assert_eq!(left, right);
    let a = terms.application("select", &[left], work).unwrap();
    let b = terms.application("select", &[right], work).unwrap();
    assert_eq!(a, b);
    let negative = terms.scale(a, -1, work).unwrap();
    let zero = terms.add(a, negative, work).unwrap();
    assert_eq!(zero, terms.number(0, work).unwrap());
    let sum = terms.add(x, left, work).unwrap();
    let two = terms.number(2, work).unwrap();
    let result = terms
        .substitute(sum, &BTreeMap::from([("x".into(), two)]), work)
        .unwrap();
    assert_eq!(result, terms.number(5, work).unwrap());
}

#[test]
fn a_deep_shared_dag_does_not_expand_into_an_exponential_tree() {
    let mut terms = Terms::new().unwrap();
    let build = &mut Work::new(100_000);
    let x = terms.variable("x", build).unwrap();
    let mut root = x;
    for _ in 0..4000 {
        root = terms.application("f", &[root, root], build).unwrap();
    }
    assert_eq!(terms.node_count(), 4001);
    assert_eq!(
        terms
            .substitute(root, &BTreeMap::new(), &mut Work::new(1))
            .unwrap(),
        root
    );
    let mut observations = Work::new(50_000);
    assert_eq!(
        terms.free_variables(root, &mut observations).unwrap(),
        BTreeSet::from(["x".into()])
    );
    assert!(observations.spent() < 25_000);
    let y = terms.variable("y", build).unwrap();
    let rewrite = &mut Work::new(100_000);
    let rewritten = terms
        .substitute(root, &BTreeMap::from([("x".into(), y)]), rewrite)
        .unwrap();
    assert!(rewrite.spent() < 60_000);
    assert_eq!(terms.node_count(), 8002);
    assert_eq!(
        terms
            .free_variables(rewritten, &mut Work::new(50_000))
            .unwrap(),
        BTreeSet::from(["y".into()])
    );
}

#[test]
fn foreign_ids_exhaustion_and_numeric_overflow_fail_closed() {
    let mut terms = Terms::new().unwrap();
    let mut other = Terms::new().unwrap();
    let work = &mut Work::new(10_000);
    let x = terms.variable("x", work).unwrap();
    let foreign = other.variable("x", work).unwrap();
    assert_ne!(x, foreign);
    assert!(terms.application("f", &[foreign], work).is_err());
    assert!(terms.add(x, foreign, work).is_err());
    assert!(terms
        .substitute(x, &BTreeMap::from([("x".into(), foreign)]), work)
        .is_err());
    assert!(terms.free_variables(foreign, work).is_err());
    let before = terms.node_count();
    assert!(terms
        .application("many", &[x; 10], &mut Work::new(2))
        .is_err());
    assert_eq!(terms.node_count(), before);
    let maximum = terms.number(i128::MAX, work).unwrap();
    let one = terms.number(1, work).unwrap();
    assert!(terms.add(maximum, one, work).is_err());
    let scaled = terms.scale(x, i128::MAX, work).unwrap();
    let two = terms.number(2, work).unwrap();
    assert!(terms
        .substitute(scaled, &BTreeMap::from([("x".into(), two)]), work)
        .is_err());
    assert_eq!(
        terms.free_variables(scaled, work).unwrap(),
        BTreeSet::from(["x".into()])
    );
}

#[test]
fn commitments_preserve_structure_and_are_bounded_by_dag_size() {
    let mut terms = Terms::new().unwrap();
    let build = &mut Work::new(100_000);
    let x = terms.variable("x", build).unwrap();
    let empty_application = terms.application("x", &[], build).unwrap();
    assert_ne!(
        terms.commitment(x, build).unwrap(),
        terms.commitment(empty_application, build).unwrap()
    );
    let mut root = x;
    for _ in 0..4000 {
        root = terms.application("f", &[root, root], build).unwrap();
    }
    assert!(terms.commitment(root, &mut Work::new(100)).is_err());
    let mut work = Work::new(400_000);
    let digest = terms.commitment(root, &mut work).unwrap();
    assert!(work.spent() < 300_000);
    assert_eq!(digest, terms.commitment(root, &mut Work::new(2)).unwrap());

    let mut foreign = Terms::new().unwrap();
    let foreign = foreign.variable("x", build).unwrap();
    assert!(terms.commitment(foreign, build).is_err());
    let one = terms.number(1, build).unwrap();
    assert!(terms
        .committed_rows(&[Affine::variable(one)], build)
        .is_err());
}
