use super::*;
use crate::compiler::kernel::terms::{Terms, Work};

fn query(version: &str, offset: i128, reverse: bool) -> Vec<Affine<CommittedAtom>> {
    let mut arena = Terms::new().unwrap();
    let work = &mut Work::new(20_000);
    if reverse {
        arena.variable("unrelated", work).unwrap();
    }
    let (x, y) = if reverse {
        let y = arena.variable("y", work).unwrap();
        let x = arena.variable("x", work).unwrap();
        (x, y)
    } else {
        (
            arena.variable("x", work).unwrap(),
            arena.variable("y", work).unwrap(),
        )
    };
    let sum = arena.add(x, y, work).unwrap();
    let offset = arena.number(offset, work).unwrap();
    let index = arena.add(sum, offset, work).unwrap();
    let earlier_side = reverse.then(|| arena.application("side", &[x], work).unwrap());
    let read = arena.application(version, &[index], work).unwrap();
    let side = earlier_side.unwrap_or_else(|| arena.application("side", &[x], work).unwrap());
    let value = arena
        .affine(read, work)
        .unwrap()
        .add(&arena.affine(side, work).unwrap().scale(2).unwrap())
        .unwrap();
    arena
        .committed_rows(
            &[
                value.clone(),
                value.scale(-1).unwrap().add(&Affine::number(-1)).unwrap(),
            ],
            work,
        )
        .unwrap()
}

#[test]
fn structured_arithmetic_artifacts_replay_across_arenas_and_interning_orders() {
    let original = query("contents_v0", 1, false);
    let regenerated = query("contents_v0", 1, true);
    // Local IDs differ, but the portable commitment describes the same terms.
    assert_ne!(original, regenerated);
    assert_eq!(statement_hash(&original), statement_hash(&regenerated));
    let mut recording = Session::recording();
    assert_eq!(recording.prove_with_support(&original).unwrap(), vec![0, 1]);
    let bundle = recording.bundle("structured term fixture").unwrap();
    let bundle = ProofBundle::parse(&bundle.to_text()).unwrap();
    let mut replay = Session::replay(&bundle);
    assert_eq!(replay.prove_with_support(&regenerated).unwrap(), vec![0, 1]);
    assert_eq!(replay.search_count(), 0);
    replay.finish().unwrap();
}

#[test]
fn structured_queries_reject_changed_versions_indices_and_forged_weights() {
    let rows = query("contents_v0", 1, false);
    let mut recording = Session::recording();
    recording.prove_with_support(&rows).unwrap();
    let bundle = recording.bundle("fixture").unwrap();
    // Matching portable digests cannot merge distinct local atom identities.
    // A malformed caller mixing arenas still needs a valid arithmetic proof.
    let another_arena = query("contents_v0", 1, true);
    let mixed = vec![rows[0].clone(), another_arena[1].clone()];
    assert_eq!(statement_hash(&rows), statement_hash(&mixed));
    assert!(Session::replay(&bundle)
        .prove_with_support(&mixed)
        .unwrap_err()
        .contains("does not establish a contradiction"));
    for changed in [
        query("contents_v1", 1, false),
        query("contents_v0", 2, false),
    ] {
        assert!(Session::replay(&bundle)
            .prove_with_support(&changed)
            .unwrap_err()
            .contains("does not match"));
    }
    let mut forged = bundle.clone();
    Arc::make_mut(&mut forged.records)[0].certificate =
        Some(Certificate::from_weights(BTreeMap::from([(0, 1)])).unwrap());
    assert!(Session::replay(&forged)
        .prove_with_support(&rows)
        .unwrap_err()
        .contains("does not establish a contradiction"));
}

#[test]
fn optional_structured_queries_do_not_gain_proofs_during_replay() {
    let rows = query("contents_v0", 1, false);
    let mut recording = Session::recording();
    assert!(!recording.probe(&rows[..1]).unwrap());
    let bundle = recording.bundle("optional fixture").unwrap();
    let regenerated = query("contents_v0", 1, true);
    let mut replay = Session::replay(&bundle);
    assert!(!replay.probe(&regenerated[..1]).unwrap());
    assert_eq!(replay.search_count(), 0);
    replay.finish().unwrap();
    assert!(Session::replay(&bundle)
        .prove_with_support(&regenerated[..1])
        .is_err());
}

#[test]
fn named_and_structured_atoms_have_separate_artifact_domains() {
    let structured = query("contents_v0", 1, false);
    let named = vec![Linear::variable("contents_v0(x+y+1)")];
    assert_ne!(statement_hash(&structured[..1]), statement_hash(&named));
}
