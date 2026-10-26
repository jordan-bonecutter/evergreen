//! Run explicitly with EVG_LEAN set: cargo test --test verification -- --ignored

use std::{fs, process::Command};

#[test]
#[ignore = "requires the pinned Lean toolchain"]
fn proof_kernel_accepts_and_rejects() {
    let cli = env!("CARGO_BIN_EXE_evg");
    for file in [
        "examples/lean_reference.evg",
        "examples/lean_implication.evg",
        "examples/lean_propositional.evg",
        "examples/lean_proof_cases.evg",
    ] {
        let output = Command::new(cli).args(["lean-run", file]).output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
    }
    for file in [
        "examples/reject_bounds.evg",
        "examples/reject_contract.evg",
        "examples/reject_proof_scope.evg",
        "examples/reject_case_scope.evg",
    ] {
        let output = Command::new(cli)
            .args(["lean-check", file])
            .output()
            .unwrap();
        assert!(!output.status.success(), "accepted {file}");
        assert!(String::from_utf8_lossy(&output.stderr).contains("Lean rejected"));
        assert!(output.stdout.is_empty());
    }
    let lean = std::env::var_os("EVG_LEAN").unwrap_or_else(|| "lean".into());
    for specification in [
        "proofs/Planes.lean",
        "proofs/LinearCertificates.lean",
        "proofs/MemoryContracts.lean",
        "proofs/SharedOwnership.lean",
        "proofs/PartialCorrectness.lean",
        "proofs/PropositionalProofs.lean",
    ] {
        let output = Command::new(&lean).arg(specification).output().unwrap();
        assert!(
            output.status.success(),
            "{specification}: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn missing_backend_never_reports_verified() {
    let output = Command::new(env!("CARGO_BIN_EXE_evg"))
        .env("EVG_LEAN", "/nonexistent/evergreen/lean")
        .args(["lean-check", "examples/lean_reference.evg"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("cannot execute"));
}

#[test]
fn emission_is_inspectable_without_backend() {
    let output = Command::new(env!("CARGO_BIN_EXE_evg"))
        .args(["emit", "examples/lean_reference.evg"])
        .output()
        .unwrap();
    assert!(output.status.success());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("Vector (Int) (n)"));
    assert!(!text.contains("#eval"));
    assert!(fs::metadata("lean-toolchain").is_ok());
}

#[test]
fn internal_backend_needs_no_external_tools() {
    for file in [
        "examples/contracts.evg",
        "examples/opaque_values.evg",
        "examples/composition.evg",
        "examples/references.evg",
        "examples/intermediate_states.evg",
        "examples/update_helpers.evg",
        "examples/update_methods.evg",
        "examples/temporary_methods.evg",
        "examples/drop.evg",
        "examples/named_facts.evg",
        "examples/selective_update.evg",
        "examples/ideal_functions.evg",
        "examples/computed_places.evg",
        "examples/old_places.evg",
        "examples/reference_fields.evg",
        "examples/drop_effects.evg",
        "examples/drop_children.evg",
        "examples/owned_borrows.evg",
        "examples/owned_planes.evg",
        "examples/owned_result_views.evg",
        "examples/heap_updates.evg",
        "examples/borrowed_view.evg",
        "examples/borrowed_array.evg",
        "examples/borrowed_array_owners.evg",
        "examples/reference_array_inputs.evg",
        "examples/aliasing_calls.evg",
        "examples/propositional_proofs.evg",
        "examples/proof_cases.evg",
        "examples/reference_identity.evg",
        "examples/conditional_borrows.evg",
        "examples/conditional_drop.evg",
        "examples/conditional_contracts.evg",
        "examples/old_selection.evg",
        "examples/old_accessors.evg",
        "examples/array_frame_history.evg",
        "examples/array_branch_history.evg",
        "examples/array_model.evg",
        "examples/record_array_history.evg",
        "examples/record_array_values.evg",
        "examples/record_array_borrows.evg",
        "examples/update_calls.evg",
        "examples/self_observing_fields.evg",
        "examples/update_borrow_writes.evg",
        "examples/ideal_borrow_resources.evg",
        "examples/ideal_update_state.evg",
        "examples/ideal_fields.evg",
        "examples/ideal_borrow_writes.evg",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_evg"))
            .env("PATH", "")
            .env("EVG_LEAN", "/nonexistent/lean")
            .args(["run", file])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
    }
    for file in [
        "examples/reject_bounds.evg",
        "examples/reject_contract.evg",
        "examples/reject_dangling.evg",
        "examples/reject_heap_use_after_free.evg",
        "examples/reject_heap_duplicate_owner.evg",
        "examples/reject_heap_borrow_write.evg",
        "examples/reject_heap_update_intermediate.evg",
        "examples/reject_incomplete_state.evg",
        "examples/reject_record_array_invariant.evg",
        "examples/reject_update_call_intermediate.evg",
        "examples/reject_self_observing_write.evg",
        "examples/reject_update_borrow_write.evg",
        "examples/reject_ideal_borrow_escape.evg",
        "examples/reject_overflow.evg",
        "examples/reject_false_proof.evg",
        "examples/reject_proof_scope.evg",
        "examples/reject_case_scope.evg",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_evg"))
            .env("PATH", "")
            .args(["check", file])
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn proof_units_share_checked_contracts_independent_of_input_order() {
    let credits = Command::new(env!("CARGO_BIN_EXE_evg"))
        .env("PATH", "")
        .args([
            "--deny-trust",
            "check",
            "stdlib/credits/credits.evg",
            "stdlib/borrow_credits/borrow_credits.evg",
            "proofs/borrow_credits.evg",
            "proofs/borrow_credit_updates.evg",
            "proofs/carried_borrow_credits.evg",
            "proofs/borrowed_credit_transfer.evg",
            "proofs/borrowed_token_transfer.evg",
        ])
        .output()
        .unwrap();
    assert!(
        credits.status.success(),
        "{}",
        String::from_utf8_lossy(&credits.stderr)
    );
    let output = Command::new(env!("CARGO_BIN_EXE_evg"))
        .env("PATH", "")
        .args([
            "check",
            "proofs/rc_protocol.evg",
            "proofs/arc_interleavings.evg",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let bad = Command::new(env!("CARGO_BIN_EXE_evg"))
        .args([
            "check",
            "proofs/rc_protocol.evg",
            "proofs/reject_arc_stale_check.evg",
        ])
        .output()
        .unwrap();
    assert!(!bad.status.success());
    assert!(bad.stdout.is_empty());
    assert!(String::from_utf8_lossy(&bad.stderr).contains("precondition of reserve"));
    let output = Command::new(env!("CARGO_BIN_EXE_evg"))
        .env("PATH", "")
        .args([
            "--deny-trust",
            "run",
            "stdlib/counter.evg",
            "examples/counter.evg",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
    for example in ["examples/array_updates.evg", "examples/write_borrows.evg"] {
        let arrays = Command::new(env!("CARGO_BIN_EXE_evg"))
            .env("PATH", "")
            .args(["--deny-trust", "run", "stdlib/arrays/array.evg", example])
            .output()
            .unwrap();
        assert!(
            arrays.status.success(),
            "{}",
            String::from_utf8_lossy(&arrays.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&arrays.stdout).trim(), "42");
    }
    let credits = Command::new(env!("CARGO_BIN_EXE_evg"))
        .env("PATH", "")
        .args([
            "--deny-trust",
            "check",
            "stdlib/credits/credits.evg",
            "proofs/opaque_credits.evg",
        ])
        .output()
        .unwrap();
    assert!(
        credits.status.success(),
        "{}",
        String::from_utf8_lossy(&credits.stderr)
    );
    let forged = Command::new(env!("CARGO_BIN_EXE_evg"))
        .args([
            "check",
            "stdlib/credits/credits.evg",
            "examples/reject_forged_credit.evg",
        ])
        .output()
        .unwrap();
    assert!(!forged.status.success());
    assert!(forged.stdout.is_empty());
    assert!(String::from_utf8_lossy(&forged.stderr).contains("opaque representation"));
    let reversed = Command::new(env!("CARGO_BIN_EXE_evg"))
        .args(["run", "examples/counter.evg", "stdlib/counter.evg"])
        .output()
        .unwrap();
    assert!(
        reversed.status.success(),
        "{}",
        String::from_utf8_lossy(&reversed.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&reversed.stdout).trim(), "42");
}

#[test]
fn proof_artifacts_and_trust_policy_are_enforced_by_cli() {
    let cli = env!("CARGO_BIN_EXE_evg");
    let dir = std::env::temp_dir().join(format!("evergreen-cache-test-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let artifact = dir.join("proof.evgproof");
    let artifact = artifact.to_str().unwrap();
    let run = |args: &[&str]| {
        Command::new(cli)
            .env("PATH", "")
            .args(args)
            .output()
            .unwrap()
    };
    let output = run(&["prove", "examples/contracts.evg", "-o", artifact]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        run(&["check", "examples/contracts.evg", "--proof", artifact])
            .status
            .success()
    );
    assert!(
        !run(&["check", "examples/increment.evg", "--proof", artifact])
            .status
            .success()
    );
    let previous = fs::read(artifact).unwrap();
    let denied = run(&[
        "--deny-trust",
        "prove",
        "examples/trustme.evg",
        "-o",
        artifact,
    ]);
    assert!(!denied.status.success());
    assert!(denied.stdout.is_empty());
    assert_eq!(fs::read(artifact).unwrap(), previous);
    let trusted = run(&["check", "examples/trustme.evg"]);
    assert!(trusted.status.success());
    assert!(String::from_utf8_lossy(&trusted.stdout).contains("checked with 1 trusted assumptions"));
    assert!(String::from_utf8_lossy(&trusted.stderr).contains("trustme at line"));
    assert!(!run(&["--deny-trust", "check", "examples/trustme.evg"])
        .status
        .success());
    let source = dir.join("source.evg");
    fs::write(&source, include_str!("../examples/contracts.evg")).unwrap();
    assert!(!run(&[
        "prove",
        source.to_str().unwrap(),
        "-o",
        source.to_str().unwrap()
    ])
    .status
    .success());
    assert_eq!(
        fs::read_to_string(&source).unwrap(),
        include_str!("../examples/contracts.evg")
    );
    fs::remove_dir_all(dir).unwrap();
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_cli_builds_without_external_tools_and_preserves_failed_outputs() {
    let cli = env!("CARGO_BIN_EXE_evg");
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "evergreen-native-cli-{}-{stamp}",
        std::process::id()
    ));
    fs::create_dir(&directory).unwrap();
    let binary = directory.join("program");
    let proof = directory.join("source.evgproof");
    let run = |args: &[&str]| {
        Command::new(cli)
            .env("PATH", "")
            .args(args)
            .output()
            .unwrap()
    };
    let saved = run(&[
        "prove",
        "examples/native.evg",
        "-o",
        proof.to_str().unwrap(),
    ]);
    assert!(saved.status.success());
    let built = run(&[
        "--deny-trust",
        "build",
        "examples/native.evg",
        "--proof",
        proof.to_str().unwrap(),
        "-o",
        binary.to_str().unwrap(),
    ]);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let output = Command::new(&binary).output().unwrap();
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    let previous = fs::read(&binary).unwrap();
    for source in [
        "proofs/affine_credits.evg",
        "examples/reject_overflow.evg",
        "examples/trustme.evg",
    ] {
        let failed = run(&[
            "--deny-trust",
            "build",
            source,
            "-o",
            binary.to_str().unwrap(),
        ]);
        assert!(!failed.status.success());
        assert!(failed.stdout.is_empty());
        assert_eq!(fs::read(&binary).unwrap(), previous);
    }
    let source = directory.join("input.evg");
    fs::write(&source, include_str!("../examples/native.evg")).unwrap();
    assert!(!run(&[
        "build",
        source.to_str().unwrap(),
        "-o",
        source.to_str().unwrap()
    ])
    .status
    .success());
    assert_eq!(
        fs::read_to_string(&source).unwrap(),
        include_str!("../examples/native.evg")
    );
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn runtime_divergence_is_reported_and_cannot_escape_into_logic() {
    let cli = env!("CARGO_BIN_EXE_evg");
    let checked = Command::new(cli)
        .args(["--deny-trust", "check", "examples/partial_recursion.evg"])
        .output()
        .unwrap();
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    assert!(String::from_utf8_lossy(&checked.stdout).contains("functions may diverge"));
    let ran = Command::new(cli)
        .args(["run", "examples/partial_recursion.evg"])
        .output()
        .unwrap();
    assert!(ran.status.success());
    assert_eq!(String::from_utf8_lossy(&ran.stdout).trim(), "42");
    let rejected = Command::new(cli)
        .args(["check", "examples/reject_divergent_proof.evg"])
        .output()
        .unwrap();
    assert!(!rejected.status.success());
    assert!(rejected.stdout.is_empty());
    assert!(String::from_utf8_lossy(&rejected.stderr).contains("potentially divergent"));
}

#[test]
fn syscall_declarations_cannot_bypass_deny_trust() {
    let cli = env!("CARGO_BIN_EXE_evg");
    let denied_atomic = Command::new(cli)
        .args([
            "--deny-trust",
            "check",
            "stdlib/x86_64_atomics/x86_64_atomics.evg",
            "examples/compare_exchange.evg",
        ])
        .output()
        .unwrap();
    assert!(!denied_atomic.status.success());
    let atomic = Command::new(cli)
        .args([
            "run",
            "stdlib/x86_64_atomics/x86_64_atomics.evg",
            "examples/compare_exchange.evg",
        ])
        .output()
        .unwrap();
    assert!(
        atomic.status.success(),
        "{}",
        String::from_utf8_lossy(&atomic.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&atomic.stdout).trim(), "42");
    let output = Command::new(cli)
        .args(["--deny-trust", "check", "examples/hello.evg"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("trust"));
    let output = Command::new(cli)
        .args(["run", "stdlib/linux_io/linux_io.evg", "examples/hello.evg"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("native executable"));
    assert!(output.stdout.is_empty());
}

#[test]
fn directory_packages_share_file_scope_and_replay_certificates() {
    let cli = env!("CARGO_BIN_EXE_evg");
    let packages = ["examples/packages/arithmetic", "examples/packages/demo"];
    let output = Command::new(cli)
        .arg("run")
        .args(packages)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
    let proof = std::env::temp_dir().join(format!(
        "evergreen-packages-{}.evgproof",
        std::process::id()
    ));
    let output = Command::new(cli)
        .arg("prove")
        .args(packages)
        .arg("-o")
        .arg(&proof)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new(cli)
        .arg("check")
        .args(packages)
        .arg("--proof")
        .arg(&proof)
        .output()
        .unwrap();
    fs::remove_file(proof).unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("certificate replay"));
    let output = Command::new(cli)
        .args(["check", "stdlib"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires one module"));
}

#[test]
fn local_imports_load_before_clients_and_bind_dependency_proofs() {
    let cli = env!("CARGO_BIN_EXE_evg");
    let output = Command::new(cli)
        .args([
            "--package-root",
            "examples/packages",
            "run",
            "examples/packages/demo",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
    let root = std::env::temp_dir().join(format!("evergreen-imports-{}", std::process::id()));
    fs::create_dir_all(root.join("a")).unwrap();
    fs::create_dir_all(root.join("b")).unwrap();
    fs::create_dir_all(root.join("app")).unwrap();
    fs::write(
        root.join("a/a.evg"),
        "module a; import b; fn answer() -> usize {b::answer()}",
    )
    .unwrap();
    fs::write(root.join("b/b.evg"), "module b; fn answer() -> usize {42}").unwrap();
    fs::write(
        root.join("app/main.evg"),
        "module main; import a; fn main() -> usize {a::answer()}",
    )
    .unwrap();
    let proof = root.join("app.evgproof");
    let output = Command::new(cli)
        .arg("--package-root")
        .arg(&root)
        .arg("prove")
        .arg(root.join("app"))
        .arg("-o")
        .arg(&proof)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new(cli)
        .arg("--package-root")
        .arg(&root)
        .arg("check")
        .arg(root.join("app"))
        .arg("--proof")
        .arg(&proof)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::write(root.join("b/b.evg"), "module b; fn answer() -> usize {43}").unwrap();
    let output = Command::new(cli)
        .arg("--package-root")
        .arg(&root)
        .arg("check")
        .arg(root.join("app"))
        .arg("--proof")
        .arg(&proof)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("source"));
    fs::write(
        root.join("b/b.evg"),
        "module b; import a; fn answer() -> usize {a::answer()}",
    )
    .unwrap();
    let output = Command::new(cli)
        .arg("--package-root")
        .arg(&root)
        .arg("check")
        .arg(root.join("app"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("cyclic package imports"));
    fs::write(
        root.join("b/b.evg"),
        "module b; import missing; fn answer() -> usize {42}",
    )
    .unwrap();
    let output = Command::new(cli)
        .arg("--package-root")
        .arg(&root)
        .arg("check")
        .arg(root.join("app"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("unresolved import missing"));
    fs::remove_dir_all(root).unwrap();
}
