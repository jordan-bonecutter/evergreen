//! Run explicitly with EVG_LEAN set: cargo test --test verification -- --ignored
use std::{fs, process::Command};

#[test]
#[ignore = "requires the pinned Lean toolchain"]
fn proof_kernel_accepts_and_rejects() {
    let cli = env!("CARGO_BIN_EXE_evg");
    let output = Command::new(cli)
        .args(["lean-run", "examples/lean_reference.evg"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
    for file in ["examples/reject_bounds.evg", "examples/reject_contract.evg"] {
        let output = Command::new(cli)
            .args(["lean-check", file])
            .output()
            .unwrap();
        assert!(!output.status.success(), "accepted {file}");
        assert!(String::from_utf8_lossy(&output.stderr).contains("Lean rejected"));
        assert!(output.stdout.is_empty());
    }
    let lean = std::env::var_os("EVG_LEAN").unwrap_or_else(|| "lean".into());
    let output = Command::new(lean)
        .arg("proofs/Planes.lean")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
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
        "examples/composition.evg",
        "examples/references.evg",
        "examples/intermediate_states.evg",
        "examples/update_helpers.evg",
        "examples/drop.evg",
        "examples/named_facts.evg",
        "examples/selective_update.evg",
        "examples/ideal_functions.evg",
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
        "examples/reject_incomplete_state.evg",
        "examples/reject_overflow.evg",
        "examples/reject_false_proof.evg",
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
fn ordered_proof_units_share_checked_contracts() {
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
    let reversed = Command::new(env!("CARGO_BIN_EXE_evg"))
        .args(["run", "examples/counter.evg", "stdlib/counter.evg"])
        .output()
        .unwrap();
    assert!(!reversed.status.success());
    assert!(reversed.stdout.is_empty());
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
