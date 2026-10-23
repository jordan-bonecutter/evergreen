//! Run explicitly with EVG_LEAN set: cargo test --test verification -- --ignored
use std::{fs, process::Command};

#[test]
#[ignore = "requires the pinned Lean toolchain"]
fn proof_kernel_accepts_and_rejects() {
    let cli = env!("CARGO_BIN_EXE_evg");
    let output = Command::new(cli)
        .args(["lean-run", "examples/contracts.evg"])
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
        .args(["lean-check", "examples/contracts.evg"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("cannot execute"));
}

#[test]
fn emission_is_inspectable_without_backend() {
    let output = Command::new(env!("CARGO_BIN_EXE_evg"))
        .args(["emit", "examples/contracts.evg"])
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
