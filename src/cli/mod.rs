//! CLI orchestration: load sources once and dispatch one command handler.

mod args;
mod output;
mod sources;

use args::{Action, Cli};
use clap::Parser;
use evergreen::compiler::{certificate::ProofBundle, verify::VerifiedProgram};
use std::{
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

pub fn run() -> Result<(), String> {
    let cli = Cli::parse();
    let loaded = sources::load(cli.command.files(), cli.package_root.as_deref())?;
    let files = loaded.files;
    let source = loaded.source;
    match &cli.command {
        Action::Build { output, proof, .. } => {
            build(&source, &files, output, proof.as_deref(), cli.deny_trust)
        }
        Action::Check { proof, .. } => check(&source, &files, proof.as_deref(), cli.deny_trust),
        Action::Prove { output, .. } => prove(&source, &files, output, cli.deny_trust),
        Action::Run { .. } => run_program(&source, cli.deny_trust),
    }
}

fn checked_program(
    source: &str,
    proof: Option<&Path>,
    deny_trust: bool,
) -> Result<VerifiedProgram, String> {
    let program = if let Some(path) = proof {
        let bundle = ProofBundle::read(path)?;
        evergreen::compiler::verify::verify_with_certificate(source, &bundle)?
    } else {
        evergreen::compiler::verify::verify(source)?
    };
    enforce_trust(&program, deny_trust)?;
    Ok(program)
}

fn build(
    source: &str,
    files: &[PathBuf],
    destination: &Path,
    proof: Option<&Path>,
    deny_trust: bool,
) -> Result<(), String> {
    let program = checked_program(source, proof, deny_trust)?;
    let binary = evergreen::compiler::native::emit(&program)?;
    output::write_executable(destination, &binary, files)?;
    println!(
        "{}; built {} (Linux x86-64)",
        status(&program),
        destination.display()
    );
    report_trust(&program);
    Ok(())
}

fn check(
    source: &str,
    files: &[PathBuf],
    proof: Option<&Path>,
    deny_trust: bool,
) -> Result<(), String> {
    let program = checked_program(source, proof, deny_trust)?;
    let names = files
        .iter()
        .map(|file| file.display().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let replay = if proof.is_some() {
        ", certificate replay"
    } else {
        ""
    };
    println!(
        "{}: {} ({} obligations, internal kernel{})",
        status(&program),
        names,
        program.obligations,
        replay
    );
    report_trust(&program);
    Ok(())
}

fn prove(
    source: &str,
    files: &[PathBuf],
    destination: &Path,
    deny_trust: bool,
) -> Result<(), String> {
    let (program, bundle) = evergreen::compiler::verify::prove(source)?;
    enforce_trust(&program, deny_trust)?;
    output::write_text(destination, &bundle.to_text(), files)?;
    println!(
        "{}; wrote {} certificates to {}",
        status(&program),
        bundle.certificate_count(),
        destination.display()
    );
    report_trust(&program);
    Ok(())
}

fn run_program(source: &str, deny_trust: bool) -> Result<(), String> {
    let program = checked_program(source, None, deny_trust)?;
    println!("{}", evergreen::interpreter::run(&program)?);
    report_trust(&program);
    Ok(())
}

fn status(program: &VerifiedProgram) -> String {
    let base = if program.trusted_assumptions().is_empty() {
        "verified".into()
    } else {
        format!(
            "checked with {} trusted assumptions",
            program.trusted_assumptions().len()
        )
    };
    let divergent = program.potentially_diverging_functions().count();
    if divergent == 0 {
        base
    } else {
        format!("{base} (safety; {divergent} functions may diverge)")
    }
}

fn enforce_trust(program: &VerifiedProgram, deny: bool) -> Result<(), String> {
    if deny && !program.trusted_assumptions().is_empty() {
        return Err("--deny-trust rejects this program's trustme assumptions".into());
    }
    Ok(())
}

fn report_trust(program: &VerifiedProgram) {
    for assumption in program.trusted_assumptions() {
        eprintln!("trustme at line {}: {}", assumption.line, assumption.goal);
    }
}

fn temporary_id() -> Result<String, String> {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_nanos();
    Ok(format!("{}-{stamp}", std::process::id()))
}
