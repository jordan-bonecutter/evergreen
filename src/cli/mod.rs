//! CLI orchestration: load sources once and dispatch one command handler.

mod args;
mod diagnostics;
mod format;
mod output;
mod sources;

use args::{Action, Cli, Target};
use clap::Parser;
use evergreen::compiler::{certificate::ProofBundle, verify::VerifiedProgram};
use evergreen::shared::diagnostics::Diagnostic;
type Result<T> = std::result::Result<T, Diagnostic>;
use std::{
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

pub fn run() -> std::result::Result<(), String> {
    let cli = Cli::parse();
    if let Action::Fmt {
        files,
        check,
        staged,
        ..
    } = &cli.command
    {
        return format::run(files, *check, *staged).map_err(|message| {
            diagnostics::render(&Diagnostic::from(message), &[], "", cli.color)
        });
    }
    let loaded = sources::load(cli.command.files(), cli.package_root.as_deref())
        .map_err(|error| diagnostics::render(&error, &[], "", cli.color))?;
    let files = loaded.files;
    let source = loaded.source;
    let result = match &cli.command {
        Action::Fmt { .. } => unreachable!("format dispatched before source loading"),
        Action::Build { output, proof, .. } => {
            let destination = match output {
                Some(path) => path.clone(),
                None => files
                    .last()
                    .ok_or("no source file for default output")?
                    .with_extension(match cli.target {
                        Target::X86_64 => "",
                        Target::Wasm32 => "wasm",
                    }),
            };
            build(
                &source,
                &files,
                &destination,
                proof.as_deref(),
                cli.deny_trust,
                cli.target,
            )
        }
        Action::Check { proof, .. } => check(
            &source,
            &files,
            proof.as_deref(),
            cli.deny_trust,
            cli.target,
        ),
        Action::Prove { output, .. } => prove(&source, &files, output, cli.deny_trust, cli.target),
        Action::Run { .. } => run_program(&source, cli.deny_trust, cli.target),
    };
    result.map_err(|error| diagnostics::render(&error, &files, &source, cli.color))
}

fn checked_program(
    source: &str,
    proof: Option<&Path>,
    deny_trust: bool,
    target: Target,
) -> Result<VerifiedProgram> {
    let program = if let Some(path) = proof {
        let bundle = ProofBundle::read(path)?;
        evergreen::compiler::verify::verify_with_certificate_diagnostic_for_target(
            source,
            &bundle,
            target.into(),
        )?
    } else {
        evergreen::compiler::verify::verify_diagnostic_for_target(source, target.into())?
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
    target: Target,
) -> Result<()> {
    let program = checked_program(source, proof, deny_trust, target)?;
    let (binary, label) = match target {
        Target::X86_64 => (evergreen::compiler::native::emit(&program)?, "Linux x86-64"),
        Target::Wasm32 => (evergreen::compiler::wasm::emit(&program)?, "WebAssembly"),
    };
    match target {
        Target::X86_64 => output::write_executable(destination, &binary, files)?,
        Target::Wasm32 => output::write_binary(destination, &binary, files)?,
    }
    println!(
        "{}; built {} ({label})",
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
    target: Target,
) -> Result<()> {
    let program = checked_program(source, proof, deny_trust, target)?;
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
    target: Target,
) -> Result<()> {
    let (program, bundle) =
        evergreen::compiler::verify::prove_diagnostic_for_target(source, target.into())?;
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

fn run_program(source: &str, deny_trust: bool, target: Target) -> Result<()> {
    let program = checked_program(source, None, deny_trust, target)?;
    let (value, bytes) = evergreen::interpreter::run_with_output(&program)?;
    use std::io::Write;
    std::io::stdout()
        .write_all(&bytes)
        .map_err(|error| error.to_string())?;
    println!("{value}");
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

fn enforce_trust(program: &VerifiedProgram, deny: bool) -> Result<()> {
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

fn temporary_id() -> std::result::Result<String, String> {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_nanos();
    Ok(format!("{}-{stamp}", std::process::id()))
}
