use clap::{Parser, Subcommand};
use std::io::Write;
use std::{
    env, fs,
    path::PathBuf,
    process::{self, Command},
    time::{SystemTime, UNIX_EPOCH},
};

#[derive(Parser)]
#[command(
    name = "evg",
    version,
    about = "Evergreen proof-oriented language compiler"
)]
struct Cli {
    /// Reject any use of trustme, including in unused definitions.
    #[arg(long, global = true)]
    deny_trust: bool,
    #[command(subcommand)]
    command: Action,
}

#[derive(Subcommand)]
enum Action {
    /// Emit a verified scalar Linux x86-64 executable.
    Build {
        #[arg(required = true)]
        files: Vec<PathBuf>,
        #[arg(short, long)]
        output: PathBuf,
        /// Replay checked source certificates before native emission.
        #[arg(long)]
        proof: Option<PathBuf>,
    },
    /// Verify a program with the internal proof kernel.
    Check {
        #[arg(required = true)]
        files: Vec<PathBuf>,
        /// Replay this proof artifact without invoking proof search.
        #[arg(long)]
        proof: Option<PathBuf>,
    },
    /// Verify source and save a portable, checked proof artifact.
    Prove {
        #[arg(required = true)]
        files: Vec<PathBuf>,
        #[arg(short, long)]
        output: PathBuf,
    },
    /// Verify and evaluate main with bounded execution.
    Run {
        #[arg(required = true)]
        files: Vec<PathBuf>,
    },
    /// Emit Lean source for the reference backend (does not verify).
    Emit {
        file: PathBuf,
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Verify with the optional pinned Lean toolchain.
    LeanCheck { file: PathBuf },
    /// Evaluate the ideal reference model using the optional Lean toolchain.
    LeanRun { file: PathBuf },
}

fn execute() -> Result<(), String> {
    let cli = Cli::parse();
    let files: Vec<&PathBuf> = match &cli.command {
        Action::Check { files, .. }
        | Action::Prove { files, .. }
        | Action::Run { files }
        | Action::Build { files, .. } => files.iter().collect(),
        Action::Emit { file, .. } | Action::LeanCheck { file } | Action::LeanRun { file } => {
            vec![file]
        }
    };
    let file = files.first().ok_or("at least one input file is required")?;
    let source = files
        .iter()
        .map(|file| fs::read_to_string(file).map_err(|e| format!("{}: {e}", file.display())))
        .collect::<Result<Vec<_>, _>>()?
        .join("\n");
    if let Action::Prove { output, .. } = &cli.command {
        let (program, bundle) = evergreen::verify::prove(&source)?;
        enforce_trust(&program, cli.deny_trust)?;
        write_output(output, &bundle.to_text(), &files)?;
        println!(
            "{}; wrote {} certificates to {}",
            status(&program),
            bundle.certificate_count(),
            output.display()
        );
        report_trust(&program);
        return Ok(());
    }
    if matches!(
        cli.command,
        Action::Check { .. } | Action::Run { .. } | Action::Build { .. }
    ) {
        let program = if let Action::Check {
            proof: Some(path), ..
        }
        | Action::Build {
            proof: Some(path), ..
        } = &cli.command
        {
            let bundle = evergreen::certificate::ProofBundle::read(path)?;
            evergreen::verify::verify_with_certificate(&source, &bundle)?
        } else {
            evergreen::verify::verify(&source)?
        };
        enforce_trust(&program, cli.deny_trust)?;
        if let Action::Build { output, .. } = &cli.command {
            let binary = evergreen::native::emit(&program)?;
            write_bytes(output, &binary, &files, true)?;
            println!(
                "{}; built {} (Linux x86-64)",
                status(&program),
                output.display()
            );
            report_trust(&program);
            return Ok(());
        }
        if matches!(cli.command, Action::Check { .. }) {
            println!(
                "{}: {} ({} obligations, internal kernel{})",
                status(&program),
                files
                    .iter()
                    .map(|file| file.display().to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                program.obligations,
                if matches!(cli.command, Action::Check { proof: Some(_), .. }) {
                    ", certificate replay"
                } else {
                    ""
                },
            );
        } else {
            println!("{}", program.run()?);
        }
        report_trust(&program);
        return Ok(());
    }
    let lean = evergreen::emit(&source, matches!(cli.command, Action::LeanRun { .. }))?;
    if let Action::Emit { output, .. } = &cli.command {
        if let Some(path) = output {
            write_output(path, &lean, &files)?;
        } else {
            print!("{lean}");
        }
        return Ok(());
    }
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_nanos();
    let dir = env::temp_dir().join(format!("evergreen-{}-{stamp}", process::id()));
    fs::create_dir(&dir).map_err(|e| e.to_string())?;
    let result = verify(&dir, &lean);
    let _ = fs::remove_dir_all(&dir);
    let output = result?;
    if matches!(cli.command, Action::LeanCheck { .. }) {
        println!("verified {}", file.display());
    } else {
        print!("{output}");
    }
    Ok(())
}

fn status(program: &evergreen::verify::VerifiedProgram) -> String {
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
fn enforce_trust(program: &evergreen::verify::VerifiedProgram, deny: bool) -> Result<(), String> {
    if deny && !program.trusted_assumptions().is_empty() {
        return Err("--deny-trust rejects this program's trustme assumptions".into());
    }
    Ok(())
}
fn report_trust(program: &evergreen::verify::VerifiedProgram) {
    for assumption in program.trusted_assumptions() {
        eprintln!("trustme at line {}: {}", assumption.line, assumption.goal);
    }
}
fn write_output(path: &std::path::Path, content: &str, inputs: &[&PathBuf]) -> Result<(), String> {
    write_bytes(path, content.as_bytes(), inputs, false)
}
fn write_bytes(
    path: &std::path::Path,
    content: &[u8],
    inputs: &[&PathBuf],
    executable: bool,
) -> Result<(), String> {
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(std::path::Path::new("."));
    let name = path.file_name().ok_or("output must be a file path")?;
    let parent = parent.canonicalize().map_err(|e| e.to_string())?;
    let destination = path.canonicalize().unwrap_or_else(|_| parent.join(name));
    for input in inputs {
        if input.canonicalize().map_err(|e| e.to_string())? == destination {
            return Err("output must not overwrite a source input".into());
        }
    }
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_nanos();
    let temp = parent.join(format!(".evg-output-{}-{stamp}.tmp", process::id()));
    let result = (|| {
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temp)
            .map_err(|e| e.to_string())?;
        file.write_all(content).map_err(|e| e.to_string())?;
        if executable {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                file.set_permissions(fs::Permissions::from_mode(0o755))
                    .map_err(|e| e.to_string())?;
            }
            #[cfg(not(unix))]
            return Err("native executable output currently requires a Unix host".into());
        }
        file.sync_all().map_err(|e| e.to_string())?;
        fs::rename(&temp, path).map_err(|e| e.to_string())
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temp);
    }
    result
}

fn verify(dir: &std::path::Path, lean: &str) -> Result<String, String> {
    let file = dir.join("Program.lean");
    fs::write(&file, lean).map_err(|e| e.to_string())?;
    let executable = env::var_os("EVG_LEAN")
        .map(PathBuf::from)
        .unwrap_or_else(|| "lean".into());
    let output = Command::new(&executable).arg(&file).current_dir(dir).output()
        .map_err(|e| format!("cannot execute {}: {e}\nInstall the pinned Lean toolchain; emission alone does not verify a program.", executable.display()))?;
    if !output.status.success() {
        return Err(format!(
            "Lean rejected the program:\n{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

fn main() {
    if let Err(e) = execute() {
        eprintln!("error: {e}");
        process::exit(1);
    }
}
