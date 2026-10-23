use clap::{Parser, Subcommand};
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
    #[command(subcommand)]
    command: Action,
}

#[derive(Subcommand)]
enum Action {
    /// Verify a program with the internal proof kernel.
    Check { file: PathBuf },
    /// Verify and evaluate main with bounded execution.
    Run { file: PathBuf },
    /// Emit Lean source for the reference backend (does not verify).
    Emit {
        file: PathBuf,
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Verify with the optional pinned Lean toolchain.
    LeanCheck { file: PathBuf },
    /// Verify and evaluate using the optional Lean toolchain.
    LeanRun { file: PathBuf },
}

fn execute() -> Result<(), String> {
    let cli = Cli::parse();
    let file = match &cli.command {
        Action::Check { file }
        | Action::Run { file }
        | Action::Emit { file, .. }
        | Action::LeanCheck { file }
        | Action::LeanRun { file } => file,
    };
    let source = fs::read_to_string(file).map_err(|e| format!("{}: {e}", file.display()))?;
    if matches!(cli.command, Action::Check { .. } | Action::Run { .. }) {
        let program = evergreen::verify::verify(&source)?;
        if matches!(cli.command, Action::Check { .. }) {
            println!(
                "verified {} ({} obligations, internal kernel)",
                file.display(),
                program.obligations
            );
        } else {
            println!("{}", program.run()?);
        }
        return Ok(());
    }
    let lean = evergreen::emit(&source, matches!(cli.command, Action::LeanRun { .. }))?;
    if let Action::Emit { output, .. } = &cli.command {
        if let Some(path) = output {
            fs::write(path, lean).map_err(|e| format!("{}: {e}", path.display()))?;
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
