use std::{
    env, fs,
    path::PathBuf,
    process::{self, Command},
    time::{SystemTime, UNIX_EPOCH},
};

fn execute() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.len() != 2 || !matches!(args[0].as_str(), "emit" | "check" | "run") {
        return Err("usage: evg <emit|check|run> <file.evg>\ncheck/run require Lean 4 on PATH (or EVG_LEAN=/path/to/lean)".into());
    }
    let source = fs::read_to_string(&args[1]).map_err(|e| format!("{}: {e}", args[1]))?;
    let lean = evergreen::emit(&source, args[0] == "run")?;
    if args[0] == "emit" {
        print!("{lean}");
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
    if args[0] == "check" {
        println!("verified {}", args[1]);
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
