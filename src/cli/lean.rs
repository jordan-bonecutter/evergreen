//! Optional Lean execution and its temporary input directory.
use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

pub(super) fn check(source: &str, file: &Path) -> Result<(), String> {
    execute(source, false)?;
    println!("verified {}", file.display());
    Ok(())
}

pub(super) fn run(source: &str) -> Result<(), String> {
    print!("{}", execute(source, true)?);
    Ok(())
}

fn execute(source: &str, evaluate: bool) -> Result<String, String> {
    let lean = evergreen::emit(source, evaluate)?;
    let dir = env::temp_dir().join(format!("evergreen-{}", super::temporary_id()?));
    fs::create_dir(&dir).map_err(|e| e.to_string())?;
    let result = verify_in(&dir, &lean);
    let _ = fs::remove_dir_all(&dir);
    result
}

fn verify_in(dir: &Path, lean: &str) -> Result<String, String> {
    let file = dir.join("Program.lean");
    fs::write(&file, lean).map_err(|e| e.to_string())?;
    let executable = env::var_os("EVG_LEAN")
        .map(PathBuf::from)
        .unwrap_or_else(|| "lean".into());
    let output = Command::new(&executable)
        .arg(&file)
        .current_dir(dir)
        .output()
        .map_err(|error| {
            format!(
                "cannot execute {}: {error}\nInstall the pinned Lean toolchain; emission alone does not verify a program.",
                executable.display()
            )
        })?;
    if !output.status.success() {
        return Err(format!(
            "Lean rejected the program:\n{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}
