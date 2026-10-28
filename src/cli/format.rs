//! Formatting selection and publication. Staged checks read the index and
//! never rewrite the working tree or stage unrelated user changes.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

pub(super) fn run(files: &[PathBuf], check: bool, staged: bool) -> Result<(), String> {
    let (root, paths) = if files.is_empty() || staged {
        let root = git(Path::new("."), &["rev-parse", "--show-toplevel"])?;
        let root = PathBuf::from(
            String::from_utf8(root)
                .map_err(|e| e.to_string())?
                .trim_end_matches('\n'),
        );
        let args: &[&str] = if staged {
            &[
                "diff",
                "--cached",
                "--name-only",
                "--diff-filter=ACMR",
                "-z",
                "--",
                "*.evg",
            ]
        } else {
            &["ls-files", "-z", "--", "*.evg"]
        };
        let paths = git(&root, args)?
            .split(|b| *b == 0)
            .filter(|p| !p.is_empty())
            .map(|p| {
                String::from_utf8(p.to_vec())
                    .map(PathBuf::from)
                    .map_err(|e| e.to_string())
            })
            .collect::<Result<Vec<_>, _>>()?;
        (root, paths)
    } else {
        (PathBuf::from("."), files.to_vec())
    };
    let mut changes = Vec::new();
    for relative in paths {
        let path = root.join(&relative);
        let source = if staged {
            let object = format!(":{}", relative.to_str().ok_or("non-UTF-8 staged path")?);
            String::from_utf8(git(&root, &["cat-file", "blob", &object])?)
                .map_err(|e| e.to_string())?
        } else {
            if !fs::symlink_metadata(&path)
                .map_err(|e| format!("{}: {e}", path.display()))?
                .is_file()
            {
                return Err(format!(
                    "{}: format input must be a regular file",
                    path.display()
                ));
            }
            fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?
        };
        let formatted = evergreen::syntax::format::source(&source)
            .map_err(|e| format!("{}: {e}", relative.display()))?;
        if formatted != source {
            changes.push((path, relative, formatted));
        }
    }
    if check || staged {
        if changes.is_empty() {
            return Ok(());
        }
        for (_, path, _) in &changes {
            eprintln!(
                "needs formatting: {}{}",
                path.display(),
                if staged { " (staged)" } else { "" }
            );
        }
        return Err("formatting check failed; run evg fmt on these files".into());
    }
    for (path, relative, formatted) in changes {
        super::output::replace_source(&path, &formatted)?;
        println!("formatted {}", relative.display());
    }
    Ok(())
}

fn git(root: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    let output = Command::new("git")
        .current_dir(root)
        .args(args)
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).trim().to_owned());
    }
    Ok(output.stdout)
}
