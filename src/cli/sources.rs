//! Expand package directories into deterministic, separately scoped source files.

use std::{collections::BTreeSet, fs, path::PathBuf};

type Result<T> = std::result::Result<T, String>;

pub(super) fn expand(inputs: &[PathBuf]) -> Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    let mut seen = BTreeSet::new();
    for input in inputs {
        let paths = if input.is_dir() {
            let mut paths = fs::read_dir(input)
                .map_err(|e| format!("{}: {e}", input.display()))?
                .map(|entry| entry.map(|entry| entry.path()))
                .collect::<std::io::Result<Vec<_>>>()
                .map_err(|e| format!("{}: {e}", input.display()))?;
            paths.retain(|path| path.is_file() && path.extension().is_some_and(|ext| ext == "evg"));
            paths.sort();
            if paths.is_empty() {
                return Err(format!(
                    "{}: package contains no .evg files",
                    input.display()
                ));
            }
            let package_path =
                fs::canonicalize(input).map_err(|e| format!("{}: {e}", input.display()))?;
            let expected = package_path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("package directory needs a name")?;
            let mut package_name = None;
            for path in &paths {
                let source =
                    fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
                let program = evergreen::syntax::parse(&source)
                    .map_err(|e| format!("{}: {e}", path.display()))?;
                if let Some(name) = program.modules.iter().next() {
                    if package_name
                        .as_ref()
                        .is_some_and(|previous| previous != name)
                    {
                        return Err(format!(
                            "{}: all files in a directory must declare the same module",
                            input.display()
                        ));
                    }
                    package_name = Some(name.clone());
                }
                if program.modules.len() != 1
                    || !program
                        .modules
                        .iter()
                        .all(|name| name == expected || name == "main")
                {
                    return Err(format!("{}: directory {} requires one module named {expected} (or main for an executable)", path.display(), input.display()));
                }
            }
            paths
        } else {
            vec![input.clone()]
        };
        for path in paths {
            let canonical =
                fs::canonicalize(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            if seen.insert(canonical) {
                files.push(path);
            }
        }
    }
    Ok(files)
}
