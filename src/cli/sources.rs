//! Deterministic package loading with explicit roots and bounded host work.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Read,
    path::{Path, PathBuf},
};

type Result<T> = std::result::Result<T, String>;
const SOURCE_LIMIT: usize = 1_000_000;

pub(super) struct Loaded {
    pub files: Vec<PathBuf>,
    pub source: String,
}

#[derive(Clone)]
struct Unit {
    path: PathBuf,
    source: String,
    program: evergreen::syntax::Program,
}

struct Loader {
    root: PathBuf,
    cache: BTreeMap<PathBuf, Unit>,
    emitted: BTreeSet<PathBuf>,
    visiting: BTreeSet<PathBuf>,
    complete: BTreeSet<PathBuf>,
    bytes: usize,
    units: Vec<Unit>,
}

pub(super) fn load(inputs: &[PathBuf], root: Option<&Path>) -> Result<Loaded> {
    if inputs.is_empty() {
        return Err("at least one input file or package is required".into());
    }
    let root = fs::canonicalize(root.unwrap_or(Path::new(".")))
        .map_err(|e| format!("package root: {e}"))?;
    if !root.is_dir() {
        return Err("package root must be a directory".into());
    }
    let mut loader = Loader {
        root,
        cache: BTreeMap::new(),
        emitted: BTreeSet::new(),
        visiting: BTreeSet::new(),
        complete: BTreeSet::new(),
        bytes: 0,
        units: Vec::new(),
    };
    for input in inputs {
        loader.input(input, false)?;
    }
    let source = evergreen::syntax::join_source_units(
        &loader
            .units
            .iter()
            .map(|unit| unit.source.clone())
            .collect::<Vec<_>>(),
    )?;
    let files = loader.units.into_iter().map(|unit| unit.path).collect();
    Ok(Loaded { files, source })
}

impl Loader {
    fn input(&mut self, input: &Path, imported: bool) -> Result<()> {
        let path = fs::canonicalize(input).map_err(|e| format!("{}: {e}", input.display()))?;
        if imported && !path.starts_with(&self.root) {
            return Err("an imported package must remain within the package root".into());
        }
        if path.is_dir() {
            return self.package(&path, imported);
        }
        let unit = self.read(&path)?;
        self.imports(&unit.program.imports)?;
        self.emit(unit);
        Ok(())
    }

    fn read(&mut self, path: &Path) -> Result<Unit> {
        if let Some(unit) = self.cache.get(path) {
            return Ok(unit.clone());
        }
        if self.cache.len() >= 1024 {
            return Err("source file limit reached (1024)".into());
        }
        let mut source = String::new();
        fs::File::open(path)
            .map_err(|e| format!("{}: {e}", path.display()))?
            .take((SOURCE_LIMIT + 1) as u64)
            .read_to_string(&mut source)
            .map_err(|e| format!("{}: {e}", path.display()))?;
        self.bytes += source.len() + usize::from(!self.cache.is_empty());
        if self.bytes > SOURCE_LIMIT {
            return Err("source and local packages exceed 1 MB bootstrap limit".into());
        }
        let program =
            evergreen::syntax::parse(&source).map_err(|e| format!("{}: {e}", path.display()))?;
        if program
            .imports
            .iter()
            .any(|name| program.modules.contains(name))
        {
            return Err(format!(
                "{}: a package cannot import itself",
                path.display()
            ));
        }
        let unit = Unit {
            path: path.to_owned(),
            source,
            program,
        };
        self.cache.insert(path.to_owned(), unit.clone());
        Ok(unit)
    }

    fn imports(&mut self, imports: &BTreeSet<String>) -> Result<()> {
        for name in imports {
            if self
                .units
                .iter()
                .any(|unit| unit.program.modules.contains(name))
            {
                continue;
            }
            let path = self.root.join(name);
            if path.is_dir() {
                self.input(&path, true)?;
            } else if !evergreen::compiler::is_bundled_module(name) {
                return Err(format!(
                    "unresolved import {name} under package root {}",
                    self.root.display()
                ));
            }
        }
        Ok(())
    }

    fn emit(&mut self, unit: Unit) {
        if self.emitted.insert(unit.path.clone()) {
            self.units.push(unit);
        }
    }

    fn package(&mut self, directory: &Path, imported: bool) -> Result<()> {
        if self.complete.contains(directory) {
            return Ok(());
        }
        if !self.visiting.insert(directory.to_owned()) {
            return Err(format!("cyclic package imports at {}", directory.display()));
        }
        if self.visiting.len() > 64 {
            return Err("package import depth limit reached (64)".into());
        }
        let paths = package_files(directory)?;
        let expected = directory
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("package directory needs a name")?;
        let mut name = None;
        let mut units = Vec::new();
        let mut imports = BTreeSet::new();
        for path in paths {
            let path =
                fs::canonicalize(path).map_err(|e| format!("{}: {e}", directory.display()))?;
            if imported && !path.starts_with(&self.root) {
                return Err("an imported source file must remain within the package root".into());
            }
            let unit = self.read(&path)?;
            if unit.program.modules.len() != 1
                || !unit
                    .program
                    .modules
                    .iter()
                    .all(|module| module == expected || module == "main")
            {
                return Err(format!("{}: directory {} requires one module named {expected} (or main for an executable)", path.display(), directory.display()));
            }
            let module = unit.program.modules.first().unwrap();
            if name.as_ref().is_some_and(|previous| previous != module) {
                return Err("all files in a directory must declare the same module".into());
            }
            if imported && module == "main" {
                return Err("an executable main package cannot be imported".into());
            }
            name = Some(module.clone());
            imports.extend(unit.program.imports.iter().cloned());
            units.push(unit);
        }
        self.imports(&imports)?;
        for unit in units {
            self.emit(unit);
        }
        self.visiting.remove(directory);
        self.complete.insert(directory.to_owned());
        Ok(())
    }
}

fn package_files(directory: &Path) -> Result<Vec<PathBuf>> {
    let entries = fs::read_dir(directory).map_err(|e| format!("{}: {e}", directory.display()))?;
    let mut paths = Vec::new();
    for (index, entry) in entries.enumerate() {
        if index >= 4096 {
            return Err("package directory entry limit reached (4096)".into());
        }
        let path = entry
            .map_err(|e| format!("{}: {e}", directory.display()))?
            .path();
        if path.is_file() && path.extension().is_some_and(|ext| ext == "evg") {
            paths.push(path);
        }
    }
    paths.sort();
    if paths.is_empty() {
        return Err(format!(
            "{}: package contains no .evg files",
            directory.display()
        ));
    }
    Ok(paths)
}
