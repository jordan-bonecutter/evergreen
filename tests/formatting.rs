//! The formatter must respect the working tree/index boundary used by hooks.

use std::{
    fs,
    path::Path,
    process::{Command, Output},
};

fn git(root: &Path, args: &[&str]) -> Output {
    let output = Command::new("git")
        .current_dir(root)
        .args(args)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

#[test]
fn staged_checks_read_only_the_index_and_format_rewrites_only_named_files() {
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root =
        std::env::temp_dir().join(format!("evergreen-format-{}-{stamp}", std::process::id()));
    fs::create_dir(&root).unwrap();
    git(&root, &["init", "--quiet"]);
    let path = root.join("staged name.evg");
    let original = "fn main()->usize{42}";
    let formatted = evergreen::syntax::format::source(original).unwrap();
    fs::write(&path, original).unwrap();
    git(&root, &["add", "--", "staged name.evg"]);
    fs::write(&path, &formatted).unwrap();
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_evg"))
            .current_dir(&root)
            .args(args)
            .output()
            .unwrap()
    };
    let staged_bad = run(&["fmt", "--check", "--staged"]);
    assert!(!staged_bad.status.success());
    assert!(String::from_utf8_lossy(&staged_bad.stderr).contains("staged name.evg (staged)"));
    assert_eq!(fs::read_to_string(&path).unwrap(), formatted);
    assert_eq!(
        git(&root, &["cat-file", "blob", ":staged name.evg"]).stdout,
        original.as_bytes()
    );
    git(&root, &["add", "--", "staged name.evg"]);
    fs::write(&path, original).unwrap();
    assert!(run(&["fmt", "--check", "--staged"]).status.success());
    assert!(!run(&["fmt", "--check", "--all"]).status.success());
    assert_eq!(fs::read_to_string(&path).unwrap(), original);
    let untracked = root.join("untracked.evg");
    fs::write(&untracked, original).unwrap();
    assert!(run(&["fmt", "--all"]).status.success());
    assert_eq!(fs::read_to_string(&path).unwrap(), formatted);
    assert_eq!(fs::read_to_string(&untracked).unwrap(), original);
    assert!(run(&["fmt", "--check", "--all"]).status.success());
    assert!(run(&["fmt", "untracked.evg"]).status.success());
    assert_eq!(fs::read_to_string(&untracked).unwrap(), formatted);
    fs::write(&path, original).unwrap();
    fs::write(&untracked, "@ malformed").unwrap();
    assert!(!run(&["fmt", "staged name.evg", "untracked.evg"])
        .status
        .success());
    assert_eq!(
        fs::read_to_string(&path).unwrap(),
        original,
        "prepare every file before rewriting any"
    );
    assert_eq!(
        git(&root, &["cat-file", "blob", ":staged name.evg"]).stdout,
        formatted.as_bytes()
    );
    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn formatting_preserves_file_permissions_and_rejects_symlinks() {
    use std::os::unix::fs::{symlink, PermissionsExt};
    let root = std::env::temp_dir().join(format!("evergreen-format-mode-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("main.evg");
    let link = root.join("link.evg");
    fs::write(&path, "fn main(){42}").unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o750)).unwrap();
    symlink(&path, &link).unwrap();
    let run = |path: &Path| {
        Command::new(env!("CARGO_BIN_EXE_evg"))
            .arg("fmt")
            .arg(path)
            .output()
            .unwrap()
    };
    assert!(!run(&link).status.success());
    assert_eq!(fs::read_to_string(&path).unwrap(), "fn main(){42}");
    assert!(run(&path).status.success());
    assert_eq!(
        fs::metadata(&path).unwrap().permissions().mode() & 0o777,
        0o750
    );
    assert!(fs::symlink_metadata(&link)
        .unwrap()
        .file_type()
        .is_symlink());
    fs::remove_dir_all(root).unwrap();
}
