use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "evergreen-diagnostics-{}-{stamp}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, source: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, source).unwrap();
        path
    }
    fn check(&self, color: &str, files: &[PathBuf]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_evg"))
            .args(["--color", color, "check"])
            .args(files)
            .output()
            .unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn invariant_errors_show_the_correct_file_line_predicate_and_readable_type() {
    let fixture = Fixture::new();
    let definition = fixture.write(
        "pair.evg",
        "type MyPair<T> struct {data: [T; 2]} where self.data[0] < self.data[1];\n",
    );
    let caller = fixture.write(
        "main.evg",
        "fn main() {\n    let pair = MyPair::<usize> {data: [2, 1]};\n}\n",
    );
    let output = fixture.check("never", &[definition.clone(), caller.clone()]);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(
        error.contains("error: cannot prove invariant of MyPair"),
        "{error}"
    );
    assert!(
        error.contains(&format!("{}:2:5", caller.display())),
        "{error}"
    );
    assert!(
        error.contains("2 |     let pair = MyPair::<usize> {data: [2, 1]};"),
        "{error}"
    );
    assert!(error.contains("^^^^"));
    assert!(
        error.contains("required: (self.data[0] < self.data[1])"),
        "{error}"
    );
    assert!(
        error.contains(&format!("invariant declared at {}:1", definition.display())),
        "{error}"
    );
    assert!(error.contains("unproved obligation:"));
    assert!(!error.contains("evg_generic_"));
    assert!(!error.contains('\x1b'));
}

#[test]
fn failures_inside_another_file_do_not_highlight_the_entry_file() {
    let fixture = Fixture::new();
    let entry = fixture.write("entry.evg", "fn main() -> usize {\n    bump(0)\n}\n");
    let helper = fixture.write(
        "helper.evg",
        "fn bump(n: usize) -> usize {\n    proof _: n < n;\n    n\n}\n",
    );
    let output = fixture.check("never", &[entry.clone(), helper.clone()]);
    assert!(!output.status.success());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(
        error.contains(&format!("{}:2:5", helper.display())),
        "{error}"
    );
    assert!(error.contains("2 |     proof _: n < n;"), "{error}");
    assert!(
        !error.contains(&format!("--> {}", entry.display())),
        "{error}"
    );
}

#[test]
fn proof_kernel_failures_highlight_the_proof_statement() {
    let fixture = Fixture::new();
    let path = fixture.write(
        "proof.evg",
        "fn check(limit: usize) {\n    let cursor: usize = 0;\n    while cursor < limit invariant(cursor <= limit) modifies(&cursor) decreases(limit - cursor) {cursor = cursor + 1;}\n    proof after: forall(i: integer) {integer(cursor) == integer(limit)} by {intro i; omega};\n}\n",
    );
    let output = fixture.check("never", std::slice::from_ref(&path));
    assert!(!output.status.success());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(
        error.contains(&format!("{}:4:5", path.display())),
        "{error}"
    );
    assert!(error.contains("cannot prove proof after: universal introduction requires fully traced context dependencies"), "{error}");
}

#[test]
fn syntax_errors_have_source_excerpts_and_color_is_controllable() {
    let fixture = Fixture::new();
    let source = "fn main() {let text = \"λ🦀\"; @}\n";
    let path = fixture.write("broken.evg", source);
    for (color, ansi) in [("never", false), ("auto", false), ("always", true)] {
        let output = fixture.check(color, std::slice::from_ref(&path));
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
        let error = String::from_utf8(output.stderr).unwrap();
        assert_eq!(error.contains('\x1b'), ansi, "{error:?}");
        assert!(error.contains("unexpected character"));
        assert!(error.contains("λ🦀"));
        assert!(error.contains("broken.evg:1:1"));
        assert!(error.contains("^^^"));
    }
    let control = fixture.write("control.evg", "fn main() {\x1b}\n");
    let output = fixture.check("never", &[control]);
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(!error.contains('\x1b'), "{error:?}");
}
