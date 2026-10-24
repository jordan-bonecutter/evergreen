//! Evergreen bootstrap: shared syntax, internal verification, and execution.

pub mod certificate;
mod effects;
pub mod kernel;
pub mod layout;
pub mod memory;
pub mod native;
pub mod runtime;
pub mod syntax;
pub mod verify;

#[derive(Clone, Debug)]
struct Token {
    text: String,
    line: usize,
}

fn lex(source: &str) -> Result<Vec<Token>, String> {
    let mut out = Vec::new();
    let chars: Vec<char> = source.chars().collect();
    let (mut i, mut line) = (0, 1);
    while i < chars.len() {
        let c = chars[i];
        if c == '\n' {
            line += 1;
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        let start = i;
        if c.is_ascii_alphabetic() || c == '_' {
            i += 1;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
        } else if c.is_ascii_digit() {
            i += 1;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
        } else if "(){}[],:;.+-*/%<>=!&|".contains(c) {
            i += 1;
            if i < chars.len()
                && matches!(
                    (c, chars[i]),
                    ('-', '>')
                        | ('<', '=')
                        | ('>', '=')
                        | ('=', '=')
                        | ('=', '>')
                        | ('!', '=')
                        | ('&', '&')
                        | ('|', '|')
                        | (':', ':')
                )
            {
                i += 1;
            }
        } else {
            return Err(format!("line {line}: unexpected character {c:?}"));
        }
        out.push(Token {
            text: chars[start..i].iter().collect(),
            line,
        });
    }
    out.push(Token {
        text: "<eof>".into(),
        line,
    });
    Ok(out)
}

mod lean;
pub use lean::emit;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn emits_contract_and_facts() {
        let s = emit(
            "ideal fn inc(n: nat) -> nat ensures (result > n) { proof h: n + 1 > n by { omega }; n + 1 }",
            false,
        )
        .unwrap();
        assert!(s.contains("{ result : Nat // (result > n) }"));
        assert!(s.contains("have h : ((n + 1) > n) := by omega"));
    }
    #[test]
    fn emits_bounds_obligation() {
        let s = emit(
            "ideal fn at(n: nat, a: [int; n], i: nat) -> int where (i < n) { a[i] }",
            false,
        )
        .unwrap();
        assert!(s.contains("Vector (Int) (n)"));
        assert!(s.contains("[i]'(by omega)"));
    }
    #[test]
    fn rejects_escape_hatches() {
        for tactic in ["sorry", "admit", "native_decide", "axiom", "exact missing"] {
            assert!(emit(
                &format!("ideal fn f() -> nat ensures (result == 1) {{ 0 }} proof {{ {tactic} }}"),
                false
            )
            .is_err());
        }
    }
    #[test]
    fn rejects_bad_programs() {
        for s in [
            "",
            "ideal fn f() -> nat { missing }",
            "ideal fn f() -> nat { 1 / 0 }",
            "ideal fn f() -> nat { 1 } ideal fn f() -> nat { 2 }",
            "ideal fn f() -> nat { let x = 1; let x = 2; x }",
            "type Vec<T> struct {}",
        ] {
            assert!(emit(s, false).is_err(), "{s}");
        }
    }
    #[test]
    fn run_requires_entrypoint() {
        assert!(emit("ideal fn f() -> nat { 1 }", true).is_err());
    }
    #[test]
    fn comments_and_precedence() {
        let s = emit("// comment\nideal fn main() -> int { 1 + 2 * 3 }", true).unwrap();
        assert!(s.contains("(1 + (2 * 3))"));
        assert!(s.contains("#eval main"));
    }
}
