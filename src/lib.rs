//! Evergreen's proof-producing bootstrap frontend. Lean is currently the backend.
use std::collections::HashSet;

pub mod kernel;
pub mod memory;
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

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    names: HashSet<String>,
}
impl Parser {
    fn peek(&self) -> &str {
        &self.tokens[self.pos].text
    }
    fn err(&self, message: &str) -> String {
        format!("line {}: {message}", self.tokens[self.pos].line)
    }
    fn eat(&mut self, text: &str) -> bool {
        if self.peek() == text {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, text: &str) -> Result<(), String> {
        if self.eat(text) {
            Ok(())
        } else {
            Err(self.err(&format!("expected {text:?}, found {:?}", self.peek())))
        }
    }
    fn ident(&mut self) -> Result<String, String> {
        let s = self.peek().to_owned();
        if !s.starts_with(|c: char| c.is_ascii_alphabetic())
            || s.starts_with("evg_")
            || matches!(
                s.as_str(),
                "by" | "sorry"
                    | "axiom"
                    | "unsafe"
                    | "partial"
                    | "result"
                    | "fn"
                    | "let"
                    | "fact"
                    | "return"
                    | "proof"
                    | "where"
                    | "ensures"
                    | "true"
                    | "false"
            )
        {
            return Err(self.err("expected identifier (evg_ prefix and result are reserved)"));
        }
        self.pos += 1;
        Ok(s)
    }
    fn bind(&mut self) -> Result<String, String> {
        let n = self.ident()?;
        if !self.names.insert(n.clone()) {
            return Err(self.err(&format!("duplicate binding {n}")));
        }
        Ok(n)
    }
    fn ty(&mut self) -> Result<String, String> {
        if self.eat("[") {
            let t = self.ty()?;
            self.expect(";")?;
            let n = self.expr(0)?;
            self.expect("]")?;
            return Ok(format!("Vector ({t}) ({n})"));
        }
        let t = match self.peek() {
            "int" => "Int",
            "nat" => "Nat",
            "bool" => "Bool",
            _ => return Err(self.err("supported types: isize, usize, bool, [T; length]")),
        };
        self.pos += 1;
        Ok(t.into())
    }
    fn expr(&mut self, min: u8) -> Result<String, String> {
        let mut lhs = if self.eat("(") {
            let e = self.expr(0)?;
            self.expect(")")?;
            e
        } else if self.eat("-") {
            format!("(-{})", self.expr(7)?)
        } else if self.eat("!") {
            format!("(¬ {})", self.expr(7)?)
        } else {
            let n = self.peek().to_owned();
            if (n.chars().all(|c| c.is_ascii_digit()) && !n.is_empty())
                || n == "true"
                || n == "false"
                || n == "result"
                || self.names.contains(&n)
            {
                self.pos += 1;
                n
            } else {
                return Err(self.err(&format!(
                    "unknown name {n:?} (function calls are not supported yet)"
                )));
            }
        };
        loop {
            if self.peek() == "[" && min <= 8 {
                self.pos += 1;
                let idx = self.expr(0)?;
                self.expect("]")?;
                lhs = format!("({lhs})[{idx}]'(by omega)");
                continue;
            }
            let (prec, op) =
                match self.peek() {
                    "||" => (1, "∨"),
                    "&&" => (2, "∧"),
                    "==" => (3, "="),
                    "!=" => (3, "≠"),
                    "<" => (4, "<"),
                    "<=" => (4, "≤"),
                    ">" => (4, ">"),
                    ">=" => (4, "≥"),
                    "+" => (5, "+"),
                    "-" => (5, "-"),
                    "*" => (6, "*"),
                    "/" | "%" => return Err(self.err(
                        "division and remainder need explicit zero-divisor semantics; unsupported",
                    )),
                    _ => break,
                };
            if prec < min {
                break;
            }
            self.pos += 1;
            let rhs = self.expr(prec + 1)?;
            lhs = format!("({lhs} {op} {rhs})");
        }
        Ok(lhs)
    }
    fn proof(&mut self) -> Result<String, String> {
        self.expect("{")?;
        let mut steps = Vec::new();
        loop {
            if self.peek() == "<eof>" {
                return Err(self.err("unterminated proof block"));
            }
            let tactic = self.peek().to_owned();
            self.pos += 1;
            let step = match tactic.as_str() {
                "omega" | "rfl" | "simp_all" | "decide" | "assumption" => tactic,
                "exact" => {
                    let n = self.ident()?;
                    if !self.names.contains(&n) {
                        return Err(self.err("exact requires a local fact or parameter"));
                    }
                    format!("exact {n}")
                }
                _ => return Err(self.err(
                    "allowed proof steps: omega, rfl, simp_all, decide, assumption, exact <name>",
                )),
            };
            steps.push(step);
            if self.eat("}") {
                break;
            }
            self.expect(";")?;
            if self.eat("}") {
                break;
            }
        }
        Ok(steps.join("; "))
    }
    fn function(&mut self) -> Result<(String, bool), String> {
        self.expect("fn")?;
        self.names.clear();
        let name = self.ident()?;
        self.expect("(")?;
        let mut params = Vec::new();
        if !self.eat(")") {
            loop {
                let n = self.bind()?;
                self.expect(":")?;
                let t = self.ty()?;
                params.push(format!("({n} : {t})"));
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
            }
        }
        self.expect("->")?;
        let ret = self.ty()?;
        if self.eat("where") {
            self.expect("(")?;
            let pre = self.expr(0)?;
            self.expect(")")?;
            params.push(format!("(evg_pre : {pre})"));
        }
        let post = if self.eat("ensures") {
            self.expect("(")?;
            let p = self.expr(0)?;
            self.expect(")")?;
            Some(p)
        } else {
            None
        };
        self.expect("{")?;
        let mut body = String::new();
        while self.peek() == "let" || self.peek() == "fact" {
            let fact = self.eat("fact");
            if !fact {
                self.expect("let")?;
            }
            let n = self.ident()?;
            if self.names.contains(&n) {
                return Err(self.err("shadowing is not supported"));
            }
            let ty = if !fact && self.eat(":") {
                Some(self.ty()?)
            } else {
                None
            };
            self.expect("=")?;
            let e = self.expr(0)?;
            if fact {
                let proof = if self.eat("by") {
                    self.proof()?
                } else {
                    "omega".into()
                };
                body.push_str(&format!("  have {n} : {e} := by {proof}\n"));
            } else {
                let annotation = ty.map(|t| format!(" : {t}")).unwrap_or_default();
                body.push_str(&format!("  let {n}{annotation} := {e}\n"));
            }
            self.names.insert(n);
            self.expect(";")?;
        }
        self.eat("return");
        let result = self.expr(0)?;
        self.eat(";");
        self.expect("}")?;
        let proof = if self.eat("proof") {
            self.proof()?
        } else {
            "omega".into()
        };
        let typ = if let Some(p) = &post {
            format!("{{ result : {ret} // {p} }}")
        } else {
            ret
        };
        if post.is_some() {
            body.push_str(&format!("  exact ⟨{result}, by {proof}⟩\n"));
        } else {
            body.push_str(&format!("  exact {result}\n"));
        }
        let runnable = name == "main" && params.is_empty();
        let eval = if runnable {
            format!("#eval main{}\n", if post.is_some() { ".val" } else { "" })
        } else {
            String::new()
        };
        Ok((
            format!("def {name} {} : {typ} := by\n{body}\n", params.join(" ")) + &eval,
            runnable,
        ))
    }
}

/// Emit closed Lean declarations. Proof text is parsed, never injected verbatim.
pub fn emit(source: &str, run: bool) -> Result<String, String> {
    let mut p = Parser {
        tokens: lex(source)?,
        pos: 0,
        names: HashSet::new(),
    };
    let mut out = "-- Generated by Evergreen. Do not treat emission as verification.\nimport Std\nset_option warningAsError true\nset_option linter.unusedVariables false\nset_option autoImplicit false\nnamespace EvgProgram\n\n".to_owned();
    let mut functions = HashSet::new();
    let mut main = false;
    while p.peek() != "<eof>" {
        let name = p
            .tokens
            .get(p.pos + 1)
            .map(|t| t.text.clone())
            .unwrap_or_default();
        if !functions.insert(name.clone()) {
            return Err(p.err("duplicate function"));
        }
        let (mut f, runnable) = p.function()?;
        main |= runnable;
        if !run {
            f = f
                .lines()
                .filter(|l| !l.starts_with("#eval"))
                .map(|l| format!("{l}\n"))
                .collect();
        }
        out.push_str(&f);
    }
    if functions.is_empty() {
        return Err("expected at least one function".into());
    }
    if run && !main {
        return Err("run requires fn main() with no preconditions".into());
    }
    out.push_str("end EvgProgram\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn emits_contract_and_facts() {
        let s = emit(
            "fn inc(n: nat) -> nat ensures (result > n) { fact h = n + 1 > n by { omega }; n + 1 }",
            false,
        )
        .unwrap();
        assert!(s.contains("{ result : Nat // (result > n) }"));
        assert!(s.contains("have h : ((n + 1) > n) := by omega"));
    }
    #[test]
    fn emits_bounds_obligation() {
        let s = emit(
            "fn at(n: nat, a: [int; n], i: nat) -> int where (i < n) { a[i] }",
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
                &format!("fn f() -> nat ensures (result == 1) {{ 0 }} proof {{ {tactic} }}"),
                false
            )
            .is_err());
        }
    }
    #[test]
    fn rejects_bad_programs() {
        for s in [
            "",
            "fn f() -> nat { missing }",
            "fn f() -> nat { 1 / 0 }",
            "fn f() -> nat { 1 } fn f() -> nat { 2 }",
            "fn f() -> nat { let x = 1; let x = 2; x }",
            "type Vec<T> struct {}",
        ] {
            assert!(emit(s, false).is_err(), "{s}");
        }
    }
    #[test]
    fn run_requires_entrypoint() {
        assert!(emit("fn f() -> nat { 1 }", true).is_err());
    }
    #[test]
    fn comments_and_precedence() {
        let s = emit("// comment\nfn main() -> int { 1 + 2 * 3 }", true).unwrap();
        assert!(s.contains("(1 + (2 * 3))"));
        assert!(s.contains("#eval main"));
    }
}
