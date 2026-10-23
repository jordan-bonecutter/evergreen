//! Optional reference backend over the shared Evergreen syntax tree.
use crate::syntax::{self, Expr, Function, Kind, Statement, Type};
use std::collections::{BTreeMap, BTreeSet};
type Result<T> = std::result::Result<T, String>;

#[derive(Default)]
struct Emitter {
    env: BTreeMap<String, Type>,
    facts: BTreeSet<String>,
    proofs: BTreeSet<String>,
}
impl Emitter {
    fn steps(&self, steps: &[String]) -> Result<String> {
        if steps.iter().any(|s| s == "trustme") {
            return Err("trustme declares a trusted assumption; the optional Lean reference backend requires checked proofs".into());
        }
        for step in steps {
            if let Some(name) = step.strip_prefix("exact ") {
                if steps.len() != 1 || !self.proofs.contains(name) {
                    return Err(format!(
                        "exact {name} must reference a checked proof declaration"
                    ));
                }
            }
        }
        Ok(steps.join("; "))
    }
    fn fresh(&self, name: &str) -> Result<()> {
        if self.env.contains_key(name) || self.facts.contains(name) || self.proofs.contains(name) {
            return Err(format!("duplicate binding {name}"));
        }
        Ok(())
    }
    fn hint(&self, e: &Expr) -> Option<Type> {
        match &e.kind {
            Kind::Name(n) => self.env.get(n).cloned(),
            Kind::Unary(_, x) => self.hint(x),
            Kind::Binary(_, a, b) => self.hint(a).or_else(|| self.hint(b)),
            _ => None,
        }
    }
    fn operand_type(&self, a: &Expr, b: &Expr, expected: Option<&Type>) -> Type {
        expected
            .cloned()
            .or_else(|| self.hint(a))
            .or_else(|| self.hint(b))
            .unwrap_or(Type::Int)
    }
    fn ty(&self, t: &Type) -> Result<String> {
        match t {
            Type::Int => Ok("Int".into()), Type::Nat => Ok("Nat".into()), Type::Bool => Ok("Bool".into()), Type::Unit => Ok("Unit".into()),
            Type::Array(t, n) => Ok(format!("Vector ({}) ({})", self.ty(t)?, self.value(n, Some(&Type::Nat))?.0)),
            _ => Err("Lean reference backend supports mathematical int/nat, bool, unit, and vectors; machine arithmetic and ownership use the internal kernel".into()),
        }
    }
    fn value(&self, e: &Expr, expected: Option<&Type>) -> Result<(String, Type)> {
        let (text, ty) = match &e.kind {
            Kind::Number(n) => (n.to_string(), expected.cloned().unwrap_or(Type::Int)),
            Kind::Bool(b) => (b.to_string(), Type::Bool),
            Kind::Unit => ("()".into(), Type::Unit),
            Kind::Name(n) => {
                if self.facts.contains(n) {
                    return Err(format!(
                        "line {}: a fact is a proposition, not a runtime value",
                        e.line
                    ));
                }
                (
                    n.clone(),
                    self.env
                        .get(n)
                        .cloned()
                        .ok_or_else(|| format!("line {}: unknown value {n}", e.line))?,
                )
            }
            Kind::Unary(op, x) if op == "-" => (
                format!("(-{})", self.value(x, Some(&Type::Int))?.0),
                Type::Int,
            ),
            Kind::Unary(op, x) if op == "!" => (
                format!("(!{})", self.value(x, Some(&Type::Bool))?.0),
                Type::Bool,
            ),
            Kind::Binary(op, a, b) if matches!(op.as_str(), "+" | "-" | "*") => {
                let t = self.operand_type(a, b, expected);
                if !matches!(t, Type::Int | Type::Nat) {
                    return Err("reference arithmetic requires int or nat operands".into());
                }
                (
                    format!(
                        "({} {op} {})",
                        self.value(a, Some(&t))?.0,
                        self.value(b, Some(&t))?.0
                    ),
                    t,
                )
            }
            Kind::Binary(op, a, b) if op == "&&" || op == "||" => (
                format!(
                    "({} {op} {})",
                    self.value(a, Some(&Type::Bool))?.0,
                    self.value(b, Some(&Type::Bool))?.0
                ),
                Type::Bool,
            ),
            Kind::Binary(..) => (format!("(decide {})", self.prop(e)?), Type::Bool),
            Kind::Index(a, i) => {
                let (array, Type::Array(element, _)) = self.value(a, None)? else {
                    return Err("reference indexing requires a vector".into());
                };
                let index = self.value(i, Some(&Type::Nat))?.0;
                (format!("({array})[{index}]'(by omega)"), *element)
            }
            Kind::If(c, a, b) => {
                let (yes, t) = self.value(a, expected)?;
                let no = self.value(b, Some(&t))?.0;
                (format!("(if {} then {yes} else {no})", self.prop(c)?), t)
            }
            _ => {
                return Err(format!(
                    "line {}: this expression is outside the optional Lean reference subset",
                    e.line
                ))
            }
        };
        self.ty(&ty)?;
        if expected.is_some_and(|t| t != &ty) {
            return Err(format!("line {}: reference backend type mismatch", e.line));
        }
        Ok((text, ty))
    }
    fn prop(&self, e: &Expr) -> Result<String> {
        match &e.kind {
            Kind::Bool(b) => Ok(if *b { "True" } else { "False" }.into()),
            Kind::Name(n) if self.facts.contains(n) => Ok(n.clone()),
            Kind::Unary(op, x) if op == "!" => Ok(format!("(¬ {})", self.prop(x)?)),
            Kind::Binary(op, a, b) if op == "&&" || op == "||" => Ok(format!(
                "({} {} {})",
                self.prop(a)?,
                if op == "&&" { "∧" } else { "∨" },
                self.prop(b)?
            )),
            Kind::Binary(op, a, b)
                if matches!(op.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=") =>
            {
                let t = self.operand_type(a, b, None);
                if !matches!(t, Type::Int | Type::Nat) {
                    return Err("reference comparisons require int or nat operands".into());
                }
                let operator = match op.as_str() {
                    "==" => "=",
                    "!=" => "≠",
                    "<=" => "≤",
                    ">=" => "≥",
                    other => other,
                };
                Ok(format!(
                    "({} {operator} {})",
                    self.value(a, Some(&t))?.0,
                    self.value(b, Some(&t))?.0
                ))
            }
            _ => Ok(format!("({} = true)", self.value(e, Some(&Type::Bool))?.0)),
        }
    }
    fn function(&mut self, f: &Function, run: bool) -> Result<(String, bool)> {
        if !f.ideal || f.decreases.is_some() {
            return Err("the optional Lean backend currently checks nonrecursive ideal mathematical functions; executable machine code uses the internal kernel".into());
        }
        self.env.clear();
        self.facts.clear();
        self.proofs.clear();
        let mut params = Vec::new();
        for (n, t) in &f.params {
            params.push(format!("({n} : {})", self.ty(t)?));
            if self.env.insert(n.clone(), t.clone()).is_some() {
                return Err("duplicate parameter".into());
            }
        }
        if let Some(p) = &f.pre {
            params.push(format!("(evg_pre : {})", self.prop(p)?));
        }
        let return_type = self.ty(&f.ret)?;
        self.env.insert("result".into(), f.ret.clone());
        let typ = if let Some(p) = &f.post {
            format!("{{ result : {return_type} // {} }}", self.prop(p)?)
        } else {
            return_type
        };
        self.env.remove("result");
        let mut body = String::new();
        for s in &f.body {
            match s {
                Statement::Let { name, ty, value } => {
                    self.fresh(name)?;
                    let (value, t) = self.value(value, ty.as_ref())?;
                    body.push_str(&format!("  let {name} : {} := {value}\n", self.ty(&t)?));
                    self.env.insert(name.clone(), t);
                }
                Statement::Fact { name, value } => {
                    self.fresh(name)?;
                    body.push_str(&format!("  let {name} : Prop := {}\n", self.prop(value)?));
                    self.facts.insert(name.clone());
                }
                Statement::Proof {
                    name,
                    proposition,
                    steps,
                } => {
                    self.fresh(name)?;
                    body.push_str(&format!(
                        "  have {name} : {} := by {}\n",
                        self.prop(proposition)?,
                        self.steps(steps)?
                    ));
                    self.proofs.insert(name.clone());
                }
                _ => return Err("ownership and mutation use the internal backend".into()),
            }
        }
        let result = self.value(&f.result, Some(&f.ret))?.0;
        if f.post.is_some() {
            body.push_str(&format!(
                "  exact ⟨{result}, by {}⟩\n",
                f.proof
                    .as_ref()
                    .map(|s| self.steps(s))
                    .transpose()?
                    .unwrap_or("omega".into())
            ));
        } else {
            if f.proof.is_some() {
                return Err("function proof requires ensures".into());
            }
            body.push_str(&format!("  exact {result}\n"));
        }
        let runnable = f.name == "main" && f.params.is_empty() && f.pre.is_none();
        let mut out = format!(
            "def {} {} : {typ} := by\n{body}\n",
            f.name,
            params.join(" ")
        );
        if run && runnable {
            out.push_str(&format!(
                "#eval main{}\n",
                if f.post.is_some() { ".val" } else { "" }
            ));
        }
        Ok((out, runnable))
    }
}

pub fn emit(source: &str, run: bool) -> Result<String> {
    let program = syntax::parse(source)?;
    if !program.structs.is_empty() || !program.destructors.is_empty() {
        return Err("structs and ownership use the internal backend".into());
    }
    let mut out = "-- Generated by Evergreen. Emission is not verification.\nimport Std\nset_option warningAsError true\nset_option linter.unusedVariables false\nset_option autoImplicit false\nnamespace EvgProgram\n\n".to_owned();
    let mut emitter = Emitter::default();
    let mut names = BTreeSet::new();
    let mut main = false;
    for f in program.functions {
        if !names.insert(f.name.clone()) {
            return Err("duplicate function".into());
        }
        let (definition, runnable) = emitter.function(&f, run)?;
        out.push_str(&definition);
        main |= runnable;
    }
    if run && !main {
        return Err("run requires main with no parameters or preconditions".into());
    }
    out.push_str("end EvgProgram\n");
    Ok(out)
}
