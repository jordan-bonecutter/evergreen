//! Internal elaboration and verification-condition generation.
use crate::{
    kernel::{self, Linear},
    syntax::{self, Expr, Function, Kind, Type},
};
use std::collections::BTreeMap;

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug)]
enum Formula {
    True,
    False,
    Ge(Linear),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
}
impl Formula {
    fn and(self, other: Self) -> Self {
        Self::And(Box::new(self), Box::new(other))
    }
    fn or(self, other: Self) -> Self {
        Self::Or(Box::new(self), Box::new(other))
    }
    fn not(self) -> Self {
        Self::Not(Box::new(self))
    }
}

#[derive(Clone, Debug)]
enum Ty {
    Int,
    Nat,
    Bool,
    Array(Box<Ty>, Linear),
}
#[derive(Clone, Debug)]
enum Symbol {
    Number(Ty, Linear),
    Bool(Formula),
    Array {
        element: Box<Ty>,
        len: Linear,
        items: Option<Vec<Symbol>>,
        identity: String,
    },
}
impl Symbol {
    fn ty(&self) -> Ty {
        match self {
            Self::Number(t, _) => t.clone(),
            Self::Bool(_) => Ty::Bool,
            Self::Array { element, len, .. } => Ty::Array(element.clone(), len.clone()),
        }
    }
    fn number(&self) -> Result<Linear> {
        if let Self::Number(_, n) = self {
            Ok(n.clone())
        } else {
            Err("expected an integer expression".into())
        }
    }
    fn proposition(&self) -> Result<Formula> {
        if let Self::Bool(p) = self {
            Ok(p.clone())
        } else {
            Err("expected a proposition or boolean".into())
        }
    }
}

/// Each path is a conjunction of inequalities. The path list is a disjunction.
fn extend(paths: &[Vec<Linear>], formula: &Formula, negated: bool) -> Result<Vec<Vec<Linear>>> {
    let result = match formula {
        Formula::True => {
            if negated {
                vec![]
            } else {
                paths.to_vec()
            }
        }
        Formula::False => {
            if negated {
                paths.to_vec()
            } else {
                vec![]
            }
        }
        Formula::Ge(value) => {
            let row = if negated {
                value.scale(-1)?.add(&Linear::number(-1))?
            } else {
                value.clone()
            };
            paths
                .iter()
                .map(|p| {
                    let mut p = p.clone();
                    p.push(row.clone());
                    p
                })
                .collect()
        }
        Formula::Not(p) => return extend(paths, p, !negated),
        Formula::And(a, b) | Formula::Or(a, b) => {
            let conjunction = matches!(formula, Formula::And(..)) != negated;
            if conjunction {
                extend(&extend(paths, a, negated)?, b, negated)?
            } else {
                let mut left = extend(paths, a, negated)?;
                left.extend(extend(paths, b, negated)?);
                left
            }
        }
    };
    if result.len() > 64 {
        return Err("verification path limit reached (64)".into());
    }
    Ok(result)
}

fn equal(a: &Linear, b: &Linear) -> Result<Formula> {
    Ok(Formula::Ge(a.sub(b)?).and(Formula::Ge(b.sub(a)?)))
}

struct Context<'a> {
    functions: &'a BTreeMap<String, Function>,
    env: BTreeMap<String, Symbol>,
    facts: BTreeMap<String, Formula>,
    paths: Vec<Vec<Linear>>,
    fresh: usize,
    obligations: usize,
}

impl<'a> Context<'a> {
    fn new(functions: &'a BTreeMap<String, Function>) -> Self {
        Self {
            functions,
            env: BTreeMap::new(),
            facts: BTreeMap::new(),
            paths: vec![vec![]],
            fresh: 0,
            obligations: 0,
        }
    }
    fn fresh_name(&mut self) -> String {
        self.fresh += 1;
        format!("evg_{}", self.fresh)
    }
    fn assume(&mut self, p: &Formula) -> Result<()> {
        self.paths = extend(&self.paths, p, false)?;
        Ok(())
    }
    fn prove(&mut self, p: &Formula, label: &str, line: usize) -> Result<()> {
        self.obligations += 1;
        for path in extend(&self.paths, p, true)? {
            let certificate = kernel::solve(&path)
                .map_err(|e| format!("line {line}: cannot prove {label}: {e}"))?;
            kernel::check(&path, &certificate)?;
        }
        Ok(())
    }
    fn resolve(&mut self, t: &Type) -> Result<Ty> {
        match t {
            Type::Int => Ok(Ty::Int),
            Type::Nat => Ok(Ty::Nat),
            Type::Bool => Ok(Ty::Bool),
            Type::Array(element, len) => {
                let element = self.resolve(element)?;
                let n = self.eval(len, Some(&Ty::Nat))?.number()?;
                Ok(Ty::Array(Box::new(element), n))
            }
        }
    }
    fn compatible(&mut self, got: &Ty, expected: &Ty, line: usize) -> Result<()> {
        match (got, expected) {
            (Ty::Int, Ty::Int) | (Ty::Nat, Ty::Nat) | (Ty::Bool, Ty::Bool) => Ok(()),
            (Ty::Array(a, n), Ty::Array(b, m)) => {
                self.compatible(a, b, line)?;
                self.prove(&equal(n, m)?, "array length equality", line)
            }
            _ => Err(format!(
                "line {line}: type mismatch: expected {expected:?}, got {got:?}"
            )),
        }
    }
    fn arbitrary(&mut self, t: &Ty) -> Result<Symbol> {
        let name = self.fresh_name();
        match t {
            Ty::Int => Ok(Symbol::Number(Ty::Int, Linear::variable(name))),
            Ty::Nat => {
                let n = Linear::variable(name);
                self.assume(&Formula::Ge(n.clone()))?;
                Ok(Symbol::Number(Ty::Nat, n))
            }
            Ty::Bool => {
                let n = Linear::variable(name);
                self.assume(&Formula::Ge(n.clone()))?;
                self.assume(&Formula::Ge(Linear::number(1).sub(&n)?))?;
                Ok(Symbol::Bool(equal(&n, &Linear::number(1))?))
            }
            Ty::Array(element, len) => Ok(Symbol::Array {
                element: element.clone(),
                len: len.clone(),
                items: None,
                identity: name,
            }),
        }
    }
    fn hint(&self, e: &Expr) -> Option<Ty> {
        match &e.kind {
            Kind::Name(n) => self.env.get(n).map(Symbol::ty),
            Kind::Unary(_, x) => self.hint(x),
            Kind::Binary(_, a, b) => self.hint(a).or_else(|| self.hint(b)),
            Kind::Call(n, _) => self.functions.get(n).and_then(|f| match f.ret {
                Type::Int => Some(Ty::Int),
                Type::Nat => Some(Ty::Nat),
                Type::Bool => Some(Ty::Bool),
                _ => None,
            }),
            _ => None,
        }
    }
    fn proof_names(&self, steps: &[String], line: usize) -> Result<()> {
        for step in steps {
            if let Some(n) = step.strip_prefix("exact ") {
                if !self.facts.contains_key(n) {
                    return Err(format!("line {line}: exact {n} is not a proven local fact"));
                }
            }
        }
        Ok(())
    }
    fn eval(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        let value = self.eval_inner(e, expected).map_err(|s| {
            if s.starts_with("line ") {
                s
            } else {
                format!("line {}: {s}", e.line)
            }
        })?;
        if let Some(t) = expected {
            self.compatible(&value.ty(), t, e.line)?;
        }
        Ok(value)
    }
    fn eval_inner(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        match &e.kind {
            Kind::Number(n) => Ok(Symbol::Number(
                if matches!(expected, Some(Ty::Nat)) {
                    Ty::Nat
                } else {
                    Ty::Int
                },
                Linear::number(*n),
            )),
            Kind::Bool(b) => Ok(Symbol::Bool(if *b {
                Formula::True
            } else {
                Formula::False
            })),
            Kind::Name(n) => self
                .env
                .get(n)
                .cloned()
                .ok_or_else(|| format!("unknown value {n}")),
            Kind::Unary(op, x) if op == "!" => Ok(Symbol::Bool(
                self.eval(x, Some(&Ty::Bool))?.proposition()?.not(),
            )),
            Kind::Unary(_, x) => {
                let n = self.eval(x, Some(&Ty::Int))?.number()?;
                Ok(Symbol::Number(Ty::Int, n.scale(-1)?))
            }
            Kind::Binary(op, a, b) if op == "&&" || op == "||" => {
                let a = self.eval(a, Some(&Ty::Bool))?.proposition()?;
                // Logical expressions are pure. Both operands must be well-defined.
                let b = self.eval(b, Some(&Ty::Bool))?.proposition()?;
                Ok(Symbol::Bool(if op == "&&" { a.and(b) } else { a.or(b) }))
            }
            Kind::Binary(op, a, b) => {
                let ty = if matches!(op.as_str(), "+" | "-" | "*") {
                    expected.cloned()
                } else {
                    None
                }
                .or_else(|| self.hint(a))
                .or_else(|| self.hint(b))
                .unwrap_or(Ty::Int);
                if !matches!(ty, Ty::Int | Ty::Nat) {
                    return Err("arithmetic and comparisons require integer operands".into());
                }
                let a = self.eval(a, Some(&ty))?.number()?;
                let b = self.eval(b, Some(&ty))?.number()?;
                match op.as_str() {
                    "+" => Ok(Symbol::Number(ty, a.add(&b)?)),
                    "-" if matches!(ty, Ty::Nat) => {
                        // Nat subtraction is truncated, with an exact two-case model.
                        let result = self.arbitrary(&Ty::Nat)?;
                        let r = result.number()?;
                        let diff = a.sub(&b)?;
                        let cases = Formula::Ge(diff.clone())
                            .and(equal(&r, &diff)?)
                            .or(Formula::Ge(diff.scale(-1)?.add(&Linear::number(-1))?)
                                .and(equal(&r, &Linear::number(0))?));
                        self.assume(&cases)?;
                        Ok(result)
                    }
                    "-" => Ok(Symbol::Number(ty, a.sub(&b)?)),
                    "*" => {
                        let n = if a.terms.is_empty() {
                            b.scale(a.constant)?
                        } else if b.terms.is_empty() {
                            a.scale(b.constant)?
                        } else {
                            return Err("nonlinear multiplication needs an extended proof theory; unsupported".into());
                        };
                        Ok(Symbol::Number(ty, n))
                    }
                    "==" => Ok(Symbol::Bool(equal(&a, &b)?)),
                    "!=" => Ok(Symbol::Bool(equal(&a, &b)?.not())),
                    ">=" => Ok(Symbol::Bool(Formula::Ge(a.sub(&b)?))),
                    "<=" => Ok(Symbol::Bool(Formula::Ge(b.sub(&a)?))),
                    ">" => Ok(Symbol::Bool(Formula::Ge(
                        a.sub(&b)?.add(&Linear::number(-1))?,
                    ))),
                    "<" => Ok(Symbol::Bool(Formula::Ge(
                        b.sub(&a)?.add(&Linear::number(-1))?,
                    ))),
                    _ => Err("unsupported binary operator".into()),
                }
            }
            Kind::Array(items) => {
                let element = if let Some(Ty::Array(t, _)) = expected {
                    (**t).clone()
                } else if let Some(first) = items.first() {
                    self.hint(first).unwrap_or(Ty::Int)
                } else {
                    return Err("empty array needs an explicit type".into());
                };
                let values = items
                    .iter()
                    .map(|x| self.eval(x, Some(&element)))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Symbol::Array {
                    element: Box::new(element),
                    len: Linear::number(values.len() as i128),
                    items: Some(values),
                    identity: self.fresh_name(),
                })
            }
            Kind::Index(array, index) => {
                let array = self.eval(array, None)?;
                let index = self.eval(index, Some(&Ty::Nat))?.number()?;
                let Symbol::Array {
                    element,
                    len,
                    items,
                    identity,
                } = array
                else {
                    return Err("indexing requires an array".into());
                };
                self.prove(
                    &Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?),
                    "array index < length",
                    e.line,
                )?;
                if index.terms.is_empty() {
                    if let Some(value) = items
                        .as_ref()
                        .and_then(|v| usize::try_from(index.constant).ok().and_then(|i| v.get(i)))
                    {
                        return Ok(value.clone());
                    }
                }
                // Repeated reads of the same symbolic element have the same value.
                let key = format!("evg_read_{identity}_{index:?}");
                if let Some(v) = self.env.get(&key) {
                    return Ok(v.clone());
                }
                let v = self.arbitrary(&element)?;
                self.env.insert(key, v.clone());
                Ok(v)
            }
            Kind::Call(name, args) => {
                let f = self.functions.get(name).cloned().ok_or_else(|| format!("unknown function {name}; calls require an earlier verified declaration (recursion is not supported yet)"))?;
                if args.len() != f.params.len() {
                    return Err(format!("{name} expects {} arguments", f.params.len()));
                }
                // Evaluate actuals in the caller; dependent parameter types in an
                // isolated callee environment. Restore the caller on completion.
                let mut actuals = Vec::new();
                for ((_, t), arg) in f.params.iter().zip(args) {
                    let hint = match t {
                        Type::Nat => Some(Ty::Nat),
                        Type::Int => Some(Ty::Int),
                        Type::Bool => Some(Ty::Bool),
                        _ => None,
                    };
                    actuals.push(self.eval(arg, hint.as_ref())?);
                }
                let saved = self.env.clone();
                self.env.clear();
                for ((n, t), value) in f.params.iter().zip(actuals) {
                    let t = self.resolve(t)?;
                    self.compatible(&value.ty(), &t, e.line)?;
                    self.env.insert(n.clone(), value);
                }
                if let Some(pre) = &f.pre {
                    let p = self.eval(pre, Some(&Ty::Bool))?.proposition()?;
                    self.prove(&p, &format!("precondition of {name}"), e.line)?;
                }
                let ret = self.resolve(&f.ret)?;
                let value = self.arbitrary(&ret)?;
                self.env.insert("result".into(), value.clone());
                if let Some(post) = &f.post {
                    let p = self.eval(post, Some(&Ty::Bool))?.proposition()?;
                    self.assume(&p)?;
                }
                self.env = saved;
                Ok(value)
            }
            Kind::If(condition, yes, no) => {
                let p = self.eval(condition, Some(&Ty::Bool))?.proposition()?;
                let base = self.paths.clone();
                let env = self.env.clone();
                self.paths = extend(&base, &p, false)?;
                let a = self.eval(yes, expected)?;
                let a_paths = self.paths.clone();
                self.paths = extend(&base, &p, true)?;
                self.env = env.clone();
                let b = self.eval(no, Some(&a.ty()))?;
                let b_paths = self.paths.clone();
                self.paths = base;
                self.env = env;
                let result = self.arbitrary(&a.ty())?;
                let relation_a = self.symbol_equal(&result, &a)?;
                let relation_b = self.symbol_equal(&result, &b)?;
                let mut paths = extend(&a_paths, &relation_a, false)?;
                paths.extend(extend(&b_paths, &relation_b, false)?);
                if paths.len() > 64 {
                    return Err("verification path limit reached (64)".into());
                }
                self.paths = paths;
                Ok(result)
            }
        }
    }
    fn symbol_equal(&self, a: &Symbol, b: &Symbol) -> Result<Formula> {
        match (a, b) {
            (Symbol::Number(_, a), Symbol::Number(_, b)) => equal(a, b),
            (Symbol::Bool(a), Symbol::Bool(b)) => Ok(a
                .clone()
                .and(b.clone())
                .or(a.clone().not().and(b.clone().not()))),
            _ => Err("conditional array values are not supported yet".into()),
        }
    }
}

#[derive(Debug)]
pub struct VerifiedProgram {
    pub(crate) functions: Vec<Function>,
    pub obligations: usize,
}

pub fn verify(source: &str) -> Result<VerifiedProgram> {
    let parsed = syntax::parse(source)?;
    let mut functions = BTreeMap::new();
    let mut obligations = 0;
    for f in &parsed {
        if functions.contains_key(&f.name) {
            return Err(format!("line {}: duplicate function {}", f.line, f.name));
        }
        let mut ctx = Context::new(&functions);
        for (n, t) in &f.params {
            if ctx.env.contains_key(n) {
                return Err(format!("line {}: duplicate parameter {n}", f.line));
            }
            let ty = ctx.resolve(t)?;
            let value = ctx.arbitrary(&ty)?;
            ctx.env.insert(n.clone(), value);
        }
        if let Some(pre) = &f.pre {
            let p = ctx.eval(pre, Some(&Ty::Bool))?.proposition()?;
            ctx.assume(&p)?;
        }
        let ret = ctx.resolve(&f.ret)?;
        for statement in &f.body {
            if ctx.env.contains_key(&statement.name) || ctx.facts.contains_key(&statement.name) {
                return Err(format!(
                    "line {}: duplicate binding {}",
                    statement.value.line, statement.name
                ));
            }
            if statement.fact {
                let p = ctx.eval(&statement.value, Some(&Ty::Bool))?.proposition()?;
                if let Some(steps) = &statement.proof {
                    ctx.proof_names(steps, statement.value.line)?;
                }
                ctx.prove(
                    &p,
                    &format!("fact {}", statement.name),
                    statement.value.line,
                )?;
                ctx.assume(&p)?;
                ctx.facts.insert(statement.name.clone(), p);
            } else {
                let ty = statement.ty.as_ref().map(|t| ctx.resolve(t)).transpose()?;
                let value = ctx.eval(&statement.value, ty.as_ref())?;
                ctx.env.insert(statement.name.clone(), value);
            }
        }
        let value = ctx.eval(&f.result, Some(&ret))?;
        ctx.env.insert("result".into(), value);
        ctx.proof_names(&f.proof, f.result.line)?;
        if let Some(post) = &f.post {
            let p = ctx.eval(post, Some(&Ty::Bool))?.proposition()?;
            ctx.prove(&p, &format!("postcondition of {}", f.name), post.line)?;
        }
        obligations += ctx.obligations;
        functions.insert(f.name.clone(), f.clone());
    }
    Ok(VerifiedProgram {
        functions: parsed,
        obligations,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn checks_contracts_and_bounds_internally() {
        let p = verify(include_str!("../examples/contracts.evg")).unwrap();
        assert!(p.obligations >= 3);
        for source in [
            include_str!("../examples/reject_bounds.evg"),
            include_str!("../examples/reject_contract.evg"),
        ] {
            assert!(verify(source).is_err());
        }
    }
    #[test]
    fn composes_calls_and_checks_preconditions() {
        let prefix =
            "fn inc(n: usize) -> usize where (n < 10) ensures (result == n + 1) { n + 1 } ";
        assert!(verify(&format!(
            "{prefix} fn main() -> usize ensures (result == 5) {{ inc(4) }}"
        ))
        .is_ok());
        assert!(verify(&format!("{prefix} fn main() -> usize {{ inc(10) }}")).is_err());
    }
    #[test]
    fn verifies_both_branches_and_natural_subtraction() {
        verify("fn abs(n: isize) -> isize ensures (result >= 0) { if n >= 0 { n } else { -n } }")
            .unwrap();
        verify("fn sub(n: usize) -> usize ensures (result <= n) { n - 1 }").unwrap();
        assert!(verify(
            "fn bad(n: isize) -> isize ensures (result >= 0) { if n >= 0 { n } else { n } }"
        )
        .is_err());
    }
    #[test]
    fn facts_are_proved_before_use() {
        assert!(verify("fn bad(n: usize) -> usize { fact lie = n < 0; n }").is_err());
        assert!(verify("fn bad() -> usize { fact h = true by { exact missing }; 0 }").is_err());
        assert!(verify("fn bad() -> usize { result }").is_err());
    }
    #[test]
    fn arrays_and_types_are_checked() {
        verify("fn main() -> usize ensures (result == 20) { let a: [usize; 2] = [10, 20]; a[1] }")
            .unwrap();
        for s in [
            "fn f() -> usize { let a: [usize; 2] = [1]; 0 }",
            "fn f() -> usize { let a: [usize; 1] = [1]; a[1] }",
            "fn f() -> usize { -1 }",
            "fn f() -> bool { 1 }",
        ] {
            assert!(verify(s).is_err(), "{s}");
        }
    }
    #[test]
    fn compound_logic_and_contradictory_preconditions() {
        verify("fn f(n: usize) -> usize where (n < 3 || n > 10) ensures (result != 5) { n }")
            .unwrap();
        verify("fn f(n: usize) -> usize where (n < 0) ensures (result > 100) { n }").unwrap();
    }
}
