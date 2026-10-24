//! Exact provenance for reference leaves in returned records and fixed arrays.
use super::*;
use crate::syntax::ReturnProjection;
pub(super) enum AliasTarget {
    Incoming(Symbol),
    Result(Expr),
}
type Aliases = BTreeMap<Vec<ReturnProjection>, AliasTarget>;

fn root(expression: &Expr) -> Option<&str> {
    match &expression.kind {
        Kind::Name(name) => Some(name),
        Kind::Field(base, _) | Kind::Index(base, _) | Kind::Unary(_, base) => root(base),
        _ => None,
    }
}

// A result anchor may traverse inline fields/arrays and owned allocations,
// never borrowed pointers. Merely referring to a result field does not give
// its temporary return slot a lifetime beyond the function.
fn check_result_anchor(
    expression: &Expr,
    ty: &Type,
    structs: &BTreeMap<String, Struct>,
) -> Result<()> {
    fn result_only(expression: &Expr) -> bool {
        match &expression.kind {
            Kind::Name(name) => name == "result",
            Kind::Number(_) | Kind::Constant(..) | Kind::Bool(_) => true,
            Kind::Field(base, _) | Kind::Unary(_, base) => result_only(base),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => result_only(a) && result_only(b),
            Kind::If(c, a, b) => result_only(c) && result_only(a) && result_only(b),
            Kind::Call(name, args) if matches!(name.as_str(), "int" | "nat") => {
                args.iter().all(result_only)
            }
            _ => false,
        }
    }
    fn project_type<'a>(
        expression: &Expr,
        ty: &'a Type,
        structs: &'a BTreeMap<String, Struct>,
        crossed: &mut bool,
    ) -> Result<&'a Type> {
        match &expression.kind {
            Kind::Name(name) if name == "result" => Ok(ty),
            Kind::Field(base, field) => {
                let Type::Named(name) = project_type(base, ty, structs, crossed)? else {
                    return Err("result anchor field needs a record".into());
                };
                structs
                    .get(name)
                    .and_then(|definition| definition.fields.iter().find(|(name, _)| name == field))
                    .map(|(_, ty)| ty)
                    .ok_or_else(|| "unknown result anchor field".into())
            }
            Kind::Index(base, index) if result_only(index) => {
                let Type::Array(inner, _) = project_type(base, ty, structs, crossed)? else {
                    return Err("result anchor index needs an array".into());
                };
                Ok(inner)
            }
            Kind::Unary(op, base) if op == "*" => {
                let Type::Plane(inner) = project_type(base, ty, structs, crossed)? else {
                    return Err(
                        "result anchors may follow owned planes, not borrowed pointers".into(),
                    );
                };
                *crossed = true;
                Ok(inner)
            }
            _ => Err("result anchors require structural projections of the returned value".into()),
        }
    }
    let Kind::Unary(op, place) = &expression.kind else {
        return Err("result borrows require an address inside a returned owned plane".into());
    };
    if op != "&" {
        return Err("result borrows require an address inside a returned owned plane".into());
    }
    let mut crossed = false;
    project_type(place, ty, structs, &mut crossed)?;
    if !crossed {
        return Err("result borrows cannot reference temporary return slots; project through a returned owned plane".into());
    }
    Ok(())
}

pub(super) fn check_return_borrows(f: &Function, structs: &BTreeMap<String, Struct>) -> Result<()> {
    fn paths(
        ty: &Type,
        structs: &BTreeMap<String, Struct>,
        path: &mut Vec<ReturnProjection>,
        out: &mut BTreeSet<Vec<ReturnProjection>>,
        work: &mut usize,
    ) -> Result<()> {
        *work += 1;
        if *work > 2048 || path.len() > 64 {
            return Err("return alias expansion exceeds verification limit".into());
        }
        match ty {
            Type::Ref(_) => {
                out.insert(path.clone());
            }
            Type::Named(name) => {
                for (name, ty) in &structs.get(name).ok_or("unknown return type")?.fields {
                    path.push(ReturnProjection::Field(name.clone()));
                    paths(ty, structs, path, out, work)?;
                    path.pop();
                }
            }
            Type::Array(element, len) if type_has_reference(element, structs) => {
                let Kind::Number(len) = len.kind else {
                    return Err("reference-bearing array returns require a literal extent".into());
                };
                let len = usize::try_from(len).map_err(|_| "invalid return array extent")?;
                if len > 2048 {
                    return Err("return alias expansion exceeds verification limit".into());
                }
                for index in 0..len {
                    path.push(ReturnProjection::Index(index));
                    paths(element, structs, path, out, work)?;
                    path.pop();
                }
            }
            _ => {}
        }
        Ok(())
    }
    let mut required = BTreeSet::new();
    paths(&f.ret, structs, &mut Vec::new(), &mut required, &mut 0)?;
    let mut supplied = BTreeSet::new();
    for alias in &f.borrows {
        if !borrow_expression(&alias.reference) || !supplied.insert(alias.path.clone()) {
            return Err(format!("line {}: borrows requires unique return paths and checked incoming reference projections", f.line));
        }
        if root(&alias.reference) == Some("result") {
            if f.params.iter().any(|(name, _)| name == "result") {
                return Err("result in a borrow contract names the returned value; rename the input parameter".into());
            }
            check_result_anchor(&alias.reference, &f.ret, structs)?;
        }
    }
    if supplied != required {
        return Err(format!(
            "line {}: borrows must name every return reference leaf exactly once",
            f.line
        ));
    }
    Ok(())
}

impl Context<'_> {
    pub(super) fn return_aliases(
        &mut self,
        f: &Function,
        inputs: Option<&[InputReference]>,
    ) -> Result<Aliases> {
        let phase = std::mem::replace(&mut self.phase, Phase::Specification);
        let result = (|| {
            let mut aliases = BTreeMap::new();
            for alias in &f.borrows {
                if root(&alias.reference) == Some("result") {
                    aliases.insert(
                        alias.path.clone(),
                        AliasTarget::Result(alias.reference.clone()),
                    );
                    continue;
                }
                let value = if let Some(inputs) = inputs {
                    let place = self.incoming_place(&alias.reference, inputs, None)?;
                    Symbol::Ref(place.ty, place.reference, place.path)
                } else {
                    self.eval(&alias.reference, None)?
                };
                if !matches!(value, Symbol::Ref(..)) {
                    return Err("return aliases must denote references".into());
                }
                aliases.insert(alias.path.clone(), AliasTarget::Incoming(value));
            }
            Ok(aliases)
        })();
        self.phase = phase;
        result
    }

    pub(super) fn check_return_aliases(
        &mut self,
        value: &Symbol,
        aliases: &Aliases,
        line: usize,
        infeasible_entry: bool,
    ) -> Result<()> {
        for (fields, expected) in aliases {
            let expected = match expected {
                AliasTarget::Incoming(value) => value.clone(),
                AliasTarget::Result(expression) => {
                    self.charge_value_work(symbol_weight(value)?)?;
                    let env = std::mem::take(&mut self.env);
                    let roots = std::mem::take(&mut self.roots);
                    let phase = std::mem::replace(&mut self.phase, Phase::Specification);
                    self.env.insert("result".into(), value.clone());
                    let evaluated = self.eval(expression, None);
                    self.env = env;
                    self.roots = roots;
                    self.phase = phase;
                    evaluated?
                }
            };
            let mut actual = value;
            for field in fields {
                actual = match (actual, field) {
                    (Symbol::Record(_, members), ReturnProjection::Field(field)) => {
                        members.get(field).ok_or("unknown return alias field")?
                    }
                    (
                        Symbol::Array {
                            items: Some(items), ..
                        },
                        ReturnProjection::Index(index),
                    ) => items
                        .get(*index)
                        .ok_or("return alias index out of bounds")?,
                    _ => return Err("return alias requires a known inline field or element".into()),
                };
            }
            let same = if let (Symbol::Ref(a_ty, a, a_path), Symbol::Ref(b_ty, b, b_path)) =
                (actual, &expected)
            {
                self.compatible(a_ty, b_ty, line)?;
                a == b && self.paths_equal(a_path, b_path)?
            } else {
                false
            };
            if !same && !infeasible_entry {
                // The independent-port declaration can be infeasible for a
                // nominal invariant requiring internal aliases. Only a checked
                // contradiction discharges that configuration; heap/overlapping
                // calls still recheck the body against their actual addresses.
                return Err(format!(
                    "line {line}: returned reference field does not match its borrows contract"
                ));
            }
        }
        Ok(())
    }

    pub(super) fn return_shape(
        &mut self,
        ty: &Ty,
        path: &mut Vec<ReturnProjection>,
        aliases: &Aliases,
    ) -> Result<Symbol> {
        self.charge_value_work(1)?;
        if !self.ty_has_reference(ty) {
            return self.arbitrary(ty);
        }
        match ty {
            Ty::Ref(_) => match aliases.get(path) {
                Some(AliasTarget::Incoming(value)) => Ok(value.clone()),
                Some(AliasTarget::Result(_)) => {
                    Err("result-owned borrows require actual storage checking".into())
                }
                None => Err("missing return reference alias".into()),
            },
            Ty::Record(name) => {
                let definition = self
                    .structs
                    .get(name)
                    .cloned()
                    .ok_or("unknown return record")?;
                let env = std::mem::take(&mut self.env);
                let roots = std::mem::take(&mut self.roots);
                let module = std::mem::replace(&mut self.module, definition.module);
                let mut fields = BTreeMap::new();
                for (field, ty) in definition.fields {
                    let phase = self.phase;
                    if definition.ideal_fields.contains(&field) && self.phase == Phase::Runtime {
                        self.phase = Phase::Ideal;
                    }
                    let ty = self.resolve(&ty)?;
                    path.push(ReturnProjection::Field(field.clone()));
                    let value = self.return_shape(&ty, path, aliases)?;
                    self.phase = phase;
                    path.pop();
                    self.env.insert(field.clone(), value.clone());
                    fields.insert(field, value);
                }
                self.env = env;
                self.roots = roots;
                self.module = module;
                Ok(Symbol::Record(name.clone(), fields))
            }
            Ty::Array(element, len) => {
                if !len.terms.is_empty() {
                    return Err("reference-bearing return array extent must be fixed".into());
                }
                let length =
                    usize::try_from(len.constant).map_err(|_| "invalid return array extent")?;
                if length > 2048 {
                    return Err("return alias expansion exceeds verification limit".into());
                }
                let mut items = Vec::with_capacity(length);
                for index in 0..length {
                    path.push(ReturnProjection::Index(index));
                    items.push(self.return_shape(element, path, aliases)?);
                    path.pop();
                }
                Ok(Symbol::Array {
                    element: element.clone(),
                    len: len.clone(),
                    items: Some(items),
                    cells: BTreeMap::new(),
                    identity: self.fresh_name(),
                })
            }
            _ => Err("invalid reference-bearing return type".into()),
        }
    }

    // These are consequences of the checked result type, not facts inferred
    // from a caller-only enclosing object. Array extents may depend on freshly
    // modeled scalar fields of the result, so their equalities are assumptions
    // at a call and obligations when the actual function body is checked.
    fn assume_return_compatible(&mut self, actual: &Ty, expected: &Ty) -> Result<()> {
        match (actual, expected) {
            (Ty::Ref(a), Ty::Ref(b)) => self.assume_return_compatible(a, b),
            (Ty::Array(a, n), Ty::Array(b, m)) => {
                self.assume_return_compatible(a, b)?;
                self.assume(&equal(n, m)?)
            }
            (a, b) if a == b => Ok(()),
            _ => Err("return alias type disagrees with the declared result type".into()),
        }
    }
    pub(super) fn assume_return_type(&mut self, value: &Symbol, ty: &Ty) -> Result<()> {
        self.charge_value_work(1)?;
        self.assume_return_compatible(&value.ty(), ty)?;
        match (value, ty) {
            (Symbol::Ref(_, reference, path), Ty::Ref(target)) => {
                self.charge_value_work(symbol_weight(project(
                    self.memory.read(*reference)?,
                    path,
                )?)?)?;
                let value = project(self.memory.read(*reference)?, path)?.clone();
                self.assume_return_type(&value, target)?;
            }
            (Symbol::Record(name, fields), Ty::Record(_)) => {
                let definition = self
                    .structs
                    .get(name)
                    .cloned()
                    .ok_or("unknown result type")?;
                let env = std::mem::replace(&mut self.env, fields.clone());
                let roots = std::mem::take(&mut self.roots);
                let facts =
                    std::mem::replace(&mut self.facts, definition.facts.into_iter().collect());
                let module = std::mem::replace(&mut self.module, definition.module);
                let phase = std::mem::replace(&mut self.phase, Phase::Specification);
                self.env.insert("self".into(), value.clone());
                for (name, ty) in definition.fields {
                    let ty = self.resolve(&ty)?;
                    self.assume_return_type(fields.get(&name).ok_or("missing result field")?, &ty)?;
                }
                if let Some(invariant) = definition.invariant {
                    let p = self.proposition(&invariant)?;
                    self.assume(&p)?;
                }
                self.env = env;
                self.roots = roots;
                self.facts = facts;
                self.module = module;
                self.phase = phase;
            }
            (
                Symbol::Array {
                    items: Some(items), ..
                },
                Ty::Array(element, _),
            ) => {
                for value in items {
                    self.assume_return_type(value, element)?;
                }
            }
            _ => self.assume_element_type(value)?,
        }
        Ok(())
    }
}
