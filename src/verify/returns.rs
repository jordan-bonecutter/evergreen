//! Exact provenance for reference leaves in returned records and fixed arrays.
use super::*;
use crate::syntax::ReturnProjection;
type Aliases = BTreeMap<Vec<ReturnProjection>, Symbol>;

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
                let value = if let Some(inputs) = inputs {
                    let place = self.incoming_place(&alias.reference, inputs, None)?;
                    Symbol::Ref(place.ty, place.reference, place.path)
                } else {
                    self.eval(&alias.reference, None)?
                };
                if !matches!(value, Symbol::Ref(..)) {
                    return Err("return aliases must denote references".into());
                }
                aliases.insert(alias.path.clone(), value);
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
    ) -> Result<()> {
        for (fields, expected) in aliases {
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
                (actual, expected)
            {
                self.compatible(a_ty, b_ty, line)?;
                a == b && self.paths_equal(a_path, b_path)?
            } else {
                false
            };
            if !same {
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
            Ty::Ref(_) => aliases
                .get(path)
                .cloned()
                .ok_or_else(|| "missing return reference alias".into()),
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
                    let ty = self.resolve(&ty)?;
                    path.push(ReturnProjection::Field(field.clone()));
                    let value = self.return_shape(&ty, path, aliases)?;
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
