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
            Kind::Call(name, args) if matches!(name.as_str(), "integer" | "nat") => {
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
    // Count only up to one more than the number of supplied aliases. This
    // detects missing coverage without enumerating elements or overflowing on
    // huge nested arrays. Named shapes are shared across repeated fields.
    fn required_count(
        ty: &Type,
        structs: &BTreeMap<String, Struct>,
        cap: usize,
        records: &mut BTreeMap<String, usize>,
    ) -> Result<usize> {
        Ok(match ty {
            Type::Ref(_) => 1,
            Type::Named(name) => {
                if let Some(count) = records.get(name) {
                    return Ok(*count);
                }
                let mut count = 0usize;
                for (_, ty) in &structs.get(name).ok_or("unknown return type")?.fields {
                    count = count
                        .saturating_add(required_count(ty, structs, cap, records)?)
                        .min(cap);
                }
                records.insert(name.clone(), count);
                count
            }
            Type::Array(element, len) => {
                let count = required_count(element, structs, cap, records)?;
                if count == 0 {
                    0
                } else {
                    let length = crate::compiler::layout::array_length(len)
                        .map_err(|_| "reference-bearing array returns require a fixed extent")?;
                    count.saturating_mul(length).min(cap)
                }
            }
            _ => 0,
        })
    }

    fn valid_path<'a>(
        mut ty: &'a Type,
        path: &[ReturnProjection],
        structs: &'a BTreeMap<String, Struct>,
    ) -> Result<bool> {
        for step in path {
            ty = match (ty, step) {
                (Type::Named(name), ReturnProjection::Field(field)) => {
                    let Some((_, ty)) = structs
                        .get(name)
                        .and_then(|record| record.fields.iter().find(|(name, _)| name == field))
                    else {
                        return Ok(false);
                    };
                    ty
                }
                (Type::Array(element, length), ReturnProjection::Index(index))
                    if *index < crate::compiler::layout::array_length(length)? =>
                {
                    element
                }
                _ => return Ok(false),
            };
        }
        Ok(matches!(ty, Type::Ref(_)))
    }
    let required = required_count(
        &f.ret,
        structs,
        f.borrows.len().saturating_add(1),
        &mut BTreeMap::new(),
    )?;
    let mut supplied = BTreeSet::new();
    let mut valid = true;
    for alias in &f.borrows {
        if !borrow_expression(&alias.reference) || !supplied.insert(alias.path.clone()) {
            return Err(format!("line {}: borrows requires unique return paths and checked incoming reference projections", f.line));
        }
        valid &= valid_path(&f.ret, &alias.path, structs)?;
        if root(&alias.reference) == Some("result") {
            if f.params.iter().any(|(name, _)| name == "result") {
                return Err("result in a borrow contract names the returned value; rename the input parameter".into());
            }
            check_result_anchor(&alias.reference, &f.ret, structs)?;
        }
    }
    if !valid || supplied.len() != required {
        if required == 0 {
            return Err(format!(
                "line {}: borrows describes return-plane provenance, but the return type contains no references",
                f.line
            ));
        }
        if !f
            .params
            .iter()
            .any(|(_, ty)| type_has_reference(ty, structs))
            && !heap::owns_planes_type(&f.ret, structs)
        {
            return Err(format!(
                "line {}: cannot return a reference into a local plane: local storage ends when this function returns; a returned reference needs a surviving incoming plane or an owner returned with it",
                f.result.line
            ));
        }
        return Err(format!(
            "line {}: returned references need surviving planes; the borrows contract must identify the plane for every reference in the return value exactly once",
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
        let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
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
                    self.incoming_borrow(&alias.reference, inputs)?
                } else {
                    self.eval(&alias.reference, None)?
                };
                if !matches!(value, Symbol::Ref(..) | Symbol::RefCases(..)) {
                    return Err("return aliases must denote references".into());
                }
                aliases.insert(alias.path.clone(), AliasTarget::Incoming(value));
            }
            Ok(aliases)
        })();
        self.execution.phase = phase;
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
                    let env = std::mem::take(&mut self.locals.values);
                    let roots = std::mem::take(&mut self.locals.places);
                    let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
                    self.locals.values.insert("result".into(), value.clone());
                    let evaluated = self.eval(expression, None);
                    self.locals.values = env;
                    self.locals.places = roots;
                    self.execution.phase = phase;
                    evaluated?
                }
            };
            let mut actual = value;
            for field in fields {
                actual = match (actual, field) {
                    (Symbol::Record(_, members), ReturnProjection::Field(field)) => {
                        members.get(field).ok_or("unknown return alias field")?
                    }
                    (Symbol::Array { items, cells, .. }, ReturnProjection::Index(index)) => items
                        .as_ref()
                        .and_then(|items| items.get(*index))
                        .or_else(|| cells.get(&Linear::number(*index as i128)))
                        .ok_or("return alias index out of bounds")?,
                    _ => return Err("return alias requires a known inline field or element".into()),
                };
            }
            let same = if let (Symbol::Ref(a_ty, a, a_path), Symbol::Ref(b_ty, b, b_path)) =
                (actual, &expected)
            {
                self.compatible(a_ty, b_ty, line)?;
                a == b && self.paths_equal(a_path, b_path)?
            } else if matches!(actual.ty(), Ty::Ref(_)) && actual.ty() == expected.ty() {
                let relation = guarded_references::identity_equal(actual, &expected)?;
                self.checked_entails(&relation)?
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
                    .declarations
                    .structs
                    .get(name)
                    .cloned()
                    .ok_or("unknown return record")?;
                let env = std::mem::take(&mut self.locals.values);
                let roots = std::mem::take(&mut self.locals.places);
                let module = std::mem::replace(&mut self.locals.module, definition.module);
                let mut fields = BTreeMap::new();
                for (field, ty) in definition.fields {
                    let phase = self.execution.phase;
                    if definition.ideal_fields.contains(&field)
                        && self.execution.phase == Phase::Runtime
                    {
                        self.execution.phase = Phase::Ideal;
                    }
                    let ty = self.resolve(&ty)?;
                    path.push(ReturnProjection::Field(field.clone()));
                    let value = self.return_shape(&ty, path, aliases)?;
                    self.execution.phase = phase;
                    path.pop();
                    self.locals.values.insert(field.clone(), value.clone());
                    fields.insert(field, value);
                }
                self.locals.values = env;
                self.locals.places = roots;
                self.locals.module = module;
                Ok(Symbol::Record(name.clone(), fields))
            }
            Ty::Array(element, len) => {
                if !len.terms.is_empty() {
                    return Err("reference-bearing return array extent must be fixed".into());
                }
                let indices = aliases
                    .keys()
                    .filter(|alias| alias.starts_with(path))
                    .filter_map(|alias| match alias.get(path.len()) {
                        Some(ReturnProjection::Index(index)) => Some(*index),
                        _ => None,
                    })
                    .collect::<BTreeSet<_>>();
                let mut cells = BTreeMap::new();
                for index in indices {
                    path.push(ReturnProjection::Index(index));
                    cells.insert(
                        Linear::number(index as i128),
                        self.return_shape(element, path, aliases)?,
                    );
                    path.pop();
                }
                Ok(Symbol::Array {
                    element: element.clone(),
                    len: len.clone(),
                    items: None,
                    cells,
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
                    self.storage.memory.read(*reference)?,
                    path,
                )?)?)?;
                let value = project(self.storage.memory.read(*reference)?, path)?.clone();
                self.assume_return_type(&value, target)?;
            }
            (Symbol::Record(name, fields), Ty::Record(_)) => {
                let definition = self
                    .declarations
                    .structs
                    .get(name)
                    .cloned()
                    .ok_or("unknown result type")?;
                let env = std::mem::replace(&mut self.locals.values, fields.clone());
                let roots = std::mem::take(&mut self.locals.places);
                let facts = std::mem::replace(
                    &mut self.proof.facts,
                    definition.facts.into_iter().collect(),
                );
                let module = std::mem::replace(&mut self.locals.module, definition.module);
                let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
                self.locals.values.insert("self".into(), value.clone());
                for (name, ty) in definition.fields {
                    let ty = self.resolve(&ty)?;
                    self.assume_return_type(fields.get(&name).ok_or("missing result field")?, &ty)?;
                }
                if let Some(invariant) = definition.invariant {
                    let p = self.proposition(&invariant)?;
                    self.assume(&p)?;
                }
                self.locals.values = env;
                self.locals.places = roots;
                self.proof.facts = facts;
                self.locals.module = module;
                self.execution.phase = phase;
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
