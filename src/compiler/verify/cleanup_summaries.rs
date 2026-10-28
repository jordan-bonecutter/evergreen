//! Universal cleanup safety for reference-free values. This imports trust
//! dependencies even when a destructor has no externally visible writes.

use super::*;

#[cfg(test)]
mod tests;

enum Pending<'a> {
    Value(&'a Symbol),
    Type(&'a Type),
    Record(&'a str),
}

impl Context<'_> {
    pub(super) fn import_cleanup_safety(&mut self, value: &Symbol) -> Result<()> {
        let structs = self.declarations.structs;
        let destructors = self.declarations.destructors;
        let mut pending = vec![Pending::Value(value)];
        let mut methods = BTreeSet::new();
        let mut types = BTreeSet::new();
        while let Some(next) = pending.pop() {
            self.charge_value_work(1)?;
            let record = match next {
                Pending::Value(Symbol::Record(name, fields)) => {
                    if !destructors.contains_key(name) {
                        let definition = structs.get(name).ok_or("unknown cleanup type")?;
                        for (field, _) in definition.runtime_fields() {
                            pending.push(Pending::Value(
                                fields.get(field).ok_or("missing cleanup field")?,
                            ));
                        }
                    }
                    Some(name.as_str())
                }
                Pending::Value(Symbol::Array {
                    len,
                    items,
                    element,
                    ..
                }) => {
                    if *len == Linear::number(0) {
                        continue;
                    }
                    if let Some(items) = items {
                        pending.extend(items.iter().map(Pending::Value));
                    } else if let Ty::Record(name) = element.as_ref() {
                        pending.push(Pending::Record(name));
                    } else if self.has_runtime_cleanup(element) {
                        return Err(
                            "opaque aggregate cleanup needs a universal element safety summary"
                                .into(),
                        );
                    }
                    None
                }
                Pending::Type(Type::Named(name)) => {
                    pending.push(Pending::Record(name));
                    None
                }
                Pending::Record(name) => {
                    if !types.insert(name) {
                        continue;
                    }
                    if !destructors.contains_key(name) {
                        pending.extend(
                            structs
                                .get(name)
                                .ok_or("unknown cleanup type")?
                                .runtime_fields()
                                .map(|(_, ty)| Pending::Type(ty)),
                        );
                    }
                    Some(name)
                }
                Pending::Type(Type::Array(element, count)) => {
                    if crate::compiler::layout::array_length(count).ok() != Some(0) {
                        pending.push(Pending::Type(element));
                    }
                    None
                }
                _ => None,
            };
            if let Some(method) = record.and_then(|name| destructors.get(name)) {
                if methods.insert(method.name.as_str()) {
                    self.note_cleanup_divergence(&method.name);
                    let safety = self.import_summary(&method.name, summaries::Aspect::Safety)?;
                    self.proof.uses.extend(safety);
                }
            }
        }
        Ok(())
    }
}
