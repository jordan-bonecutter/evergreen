//! Congruent propositions for pure observations. References include their exact
//! projection revision; materializing a view cannot keep a result after a write.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Argument {
    Number(Ty, Linear),
    Bool(Formula),
    Unit,
    Array(Ty, Linear, String),
    Read(Ty, subjects::Stamp),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Application {
    function: String,
    arguments: Vec<Argument>,
}

#[derive(Default)]
pub(in crate::compiler::verify) struct Applications {
    model: BTreeMap<Application, Symbol>,
    pub(super) computed: BTreeMap<Application, Symbol>,
}

impl Context<'_> {
    pub(in crate::compiler::verify) fn model_ideal_predicate(
        &mut self,
        function: &Function,
    ) -> Result<Option<Symbol>> {
        let Some(key) = self.predicate_application(function)? else {
            return Ok(None);
        };
        if let Some(value) = self
            .applications
            .computed
            .get(&key)
            .or_else(|| self.applications.model.get(&key))
        {
            return Ok(Some(value.clone()));
        }
        let value = self.arbitrary(&Ty::Bool)?;
        self.applications.model.insert(key, value.clone());
        Ok(Some(value))
    }

    pub(super) fn predicate_application(
        &mut self,
        function: &Function,
    ) -> Result<Option<Application>> {
        if !function.ideal || function.ret != Type::Bool || !eligible(self, function) {
            return Ok(None);
        }
        self.charge_value_work(1 + function.name.len() / 32)?;
        let mut arguments = Vec::with_capacity(function.params.len());
        for (name, _) in &function.params {
            let value = self
                .locals
                .values
                .get(name)
                .ok_or("missing predicate argument")?;
            // Charge type/value-key clones without expanding array contents.
            self.charge_value_work(symbol_weight(&Symbol::Shape(Box::new(value.ty())))?)?;
            let value = self
                .locals
                .values
                .get(name)
                .ok_or("missing predicate argument")?;
            let argument = match value {
                Symbol::Number(ty, n) => {
                    let value = Argument::Number(ty.clone(), n.clone());
                    self.charge_value_work(n.terms.len().saturating_add(1))?;
                    value
                }
                Symbol::Bool(p) => {
                    let value = Argument::Bool(p.clone());
                    self.charge_value_work(p.storage_weight()?)?;
                    value
                }
                Symbol::Unit => Argument::Unit,
                Symbol::Array {
                    element,
                    len,
                    identity,
                    ..
                } if self.observation_type(element) => {
                    Argument::Array(*element.clone(), len.clone(), identity.clone())
                }
                Symbol::Ref(ty, reference, path) if self.observation_type(ty) => {
                    let ty = *ty.clone();
                    let stamp = self.proof.subjects.observe(
                        &self.storage.memory,
                        *reference,
                        path.clone(),
                    )?;
                    Argument::Read(ty, stamp)
                }
                // Nested references require a transitive observation footprint.
                // Owned resources and their identities are not flattened here.
                _ => return Ok(None),
            };
            arguments.push(argument);
        }
        Ok(Some(Application {
            function: function.name.clone(),
            arguments,
        }))
    }

    fn observation_type(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Int | Ty::Nat | Ty::Machine(_) | Ty::Bool | Ty::Unit => true,
            Ty::Array(element, _) => self.observation_type(element),
            Ty::Record(_) => self.scalar_field_value(ty) && !self.has_runtime_cleanup(ty),
            _ => false,
        }
    }
}
