//! Reference identity and the independent-input boundary of modular contracts.
use super::*;

impl Context<'_> {
    pub(super) fn reference_equality(&mut self, a: &Symbol, b: &Symbol) -> Result<Formula> {
        let (Symbol::Ref(_, a, a_path), Symbol::Ref(_, b, b_path)) = (a, b) else {
            return Err("reference equality requires reference operands".into());
        };
        // Identity comparisons do not make stale generations observable again.
        project(self.memory.read(*a)?, a_path)?;
        project(self.memory.read(*b)?, b_path)?;
        self.charge_value_work(a_path.len().saturating_add(b_path.len()))?;
        if a != b || a_path.len() != b_path.len() {
            return Ok(Formula::False);
        }
        let mut same = Formula::True;
        for (a, b) in a_path.iter().zip(b_path) {
            let component = match (a, b) {
                (Projection::Field(a), Projection::Field(b)) if a == b => Formula::True,
                (Projection::Index(a), Projection::Index(b)) => equal(a, b)?,
                _ => return Ok(Formula::False),
            };
            same = same.and(component);
        }
        Ok(same)
    }

    pub(super) fn reference_ports_overlap(&mut self, inputs: &[InputReference]) -> Result<bool> {
        // Distinct planes need no pairwise arithmetic checks. Charge every
        // input and every same-plane comparison to the common proof-work budget.
        let mut planes: BTreeMap<PlaneId, Vec<usize>> = BTreeMap::new();
        for (index, input) in inputs.iter().enumerate() {
            self.charge_value_work(1)?;
            let plane = self.memory.plane(input.reference)?;
            let previous = planes.entry(plane).or_default();
            for other in previous.iter().map(|index| &inputs[*index]) {
                self.charge_value_work(1)?;
                if !self.paths_disjoint(&input.path, &other.path)? {
                    return Ok(true);
                }
            }
            previous.push(index);
        }
        Ok(false)
    }
}
