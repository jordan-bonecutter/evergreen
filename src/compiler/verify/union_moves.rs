//! Extract a member into its matching shape without moving the containing
//! storage. Existing aliases observe the new member through the same plane.

use super::*;

impl Context<'_> {
    pub(super) fn union_move_place(&self, expression: &Expr, target: &Ty) -> bool {
        let projected = matches!(expression.kind, Kind::Field(..) | Kind::Index(..))
            || matches!(&expression.kind, Kind::Unary(op, _) if op == "*");
        if !projected {
            return false;
        }
        let Some(Ty::Union(members)) = self.hint(expression) else {
            return false;
        };
        members.contains(target) && members.contains(&Ty::Shape(Box::new(target.clone())))
    }

    pub(super) fn move_union_member(&mut self, expression: &Expr, target: &Ty) -> Result<Symbol> {
        if self.execution.phase != Phase::Runtime {
            return Err("extracting a runtime union member cannot be erased".into());
        }
        if !self.storage.opened_planes.is_empty() {
            return Err("runtime ownership moves are forbidden while invariants are open".into());
        }
        if self.execution.dropping && !self.drop_receiver_consumed() {
            return Err(
                "destructor moves require a complete local binding; decompose self first".into(),
            );
        }
        let reference = self.place_reference(expression)?;
        self.on_reference_places(
            &guarded_references::cases(&reference)?,
            Some(target),
            expression.line,
            &|ctx, case| {
                let stored = project(ctx.storage.memory.read(case.reference)?, &case.path)?.clone();
                let Symbol::Union { members, .. } = &stored else {
                    return Err("member extraction requires union storage".into());
                };
                let shape = Ty::Shape(Box::new(target.clone()));
                let index = members
                    .iter()
                    .position(|member| member == &shape)
                    .ok_or("member extraction requires a matching shape alternative")?;
                let mut payloads = vec![None; members.len()];
                payloads[index] = Some(Symbol::Shape(Box::new(target.clone())));
                let empty = Symbol::Union {
                    members: members.clone(),
                    active: Linear::number(index as i128),
                    payloads,
                };
                let value =
                    ctx.union_coercion(stored, Some(target), expression.line, Some(expression))?;
                ctx.validate_argument(&value, expression.line)?;
                // The result still owns its payload during retained-view checks.
                let pending = ctx.fresh_name();
                ctx.charge_value_work(symbol_weight(&value)?)?;
                ctx.locals.values.insert(pending.clone(), value.clone());
                let stored = ctx.replace_reference_contents(
                    case.reference,
                    &case.path,
                    empty,
                    expression.line,
                );
                ctx.locals.values.remove(&pending);
                stored?;
                Ok(value)
            },
        )
    }
}
