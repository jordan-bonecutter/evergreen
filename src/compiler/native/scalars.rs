//! Scalar expression lowering and fixed-register x86-64 operations.
//! Binary operands are evaluated left-to-right. The encoder receives the left
//! operand in rcx and the right operand in rax, and leaves its result in rax.

use super::*;

#[derive(Clone, Copy)]
enum Operation {
    Arithmetic(Arithmetic),
    Logical(Logical),
    Compare(Comparison),
}

#[derive(Clone, Copy)]
enum Arithmetic {
    Add,
    Subtract,
    Multiply,
}

#[derive(Clone, Copy)]
enum Logical {
    And,
    Or,
    Implies,
}

#[derive(Clone, Copy)]
enum Comparison {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

impl Operation {
    fn parse(operator: &str) -> Result<Self> {
        Ok(match operator {
            "+" => Self::Arithmetic(Arithmetic::Add),
            "-" => Self::Arithmetic(Arithmetic::Subtract),
            "*" => Self::Arithmetic(Arithmetic::Multiply),
            "&&" => Self::Logical(Logical::And),
            "||" => Self::Logical(Logical::Or),
            "=>" => Self::Logical(Logical::Implies),
            "==" => Self::Compare(Comparison::Equal),
            "!=" => Self::Compare(Comparison::NotEqual),
            "<" => Self::Compare(Comparison::Less),
            "<=" => Self::Compare(Comparison::LessEqual),
            ">" => Self::Compare(Comparison::Greater),
            ">=" => Self::Compare(Comparison::GreaterEqual),
            _ => return Err("unsupported native operator".into()),
        })
    }

    fn encode(self, code: &mut Vec<u8>, signed: bool) {
        match self {
            Self::Arithmetic(operation) => code.extend(match operation {
                Arithmetic::Add => &[0x48, 0x01, 0xc8][..], // add rax, rcx
                Arithmetic::Subtract => &[
                    0x48, 0x29, 0xc1, // sub rcx, rax
                    0x48, 0x89, 0xc8, // mov rax, rcx
                ],
                Arithmetic::Multiply => &[0x48, 0x0f, 0xaf, 0xc1], // imul rax, rcx
            }),
            Self::Logical(operation) => code.extend(match operation {
                Logical::And => &[0x48, 0x21, 0xc8][..], // and rax, rcx
                Logical::Or => &[0x48, 0x09, 0xc8],      // or rax, rcx
                Logical::Implies => &[
                    0x48, 0x83, 0xf1, 1, // xor rcx, 1
                    0x48, 0x09, 0xc8, // or rax, rcx
                ],
            }),
            Self::Compare(comparison) => {
                code.extend([0x48, 0x39, 0xc1]); // cmp rcx, rax
                code.extend([0x0f, comparison.condition(signed), 0xc0]); // setcc al
                code.extend([0x0f, 0xb6, 0xc0]); // movzx eax, al
            }
        }
    }
}

impl Comparison {
    fn condition(self, signed: bool) -> u8 {
        match (self, signed) {
            (Self::Equal, _) => 0x94,
            (Self::NotEqual, _) => 0x95,
            (Self::Less, true) => 0x9c,
            (Self::Less, false) => 0x92,
            (Self::LessEqual, true) => 0x9e,
            (Self::LessEqual, false) => 0x96,
            (Self::Greater, true) => 0x9f,
            (Self::Greater, false) => 0x97,
            (Self::GreaterEqual, true) => 0x9d,
            (Self::GreaterEqual, false) => 0x93,
        }
    }
}

impl Emitter<'_> {
    pub(super) fn binary(
        &mut self,
        operator: &str,
        left: &Expr,
        right: &Expr,
        expected: Option<&Type>,
    ) -> Result<Type> {
        let operation = Operation::parse(operator)?;
        let arithmetic = matches!(operation, Operation::Arithmetic(_));
        let operand = if matches!(operation, Operation::Logical(_)) {
            Type::Bool
        } else {
            (if arithmetic { expected.cloned() } else { None })
                .or_else(|| self.hint(left))
                .or_else(|| self.hint(right))
                .unwrap_or_else(machine)
        };
        self.expr(left, Some(&operand))?;
        self.push();
        self.expr(right, Some(&operand))?;
        self.pop();
        let signed = matches!(operand, Type::Machine(integer) if integer.signed);
        operation.encode(self.code, signed);
        if arithmetic {
            self.normalize_machine(&operand)?;
            Ok(operand)
        } else {
            Ok(Type::Bool)
        }
    }

    pub(super) fn logical_not(&mut self, value: &Expr) -> Result<Type> {
        self.expr(value, Some(&Type::Bool))?;
        self.code.extend([0x83, 0xf0, 1]); // xor eax, 1
        Ok(Type::Bool)
    }

    pub(super) fn negate(&mut self, value: &Expr, expected: Option<&Type>) -> Result<Type> {
        let ty = expected
            .cloned()
            .or_else(|| self.hint(value))
            .unwrap_or_else(machine);
        if !matches!(ty, Type::Machine(_)) {
            return Err("native negation requires a machine integer".into());
        }
        self.expr(value, Some(&ty))?;
        self.code.extend([0x48, 0xf7, 0xd8]); // neg rax
        self.normalize_machine(&ty)?;
        Ok(ty)
    }

    /// Choose the low result bits, then restore the signed/unsigned register
    /// representation. Overflow is unspecified in source; this is a target choice.
    pub(super) fn normalize_machine(&mut self, ty: &Type) -> Result<()> {
        let Type::Machine(integer) = ty else {
            return Err("native arithmetic requires a machine integer".into());
        };
        self.code.extend(match (integer.bits, integer.signed) {
            (8, false) => &[0x0f, 0xb6, 0xc0][..],
            (8, true) => &[0x48, 0x0f, 0xbe, 0xc0],
            (16, false) => &[0x0f, 0xb7, 0xc0],
            (16, true) => &[0x48, 0x0f, 0xbf, 0xc0],
            (32, false) => &[0x89, 0xc0],
            (32, true) => &[0x48, 0x63, 0xc0],
            (64, _) => &[],
            _ => return Err("invalid native arithmetic width".into()),
        });
        Ok(())
    }
}
