use std::{fmt::Display, rc::Rc, cell::RefCell};

use crate::context::Context;
use crate::syntax::*;

#[derive(Debug, Clone)]
pub enum Type {
    Unknown(),
    Top(),
    Bottom(),
    Number(),
    String(),
    Boolean(),
    Tuple(Vec<Type>),
    Arrow(Box<Type>, Box<Type>),
}

impl Type {
    pub fn as_number(&self) {
        match self {
            Self::Number() => {},
            _ => panic!("Expected number, received {}", self),
        }
    }

    pub fn as_function(&self) -> (&Type, &Type) {
        match self {
            Self::Arrow(ty1, ty2) => (ty1, ty2),
            _ => panic!("Expected function, received {}", self),
        }
    }

    pub fn as_tuple(&self, length: usize) -> Vec<Type> {
        match self {
            Self::Tuple(vec) => {
                if vec.len() != length {
                    panic!("Expected tuple with length {}, received {}", length, self)
                }
                vec.clone()
            },
            Self::Bottom() => {
                let mut vec = Vec::new();
                for _ in 0..length {
                    vec.push(Self::Bottom());
                }
                vec
            },
            _ => panic!("Expected tuple, received {}", self),
        }
    }

    pub fn subtype(ty1: &Type, ty2: &Type) -> bool {
        match (ty1, ty2) {
            (_, Self::Top()) => true,
            (Self::Bottom(), _) => true,
            (Self::Number(), Self::Number()) => true,
            (Self::String(), Self::String()) => true,
            (Self::Boolean(), Self::Boolean()) => true,
            (Self::Tuple(vec1), Self::Tuple(vec2)) => {
                if vec1.len() != vec2.len() {
                    false
                } else {
                    vec1.iter().zip(vec2.iter()).all(|(ty1, ty2)| Self::subtype(ty1, ty2))
                }
            },
            (Self::Arrow(ty11, ty12), Self::Arrow(ty21, ty22)) => {
                Self::subtype(&ty21, &ty11) && Self::subtype(&ty12, &ty22)
            },
            _ => false,
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unknown() => write!(f, "unknown"),
            Self::Top() => write!(f, "top"),
            Self::Bottom() => write!(f, "bottom"),
            Self::Number() => write!(f, "number"),
            Self::String() => write!(f, "string"),
            Self::Boolean() => write!(f, "boolean"),
            Self::Tuple(children) => {
                write!(f, "(")?;
                for (i, child) in children.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", child)?;
                }
                write!(f, ")")
            },
            Self::Arrow(left, right) => write!(f, "{} -> {}", left, right),
        }
    }
}

pub trait Typing {
    fn to_type(&self, ctx: &Rc<RefCell<Context>>) -> Type;
}

impl Typing for TypeExpr {
    fn to_type(&self, ctx: &Rc<RefCell<Context>>) -> Type {
        match self {
            Self::Binary(_, binary) => {
                let left = binary.left.to_type(ctx);
                let right = binary.right.to_type(ctx);
                match binary.operator {
                    TypeBinaryOperator::Arrow => Type::Arrow(Box::from(left), Box::from(right)),
                }
            },
            Self::Identifier(_, identifier) => {
                match ctx.as_ref().borrow().types.get(&identifier.name) {
                    Some(value) => value.as_ref().clone(),
                    None => panic!("Undefined variable: {}", identifier.name),
                }
            },
            Self::Tuple(_, exprs) => {
                Type::Tuple(exprs.iter().map(|expr| expr.to_type(ctx)).collect())
            },
            #[allow(unreachable_patterns)]
            _ => panic!("Unsuppored evaluation: {:?}", self)
        }
    }
}

impl Typing for Pattern {
    fn to_type(&self, ctx: &Rc<RefCell<Context>>) -> Type {
        match self {
            Self::Identifier(_, _, oty) => {
                oty.clone().map_or(Type::Unknown(), |ty| ty.to_type(ctx))
            },
            Self::Tuple(_, children) => {
                Type::Tuple(children.iter().map(|child| child.to_type(ctx)).collect())
            }
        }
    }
}

impl Typing for Expression {
    fn to_type(&self, ctx: &Rc<RefCell<Context>>) -> Type {
        match self {
            Self::Unary(_, unary) => {
                let operand = unary.operand.to_type(ctx);
                match unary.operator {
                    UnaryOperator::Neg => {
                        operand.as_number();
                        Type::Number()
                    },
                }
            },
            Self::Binary(_, binary) => {
                let left = binary.left.to_type(ctx);
                let right = binary.right.to_type(ctx);
                match binary.operator {
                    BinaryOperator::Add | BinaryOperator::Sub | BinaryOperator::Mul | BinaryOperator::Div | BinaryOperator::Pow => {
                        left.as_number();
                        right.as_number();
                        Type::Number()
                    },
                }
            },
            Self::Number(_, _) => Type::Number(),
            Self::String(_, _) => Type::String(),
            Self::Boolean(_, _) => Type::Boolean(),
            Self::Identifier(_, identifier) => {
                match ctx.as_ref().borrow().valty.get(&identifier.name) {
                    Some(value) => value.as_ref().clone(),
                    None => panic!("Undefined variable: {}", identifier.name),
                }
            },
            Self::Tuple(_, exprs) => {
                Type::Tuple(exprs.iter().map(|expr| expr.to_type(ctx)).collect())
            },
            Self::Function(_, func) => {
                let ty = func.pattern.to_type(ctx);
                let mut ctx = ctx.borrow_mut().clone();
                ctx.bind_valty(&func.pattern, &Type::Bottom());
                Type::Arrow(Box::from(ty), Box::from(func.expr.to_type(&Rc::from(RefCell::from(ctx)))))
            },
            Self::Call(_, call) => {
                let ty1 = call.callee.to_type(ctx);
                let ty2 = call.argument.to_type(ctx);
                let (ty11, ty12) = ty1.as_function();
                if Type::subtype(&ty2, ty11) {
                    ty12.clone()
                } else {
                    panic!("subtype check failed")
                }
            },
            _ => panic!("Unsuppored type: {:?}", self)
        }
    }
}
