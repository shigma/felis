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

    pub fn as_boolean(&self) {
        match self {
            Self::Boolean() => {},
            _ => panic!("Expected boolean, received {}", self),
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

    pub fn join(ty1: &Type, ty2: &Type) -> Type {
        if Type::subtype(ty1, ty2) { return ty2.clone() }
        if Type::subtype(ty2, ty1) { return ty1.clone() }
        match (ty1, ty2) {
            (Self::Tuple(vec1), Self::Tuple(vec2)) => {
                if vec1.len() != vec2.len() {
                    Type::Top()
                } else {
                    Type::Tuple(vec1.iter().zip(vec2.iter()).map(|(ty1, ty2)| Type::join(ty1, ty2)).collect())
                }
            },
            (Self::Arrow(ty11, ty12), Self::Arrow(ty21, ty22)) => {
                Type::Arrow(Box::from(Type::meet(ty11, ty21)), Box::from(Type::join(ty12, ty22)))
            },
            _ => Type::Top()
        }
    }

    pub fn meet(ty1: &Type, ty2: &Type) -> Type {
        if Type::subtype(ty1, ty2) { return ty1.clone() }
        if Type::subtype(ty2, ty1) { return ty2.clone() }
        match (ty1, ty2) {
            (Self::Tuple(vec1), Self::Tuple(vec2)) => {
                if vec1.len() != vec2.len() {
                    Type::Bottom()
                } else {
                    Type::Tuple(vec1.iter().zip(vec2.iter()).map(|(ty1, ty2)| Type::meet(ty1, ty2)).collect())
                }
            },
            (Self::Arrow(ty11, ty12), Self::Arrow(ty21, ty22)) => {
                Type::Arrow(Box::from(Type::join(ty11, ty21)), Box::from(Type::meet(ty12, ty22)))
            },
            _ => Type::Bottom()
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
                    BinaryOperator::Gt | BinaryOperator::Lt | BinaryOperator::Ge | BinaryOperator::Le | BinaryOperator::Eq | BinaryOperator::Ne => {
                        left.as_number();
                        right.as_number();
                        Type::Boolean()
                    },
                    BinaryOperator::And | BinaryOperator::Or => {
                        left.as_boolean();
                        right.as_boolean();
                        Type::Boolean()
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
            Self::Block(_, vec, open) => {
                let ctx = ctx.borrow_mut().clone();
                let rc = &Rc::from(RefCell::from(ctx));
                let mut ty = Type::Bottom();
                for stmt in vec.iter() {
                    ty = stmt.to_type(rc);
                }
                if *open { ty } else { Type::Bottom() }
            },
            Self::If(_, cond, then, else_) => {
                cond.to_type(ctx).as_boolean();
                if let Some(else_) = &else_ {
                    Type::join(&then.to_type(ctx), &else_.to_type(ctx))
                } else {
                    Type::Bottom()
                }
            },
            #[allow(unreachable_patterns)]
            _ => panic!("Unsuppored type: {:?}", self)
        }
    }
}

impl Typing for Statement {
    fn to_type(&self, ctx: &Rc<RefCell<Context>>) -> Type {
        match self {
            Self::Empty() => {},
            Self::Expression(_, expr) => {
                return expr.to_type(ctx);
            },
            Self::ValueBind(_, bind) => {
                let ty = bind.expr.to_type(ctx);
                ctx.borrow_mut().bind_valty(&bind.pattern, &ty);
                return ty;
            },
            Self::TypeBind(_, bind) => {
                let ident = bind.ident.clone();
                let ty = bind.expr.to_type(ctx);
                ctx.borrow_mut().bind_type(ident, &ty);
            },
        }
        Type::Bottom()
    }
}
