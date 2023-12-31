use std::{fmt::Display, rc::Rc, cell::RefCell};

use crate::context::Context;
use crate::syntax::*;

#[derive(Debug, Clone)]
pub enum Value {
    Void(),
    Number(f64),
    String(String),
    Boolean(bool),
    Tuple(Vec<Value>),
    Function(Function, Rc<RefCell<Context>>),
}

impl Value {
    pub fn as_number(&self) -> f64 {
        match self {
            Self::Number(number) => *number,
            _ => panic!("Expected number"),
        }
    }

    pub fn as_boolean(&self) -> bool {
        match self {
            Self::Boolean(boolean) => *boolean,
            _ => panic!("Expected boolean"),
        }
    }

    pub fn as_function(&self) -> (&Function, &Rc<RefCell<Context>>) {
        match self {
            Self::Function(function, ctx) => (function, ctx),
            _ => panic!("Expected function"),
        }
    }

    pub fn as_tuple(&self, length: usize) -> Vec<Value> {
        match self {
            Self::Tuple(vec) => {
                if vec.len() != length {
                    panic!("Expected tuple with length {}", length)
                }
                vec.clone()
            },
            Self::Void() => {
                let mut vec = Vec::new();
                for _ in 0..length {
                    vec.push(Self::Void());
                }
                vec
            },
            _ => panic!("Expected tuple"),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Void() => write!(f, "<void>"),
            Self::Number(number) => write!(f, "{}", number),
            Self::String(string) => write!(f, "{}", string),
            Self::Boolean(bool) => write!(f, "{}", bool),
            Self::Tuple(values) => {
                write!(f, "(")?;
                for (i, value) in values.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", value)?;
                }
                write!(f, ")")
            },
            Self::Function(_, _) => write!(f, "<function>"),
        }
    }
}

pub trait Evaluation {
    fn to_value(&self, ctx: &Rc<RefCell<Context>>) -> Value;
}

impl Evaluation for Expression {
    fn to_value(&self, ctx: &Rc<RefCell<Context>>) -> Value {
        match self {
            Self::Binary(_, binary) => {
                let left = binary.left.to_value(ctx);
                let right = binary.right.to_value(ctx);
                match binary.operator {
                    BinaryOperator::Add => Value::Number(left.as_number() + right.as_number()),
                    BinaryOperator::Sub => Value::Number(left.as_number() - right.as_number()),
                    BinaryOperator::Mul => Value::Number(left.as_number() * right.as_number()),
                    BinaryOperator::Div => Value::Number(left.as_number() / right.as_number()),
                    BinaryOperator::Pow => Value::Number(left.as_number().powf(right.as_number())),
                    BinaryOperator::Gt => Value::Boolean(left.as_number() > right.as_number()),
                    BinaryOperator::Lt => Value::Boolean(left.as_number() < right.as_number()),
                    BinaryOperator::Ge => Value::Boolean(left.as_number() >= right.as_number()),
                    BinaryOperator::Le => Value::Boolean(left.as_number() <= right.as_number()),
                    BinaryOperator::Eq => Value::Boolean(left.as_number() == right.as_number()),
                    BinaryOperator::Ne => Value::Boolean(left.as_number() != right.as_number()),
                    BinaryOperator::And => Value::Boolean(left.as_boolean() && right.as_boolean()),
                    BinaryOperator::Or => Value::Boolean(left.as_boolean() || right.as_boolean()),
                }
            },
            Self::Unary(_, unary) => {
                let operand = unary.operand.to_value(ctx);
                match unary.operator {
                    UnaryOperator::Neg => Value::Number(-operand.as_number()),
                }
            },
            Self::Number(_, number) => Value::Number(number.parse().unwrap()),
            Self::String(_, string) => Value::String(string.clone()),
            Self::Boolean(_, boolean) => Value::Boolean(*boolean),
            Self::Identifier(_, identifier) => {
                match ctx.as_ref().borrow().values.get(&identifier.name) {
                    Some(value) => value.as_ref().clone(),
                    None => panic!("Undefined variable: {}", identifier.name),
                }
            },
            Self::Tuple(_, exprs) => {
                Value::Tuple(exprs.iter().map(|expr| expr.to_value(ctx)).collect())
            },
            Self::Function(_, function) => {
                Value::Function(function.clone(), ctx.clone())
            },
            Self::Call(_, call) => {
                let callee = call.callee.to_value(ctx);
                let val = call.argument.to_value(ctx);
                let (func, ctx) = callee.as_function();
                let mut ctx = ctx.borrow_mut().clone();
                ctx.bind_value(&func.pattern, &val);
                func.expr.to_value(&Rc::from(RefCell::from(ctx)))
            },
            Self::Block(_, vec, open) => {
                let ctx = ctx.borrow_mut().clone();
                let rc = &Rc::from(RefCell::from(ctx));
                let mut val = Value::Void();
                for stmt in vec.iter() {
                    val = stmt.to_value(rc);
                }
                if *open { val } else { Value::Void() }
            },
            Self::If(_, cond, then, else_) => {
                let cond = cond.to_value(ctx);
                if cond.as_boolean() {
                    then.to_value(ctx)
                } else if let Some(else_) = &else_ {
                    else_.to_value(ctx)
                } else {
                    Value::Void()
                }
            },
            #[allow(unreachable_patterns)]
            _ => panic!("Unsuppored evaluation: {:?}", self)
        }
    }
}

impl Evaluation for Statement {
    fn to_value(&self, ctx: &Rc<RefCell<Context>>) -> Value {
        match self {
            Self::Empty() => {},
            Self::Expression(_, expr) => {
                return expr.to_value(ctx)
            },
            Self::ValueBind(_, bind) => {
                let val = bind.expr.to_value(ctx);
                ctx.borrow_mut().bind_value(&bind.pattern, &val);
                return val
            },
            Self::TypeBind(_, _) => {},
        }
        Value::Void()
    }
}
