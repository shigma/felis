use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::rc::Rc;

use crate::evaluation::{Value, Evaluation};
use crate::syntax::*;
use crate::typing::{Type, Typing};

#[derive(Debug, Clone)]
pub struct Context {
    pub values: HashMap<String, Box<Value>>,
    pub valty: HashMap<String, Box<Type>>,
    pub types: HashMap<String, Box<Type>>,
}

impl Context {
    pub fn new() -> Rc<RefCell<Context>> {
        let mut ctx = Context { values: HashMap::new(), valty: HashMap::new(), types: HashMap::new() };
        ctx.types.insert("number".to_string(), Box::from(Type::Number()));
        ctx.types.insert("string".to_string(), Box::from(Type::String()));
        ctx.types.insert("boolean".to_string(), Box::from(Type::Boolean()));
        ctx.types.insert("top".to_string(), Box::from(Type::Top()));
        ctx.types.insert("bottom".to_string(), Box::from(Type::Bottom()));
        Rc::new(RefCell::new(ctx))
    }

    pub fn bind_value(&mut self, pattern: &Pattern, val: &Value) {
        match pattern {
            Pattern::Identifier(_, ident, _) => {
                self.values.insert(ident.name.clone(), Box::from(val.clone()));
            },
            Pattern::Tuple(_, tuple) => {
                let val = val.as_tuple(tuple.len());
                for (pattern, val) in tuple.into_iter().zip(val.into_iter()) {
                    self.bind_value(pattern, &val);
                }
            },
        }
    }

    pub fn bind_valty(&mut self, pattern: &Pattern, ty: &Type) {
        match pattern {
            Pattern::Identifier(_, ident, _) => {
                let ty2: &Type = &pattern.to_type(&Rc::new(RefCell::new(self.clone())));
                if let Type::Unknown() = ty2 {
                    self.valty.insert(ident.name.clone(), Box::from(ty.clone()));
                } else if Type::subtype(ty, ty2) {
                    self.valty.insert(ident.name.clone(), Box::from(ty2.clone()));
                } else {
                    panic!("type checking failed")
                }
            },
            Pattern::Tuple(_, tuple) => {
                let ty = ty.as_tuple(tuple.len());
                for (pattern, ty) in tuple.into_iter().zip(ty.into_iter()) {
                    self.bind_valty(pattern, &ty);
                }
            },
        }
    }

    pub fn bind_type(&mut self, ident: Identifier, ty: &Type) {
        self.types.insert(ident.name.clone(), Box::from(ty.clone()));
    }
}

pub trait Execution {
    fn execute(&self, ctx: &Rc<RefCell<Context>>) -> Value;
}

impl Execution for Program {
    fn execute(&self, ctx: &Rc<RefCell<Context>>) -> Value {
        for statement in &self.statements {
            let ty = statement.to_type(ctx);
            let val = statement.to_value(ctx);
            match statement {
                Statement::Empty() => {},
                Statement::Expression(_, _) => {
                    println!("{}: {}", val, ty);
                },
                Statement::ValueBind(_, bind) => {
                    println!("{}: {}", bind.pattern, ty);
                },
                Statement::TypeBind(_, bind) => {
                    println!("{} :: *", bind.ident.name.clone());
                },
            }
        }
        Value::Void()
    }
}
