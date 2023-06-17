extern crate pest;
#[macro_use]
extern crate pest_derive;

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::fs::File;
use std::io::Read;
use std::rc::Rc;

use pest::{Parser, iterators::Pairs, iterators::Pair};
use pest::{pratt_parser::*, Span};

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct Grammar;

struct Formatter {
    indent: usize,
    label: Option<String>,
}

trait Node {
    fn print(&self, f: Formatter);
}

impl Formatter {
    fn new() -> Formatter {
        Formatter { indent: 0, label: None }
    }

    fn header(&self) {
        let prefix = match self.label {
            Some(ref label) => format!("{}: ", label),
            None => "".to_string(),
        };
        print!("{:indent$}{}", "", prefix, indent = self.indent);
    }

    fn indent(&self, label: Option<String>) -> Formatter {
        Formatter { indent: self.indent + 2, label }
    }
}

#[derive(Debug, Clone)]
struct Range {
    start: (usize, usize),
    end: (usize, usize),
}

impl Range {
    fn from(span: &Span) -> Range {
        Range {
            start: span.start_pos().line_col(),
            end: span.start_pos().line_col(),
        }
    }
}

#[derive(Debug, Clone)]
struct Context {
    values: HashMap<String, Box<(Value, Type)>>,
    types: HashMap<String, Box<Type>>,
}

impl Context {
    fn new() -> Context {
        let mut ctx = Context { values: HashMap::new(), types: HashMap::new() };
        ctx.types.insert("number".to_string(), Box::from(Type::Number()));
        ctx.types.insert("string".to_string(), Box::from(Type::String()));
        ctx.types.insert("boolean".to_string(), Box::from(Type::Boolean()));
        ctx.types.insert("top".to_string(), Box::from(Type::Top()));
        ctx.types.insert("bottom".to_string(), Box::from(Type::Bottom()));
        ctx
    }

    fn bind(&mut self, pattern: &Pattern, val: &Value, ty: &Type) {
        match pattern {
            Pattern::Identifier(_, ident, _) => {
                let ty2 = &pattern.to_type(&Rc::new(RefCell::new(self.clone())));
                if Type::subtype(ty, ty2) {
                    self.values.insert(ident.name.clone(), Box::from((val.clone(), match ty2 {
                        Type::Unknown() => ty.clone(),
                        _ => ty2.clone(),
                    })));
                } else {
                    panic!("type checking failed")
                }
            },
            Pattern::Tuple(_, tuple) => {
                let val = val.as_tuple(tuple.len());
                let ty = ty.as_tuple(tuple.len());
                for (pattern, (val, ty)) in tuple.into_iter().zip(val.into_iter().zip(ty.into_iter())) {
                    self.bind(pattern, &val, &ty);
                }
            },
        }
    }

    fn alias(&mut self, ident: Identifier, ty: &Type) {
        self.types.insert(ident.name.clone(), Box::from(ty.clone()));
    }
}

#[derive(Debug)]
struct Program {
    statements: Vec<Statement>
}

impl Program {
    fn parse(input: &String) -> Program {
        let pairs = Grammar::parse(Rule::main, input.as_str())
            .unwrap_or_else(|e| panic!("{}", e));
        let mut statements = Vec::new();
        for pair in pairs {
            let range = Range::from(&pair.as_span());
            match pair.as_rule() {
                Rule::stmt_expr => {
                    let pair = pair.into_inner().next().unwrap();
                    statements.push(Statement::Expression(range, Expression::parse(pair.into_inner())));
                },
                Rule::stmt_valbind => {
                    let mut inner = pair.into_inner();
                    let pattern = Pattern::parse(inner.next().unwrap());
                    let expr = Expression::parse(inner.next().unwrap().into_inner());
                    statements.push(Statement::ValueBind(range, ValueBind { pattern: Box::from(pattern), expr: Box::from(expr) }));
                },
                Rule::stmt_tybind => {
                    let mut inner = pair.into_inner();
                    let ident = Identifier { name: inner.next().unwrap().as_str().to_string() };
                    let expr = TypeExpr::parse(inner.next().unwrap().into_inner());
                    statements.push(Statement::TypeBind(range, TypeBind { ident, expr: Box::from(expr) }));
                },
                Rule::EOI => {},
                _ => panic!("Unexpected statement rule: {:?}", pair.as_rule()),
            }
        }
        Program { statements }
    }

    fn print(&self) {
        println!("Program");
        let formatter = Formatter::new();
        for statement in &self.statements {
            statement.print(formatter.indent(None));
        }
    }

    fn execute(&self) {
        let ctx = Rc::from(RefCell::from(Context::new()));
        for statement in &self.statements {
            statement.execute(&ctx);
        }
    }
}

#[derive(Debug, Clone)]
enum Statement {
    Expression(Range, Expression),
    ValueBind(Range, ValueBind),
    TypeBind(Range, TypeBind),
}

impl Statement {
    fn execute(&self, ctx: &Rc<RefCell<Context>>) {
        match self {
            Statement::Expression(_, expr) => {
                let ty = expr.to_type(ctx);
                let val = expr.to_value(ctx);
                println!("{}: {}", val, ty);
            },
            Statement::ValueBind(_, bind) => {
                let ty = bind.expr.to_type(ctx);
                let val = bind.expr.to_value(ctx);
                ctx.borrow_mut().bind(&bind.pattern, &val, &ty);
                println!("{}: {}", bind.pattern, ty);
            },
            Statement::TypeBind(_, bind) => {
                let ident = bind.ident.clone();
                let ty = bind.expr.to_type(ctx);
                ctx.borrow_mut().alias(ident, &ty);
                println!("{}:: *", ty);
            },
        }
    }
}

impl Node for Statement {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            Statement::Expression(_, expr) => {
                println!("ExpressionStatement");
                expr.print(f.indent(None));
            },
            Statement::ValueBind(_, bind) => {
                println!("ValueBind");
                bind.pattern.print(f.indent(Some("pattern".to_string())));
                bind.expr.print(f.indent(Some("expression".to_string())));
            },
            Statement::TypeBind(_, bind) => {
                println!("TypeBind {}", bind.ident.name);
                bind.expr.print(f.indent(Some("expression".to_string())));
            },
        }
    }
}

#[derive(Debug, Clone)]
struct ValueBind {
    pattern: Box<Pattern>,
    expr: Box<Expression>,
}

#[derive(Debug, Clone)]
struct TypeBind {
    ident: Identifier,
    expr: Box<TypeExpr>,
}

#[derive(Debug, Clone)]
enum Pattern {
    Identifier(Range, Identifier, Option<TypeExpr>),
    Tuple(Range, Vec<Pattern>),
}

impl Pattern {
    fn parse(pair: Pair<'_, Rule>) -> Pattern {
        let range = Range::from(&pair.as_span());
        match pair.as_rule() {
            Rule::patt_ident => {
                let mut pairs = pair.into_inner();
                let ident = Identifier { name: pairs.next().unwrap().as_str().to_string() };
                let ty = pairs.next().map(|pair| TypeExpr::parse(pair.into_inner()));
                Pattern::Identifier(range, ident, ty)
            },
            Rule::patt_tuple => {
                let mut vec: Vec<Pattern> = pair.into_inner().map(|pair| Pattern::parse(pair)).collect();
                if vec.len() == 1 {
                    vec.swap_remove(0)
                } else {
                    Pattern::Tuple(range, vec)
                }
            },
            _ => panic!("Unexpected rule: {:?}", pair.as_rule()),
        }
    }

    fn to_type(&self, ctx: &Rc<RefCell<Context>>) -> Type {
        match self {
            Pattern::Identifier(_, _, oty) => {
                oty.clone().map_or(Type::Unknown(), |ty| ty.to_type(ctx))
            },
            Pattern::Tuple(_, children) => {
                Type::Tuple(children.iter().map(|child| child.to_type(ctx)).collect())
            }
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Identifier(_, ident, _) => write!(f, "{}", ident.name),
            Pattern::Tuple(_, children) => {
                write!(f, "(")?;
                for (i, child) in children.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", child)?;
                }
                write!(f, ")")
            },
        }
    }
}

impl Node for Pattern {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            Pattern::Identifier(_, ident, _) => {
                println!("Identifier ({})", ident.name);
            },
            Pattern::Tuple(_, exprs) => {
                println!("Tuple");
                for (i, expr) in exprs.iter().enumerate() {
                    expr.print(f.indent(Some(format!("{}", i))));
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
enum Value {
    Unknown(),
    Number(f64),
    String(String),
    Boolean(bool),
    Tuple(Vec<Value>),
    Function(Function, Rc<RefCell<Context>>),
}

impl Value {
    fn as_number(&self) -> f64 {
        match self {
            Value::Number(number) => *number,
            _ => panic!("Expected number"),
        }
    }

    fn as_function(&self) -> (&Function, &Rc<RefCell<Context>>) {
        match self {
            Value::Function(function, ctx) => (function, ctx),
            _ => panic!("Expected function"),
        }
    }

    fn as_tuple(&self, length: usize) -> Vec<Value> {
        match self {
            Value::Tuple(vec) => {
                if vec.len() != length {
                    panic!("Expected value")
                }
                vec.clone()
            },
            Value::Unknown() => {
                let mut vec = Vec::new();
                for _ in 0..length {
                    vec.push(Value::Unknown());
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
            Value::Unknown() => write!(f, "<unbound>"),
            Value::Number(number) => write!(f, "{}", number),
            Value::String(string) => write!(f, "{}", string),
            Value::Boolean(bool) => write!(f, "{}", bool),
            Value::Tuple(values) => {
                write!(f, "(")?;
                for (i, value) in values.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", value)?;
                }
                write!(f, ")")
            },
            Value::Function(_, _) => write!(f, "<function>"),
        }
    }
}

#[derive(Debug, Clone)]
enum Expression {
    Binary(Range, Binary),
    Unary(Range, Unary),
    Function(Range, Function),
    Call(Range, Call),
    Number(Range, String),
    String(Range, String),
    Boolean(Range, bool),
    Identifier(Range, Identifier),
    Tuple(Range, Vec<Expression>),
}

impl Expression {
    fn parse(pairs: Pairs<'_, Rule>) -> Expression {
        PrattParser::new()
            .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
            .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
            .op(Op::infix(Rule::pow, Assoc::Right))
            .op(Op::prefix(Rule::neg))
            .op(Op::postfix(Rule::call))
            .map_primary(|primary| {
                let range = Range::from(&primary.as_span());
                match primary.as_rule() {
                    Rule::number => Expression::Number(range, primary.as_str().to_string()),
                    Rule::string => Expression::String(range, primary.as_str().to_string()),
                    Rule::tru => Expression::Boolean(range, true),
                    Rule::fls => Expression::Boolean(range, false),
                    Rule::ident => Expression::Identifier(range, Identifier { name: primary.as_str().to_string() }),
                    Rule::val_tuple => {
                        let mut vec: Vec<Expression> = primary.into_inner().map(|pair| Expression::parse(pair.into_inner())).collect();
                        if vec.len() == 1 {
                            vec.swap_remove(0)
                        } else {
                            Expression::Tuple(range, vec)
                        }
                    },
                    Rule::func => {
                        let mut inner = primary.into_inner();
                        let pattern = Pattern::parse(inner.next().unwrap());
                        let expression = Expression::parse(inner.next().unwrap().into_inner());
                        Expression::Function(range, Function { pattern: Box::new(pattern), expression: Box::new(expression) })
                    },
                    _ => panic!("Unexpected rule: {:?}", primary.as_rule()),
                }
            })
            .map_infix(|lhs, op, rhs| {
                Expression::Binary(Range::from(&op.as_span()), Binary::parse(lhs, op, rhs))
            })
            .map_prefix(|op, rhs| {
                Expression::Unary(Range::from(&op.as_span()), Unary::parse(op, rhs))
            })
            .map_postfix(|lhs, op| {
                Expression::Call(Range::from(&op.as_span()), Call {
                    callee: Box::new(lhs),
                    argument: Box::new(Expression::parse(op.into_inner())),
                })
            })
            .parse(pairs)
    }

    fn to_value(&self, ctx: &Rc<RefCell<Context>>) -> Value {
        match self {
            Expression::Binary(_, binary) => {
                let left = binary.left.to_value(ctx);
                let right = binary.right.to_value(ctx);
                match binary.operator {
                    BinaryOperator::Add => Value::Number(left.as_number() + right.as_number()),
                    BinaryOperator::Sub => Value::Number(left.as_number() - right.as_number()),
                    BinaryOperator::Mul => Value::Number(left.as_number() * right.as_number()),
                    BinaryOperator::Div => Value::Number(left.as_number() / right.as_number()),
                    BinaryOperator::Pow => Value::Number(left.as_number().powf(right.as_number())),
                }
            },
            Expression::Unary(_, unary) => {
                let operand = unary.operand.to_value(ctx).as_number();
                match unary.operator {
                    UnaryOperator::Neg => Value::Number(-operand),
                }
            },
            Expression::Number(_, number) => Value::Number(number.parse().unwrap()),
            Expression::String(_, string) => Value::String(string.clone()),
            Expression::Boolean(_, boolean) => Value::Boolean(*boolean),
            Expression::Identifier(_, identifier) => {
                match ctx.as_ref().borrow().values.get(&identifier.name) {
                    Some(value) => value.as_ref().0.clone(),
                    None => panic!("Undefined variable: {}", identifier.name),
                }
            },
            Expression::Tuple(_, exprs) => {
                Value::Tuple(exprs.iter().map(|expr| expr.to_value(ctx)).collect())
            },
            Expression::Function(_, function) => {
                Value::Function(function.clone(), ctx.clone())
            },
            Expression::Call(_, call) => {
                let callee = call.callee.to_value(ctx);
                let ty = call.argument.to_type(ctx);
                let val = call.argument.to_value(ctx);
                let (func, ctx) = callee.as_function();
                let mut ctx = ctx.borrow_mut().clone();
                ctx.bind(&func.pattern, &val, &ty);
                func.expression.to_value(&Rc::from(RefCell::from(ctx)))
            },
            _ => panic!("Unsuppored evaluation: {:?}", self)
        }
    }

    fn to_type(&self, ctx: &Rc<RefCell<Context>>) -> Type {
        match self {
            Expression::Unary(_, unary) => {
                let operand = unary.operand.to_type(ctx);
                match unary.operator {
                    UnaryOperator::Neg => {
                        operand.as_number();
                        Type::Number()
                    },
                }
            },
            Expression::Binary(_, binary) => {
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
            Expression::Number(_, _) => Type::Number(),
            Expression::String(_, _) => Type::String(),
            Expression::Boolean(_, _) => Type::Boolean(),
            Expression::Identifier(_, identifier) => {
                match ctx.as_ref().borrow().values.get(&identifier.name) {
                    Some(value) => value.as_ref().1.clone(),
                    None => panic!("Undefined variable: {}", identifier.name),
                }
            },
            Expression::Tuple(_, exprs) => {
                Type::Tuple(exprs.iter().map(|expr| expr.to_type(ctx)).collect())
            },
            Expression::Function(_, func) => {
                let ty = func.pattern.to_type(ctx);
                let mut ctx = ctx.borrow_mut().clone();
                ctx.bind(&func.pattern, &Value::Unknown(), &Type::Bottom());
                Type::Arrow(Box::from(ty), Box::from(func.expression.to_type(&Rc::from(RefCell::from(ctx)))))
            },
            Expression::Call(_, call) => {
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

impl Node for Expression {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            Expression::Binary(_, binary) => {
                println!("BinaryExpression ({})", binary.operator);
                binary.left.print(f.indent(Some("left".to_string())));
                binary.right.print(f.indent(Some("right".to_string())));
            },
            Expression::Unary(_, unary) => {
                println!("UnaryExpression ({})", unary.operator);
                unary.operand.print(f.indent(None));
            },
            Expression::Number(_, number) => {
                println!("NumberLiteral ({})", number);
            },
            Expression::String(_, string) => {
                println!("StringLiteral ({})", string);
            },
            Expression::Boolean(_, boolean) => {
                println!("BooleanLiteral ({})", boolean);
            },
            Expression::Identifier(_, identifier) => {
                println!("Identifier ({})", identifier.name);
            },
            Expression::Function(_, function) => {
                println!("Function");
                function.pattern.print(f.indent(Some("pattern".to_string())));
                function.expression.print(f.indent(Some("expression".to_string())));
            },
            Expression::Call(_, call) => {
                println!("FunctionCall");
                call.callee.print(f.indent(Some("callee".to_string())));
                call.argument.print(f.indent(Some("argument".to_string())));
            },
            Expression::Tuple(_, exprs) => {
                println!("Tuple");
                for (i, expr) in exprs.iter().enumerate() {
                    expr.print(f.indent(Some(format!("{}", i))));
                }
            },
        }
    }
}

#[derive(Debug, Clone)]
enum UnaryOperator {
    Neg,
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Neg => write!(f, "-"),
        }
    }
}

#[derive(Debug, Clone)]
struct Unary {
    operator: UnaryOperator,
    operand: Box<Expression>,
}

impl Unary {
    fn parse(prefix: Pair<'_, Rule>, operand: Expression) -> Unary {
        Unary {
            operator: match prefix.as_rule() {
                Rule::neg => UnaryOperator::Neg,
                _ => panic!("Unexpected rule: {:?}", prefix.as_rule()),
            },
            operand: Box::new(operand),
        }
    }
}

#[derive(Debug, Clone)]
enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Sub => write!(f, "-"),
            BinaryOperator::Mul => write!(f, "*"),
            BinaryOperator::Div => write!(f, "/"),
            BinaryOperator::Pow => write!(f, "**"),
        }
    }
}

#[derive(Debug, Clone)]
struct Binary {
    operator: BinaryOperator,
    left: Box<Expression>,
    right: Box<Expression>,
}

impl Binary {
    fn parse(left: Expression, infix: Pair<'_, Rule>, right: Expression) -> Binary {
        Binary {
            operator: match infix.as_rule() {
                Rule::add => BinaryOperator::Add,
                Rule::sub => BinaryOperator::Sub,
                Rule::mul => BinaryOperator::Mul,
                Rule::div => BinaryOperator::Div,
                Rule::pow => BinaryOperator::Pow,
                _ => panic!("Unexpected rule: {:?}", infix.as_rule()),
            },
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

#[derive(Debug, Clone)]
struct Call {
    callee: Box<Expression>,
    argument: Box<Expression>,
}

#[derive(Debug, Clone)]
struct Identifier {
    name: String,
}

#[derive(Debug, Clone)]
struct Function {
    pattern: Box<Pattern>,
    expression: Box<Expression>,
}

#[derive(Debug, Clone)]
enum Type {
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
    fn as_number(&self) {
        match self {
            Type::Number() => {},
            _ => panic!("Expected number, received {}", self),
        }
    }

    fn as_function(&self) -> (&Type, &Type) {
        match self {
            Type::Arrow(ty1, ty2) => (ty1, ty2),
            _ => panic!("Expected function, received {}", self),
        }
    }

    fn as_tuple(&self, length: usize) -> Vec<Type> {
        match self {
            Type::Tuple(vec) => {
                if vec.len() != length {
                    panic!("Expected tuple with length {}, received {}", length, self)
                }
                vec.clone()
            },
            Type::Bottom() => {
                let mut vec = Vec::new();
                for _ in 0..length {
                    vec.push(Type::Bottom());
                }
                vec
            },
            _ => panic!("Expected tuple, received {}", self),
        }
    }

    fn subtype(ty1: &Type, ty2: &Type) -> bool {
        match (ty1, ty2) {
            (_, Type::Unknown()) => true,
            (_, Type::Top()) => true,
            (Type::Bottom(), _) => true,
            (Type::Number(), Type::Number()) => true,
            (Type::String(), Type::String()) => true,
            (Type::Boolean(), Type::Boolean()) => true,
            (Type::Tuple(vec1), Type::Tuple(vec2)) => {
                if vec1.len() != vec2.len() {
                    false
                } else {
                    vec1.iter().zip(vec2.iter()).all(|(ty1, ty2)| Type::subtype(ty1, ty2))
                }
            },
            (Type::Arrow(ty11, ty12), Type::Arrow(ty21, ty22)) => {
                Type::subtype(&ty21, &ty11) && Type::subtype(&ty12, &ty22)
            },
            _ => false,
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unknown() => write!(f, "unknown"),
            Type::Top() => write!(f, "top"),
            Type::Bottom() => write!(f, "bottom"),
            Type::Number() => write!(f, "number"),
            Type::String() => write!(f, "string"),
            Type::Boolean() => write!(f, "boolean"),
            Type::Tuple(children) => {
                write!(f, "(")?;
                for (i, child) in children.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", child)?;
                }
                write!(f, ")")
            },
            Type::Arrow(left, right) => write!(f, "{} -> {}", left, right),
        }
    }
}

#[derive(Debug, Clone)]
enum TypeExpr {
    Binary(Range, TypeBinary),
    Identifier(Range, Identifier),
    Tuple(Range, Vec<TypeExpr>),
}

impl TypeExpr {
    fn parse(pairs: Pairs<'_, Rule>) -> TypeExpr {
        PrattParser::new()
            .op(Op::infix(Rule::arrow, Assoc::Right))
            // .op(Op::prefix(Rule::neg))
            // .op(Op::postfix(Rule::call))
            .map_primary(|primary| {
                let range = Range::from(&primary.as_span());
                match primary.as_rule() {
                    Rule::ident => TypeExpr::Identifier(range, Identifier { name: primary.as_str().to_string() }),
                    Rule::type_tuple => {
                        let mut vec: Vec<TypeExpr> = primary.into_inner().map(|pair| TypeExpr::parse(pair.into_inner())).collect();
                        if vec.len() == 1 {
                            vec.swap_remove(0)
                        } else {
                            TypeExpr::Tuple(range, vec)
                        }
                    },
                    _ => panic!("Unexpected type rule: {:?}", primary.as_rule()),
                }
            })
            .map_infix(|lhs, op, rhs| {
                TypeExpr::Binary(Range::from(&op.as_span()), TypeBinary::parse(lhs, op, rhs))
            })
            .parse(pairs)
    }

    fn to_type(&self, ctx: &Rc<RefCell<Context>>) -> Type {
        match self {
            TypeExpr::Binary(_, binary) => {
                let left = binary.left.to_type(ctx);
                let right = binary.right.to_type(ctx);
                match binary.operator {
                    TypeBinaryOperator::Arrow => Type::Arrow(Box::from(left), Box::from(right)),
                }
            },
            TypeExpr::Identifier(_, identifier) => {
                match ctx.as_ref().borrow().types.get(&identifier.name) {
                    Some(value) => value.as_ref().clone(),
                    None => panic!("Undefined variable: {}", identifier.name),
                }
            },
            TypeExpr::Tuple(_, exprs) => {
                Type::Tuple(exprs.iter().map(|expr| expr.to_type(ctx)).collect())
            },
            _ => panic!("Unsuppored evaluation: {:?}", self)
        }
    }
}

impl Node for TypeExpr {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            TypeExpr::Binary(_, binary) => {
                println!("BinaryExpression ({})", binary.operator);
                binary.left.print(f.indent(Some("left".to_string())));
                binary.right.print(f.indent(Some("right".to_string())));
            },
            TypeExpr::Identifier(_, identifier) => {
                println!("Identifier ({})", identifier.name);
            },
            TypeExpr::Tuple(_, exprs) => {
                println!("Tuple");
                for (i, expr) in exprs.iter().enumerate() {
                    expr.print(f.indent(Some(format!("{}", i))));
                }
            },
        }
    }
}

#[derive(Debug, Clone)]
enum TypeBinaryOperator {
    Arrow,
}

impl Display for TypeBinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeBinaryOperator::Arrow => write!(f, "->"),
        }
    }
}

#[derive(Debug, Clone)]
struct TypeBinary {
    operator: TypeBinaryOperator,
    left: Box<TypeExpr>,
    right: Box<TypeExpr>,
}

impl TypeBinary {
    fn parse(left: TypeExpr, infix: Pair<'_, Rule>, right: TypeExpr) -> TypeBinary {
        TypeBinary {
            operator: match infix.as_rule() {
                Rule::arrow => TypeBinaryOperator::Arrow,
                _ => panic!("Unexpected rule: {:?}", infix.as_rule()),
            },
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

fn main() {
    let mut file = File::open("examples/1.txt").unwrap();
    let mut source = String::new();
    file.read_to_string(&mut source).unwrap();
    let program = Program::parse(&source);
    program.print();
    program.execute();
}
