extern crate pest;
#[macro_use]
extern crate pest_derive;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::Debug;

use pest::{Parser, iterators::Pairs, iterators::Pair};
use pest::pratt_parser::*;

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

struct Context {
    values: HashMap<String, Box<Value>>,
}

impl Context {
    fn new() -> Context {
        Context { values: HashMap::new() }
    }
}

#[derive(Debug)]
struct Program {
    statements: Vec<Statement>
}

impl Program {
    fn parse(input: &str) -> Program {
        let pairs = Grammar::parse(Rule::main, input)
            .unwrap_or_else(|e| panic!("{}", e));
        let mut statements = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::stmt_expr => {
                    let inner = pair.into_inner().next().unwrap();
                    statements.push(Statement::Expression(Expression::parse(inner.into_inner())));
                },
                Rule::stmt_valbind => {
                    let mut inner = pair.into_inner();
                    let pattern = Pattern::parse(inner.next().unwrap());
                    let _ = inner.next().unwrap();
                    let expression = Expression::parse(inner.next().unwrap().into_inner());
                    statements.push(Statement::ValueBind(ValueBind { pattern: Box::from(pattern), expression: Box::from(expression) }));
                },
                _ => {},
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

    fn eval(&self) {
        let mut ctx = Context::new();
        for statement in &self.statements {
            statement.eval(&mut ctx);
        }
    }
}

#[derive(Debug)]
enum Statement {
    Expression(Expression),
    ValueBind(ValueBind),
    // Assignment(Assignment),
    // If(If),
    // While(While),
    // For(For),
    // Return(Return),
    // Break(Break),
    // Continue(Continue),
    // Block(Block)
}

impl Statement {
    fn eval(&self, ctx: &mut Context) {
        match self {
            Statement::Expression(expr) => {
                expr.eval(ctx);
            },
            Statement::ValueBind(bind) => {
                if let Pattern::Identifier(identifier) = bind.pattern.borrow() {
                    ctx.values.insert(identifier.name.clone(), Box::from(bind.expression.eval(ctx)));
                } else {
                    panic!("Unsupported pattern: {:?}", bind.pattern);
                }
            },
            _ => panic!("Unsuppored statement: {:?}", self)
        }
    }
}

impl Node for Statement {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            Statement::Expression(expr) => {
                println!("ExpressionStatement");
                expr.print(f.indent(None));
            },
            Statement::ValueBind(bind) => {
                println!("ValueBind");
                bind.pattern.print(f.indent(Some("pattern".to_string())));
                bind.expression.print(f.indent(Some("expression".to_string())));
            },
        }
    }
}

#[derive(Debug)]
struct ValueBind {
    pattern: Box<Pattern>,
    expression: Box<Expression>,
}

#[derive(Debug, Clone)]
enum Pattern {
    Identifier(Identifier),
    Tuple(Vec<Pattern>),
}

impl Pattern {
    fn parse(pair: Pair<'_, Rule>) -> Pattern {
        match pair.as_rule() {
            Rule::ident => Pattern::Identifier(Identifier { name: pair.as_str().to_string() }),
            Rule::patt_tuple => {
                let mut vec: Vec<Pattern> = pair.into_inner().map(|pair| Pattern::parse(pair)).collect();
                if vec.len() == 1 {
                    vec.swap_remove(0)
                } else {
                    Pattern::Tuple(vec)
                }
            },
            _ => panic!("Unexpected rule: {:?}", pair.as_rule()),
        }
    }
}

impl Node for Pattern {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            Pattern::Identifier(identifier) => {
                println!("Identifier ({})", identifier.name);
            },
            Pattern::Tuple(exprs) => {
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
    Number(f64),
    String(String),
    Boolean(bool),
    Tuple(Vec<Value>),
    Function(Function),
}

impl Value {
    fn as_number(&self) -> f64 {
        match self {
            Value::Number(number) => *number,
            _ => panic!("Expected number"),
        }
    }

    fn as_function(&self) -> &Function {
        match self {
            Value::Function(function) => function,
            _ => panic!("Expected function"),
        }
    }
}

#[derive(Debug, Clone)]
enum Expression {
    Binary(Binary),
    Unary(Unary),
    Function(Function),
    Call(Call),
    Number(String),
    String(String),
    Boolean(bool),
    Identifier(Identifier),
    Tuple(Vec<Expression>),
}

impl Expression {
    fn parse(pairs: Pairs<'_, Rule>) -> Expression {
        PrattParser::new()
            .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
            .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
            .op(Op::infix(Rule::pow, Assoc::Right))
            .op(Op::prefix(Rule::neg))
            .op(Op::postfix(Rule::call))
            .map_primary(|primary| match primary.as_rule() {
                Rule::number => Expression::Number(primary.as_str().to_string()),
                Rule::string => Expression::String(primary.as_str().to_string()),
                Rule::tru => Expression::Boolean(true),
                Rule::fls => Expression::Boolean(false),
                Rule::ident => Expression::Identifier(Identifier { name: primary.as_str().to_string() }),
                Rule::tuple => {
                    let mut vec: Vec<Expression> = primary.into_inner().map(|pair| Expression::parse(pair.into_inner())).collect();
                    if vec.len() == 1 {
                        vec.swap_remove(0)
                    } else {
                        Expression::Tuple(vec)
                    }
                },
                Rule::func => {
                    let mut inner = primary.into_inner();
                    let pattern = Pattern::parse(inner.next().unwrap());
                    let expression = Expression::parse(inner.next().unwrap().into_inner());
                    Expression::Function(Function { pattern: Box::new(pattern), expression: Box::new(expression) })
                },
                _ => panic!("Unexpected rule: {:?}", primary.as_rule()),
            })
            .map_infix(|lhs, op, rhs| {
                Expression::Binary(Binary::parse(lhs, op, rhs))
            })
            .map_prefix(|op, rhs| {
                Expression::Unary(Unary::parse(op, rhs))
            })
            .map_postfix(|lhs, op| {
                Expression::Call(Call {
                    callee: Box::new(lhs),
                    argument: Box::new(Expression::parse(op.into_inner())),
                })
            })
            .parse(pairs)
    }

    fn eval(&self, ctx: &Context) -> Value {
        match self {
            Expression::Binary(binary) => {
                let left = binary.left.eval(ctx).as_number();
                let right = binary.right.eval(ctx).as_number();
                match binary.operator.as_str() {
                    "+" => Value::Number(left + right),
                    "-" => Value::Number(left - right),
                    "*" => Value::Number(left * right),
                    "/" => Value::Number(left / right),
                    "**" => Value::Number(left.powf(right)),
                    _ => panic!("Unexpected operator: {}", binary.operator),
                }
            },
            Expression::Unary(unary) => {
                let operand = unary.operand.eval(ctx).as_number();
                match unary.operator.as_str() {
                    "-" => Value::Number(-operand),
                    _ => panic!("Unexpected operator: {}", unary.operator),
                }
            },
            Expression::Number(number) => Value::Number(number.parse().unwrap()),
            Expression::String(string) => Value::String(string.clone()),
            Expression::Boolean(boolean) => Value::Boolean(*boolean),
            Expression::Identifier(identifier) => {
                match ctx.values.get(&identifier.name) {
                    Some(value) => value.as_ref().clone(),
                    None => panic!("Undefined variable: {}", identifier.name),
                }
            },
            _ => panic!("Unsuppored evaluation: {:?}", self)
        }
    }
}

impl Node for Expression {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            Expression::Binary(binary) => {
                println!("BinaryExpression ({})", binary.operator);
                binary.left.print(f.indent(Some("left".to_string())));
                binary.right.print(f.indent(Some("right".to_string())));
            },
            Expression::Unary(unary) => {
                println!("UnaryExpression ({})", unary.operator);
                unary.operand.print(f.indent(None));
            },
            Expression::Number(number) => {
                println!("NumberLiteral ({})", number);
            },
            Expression::String(string) => {
                println!("StringLiteral ({})", string);
            },
            Expression::Boolean(boolean) => {
                println!("BooleanLiteral ({})", boolean);
            },
            Expression::Identifier(identifier) => {
                println!("Identifier ({})", identifier.name);
            },
            Expression::Function(function) => {
                println!("Function");
                function.pattern.print(f.indent(Some("pattern".to_string())));
                function.expression.print(f.indent(Some("expression".to_string())));
            },
            Expression::Call(call) => {
                println!("FunctionCall");
                call.callee.print(f.indent(Some("callee".to_string())));
                call.argument.print(f.indent(Some("argument".to_string())));
            },
            Expression::Tuple(exprs) => {
                println!("Tuple");
                for (i, expr) in exprs.iter().enumerate() {
                    expr.print(f.indent(Some(format!("{}", i))));
                }
            },
        }
    }
}

#[derive(Debug, Clone)]
struct Unary {
    operator: String,
    operand: Box<Expression>,
}

impl Unary {
    fn parse(prefix: Pair<'_, Rule>, operand: Expression) -> Unary {
        Unary {
            operator: prefix.as_str().to_string(),
            operand: Box::new(operand),
        }
    }
}

#[derive(Debug, Clone)]
struct Binary {
    operator: String,
    left: Box<Expression>,
    right: Box<Expression>,
}

impl Binary {
    fn parse(left: Expression, infix: Pair<'_, Rule>, right: Expression) -> Binary {
        Binary {
            operator: infix.as_str().to_string(),
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

fn main() {
    let program = Program::parse("
        let a = 10;
        let b = fn (x, y) -> fn (z) -> x + y + z;
        (a - b (1, -2) (3) ** 2) / 3;
    ");
    program.print();
    program.eval();
}
