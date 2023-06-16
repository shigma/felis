extern crate pest;
#[macro_use]
extern crate pest_derive;

use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;

use pest::{Parser, iterators::Pairs, iterators::Pair};
use pest::pratt_parser::*;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct Grammar;

struct Formatter {
    indent: usize,
    label: Option<String>,
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
                _ => {},
            }
        }
        Program { statements }
    }

    fn print(&self) {
        for statement in &self.statements {
            println!("Program");
            statement.print(2);
        }
    }
}

#[derive(Debug)]
enum Statement {
    Expression(Expression),
    // Declaration(Declaration),
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
    fn print(&self, indent: usize) {
        match self {
            Statement::Expression(expression) => {
                println!("{:indent$}ExpressionStatement", "", indent = indent);
                expression.print(Formatter { indent: indent + 2, label: None });
            },
        }
    }
}

#[derive(Debug)]
enum Expression {
    Binary(Binary),
    Unary(Unary),
    // Call(Call),
    Number(String),
    String(String),
    Boolean(bool),
    Identifier(Identifier),
}

impl Expression {
    fn parse(pairs: Pairs<'_, Rule>) -> Expression {
        PrattParser::new()
            .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
            .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
            .op(Op::infix(Rule::pow, Assoc::Right))
            .op(Op::prefix(Rule::neg))
            .map_primary(|atom| match atom.as_rule() {
                Rule::number => Expression::Number(atom.as_str().to_string()),
                Rule::string => Expression::String(atom.as_str().to_string()),
                Rule::tru => Expression::Boolean(true),
                Rule::fls => Expression::Boolean(false),
                Rule::ident => Expression::Identifier(Identifier { name: atom.as_str().to_string() }),
                Rule::unary => Expression::Unary(Unary::parse(atom)),
                Rule::expr => Expression::parse(atom.into_inner()),
                _ => panic!("Unexpected rule: {:?}", atom.as_rule()),
            })
            .map_infix(|left, infix, right| {
                Expression::Binary(Binary::parse(left, infix, right))
            })
            .parse(pairs)
    }

    fn print(&self, f: Formatter) {
        let prefix = match f.label {
            Some(label) => format!("{}: ", label),
            None => "".to_string(),
        };
        match self {
            Expression::Binary(binary) => {
                println!("{:indent$}{}BinaryExpression ({})", "", prefix, binary.operator, indent = f.indent);
                binary.left.borrow().print(Formatter { indent: f.indent + 2, label: Some("left".to_string()) });
                binary.right.borrow().print(Formatter { indent: f.indent + 2, label: Some("right".to_string()) });
            },
            Expression::Unary(unary) => {
                println!("{:indent$}{}UnaryExpression ({})", "", prefix, unary.operator, indent = f.indent);
                unary.operand.borrow().print(Formatter { indent: f.indent + 2, label: None });
            },
            Expression::Number(number) => {
                println!("{:indent$}{}NumberLiteral ({})", "", prefix, number, indent = f.indent);
            },
            Expression::String(string) => {
                println!("{:indent$}{}StringLiteral ({})", "", prefix, string, indent = f.indent);
            },
            Expression::Boolean(boolean) => {
                println!("{:indent$}{}BooleanLiteral ({})", "", prefix, boolean, indent = f.indent);
            },
            Expression::Identifier(identifier) => {
                println!("{:indent$}{}Identifier ({})", "", prefix, identifier.name, indent = f.indent);
            },
        }
    }
}

#[derive(Debug)]
struct Unary {
    operator: String,
    operand: Rc<RefCell<Expression>>,
}

impl Unary {
    fn parse(atom: Pair<'_, Rule>) -> Unary {
        let mut pairs = atom.into_inner();
        let operator = pairs.next().unwrap().as_str().to_string();
        let operand = Expression::parse(pairs.next().unwrap().into_inner());
        Unary {
            operator,
            operand: Rc::new(RefCell::new(operand)),
        }
    }
}

#[derive(Debug)]
struct Binary {
    operator: String,
    left: Rc<RefCell<Expression>>,
    right: Rc<RefCell<Expression>>,
}

impl Binary {
    fn parse(left: Expression, infix: Pair<'_, Rule>, right: Expression) -> Binary {
        Binary {
            operator: infix.as_str().to_string(),
            left: Rc::new(RefCell::new(left)),
            right: Rc::new(RefCell::new(right)),
        }
    }
}

#[derive(Debug)]
struct Identifier {
    name: String,
}

fn main() {
    let program = Program::parse("(a - b ** 2) / 3;");
    program.print();
}
