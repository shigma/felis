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
                    let vec: Vec<Expression> = primary.into_inner().map(|pair| Expression::parse(pair.into_inner())).collect();
                    if vec.len() == 1 {
                        // vec[0]
                        Expression::Tuple(vec)
                    } else {
                        Expression::Tuple(vec)
                    }
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
                    callee: Rc::new(RefCell::new(lhs)),
                    argument: Rc::new(RefCell::new(Expression::parse(op.into_inner()))),
                })
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
            Expression::Call(call) => {
                println!("{:indent$}{}FunctionCall", "", prefix, indent = f.indent);
                call.callee.borrow().print(Formatter { indent: f.indent + 2, label: Some("callee".to_string()) });
                call.argument.borrow().print(Formatter { indent: f.indent + 2, label: Some("argument".to_string()) });
            },
            Expression::Tuple(exprs) => {
                println!("{:indent$}{}Tuple", "", prefix, indent = f.indent);
                for (i, expr) in exprs.iter().enumerate() {
                    expr.print(Formatter { indent: f.indent + 2, label: Some(format!("{}", i)) });
                }
            }
        }
    }
}

#[derive(Debug)]
struct Unary {
    operator: String,
    operand: Rc<RefCell<Expression>>,
}

impl Unary {
    fn parse(prefix: Pair<'_, Rule>, operand: Expression) -> Unary {
        Unary {
            operator: prefix.as_str().to_string(),
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
struct Call {
    callee: Rc<RefCell<Expression>>,
    argument: Rc<RefCell<Expression>>,
}

#[derive(Debug)]
struct Identifier {
    name: String,
}

fn main() {
    let program = Program::parse("(a - b (1, -2) (3) ** 2) / 3;");
    program.print();
}
