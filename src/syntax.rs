use std::fmt::Display;

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
pub struct Range {
    pub start: (usize, usize),
    pub end: (usize, usize),
}

impl Range {
    fn from(span: &Span) -> Range {
        Range {
            start: span.start_pos().line_col(),
            end: span.start_pos().line_col(),
        }
    }
}

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>
}

impl Program {
    pub fn parse(input: &String) -> Program {
        let pairs = Grammar
            ::parse(Rule::main, input.as_str())
            .unwrap_or_else(|e| panic!("{}", e))
            .next().unwrap().into_inner();
        let statements = pairs.map(|pair| Statement::from(pair)).collect();
        Program { statements }
    }

    pub fn print(&self) {
        println!("Program");
        let formatter = Formatter::new();
        for statement in &self.statements {
            statement.print(formatter.indent(None));
        }
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Expression(Range, Expression),
    ValueBind(Range, ValueBind),
    TypeBind(Range, TypeBind),
    Empty(),
}

impl Statement {
    fn from(pair: Pair<'_, Rule>) -> Statement {
        let range = Range::from(&pair.as_span());
        match pair.as_rule() {
            Rule::val_expr => {
                Statement::Expression(range, Expression::parse(pair.into_inner()))
            },
            Rule::stmt_valbind => {
                let mut inner = pair.into_inner();
                let pattern = Pattern::parse(inner.next().unwrap());
                let expr = Expression::parse(inner.next().unwrap().into_inner());
                Statement::ValueBind(range, ValueBind { pattern: Box::from(pattern), expr: Box::from(expr) })
            },
            Rule::stmt_tybind => {
                let mut inner = pair.into_inner();
                let ident = Identifier { name: inner.next().unwrap().as_str().to_string() };
                let expr = TypeExpr::parse(inner.next().unwrap().into_inner());
                Statement::TypeBind(range, TypeBind { ident, expr: Box::from(expr) })
            },
            Rule::EOI => Statement::Empty(),
            _ => panic!("Unexpected statement rule: {:?}", pair.as_rule()),
        }
    }
}

impl Node for Statement {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            Self::Empty() => {},
            Self::Expression(_, expr) => {
                println!("ExpressionStatement");
                expr.print(f.indent(None));
            },
            Self::ValueBind(_, bind) => {
                println!("ValueBind");
                bind.pattern.print(f.indent(Some("pattern".to_string())));
                bind.expr.print(f.indent(Some("expression".to_string())));
            },
            Self::TypeBind(_, bind) => {
                println!("TypeBind {}", bind.ident.name);
                bind.expr.print(f.indent(Some("expression".to_string())));
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct ValueBind {
    pub pattern: Box<Pattern>,
    pub expr: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct TypeBind {
    pub ident: Identifier,
    pub expr: Box<TypeExpr>,
}

#[derive(Debug, Clone)]
pub enum Pattern {
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
            _ => panic!("Unexpected pattern: {:?}", pair.as_rule()),
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identifier(_, ident, _) => write!(f, "{}", ident.name),
            Self::Tuple(_, children) => {
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
            Self::Identifier(_, ident, _) => {
                println!("Identifier ({})", ident.name);
            },
            Self::Tuple(_, exprs) => {
                println!("Tuple");
                for (i, expr) in exprs.iter().enumerate() {
                    expr.print(f.indent(Some(format!("{}", i))));
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expression {
    Binary(Range, Binary),
    Unary(Range, Unary),
    Function(Range, Function),
    Call(Range, Call),
    Number(Range, String),
    String(Range, String),
    Boolean(Range, bool),
    Identifier(Range, Identifier),
    Tuple(Range, Vec<Expression>),
    Block(Range, Vec<Statement>, bool),
    If(Range, Box<Expression>, Box<Expression>, Option<Box<Expression>>),
}

impl Expression {
    fn parse_block(pair: Pair<'_, Rule>) -> Expression {
        let range = Range::from(&pair.as_span());
        let mut inner = pair.into_inner();
        let mut vec: Vec<Statement> = inner.next().unwrap().into_inner().map(|pair| Statement::from(pair)).collect();
        if let Some(pair) = inner.next() {
            vec.push(Statement::from(pair));
            Expression::Block(range, vec, true)
        } else {
            Expression::Block(range, vec, false)
        }
    }

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
                    Rule::block => Expression::parse_block(primary),
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
                        Expression::Function(range, Function { pattern: Box::new(pattern), expr: Box::new(expression) })
                    },
                    Rule::if_ => {
                        let mut inner = primary.into_inner();
                        let cond = Expression::parse(inner.next().unwrap().into_inner());
                        let then = Expression::parse_block(inner.next().unwrap());
                        let else_ = inner.next().map(|pair| Expression::parse_block(pair));
                        Expression::If(range, Box::new(cond), Box::new(then), else_.map(Box::new))
                    }
                    _ => panic!("Unexpected expression: {:?}", primary.as_rule()),
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
}

impl Node for Expression {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            Self::Binary(_, binary) => {
                println!("BinaryExpression ({})", binary.operator);
                binary.left.print(f.indent(Some("left".to_string())));
                binary.right.print(f.indent(Some("right".to_string())));
            },
            Self::Unary(_, unary) => {
                println!("UnaryExpression ({})", unary.operator);
                unary.operand.print(f.indent(None));
            },
            Self::Number(_, number) => {
                println!("NumberLiteral ({})", number);
            },
            Self::String(_, string) => {
                println!("StringLiteral ({})", string);
            },
            Self::Boolean(_, boolean) => {
                println!("BooleanLiteral ({})", boolean);
            },
            Self::Identifier(_, identifier) => {
                println!("Identifier ({})", identifier.name);
            },
            Self::Function(_, function) => {
                println!("Function");
                function.pattern.print(f.indent(Some("pattern".to_string())));
                function.expr.print(f.indent(Some("expression".to_string())));
            },
            Self::Call(_, call) => {
                println!("FunctionCall");
                call.callee.print(f.indent(Some("callee".to_string())));
                call.argument.print(f.indent(Some("argument".to_string())));
            },
            Self::Tuple(_, exprs) => {
                println!("Tuple");
                for expr in exprs.iter() {
                    expr.print(f.indent(None));
                }
            },
            Self::Block(_, stmts, _) => {
                println!("Block");
                for stmt in stmts.iter() {
                    stmt.print(f.indent(None));
                }
            },
            Self::If(_, cond, then, else_) => {
                println!("If");
                cond.print(f.indent(Some("condition".to_string())));
                then.print(f.indent(Some("then".to_string())));
                if let Some(else_) = else_ {
                    else_.print(f.indent(Some("else".to_string())));
                }
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnaryOperator {
    Neg,
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Neg => write!(f, "-"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Unary {
    pub operator: UnaryOperator,
    pub operand: Box<Expression>,
}

impl Unary {
    fn parse(prefix: Pair<'_, Rule>, operand: Expression) -> Unary {
        Unary {
            operator: match prefix.as_rule() {
                Rule::neg => UnaryOperator::Neg,
                _ => panic!("Unexpected unary operator: {:?}", prefix.as_rule()),
            },
            operand: Box::new(operand),
        }
    }
}

#[derive(Debug, Clone)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::Pow => write!(f, "**"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Binary {
    pub operator: BinaryOperator,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
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
                _ => panic!("Unexpected binary operator: {:?}", infix.as_rule()),
            },
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Call {
    pub callee: Box<Expression>,
    pub argument: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct Identifier {
    pub name: String,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub pattern: Box<Pattern>,
    pub expr: Box<Expression>,
}

#[derive(Debug, Clone)]
pub enum TypeExpr {
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
}

impl Node for TypeExpr {
    fn print(&self, f: Formatter) {
        f.header();
        match self {
            Self::Binary(_, binary) => {
                println!("BinaryExpression ({})", binary.operator);
                binary.left.print(f.indent(Some("left".to_string())));
                binary.right.print(f.indent(Some("right".to_string())));
            },
            Self::Identifier(_, identifier) => {
                println!("Identifier ({})", identifier.name);
            },
            Self::Tuple(_, exprs) => {
                println!("Tuple");
                for (i, expr) in exprs.iter().enumerate() {
                    expr.print(f.indent(Some(format!("{}", i))));
                }
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeBinaryOperator {
    Arrow,
}

impl Display for TypeBinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Arrow => write!(f, "->"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeBinary {
    pub operator: TypeBinaryOperator,
    pub left: Box<TypeExpr>,
    pub right: Box<TypeExpr>,
}

impl TypeBinary {
    fn parse(left: TypeExpr, infix: Pair<'_, Rule>, right: TypeExpr) -> TypeBinary {
        TypeBinary {
            operator: match infix.as_rule() {
                Rule::arrow => TypeBinaryOperator::Arrow,
                _ => panic!("Unexpected type binary operator: {:?}", infix.as_rule()),
            },
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}
