extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::{Parser, iterators::Pairs, iterators::Pair};

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct IdentParser;

fn main() {
    let pairs = IdentParser::parse(Rule::main, "a1 +(b2**3-4);").unwrap_or_else(|e| panic!("{}", e));
    print_pairs(pairs, 0);
}

fn print_pairs(pairs: Pairs<'_, Rule>, indent: usize) {
    for pair in pairs {
        print_pair(&pair, indent);
        print_pairs(pair.into_inner(), indent + 2);
    }
}

fn print_pair(pair: &Pair<'_, Rule>, indent: usize) {
    let span = pair.as_span();
    println!("{:indent$}{:?} {:?} ({:?}-{:?})", "", pair.as_rule(), span.as_str(), span.start(), span.end(), indent = indent);
}
