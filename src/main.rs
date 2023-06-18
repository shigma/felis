use std::{fs::File, io::Read};

use context::{Execution, Context};
use syntax::Program;

mod context;
mod evaluation;
mod syntax;
mod typing;

extern crate pest;
#[macro_use]
extern crate pest_derive;

fn main() {
    let mut file = File::open("examples/1.txt").unwrap();
    let mut source = String::new();
    file.read_to_string(&mut source).unwrap();
    let program = Program::parse(&source);
    program.print();
    program.execute(&Context::new());
}
