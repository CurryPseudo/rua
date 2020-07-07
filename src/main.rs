#[macro_use]
extern crate log;
#[macro_use]
extern crate lazy_static;
mod builtin_functions;
pub use builtin_functions::*;
mod vm;
pub use vm::*;
mod parser;
pub use parser::*;
mod lexer;
pub use lexer::*;

fn main() {
    let _ = pretty_env_logger::init();
    let mut vm = VM::new();
    vm.import_builtin_function();
    add_code("
local a = 5
local b = a
local c = 3
print(1,a,b,555)
print(c)
 print(5)", &mut vm);
    vm.instructions.push(Instruction::Return(0, 1));
    while vm.run() {}
}
