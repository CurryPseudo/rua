#[macro_use]
extern crate nom;
#[macro_use]
extern crate lazy_static;
mod builtin_functions;
pub use builtin_functions::*;
mod vm;
pub use vm::*;
mod parser;
pub use parser::*;

fn main() {
    let mut vm = VM::new();
    vm.import_builtin_function();
    let stack = FunctionStack::from_statements(
"print(1)
 print(2)
print(123)");
    //let stack = FunctionStack::from_statements("print(1)print(2)");
    vm.add_function(stack);
    vm.instructions.push(Instruction::Return(0, 1));
    while vm.run() {}
}
