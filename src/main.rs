#[macro_use]
extern crate lazy_static;
mod builtin_functions;
pub use builtin_functions::*;
mod vm;
pub use vm::*;

fn main() {
    let mut vm = VM::new();
    vm.import_builtin_function();
    vm.stack.push(CallInfo::new(2, 0, 0));
    vm.constants.push(Value::String(String::from("print")));
    vm.constants.push(Value::Number(1));
    vm.instructions.push(Instruction::GetTabUp(0, 0, -1));
    vm.instructions.push(Instruction::LoadK(1, 1));
    vm.instructions.push(Instruction::Call(0, 2, 1));
    vm.instructions.push(Instruction::Return(0, 1));
    while vm.run() {}
}
