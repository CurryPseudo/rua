#[macro_use]
extern crate log;
#[macro_use]
extern crate lazy_static;
#[macro_use]
mod foreign;
pub use foreign::*;
mod builtin;
pub use builtin::*;
mod vm;
pub use vm::*;
mod parser;
pub use parser::*;
mod lexer;
pub use lexer::*;
mod def;
pub use def::*;

fn main() {
    use std::fs::File;
    use std::io::prelude::*;
    let _ = pretty_env_logger::init();
    let mut vm = VM::new();
    vm.import_builtin();
    let args: Vec<_> = std::env::args().collect();
    let lua_file_name = &args[1];
    let mut lua_file = File::open(lua_file_name).unwrap();
    let mut lua_content = String::new();
    lua_file.read_to_string(&mut lua_content).unwrap();
    add_code(&lua_content, &mut vm);
    vm.instructions.push(Instruction::Return(0, 1));
    debug!("{:#?}", vm);
    while vm.run() {}
}
