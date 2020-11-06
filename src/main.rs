#[macro_use]
extern crate log;
#[macro_use]
extern crate lazy_static;
#[macro_use]
mod foreign;
pub use foreign::*;
mod vm;
pub use vm::*;
mod parser;
pub use parser::*;
mod lexer;
pub use lexer::*;
mod def;
pub use def::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
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
    let mut stack = FunctionParseResult::default();
    let tokens = Token::lexer(&lua_content).collect();
    info!("{:?}", tokens);
    let ast = lua_parse(tokens);
    stack.add(ast);
    {
        vm.add_main_function(stack.into());
    }
    debug!("{:#?}", vm);
    while vm.run()? {}
    Ok(())
}
