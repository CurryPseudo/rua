use crate::*;

lazy_static! {
    pub static ref FUNCTIONS: Vec<(&'static str, ExportLuaFunction)> = vec![
        ("print", print)
    ];
}

pub fn get_builtin_functions() -> &'static Vec<(&'static str, ExportLuaFunction)> {
    &FUNCTIONS
}

fn print(args: Vec<Value>) -> Vec<Value> {
    let mut to_print = String::new();
    if !args.is_empty() {
        to_print.push_str(args[0].to_string().as_str())
    }
    for i in 1..args.len() {
        to_print.push('\t');
        to_print.push_str(args[i].to_string().as_str())
    }
    println!("{}", to_print);
    Vec::new()
}
