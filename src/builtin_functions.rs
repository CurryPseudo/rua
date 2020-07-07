use crate::*;

pub trait LuaFunction: Sync {
    fn name(&self) -> &str;
    fn evaluate(&self, args: &[Value]) -> Vec<Value>;
}

struct Print;

impl LuaFunction for Print {
    fn name(&self) -> &str {
        "print"
    }
    fn evaluate(&self, args: &[Value]) -> Vec<Value> {
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
}

lazy_static! {
    pub static ref FUNCTIONS: Vec<Box<dyn LuaFunction>> = vec![Box::new(Print {})];
}

pub fn get_lua_functions() -> Vec<&'static dyn LuaFunction> {
    FUNCTIONS.iter().map(|b| b.as_ref()).collect()
}

pub fn get_lua_function(index: usize) -> &'static dyn LuaFunction {
    FUNCTIONS[index].as_ref()
}
