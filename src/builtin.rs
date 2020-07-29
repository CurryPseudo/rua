use crate::*;
use crate::Foreign;

lazy_static! {
    pub static ref BUILTIN: Vec<Foreign> = vec![
        foreign!(print = |args| {
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
        }),
        foreign!(math.sqrt = |args| {
            let f = args[0].as_number() as Float;
            let r = f.sqrt() as Integer;
            vec![Value::Number(r)]
        })
    ];
}

pub fn get_builtins() -> &'static Vec<Foreign> {
    &BUILTIN
}

