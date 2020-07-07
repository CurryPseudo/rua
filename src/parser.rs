use crate::*;
use enum_as_inner::EnumAsInner;
use std::collections::HashMap;
use std::collections::VecDeque;
#[macro_use]
mod lalr1;
use lalr1::*;
use crate::lexer::*;
macro_rules! pop_front_unwrap {
    ($vec_deque:ident, $into_inner:tt) => {
        $vec_deque.pop_front().unwrap().$into_inner().unwrap()
    };
}
#[derive(Debug, EnumAsInner)]
enum AST {
    Function { name: String, param_list: Vec<i32> },
    ParamList(Vec<i32>),
    Statements(VecDeque<AST>),
}
parser!(
    ParseFunctionName = lua_parse;
    Token = token: Token;
    AST = ast: AST;
    Statements -> Function, Statements => {
        let function = ast.pop_front().unwrap();
        let mut functions = pop_front_unwrap!(ast, into_statements);
        functions.push_front(function);
        AST::Statements(functions)
    }
    | Function => {
        let mut r = VecDeque::new();
        r.push_front(ast.pop_front().unwrap());
        AST::Statements(r)
    };
    Function -> id, left_bracket, ParamList, right_bracket => {
        let name = pop_front_unwrap!(token, into_id);
        let param_list = pop_front_unwrap!(ast, into_param_list);
        AST::Function{ name, param_list }
    };
    ParamList -> ParamList, comma, number => {
        let mut param_list = pop_front_unwrap!(ast, into_param_list);
        token.pop_front();
        let number = pop_front_unwrap!(token, into_number);
        param_list.push(number);
        AST::ParamList(param_list)
    }
    | number => {
        let number = pop_front_unwrap!(token, into_number);
        AST::ParamList(vec![number])
    }
);
use strum::VariantNames;
impl ToTerminalName for Token {
    fn to_terminal_name(&self) -> &'static str {
        self.into()
    }
    fn all_terminal_names() -> &'static [&'static str] {
        Self::VARIANTS
    }
}

#[derive(Default, Debug)]
pub struct FunctionStack {
    pub variable_count: u32,
    free_variable_index: u32,
    pub constants: Vec<Value>,
    pub instructions: Vec<Instruction>,
    constant_map: HashMap<Value, u32>,
}

impl FunctionStack {
    fn get_free_variable_index_temp(&mut self, count: u32) -> u32 {
        if self.free_variable_index + count > self.variable_count {
            self.variable_count += count;
        }
        self.free_variable_index
    }
    fn get_constant_index(&mut self, value: Value) -> u32 {
        if let Some(index) = self.constant_map.get(&value) {
            *index
        } else {
            let index = self.constants.len() as u32;
            self.constant_map.insert(value.clone(), index);
            self.constants.push(value);
            index
        }
    }
    fn get_constant_rk_index(&mut self, value: Value) -> i32 {
        -1 - self.get_constant_index(value) as i32
    }
    fn add_statement(&mut self, ast: AST) {
        let (name, param_list) = ast.into_function().unwrap();
        let name = Value::String(String::from(name));
        let param_len = param_list.len();
        let r = self.get_free_variable_index_temp(param_len as u32 + 1);
        let k0 = self.get_constant_rk_index(name) as i32;
        self.instructions.push(Instruction::GetTabUp(r, 0, k0));
        for (i, param) in param_list.into_iter().enumerate() {
            let k1 = self.get_constant_index(Value::Number(param));
            self.instructions.push(Instruction::LoadK(r + 1 + i as u32, k1));
        }
        self.instructions.push(Instruction::Call(r, param_len as u32 + 1, 1));
    }
    pub fn from_statements(input: &str) -> Self {
        let functions = lua_parse(Token::lexer(input).into_iter().collect()).into_statements().unwrap();
        let mut r = Self::default();
        for function in functions {
            r.add_statement(function);
        }
        r
    }
}
