use crate::*;
use enum_as_inner::EnumAsInner;
use std::collections::HashMap;
use std::collections::VecDeque;
#[macro_use]
mod lalr1;
use crate::lexer::*;
use lalr1::*;
macro_rules! pop_front_unwrap {
    ($vec_deque:ident, $into_inner:tt) => {
        $vec_deque.pop_front().unwrap().$into_inner().unwrap()
    };
}
#[derive(Debug, EnumAsInner)]
enum AST {
    Literal(i32),
    LocalVariable(String),
    LocalVariableDeclare(String, Box<AST>),
    FunctionCall(String, Box<AST>),
    ParamList(Vec<AST>),
    Statements(VecDeque<AST>),
}
use AST::*;
parser!(
    ParseFunctionName = lua_parse;
    Token = token: Token;
    AST = ast: AST;
    Statements -> Statement, Statements => {
        let function = ast.pop_front().unwrap();
        let mut functions = pop_front_unwrap!(ast, into_statements);
        functions.push_front(function);
        Statements(functions)
    }
    | Statement => {
        let mut r = VecDeque::new();
        r.push_front(ast.pop_front().unwrap());
        Statements(r)
    };
    Statement -> LOCAL, ID, EQUAL, Expression => {
        token.pop_front();
        let name = pop_front_unwrap!(token, into_id);
        LocalVariableDeclare(name, ast.pop_front().unwrap().into())
    }
    | FunctionCall => {
        ast.pop_front().unwrap()
    };
    Expression -> FunctionCall => {
        ast.pop_front().unwrap()
    }
    | NUMBER => {
        Literal(pop_front_unwrap!(token, into_number))
    }
    | ID => {
        LocalVariable(pop_front_unwrap!(token, into_id))
    };
    FunctionCall -> ID, LEFT_BRACKET, ParamList, RIGHT_BRACKET => {
        let name = pop_front_unwrap!(token, into_id);
        FunctionCall (name, Box::new(ast.pop_front().unwrap()))
    };
    ParamList -> ParamList, COMMA, Expression => {
        let mut param_list = pop_front_unwrap!(ast, into_param_list);
        token.pop_front();
        param_list.push(ast.pop_front().unwrap());
        AST::ParamList(param_list)
    }
    | Expression => {
        AST::ParamList(vec![ast.pop_front().unwrap()])
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
    variable_map: HashMap<String, u32>,
}

impl FunctionStack {
    fn get_free_variable_index_temp(&mut self, count: u32) -> u32 {
        if self.free_variable_index + count > self.variable_count {
            self.variable_count += count;
        }
        self.free_variable_index
    }
    fn get_variable_index(&self, variable: &str) -> Option<u32> {
        self.variable_map.get(variable).map(|x| *x)
    }
    fn add_variable(&mut self, name: String) -> u32 {
        if self.free_variable_index + 1 > self.variable_count {
            self.variable_count += 1;
        }
        let index = self.free_variable_index;
        self.free_variable_index += 1;
        self.variable_map.insert(name, index);
        index
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
    fn set_expression_to_register(&mut self, register: u32, expression: AST) {
        match expression {
            Literal(number) => {
                let k = self.get_constant_index(Value::Number(number));
                self.instructions.push(Instruction::LoadK(register, k));
            }
            LocalVariable(id) => {
                if let Some(b) = self.get_variable_index(&id) {
                    self.instructions.push(Instruction::Move(register, b));
                } else {
                    panic!("Cant find symbol {}", id);
                }
            }
            _ => {
                panic!();
            }
        }
    }
    fn add(&mut self, ast: AST) {
        use AST::*;
        match ast {
            FunctionCall(name, param_list) => {
                let name = Value::String(String::from(name));
                let param_list = param_list.into_param_list().unwrap();
                let param_len = param_list.len();
                let r = self.get_free_variable_index_temp(param_len as u32 + 1);
                let k0 = self.get_constant_rk_index(name) as i32;
                self.instructions.push(Instruction::GetTabUp(r, 0, k0));
                for (i, param) in param_list.into_iter().enumerate() {
                    self.set_expression_to_register(r + 1 + i as u32, param);
                }
                self.instructions
                    .push(Instruction::Call(r, param_len as u32 + 1, 1));
            }
            Statements(statements) => {
                for statement in statements {
                    self.add(statement);
                }
            }
            LocalVariableDeclare(variable_name, expression) => {
                let a = self.add_variable(variable_name);
                self.set_expression_to_register(a, *expression);
            }
            _ => panic!(),
        }
    }
}
pub fn add_code(input: &str, vm: &mut VM) {
    let mut stack = FunctionStack::default();
    let tokens = Token::lexer(input).collect();
    let ast = lua_parse(tokens);
    stack.add(ast);
    vm.add_function(stack);
}
