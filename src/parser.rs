use crate::*;
use enum_as_inner::EnumAsInner;
use std::collections::HashMap;
#[macro_use]
mod lalr1;
use crate::lexer::*;
use lalr1::{Grammar, ToTerminalName};
#[derive(Debug, EnumAsInner)]
enum AST {
    Literal(Value),
    LocalVariable(String),
    LocalVariableDeclare(String, Box<AST>),
    FunctionCall(String, Box<AST>),
    ParamList(Box<AST>, Box<AST>),
    Statements(Box<AST>, Box<AST>),
    BinaryOp(Token, Box<AST>, Box<AST>),
}
use AST::*;
parser!{
    lua_parse = |token: Token, ast: AST|
    Statements -> 
      (Statement, {Statement} => Statements(ast.get(0).into(), ast.get(1).into()));

    Statement -> 
      (LOCAL, ID, ASSIGN, Expression => {
        let name = token.get(1).into_id().unwrap();
        LocalVariableDeclare(name, ast.get(0).into())
    })
    | (FunctionCall);

    Expression -> 
      (Expression0, {EQUAL, Expression0} => BinaryOp(token.get(0), ast.get(0).into(), ast.get(1).into()));

    Expression0 -> 
      (Expression1, {ADD, Expression1} => BinaryOp(token.get(0), ast.get(0).into(), ast.get(1).into()));

    Expression1 -> 
      (FunctionCall => ast.get(0))
    | (TRUE => Literal(Value::Boolean(true)))
    | (FALSE => Literal(Value::Boolean(false)))
    | (NUMBER => Literal(Value::Number(token.get(0).into_number().unwrap())))
    | (ID => LocalVariable(token.get(0).into_id().unwrap()));

    FunctionCall -> 
      (ID, LEFT_BRACKET, ParamList, RIGHT_BRACKET => {
        let name = token.get(0).into_id().unwrap();
        FunctionCall (name, ast.get(0).into())
    });

    ParamList -> 
      (Expression, {COMMA, Expression} => AST::ParamList(ast.get(0).into(), ast.get(1).into()))
}
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
    fn allocate_temp_variable(&mut self, count: u32) -> u32 {
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
    fn get_expression_rk_index(&mut self, free_register: Option<u32>, expression: AST) -> i32 {
        match expression {
            Literal(value) => self.get_constant_rk_index(value),
            LocalVariable(id) => {
                if let Some(b) = self.get_variable_index(&id) {
                    b as i32
                } else {
                    panic!("Cant find symbol {}", id);
                }
            }
            other => {
                let r = free_register.unwrap_or_else(|| self.allocate_temp_variable(1));
                self.set_expression_to_register(r, other);
                r as i32
            }
        }
    }
    fn set_expression_to_register(&mut self, register: u32, expression: AST) {
        match expression {
            Literal(value) => {
                let k = self.get_constant_index(value);
                self.instructions.push(Instruction::LoadK(register, k));
            }
            LocalVariable(id) => {
                if let Some(b) = self.get_variable_index(&id) {
                    self.instructions.push(Instruction::Move(register, b));
                } else {
                    panic!("Cant find symbol {}", id);
                }
            }
            BinaryOp(op, left, right) => match op {
                Token::ADD => {
                    let b = self.get_expression_rk_index(Some(register), *left);
                    let c = self.get_expression_rk_index(None, *right);
                    self.instructions.push(Instruction::ADD(register, b, c));
                }
                Token::EQUAL => {
                    let b = self.get_expression_rk_index(Some(register), *left);
                    let c = self.get_expression_rk_index(None, *right);
                    self.instructions.push(Instruction::Eq(1, b, c));
                    self.instructions.push(Instruction::JMP(0, 1));
                    self.instructions
                        .push(Instruction::LoadBool(register, 0, 1));
                    self.instructions
                        .push(Instruction::LoadBool(register, 1, 0));
                }
                _ => unreachable!(),
            },
            _ => {
                panic!();
            }
        }
    }
    fn add_param(&mut self, register: u32, ast: AST) -> u32 {
        match ast {
            ParamList(left, right) => {
                let len = self.add_param(register, *left);
                return self.add_param(register + len, *right) + len;
            }
            other => {
                self.set_expression_to_register(register, other);
                return 1;
            }
        }
    }
    fn add(&mut self, ast: AST) {
        use AST::*;
        match ast {
            FunctionCall(name, param_list) => {
                let name = Value::String(String::from(name));
                let k0 = self.get_constant_rk_index(name) as i32;
                self.instructions
                    .push(Instruction::GetTabUp(self.free_variable_index, 0, k0));
                let len = self.add_param(self.free_variable_index + 1, *param_list);
                self.allocate_temp_variable(len + 1);
                self.instructions
                    .push(Instruction::Call(self.free_variable_index, len + 1, 1));
            }
            Statements(left, right) => {
                self.add(*left);
                self.add(*right);
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
