use crate::*;
use enum_as_inner::EnumAsInner;
use std::collections::HashMap;
#[macro_use]
mod lalr1;
use crate::lexer::*;
use lalr1::ToTerminalName;
#[derive(Debug, EnumAsInner)]
enum AST {
    Literal(Value),
    LocalVariable(String),
    LocalVariableDeclare(String, Box<AST>),
    Assign(String, Box<AST>),
    FunctionCall(String, Box<AST>),
    ParamList(Box<AST>, Box<AST>),
    Statements(Box<AST>, Box<AST>),
    BinaryOp(Token, Box<AST>, Box<AST>),
    If(Box<AST>, Box<AST>),
    While(Box<AST>, Box<AST>),
}
use AST::*;
parser!{
    lua_parse = |token: Token, ast: AST| 
    production!(
        Statements -> 
            right!(Statements, Statement => Statements(ast.get(0).into(), ast.get(1).into())),
            right!(Statement)
    )

    production!(
        Statement -> 
            right!(LOCAL, ID, ASSIGN, Expression => {
                let name = token.get(1).into_id().unwrap();
                LocalVariableDeclare(name, ast.get(0).into())
            }),
            right!(ID, ASSIGN, Expression => {
                let name = token.get(0).into_id().unwrap();
                Assign(name, ast.get(0).into())
            }),
            right!(FunctionCall),
            right!(WHILE, Expression, DO, Statements, END => {
                While(ast.get(0).into(), ast.get(1).into())
            }),
            right!(IF, Expression, THEN, Statements, END => {
                If(ast.get(0).into(), ast.get(1).into())
            })
    )

    production!(
        Expression -> 
            right!(Expression + (EQUAL | INEQUAL | LESSTHAN) + Expression0 => BinaryOp(token.get(0), ast.get(0).into(), ast.get(1).into())),
            right!(Expression0)
    )
    production!(
        Expression0 -> 
            right!(Expression0, ADD, Expression1 => BinaryOp(token.get(0), ast.get(0).into(), ast.get(1).into())),
            right!(Expression1)
    )
    production!(
        Expression1 -> 
            right!(FunctionCall => ast.get(0)),
            right!(TRUE => Literal(Value::Boolean(true))),
            right!(FALSE => Literal(Value::Boolean(false))),
            right!(NUMBER => Literal(Value::Number(token.get(0).into_number().unwrap()))),
            right!(STRING => Literal(Value::String(token.get(0).into_string().unwrap()))),
            right!(ID => LocalVariable(token.get(0).into_id().unwrap()))
    )
    production!(
        FunctionCall -> 
            right!(ID, LEFT_BRACKET, ParamList, RIGHT_BRACKET => {
              let name = token.get(0).into_id().unwrap();
              FunctionCall (name, ast.get(0).into())
            })
    )
    production!(
        ParamList ->  
            right!(ParamList, COMMA, Expression => 
                   AST::ParamList(ast.get(0).into(), ast.get(1).into())),
            right!(Expression)
    )
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

#[allow(unused_must_use)]
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
    fn get_free_register_or_allocate(&mut self, free_register: Option<u32>) -> u32 {
        free_register.unwrap_or_else(|| self.allocate_temp_variable(1))
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
                let r = self.get_free_register_or_allocate(free_register);
                self.set_expression_to_register(r, other);
                r as i32
            }
        }
    }
    fn test_expression(&mut self, free_register: Option<u32>, expression: AST, jmp_length: i32) -> Box<dyn Fn(&mut FunctionStack)> {
        let mut straight_test = |expression| {
            let register = self.get_free_register_or_allocate(free_register);
            self.set_expression_to_register(register, expression);
            self.instructions.push(Instruction::Test(register, 0));
        };
        match expression {
            BinaryOp(op, left, right) => match op {
                Token::EQUAL | Token::INEQUAL | Token::LESSTHAN => {
                    let b = self.get_expression_rk_index(free_register, *left);
                    let c = self.get_expression_rk_index(None, *right);
                    match op {
                        Token::EQUAL => self.instructions.push(Instruction::Eq(0, b, c)),
                        Token::INEQUAL => self.instructions.push(Instruction::Eq(1, b, c)),
                        Token::LESSTHAN => self.instructions.push(Instruction::Lt(0, b, c)),
                        _ => unreachable!()
                    }
                }
                _ => straight_test(BinaryOp(op, left, right))
            }
            _ => straight_test(expression)
        }
        let current = self.instructions.len();
        self.instructions.push(Instruction::JMP(0, jmp_length));
        Box::new(move |stack| {
            let jmp_to = stack.instructions.len();
            stack.instructions[current] = Instruction::JMP(0, (jmp_to - (current + 1)) as i32);
        })
    }
    fn set_expression_to_register(&mut self, register: u32, expression: AST) {
        match expression {
            Literal(value) => {
                let k = self.get_constant_index(value);
                self.instructions.push(Instruction::LoadK(register, k));
            }
            LocalVariable(id) => {
                if let Some(b) = self.get_variable_index(&id) {
                    self.instructions.push(Instruction::Move(register, b))
                } else {
                    panic!("Cant find symbol {}", id);
                }
            }
            BinaryOp(op, left, right) => match op {
                Token::ADD => {
                    let b = self.get_expression_rk_index(Some(register), *left);
                    let c = self.get_expression_rk_index(None, *right);
                    self.instructions.push(Instruction::ADD(register, b, c))
                }
                Token::EQUAL | Token::INEQUAL | Token::LESSTHAN => {
                    self.test_expression(Some(register), BinaryOp(op, left, right), 1);
                    self.instructions.push(Instruction::LoadBool(register, 1, 1));
                    self.instructions.push(Instruction::LoadBool(register, 0, 0));
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
            Assign(variable_name, expression) => {
                let a = self.get_variable_index(&variable_name).unwrap();
                self.set_expression_to_register(a, *expression);
            }
            If(expression, then) => {
                let set_jmp_to = self.test_expression(None, *expression, 1);
                self.add(*then);
                set_jmp_to(self);
            }
            While(expression, then) => {
                let pos = self.instructions.len();
                let set_jmp_to = self.test_expression(None, *expression, 1);
                self.add(*then);
                self.instructions.push(Instruction::JMP(0, pos as i32 - self.instructions.len() as i32 - 1));
                set_jmp_to(self);
            }
            _ => unimplemented!(),
        }
    }
}
pub fn add_code(input: &str, vm: &mut VM) {
    let mut stack = FunctionStack::default();
    let tokens = Token::lexer(input).collect();
    info!("{:?}", tokens);
    let ast = lua_parse(tokens);
    stack.add(ast);
    vm.add_function(stack);
}
