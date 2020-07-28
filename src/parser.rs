use crate::*;
use enum_as_inner::EnumAsInner;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
#[macro_use]
mod lalr1;
use crate::lexer::*;
use lalr1::ToTerminalName;
#[derive(Debug, EnumAsInner)]
enum AST {
    Literal(Value),
    LocalVariable(String),
    LocalVariableDeclare(String, Box<AST>),
    Assign(Box<AST>, Box<AST>),
    FunctionCall(String, Option<Box<AST>>),
    ParamList(Box<AST>, Box<AST>),
    Statements(Box<AST>, Box<AST>),
    BinaryOp(Token, Box<AST>, Box<AST>),
    If(Box<AST>, Box<AST>),
    While(Box<AST>, Box<AST>),
    Table,
    Index(Box<AST>, Box<AST>),
}
use AST::*;
parser! {
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
            right!(LeftVariable, ASSIGN, Expression => {
                Assign(ast.get(0).into(), ast.get(1).into())
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
            right!(LEFT_CURLY_BRACKET, RIGHT_CURLY_BRACKET => Table),
            right!(LEFT_BRACKET, Expression, RIGHT_BRACKET),
            right!(LeftVariable)
    )
    production!(
        LeftVariable ->
            right!(ID => LocalVariable(token.get(0).into_id().unwrap())),
            right!(LeftVariable, LEFT_SQUARE_BRACKET, Expression, RIGHT_SQUARE_BRACKET => Index(ast.get(0).into(), ast.get(1).into()))
    )
    production!(
        FunctionCall ->
            right!(ID, LEFT_BRACKET, ParamList, RIGHT_BRACKET => {
              let name = token.get(0).into_id().unwrap();
              FunctionCall (name, Some(ast.get(0).into()))
            }),
            right!(ID, LEFT_BRACKET, RIGHT_BRACKET => {
              let name = token.get(0).into_id().unwrap();
              FunctionCall (name, None)
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

enum Variable {
    RK(i32),
    Temp(TempVariable),
}
impl Variable {
    pub fn new_r_register(x: u32) -> Self {
        RK(x as i32)
    }
    pub fn r_index(&self) -> u32 {
        match self {
            RK(x) => {
                if *x >= 0 {
                    *x as u32
                } else {
                    panic!("Attempt to cast a constant to a register")
                }
            }
            Temp(temp_variables) => temp_variables.r_index(),
        }
    }
    pub fn rk_index(&self) -> i32 {
        match self {
            RK(x) => *x,
            Temp(temp_variables) => temp_variables.r_index() as i32,
        }
    }
}
use Variable::*;

struct TempVariable {
    free_variable_index: Arc<Mutex<u32>>,
    r_index: u32,
    count: u32,
}

impl TempVariable {
    pub fn new(free_variable_index: Arc<Mutex<u32>>, r_index: u32) -> Self {
        Self {
            free_variable_index,
            r_index,
            count: 1,
        }
    }
    pub fn r_index(&self) -> u32 {
        self.r_index
    }
}

impl Drop for TempVariable {
    fn drop(&mut self) {
        let mut free_variable_index = self.free_variable_index.lock().unwrap();
        *free_variable_index = *free_variable_index - self.count;
    }
}

#[derive(Default, Debug)]
pub struct FunctionStack {
    pub variable_count: u32,
    free_variable_index: Arc<Mutex<u32>>,
    pub constants: Vec<Value>,
    pub instructions: Vec<Instruction>,
    constant_map: HashMap<Value, u32>,
    variable_map: HashMap<String, u32>,
}

#[allow(unused_must_use)]
impl FunctionStack {
    fn inc_free_variable_index(&mut self) -> u32 {
        let mut free_variable_index = self.free_variable_index.lock().unwrap();
        let index = *free_variable_index;
        *free_variable_index = *free_variable_index + 1;
        if *free_variable_index > self.variable_count {
            self.variable_count = *free_variable_index;
        }
        index
    }
    fn allocate_temp_variable(&mut self) -> TempVariable {
        let index = self.inc_free_variable_index();
        TempVariable::new(self.free_variable_index.clone(), index)
    }
    fn append_temp_variable(&mut self, temp_variable: &mut TempVariable) {
        self.inc_free_variable_index();
        temp_variable.r_index = temp_variable.r_index + 1;
        temp_variable.count = temp_variable.count + 1;
    }
    fn get_variable_index(&self, variable: &str) -> Option<u32> {
        self.variable_map.get(variable).map(|x| *x)
    }
    fn add_variable(&mut self, name: String) -> u32 {
        let index = self.inc_free_variable_index();
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
    fn get_free_register_or_allocate(&mut self, free_register: Option<u32>) -> Variable {
        if let Some(register) = free_register {
            Variable::new_r_register(register)
        } else {
            Temp(self.allocate_temp_variable())
        }
    }
    fn get_expression_rk_index(&mut self, free_register: Option<u32>, expression: AST) -> Variable {
        match expression {
            Literal(value) => RK(self.get_constant_rk_index(value)),
            other => self.get_expression_r_index(free_register, other),
        }
    }
    fn get_expression_r_index(&mut self, free_register: Option<u32>, expression: AST) -> Variable {
        match expression {
            Index(left, right) => {
                let a = self.get_free_register_or_allocate(free_register);
                let b = self.get_expression_r_index(None, *left);
                let c = self.get_expression_rk_index(None, *right);
                self.instructions.push(Instruction::GetTable(a.r_index(), b.r_index(), c.rk_index()));
                a
            }
            LocalVariable(id) => {
                if let Some(b) = self.get_variable_index(&id) {
                    Variable::new_r_register(b)
                } else {
                    panic!("Cant find symbol {}", id);
                }
            }
            other => {
                let r = self.get_free_register_or_allocate(free_register);
                self.set_expression_to_register(r.r_index(), other);
                r
            }
        }
    }
    fn test_expression(
        &mut self,
        free_register: Option<u32>,
        expression: AST,
        jmp_length: i32,
    ) -> Box<dyn Fn(&mut FunctionStack)> {
        let mut straight_test = |expression| {
            let register = self.get_free_register_or_allocate(free_register);
            self.set_expression_to_register(register.r_index(), expression);
            self.instructions
                .push(Instruction::Test(register.r_index(), 0));
        };
        match expression {
            BinaryOp(op, left, right) => match op {
                Token::EQUAL | Token::INEQUAL | Token::LESSTHAN => {
                    let b = self.get_expression_rk_index(free_register, *left);
                    let c = self.get_expression_rk_index(None, *right);
                    match op {
                        Token::EQUAL => {
                            self.instructions
                                .push(Instruction::Eq(0, b.rk_index(), c.rk_index()))
                        }
                        Token::INEQUAL => {
                            self.instructions
                                .push(Instruction::Eq(1, b.rk_index(), c.rk_index()))
                        }
                        Token::LESSTHAN => {
                            self.instructions
                                .push(Instruction::Lt(0, b.rk_index(), c.rk_index()))
                        }
                        _ => unreachable!(),
                    }
                }
                _ => straight_test(BinaryOp(op, left, right)),
            },
            _ => straight_test(expression),
        }
        let current = self.instructions.len();
        self.instructions.push(Instruction::JMP(jmp_length));
        Box::new(move |stack| {
            let jmp_to = stack.instructions.len();
            stack.instructions[current] = Instruction::JMP((jmp_to - (current + 1)) as i32);
        })
    }
    fn set_expression_to_register(&mut self, register: u32, expression: AST) {
        match expression {
            Literal(value) => {
                let k = self.get_constant_index(value);
                self.instructions.push(Instruction::LoadK(register, k));
            }
            Table => self.instructions.push(Instruction::NewTable(register)),
            Index(left, right) => {
                self.set_expression_to_register(register, *left);
                let c = self.get_expression_rk_index(None, *right);
                self.instructions
                    .push(Instruction::GetTable(register, register, c.rk_index()));
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
                    self.instructions
                        .push(Instruction::ADD(register, b.rk_index(), c.rk_index()))
                }
                Token::EQUAL | Token::INEQUAL | Token::LESSTHAN => {
                    self.test_expression(Some(register), BinaryOp(op, left, right), 1);
                    self.instructions
                        .push(Instruction::LoadBool(register, 1, 1));
                    self.instructions
                        .push(Instruction::LoadBool(register, 0, 0));
                }
                _ => unreachable!(),
            },
            _ => {
                panic!();
            }
        }
    }
    fn add_param(&mut self, temp_variable: &mut TempVariable, ast: AST) {
        match ast {
            ParamList(left, right) => {
                self.add_param(temp_variable, *left);
                self.append_temp_variable(temp_variable);
                self.add_param(temp_variable, *right);
            }
            other => {
                self.set_expression_to_register(temp_variable.r_index(), other);
            }
        }
    }
    fn add(&mut self, ast: AST) {
        use AST::*;
        match ast {
            FunctionCall(name, param_list) => {
                let name = Value::String(String::from(name));
                let k0 = self.get_constant_rk_index(name) as i32;
                let mut temp_variable = self.allocate_temp_variable();
                let call_index = temp_variable.r_index();
                self.instructions
                    .push(Instruction::GetTabUp(call_index, 0, k0));
                if let Some(param_list) = param_list {
                    self.append_temp_variable(&mut temp_variable);
                    self.add_param(&mut temp_variable, *param_list);
                }
                self.instructions
                    .push(Instruction::Call(call_index, temp_variable.count, 1));
            }
            Statements(left, right) => {
                self.add(*left);
                self.add(*right);
            }
            LocalVariableDeclare(variable_name, expression) => {
                let a = self.add_variable(variable_name);
                self.set_expression_to_register(a, *expression);
            }
            Assign(left, right) => match *left {
                LocalVariable(name) => {
                    let a = self.get_variable_index(&name).unwrap();
                    self.set_expression_to_register(a, *right);
                }
                Index(index_left, index_right) => {
                    let a = self.get_expression_r_index(None, *index_left);
                    let b = self.get_expression_rk_index(None, *index_right);
                    let c = self.get_expression_rk_index(None, *right);
                    self.instructions.push(Instruction::SetTable(a.r_index(), b.rk_index(), c.rk_index()));
                }
                _ => unreachable!(),
            },
            If(expression, then) => {
                let set_jmp_to = self.test_expression(None, *expression, 1);
                self.add(*then);
                set_jmp_to(self);
            }
            While(expression, then) => {
                let pos = self.instructions.len();
                let set_jmp_to = self.test_expression(None, *expression, 1);
                self.add(*then);
                self.instructions.push(Instruction::JMP(
                    pos as i32 - self.instructions.len() as i32 - 1,
                ));
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
