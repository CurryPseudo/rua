use enum_as_inner::EnumAsInner;
use std::{cell::RefCell, collections::HashMap, rc::Weak};
use std::{ops::Range, rc::Rc};
#[macro_use]
mod lalr1;
use crate::{lexer::*, Instruction, Value};
use lalr1::ToTerminalName;
#[derive(Debug, EnumAsInner)]
pub enum AST {
    Literal(Value),
    LocalVariable(String),
    LocalVariableDeclare(String, Box<AST>),
    Assign(Box<AST>, Box<AST>),
    FunctionCall(Box<AST>, Option<Box<AST>>),
    ParamList(Box<AST>, Box<AST>),
    Statements(Box<AST>, Box<AST>),
    BinaryOp(Token, Box<AST>, Box<AST>),
    SingleOp(Token, Box<AST>),
    If(Box<AST>, Box<AST>),
    While(Box<AST>, Box<AST>),
    Table,
    Index(Box<AST>, Box<AST>),
}

impl AST {
    pub fn is_test(&self) -> bool {
        match self {
            BinaryOp(token, _, _) => match token {
                Token::EQUAL | Token::INEQUAL | Token::LESSTHAN => true,
                _ => false,
            },
            SingleOp(token, _) => match token {
                Token::NOT => true,
                _ => false,
            },
            _ => false,
        }
    }
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
            right!(Expression + (EQUAL | INEQUAL | LESSTHAN) + ExpressionAdd => BinaryOp(token.get(0), ast.get(0).into(), ast.get(1).into())),
            right!(ExpressionAdd)
    )
    production!(
        ExpressionAdd ->
            right!(ExpressionAdd, ADD, ExpressionMul => BinaryOp(token.get(0), ast.get(0).into(), ast.get(1).into())),
            right!(ExpressionMul)
    )
    production!(
        ExpressionMul ->
            right!(ExpressionMul, MUL, ExpressionNot => BinaryOp(token.get(0), ast.get(0).into(), ast.get(1).into())),
            right!(ExpressionNot)
    )
    production!(
        ExpressionNot ->
            right!(NOT, ExpressionFinal => SingleOp(token.get(0), ast.get(0).into())),
            right!(ExpressionFinal)
    )
    production!(
        ExpressionFinal ->
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
            right!(LeftVariable, LEFT_SQUARE_BRACKET, Expression, RIGHT_SQUARE_BRACKET => Index(ast.get(0).into(), ast.get(1).into())),
            right!(LeftVariable, DOT, ID => Index(ast.get(0).into(), Box::new(Literal(Value::String(token.get(1).into_id().unwrap())))))
    )
    production!(
        FunctionCall ->
            right!(LeftVariable, LEFT_BRACKET, ParamList, RIGHT_BRACKET => {
              FunctionCall (ast.get(0).into(), Some(ast.get(1).into()))
            }),
            right!(LeftVariable, LEFT_BRACKET, RIGHT_BRACKET => {
              FunctionCall (ast.get(0).into(), None)
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
    free_variable_index: Weak<RefCell<u32>>,
    r_index: u32,
    count: u32,
}

impl TempVariable {
    pub fn new(free_variable_index: &Rc<RefCell<u32>>, r_index: u32, count: u32) -> Self {
        Self {
            free_variable_index: Rc::downgrade(free_variable_index),
            r_index,
            count,
        }
    }
    pub fn r_index(&self) -> u32 {
        self.r_index
    }
}

impl Drop for TempVariable {
    fn drop(&mut self) {
        let rc = self.free_variable_index.upgrade().unwrap();
        let mut free_variable_index = rc.borrow_mut();
        *free_variable_index = *free_variable_index - self.count;
    }
}

#[derive(Default, Debug)]
pub struct FunctionParseResult {
    pub variable_count: u32,
    free_variable_index: Rc<RefCell<u32>>,
    pub constants: Vec<Value>,
    pub instructions: Vec<Instruction>,
    constant_map: HashMap<Value, u32>,
    variable_map: HashMap<String, u32>,
}

#[allow(unused_must_use)]
impl FunctionParseResult {
    fn inc_free_variable_index(&mut self, count: u32) -> u32 {
        let mut free_variable_index = self.free_variable_index.borrow_mut();
        let index = *free_variable_index;
        *free_variable_index = *free_variable_index + count;
        if *free_variable_index > self.variable_count {
            self.variable_count = *free_variable_index;
        }
        index
    }
    fn allocate_temp_variable(&mut self, count: u32) -> TempVariable {
        let index = self.inc_free_variable_index(count);
        TempVariable::new(&self.free_variable_index, index, count)
    }
    fn get_variable_index(&self, variable: &str) -> Option<u32> {
        self.variable_map.get(variable).map(|x| *x)
    }
    fn add_variable(&mut self, name: String) -> u32 {
        let index = self.inc_free_variable_index(1);
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
            Temp(self.allocate_temp_variable(1))
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
                self.instructions.push(Instruction::GetTable(
                    a.r_index(),
                    b.r_index(),
                    c.rk_index(),
                ));
                a
            }
            LocalVariable(id) => {
                if let Some(b) = self.get_variable_index(&id) {
                    Variable::new_r_register(b)
                } else {
                    let r = self.get_free_register_or_allocate(free_register);
                    let k = self.get_constant_rk_index(Value::String(id));
                    self.instructions
                        .push(Instruction::GetTabUp(r.r_index(), 0, k));
                    r
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
        is_true: bool,
        free_register: Option<u32>,
        expression: AST,
        jmp_length: i32,
    ) -> Box<dyn Fn(&mut FunctionParseResult)> {
        let is_true_value = if is_true { 0 } else { 1 };
        let reverse_value = 1 - is_true_value;
        let mut straight_test = |expression| {
            let register = self.get_free_register_or_allocate(free_register);
            self.set_expression_to_register(register.r_index(), expression);
            self.instructions
                .push(Instruction::Test(register.r_index(), is_true_value));
        };
        match expression {
            BinaryOp(op, left, right) => match op {
                Token::EQUAL | Token::INEQUAL | Token::LESSTHAN => {
                    let b = self.get_expression_rk_index(free_register, *left);
                    let c = self.get_expression_rk_index(None, *right);
                    match op {
                        Token::EQUAL => self.instructions.push(Instruction::Eq(
                            is_true_value,
                            b.rk_index(),
                            c.rk_index(),
                        )),
                        Token::INEQUAL => self.instructions.push(Instruction::Eq(
                            reverse_value,
                            b.rk_index(),
                            c.rk_index(),
                        )),
                        Token::LESSTHAN => self.instructions.push(Instruction::Lt(
                            is_true_value,
                            b.rk_index(),
                            c.rk_index(),
                        )),
                        _ => unreachable!(),
                    }
                }
                _ => straight_test(BinaryOp(op, left, right)),
            },
            SingleOp(op, right) => match op {
                Token::NOT => {
                    return self.test_expression(!is_true, free_register, *right, jmp_length)
                }
                _ => straight_test(SingleOp(op, right)),
            },
            _ => straight_test(expression),
        }
        let current = self.instructions.len();
        self.instructions.push(Instruction::Jmp(jmp_length));
        Box::new(move |stack| {
            let jmp_to = stack.instructions.len();
            stack.instructions[current] = Instruction::Jmp((jmp_to - (current + 1)) as i32);
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
                    let c = self.get_constant_rk_index(Value::String(id));
                    self.instructions
                        .push(Instruction::GetTabUp(register, 0, c));
                }
            }
            FunctionCall(func, param_list) => {
                self.get_function_call(func, param_list, Some(register..register + 1));
            }
            expression if expression.is_test() => {
                self.test_expression(true, Some(register), expression, 1);
                self.instructions
                    .push(Instruction::LoadBool(register, 1, 1));
                self.instructions
                    .push(Instruction::LoadBool(register, 0, 0));
            }
            BinaryOp(op, left, right) => {
                let b = self.get_expression_rk_index(Some(register), *left);
                let c = self.get_expression_rk_index(None, *right);
                self.instructions.push(match op {
                    Token::ADD => Instruction::Add(register, b.rk_index(), c.rk_index()),
                    Token::MUL => Instruction::Mul(register, b.rk_index(), c.rk_index()),
                    _ => unreachable!(),
                })
            }
            other => {
                panic!("not solve AST {:?}", other);
            }
        }
    }
    fn get_function_call(
        &mut self,
        func: Box<AST>,
        param_list: Option<Box<AST>>,
        ret_range: Option<Range<u32>>,
    ) {
        let count = if let Some(ret_range) = &ret_range {
            ret_range.end - ret_range.start
        } else {
            0
        };

        let param_list = if let Some(param_list) = param_list {
            flatten_binary_ast(param_list, |ast| {
                if let ParamList(left, right) = *ast {
                    Err((left, right))
                } else {
                    Ok(ast)
                }
            })
        } else {
            Vec::new()
        };

        let len = param_list.len() as u32;
        if len + 1 > count {
            let temp_variable = self.allocate_temp_variable(len + 1);
            self.set_expression_to_register(temp_variable.r_index(), *func);
            for (i, param) in param_list.into_iter().enumerate() {
                self.set_expression_to_register(temp_variable.r_index() + i as u32 + 1, *param);
            }
            self.instructions.push(Instruction::Call(
                temp_variable.r_index(),
                temp_variable.count,
                count + 1,
            ));
            if count > 0 {
                let ret_begin = ret_range.unwrap().start;
                for i in 0..count {
                    self.instructions.push(Instruction::Move(
                        ret_begin + i,
                        temp_variable.r_index() + i,
                    ))
                }
            }
        } else {
            let ret_begin = ret_range.unwrap().start;
            self.set_expression_to_register(ret_begin, *func);
            for (i, param) in param_list.into_iter().enumerate() {
                self.set_expression_to_register(ret_begin + i as u32 + 1, *param);
            }
            self.instructions
                .push(Instruction::Call(ret_begin, len + 1, count + 1));
        }
    }
    pub fn add(&mut self, ast: AST) {
        use AST::*;
        match ast {
            FunctionCall(func, param_list) => {
                self.get_function_call(func, param_list, None);
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
                    self.instructions.push(Instruction::SetTable(
                        a.r_index(),
                        b.rk_index(),
                        c.rk_index(),
                    ));
                }
                _ => unreachable!(),
            },
            If(expression, then) => {
                let set_jmp_to = self.test_expression(true, None, *expression, 1);
                self.add(*then);
                set_jmp_to(self);
            }
            While(expression, then) => {
                let pos = self.instructions.len();
                let set_jmp_to = self.test_expression(true, None, *expression, 1);
                self.add(*then);
                self.instructions.push(Instruction::Jmp(
                    pos as i32 - self.instructions.len() as i32 - 1,
                ));
                set_jmp_to(self);
            }
            _ => unimplemented!(),
        }
    }
}
fn flatten_binary_ast<T>(t: T, f: fn(T) -> Result<T, (T, T)>) -> Vec<T> {
    match f(t) {
        Err((left, right)) => {
            let mut r = flatten_binary_ast(left, f.clone());
            r.append(&mut flatten_binary_ast(right, f));
            r
        }
        Ok(t) => vec![t],
    }
}
