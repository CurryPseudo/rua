use std::{cell::RefCell, collections::HashMap, fmt::Debug, rc::Weak};
use std::{ops::Range, rc::Rc};
#[macro_use]
mod lalr1;
use crate::ConstantValue;
use crate::ConstantValue::*;
use crate::{lexer::*, Instruction};
use lalr1::ToTerminalName;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("cast ast {0:?} to type {1} failed")]
    ASTCastError(AST, &'static str),
    #[error("expression {0:?} is not literal")]
    NotLiteralExpression(ASTExpression),
}
use ParseError::*;

#[derive(Debug)]
pub enum AST {
    ParamList(Vec<ASTExpression>),
    Statements(Vec<ASTStatement>),
    Statement(ASTStatement),
    Expression(ASTExpression),
    FunctionCall(ASTFunctionCall),
}

pub trait FromAST {
    fn from_ast(ast: AST) -> Result<Self, ParseError>
    where
        Self: std::marker::Sized;
}

impl<T: FromAST> FromAST for Box<T> {
    fn from_ast(ast: AST) -> Result<Self, ParseError>
    where
        Self: Sized,
    {
        T::from_ast(ast).map(|t| Box::new(t))
    }
}

macro_rules! impl_cast_ast {
    ($into_type:ty, $pattern:pat => $inner:expr) => {
        impl FromAST for $into_type {
            fn from_ast(ast: AST) -> Result<Self, ParseError> {
                match ast {
                    $pattern => $inner,
                    other => Err(ASTCastError(other, std::any::type_name::<Self>()))?,
                }
            }
        }
    };
}

impl AST {
    pub fn into_sub<T: FromAST>(self) -> Result<T, ParseError> {
        T::from_ast(self)
    }
}

#[derive(Debug)]
pub enum ASTStatement {
    FunctionCallState(ASTFunctionCall),
    Assign(ASTLeftVariable, ASTExpression),
    LocalVariableDeclare(String, ASTExpression),
    If(ASTExpression, Vec<ASTStatement>),
    While(ASTExpression, Vec<ASTStatement>),
}
impl_cast_ast!(Vec<ASTStatement>, Statements(v) => Ok(v));
impl_cast_ast!(ASTStatement, Statement(v) => Ok(v));
#[derive(Debug)]
pub enum ASTExpression {
    Literal(ConstantValue),
    FunctionCallExpr(ASTFunctionCall),
    BinaryOp(Token, Box<ASTExpression>, Box<ASTExpression>),
    SingleOp(Token, Box<ASTExpression>),
    Table,
    LeftVariable(ASTLeftVariable),
}
impl_cast_ast!(Vec<ASTExpression>, ParamList(v) => Ok(v));
impl_cast_ast!(ASTExpression, Expression(v) => Ok(v));
#[derive(Debug)]
pub enum ASTLeftVariable {
    LocalVariable(String),
    Index(Box<ASTLeftVariable>, Box<ASTExpression>),
}
impl_cast_ast!(ASTLeftVariable, Expression(LeftVariable(v)) => Ok(v));
#[derive(Debug)]
pub struct ASTFunctionCall(Box<ASTExpression>, Vec<ASTExpression>);
impl_cast_ast!(ASTFunctionCall, FunctionCall(v) => Ok(v));

impl ASTExpression {
    pub fn is_test(&self) -> bool {
        match self {
            Self::BinaryOp(token, _, _) => match token {
                Token::EQUAL | Token::INEQUAL | Token::LESSTHAN => true,
                _ => false,
            },
            Self::SingleOp(token, _) => match token {
                Token::NOT => true,
                _ => false,
            },
            _ => false,
        }
    }
}
use ASTExpression::*;
use ASTLeftVariable::*;
use ASTStatement::*;
use AST::*;
parser! {
    lua_parse = |token: Token, ast: AST, ParseError|
    production!(
        Statements ->
            right!(Statements, Statement => {
                let mut statements: Vec<ASTStatement> = ast.get(0).into_sub()?;
                statements.push(ast.get(1).into_sub()?);
                Ok(Statements(statements))
            }),
            right!(Statement => {
                Ok(Statements(vec![ast.get(0).into_sub()?]))
            })
    )

    production!(
        Statement ->
            right!(LOCAL, ID, ASSIGN, Expression => {
                let name = inner!(token.get(1), if Token::ID);
                Ok(Statement(LocalVariableDeclare(name, ast.get(0).into_sub()?)))
            }),
            right!(LeftVariable, ASSIGN, Expression => {
                Ok(Statement(Assign(ast.get(0).into_sub()?, ast.get(1).into_sub()?)))
            }),
            right!(FunctionCall => {
                Ok(Statement(FunctionCallState(ast.get(0).into_sub()?)))
            }),
            right!(WHILE, Expression, DO, Statements, END => {
                Ok(Statement(While(ast.get(0).into_sub()?, ast.get(1).into_sub()?)))
            }),
            right!(IF, Expression, THEN, Statements, END => {
                Ok(Statement(If(ast.get(0).into_sub()?, ast.get(1).into_sub()?)))
            })
    )

    production!(
        Expression ->
            right!(Expression + (EQUAL | INEQUAL | LESSTHAN) + ExpressionAdd =>
                Ok(Expression(BinaryOp(
                    token.get(0),
                    ast.get(0).into_sub()?,
                    ast.get(1).into_sub()?)))),
            right!(ExpressionAdd)
    )
    production!(
        ExpressionAdd ->
            right!(ExpressionAdd, ADD, ExpressionMul =>
                Ok(Expression(BinaryOp(
                    token.get(0),
                    ast.get(0).into_sub()?,
                    ast.get(1).into_sub()?)))),
            right!(ExpressionMul)
    )
    production!(
        ExpressionMul ->
            right!(ExpressionMul, MUL, ExpressionNot =>
                Ok(Expression(BinaryOp(
                    token.get(0),
                    ast.get(0).into_sub()?,
                    ast.get(1).into_sub()?)))),
            right!(ExpressionNot)
    )
    production!(
        ExpressionNot ->
            right!(NOT, ExpressionFinal =>
                Ok(Expression(SingleOp(
                    token.get(0),
                    ast.get(0).into_sub()?)))),
            right!(ExpressionFinal)
    )
    production!(
        ExpressionFinal ->
            right!(FunctionCall => Ok(Expression(FunctionCallExpr(ast.get(0).into_sub()?)))),
            right!(TRUE => Ok(Expression(Literal(Boolean(true))))),
            right!(FALSE => Ok(Expression(Literal(Boolean(false))))),
            right!(NUMBER => Ok(Expression(Literal(Number(inner!(token.get(0), if Token::NUMBER)))))),
            right!(STRING => Ok(Expression(Literal(LuaString(inner!(token.get(0), if Token::STRING)))))),
            right!(LEFT_CURLY_BRACKET, RIGHT_CURLY_BRACKET => Ok(Expression(Table))),
            right!(LEFT_BRACKET, Expression, RIGHT_BRACKET),
            right!(LeftVariable)
    )
    production!(
        LeftVariable ->
            right!(ID => Ok(Expression(LeftVariable(LocalVariable(inner!(token.get(0), if Token::ID)))))),
            right!(LeftVariable, LEFT_SQUARE_BRACKET, Expression, RIGHT_SQUARE_BRACKET =>
                Ok(Expression(LeftVariable(Index(
                    ast.get(0).into_sub()?,
                    ast.get(1).into_sub()?))))),
            right!(LeftVariable, DOT, ID =>
                Ok(Expression(LeftVariable(Index(
                    ast.get(0).into_sub()?,
                    Box::new(Literal(LuaString(inner!(token.get(1), if Token::ID)))))))))
    )
    production!(
        FunctionCall ->
            right!(LeftVariable, LEFT_BRACKET, ParamList, RIGHT_BRACKET => {
                Ok(FunctionCall(ASTFunctionCall(
                    ast.get(0).into_sub()?,
                    ast.get(1).into_sub()?)))
            }),
            right!(LeftVariable, LEFT_BRACKET, RIGHT_BRACKET => {
                Ok(FunctionCall(ASTFunctionCall(
                    ast.get(0).into_sub()?,
                    vec![])))
            })

    )
    production!(
        ParamList ->
            right!(ParamList, COMMA, Expression => {
                let mut params: Vec<ASTExpression> = ast.get(0).into_sub()?;
                params.push(ast.get(1).into_sub()?);
                Ok(ParamList(params))
            }),
            right!(Expression => {
                Ok(ParamList(vec![ast.get(0).into_sub()?]))
            })
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
pub struct FunctionCompiler {
    pub variable_count: u32,
    free_variable_index: Rc<RefCell<u32>>,
    pub constants: Vec<ConstantValue>,
    pub instructions: Vec<Instruction>,
    constant_map: HashMap<ConstantValue, u32>,
    variable_map: HashMap<String, u32>,
}

#[allow(unused_must_use)]
impl FunctionCompiler {
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
    fn get_constant_index(&mut self, value: ConstantValue) -> u32 {
        if let Some(index) = self.constant_map.get(&value) {
            *index
        } else {
            let index = self.constants.len() as u32;
            self.constant_map.insert(value.clone(), index);
            self.constants.push(value);
            index
        }
    }
    fn get_constant_rk_index(&mut self, value: ConstantValue) -> i32 {
        -1 - self.get_constant_index(value) as i32
    }
    fn get_free_register_or_allocate(&mut self, free_register: Option<u32>) -> Variable {
        if let Some(register) = free_register {
            Variable::new_r_register(register)
        } else {
            Temp(self.allocate_temp_variable(1))
        }
    }
    fn get_expression_rk_index(
        &mut self,
        free_register: Option<u32>,
        expression: ASTExpression,
    ) -> Variable {
        match expression {
            Literal(value) => RK(self.get_constant_rk_index(value)),
            expression => self.get_expression_r_index(free_register, expression),
        }
    }
    fn get_left_variable_r_index(
        &mut self,
        free_register: Option<u32>,
        left_variable: ASTLeftVariable,
    ) -> Variable {
        match left_variable {
            Index(left, right) => {
                let a = self.get_free_register_or_allocate(free_register);
                let b = self.get_left_variable_r_index(None, *left);
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
                    let k = self.get_constant_rk_index(LuaString(id));
                    self.instructions
                        .push(Instruction::GetTabUp(r.r_index(), 0, k));
                    r
                }
            }
        }
    }
    fn get_expression_r_index(
        &mut self,
        free_register: Option<u32>,
        expression: ASTExpression,
    ) -> Variable {
        match expression {
            LeftVariable(left_variable) => {
                self.get_left_variable_r_index(free_register, left_variable)
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
        expression: ASTExpression,
        jmp_length: i32,
    ) -> Box<dyn Fn(&mut FunctionCompiler)> {
        let is_true_value = if is_true { 0 } else { 1 };
        let reverse_value = 1 - is_true_value;
        let mut straight_test = |expression: ASTExpression| {
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
    fn set_left_variable_to_register(&mut self, register: u32, left_variable: ASTLeftVariable) {
        match left_variable {
            Index(left, right) => {
                self.set_left_variable_to_register(register, *left);
                let c = self.get_expression_rk_index(None, *right);
                self.instructions
                    .push(Instruction::GetTable(register, register, c.rk_index()));
            }
            LocalVariable(id) => {
                if let Some(b) = self.get_variable_index(&id) {
                    self.instructions.push(Instruction::Move(register, b))
                } else {
                    let c = self.get_constant_rk_index(LuaString(id));
                    self.instructions
                        .push(Instruction::GetTabUp(register, 0, c));
                }
            }
        }
    }
    fn set_expression_to_register(&mut self, register: u32, expression: ASTExpression) {
        match expression {
            LeftVariable(left_variable) => {
                self.set_left_variable_to_register(register, left_variable)
            }
            Literal(value) => {
                let k = self.get_constant_index(value);
                self.instructions.push(Instruction::LoadK(register, k));
            }
            Table => self.instructions.push(Instruction::NewTable(register)),
            FunctionCallExpr(func) => {
                self.get_function_call(func, Some(register..register + 1));
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
                    _ => todo!(),
                })
            }
            SingleOp(_, _) => todo!(),
        }
    }
    fn get_function_call(&mut self, function_call: ASTFunctionCall, ret_range: Option<Range<u32>>) {
        let count = if let Some(ret_range) = &ret_range {
            ret_range.end - ret_range.start
        } else {
            0
        };

        let len = function_call.1.len() as u32;
        if len + 1 > count {
            let temp_variable = self.allocate_temp_variable(len + 1);
            self.set_expression_to_register(temp_variable.r_index(), *function_call.0);
            for (i, param) in function_call.1.into_iter().enumerate() {
                self.set_expression_to_register(temp_variable.r_index() + i as u32 + 1, param);
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
            self.set_expression_to_register(ret_begin, *function_call.0);
            for (i, param) in function_call.1.into_iter().enumerate() {
                self.set_expression_to_register(ret_begin + i as u32 + 1, param);
            }
            self.instructions
                .push(Instruction::Call(ret_begin, len + 1, count + 1));
        }
    }
    pub fn push_statements(&mut self, statements: Vec<ASTStatement>) {
        for statement in statements {
            self.push_statement(statement)
        }
    }
    fn push_statement(&mut self, statement: ASTStatement) {
        match statement {
            Assign(left, right) => match left {
                LocalVariable(name) => {
                    let a = self.get_variable_index(&name).unwrap();
                    self.set_expression_to_register(a, right);
                }
                Index(index_left, index_right) => {
                    let a = self.get_left_variable_r_index(None, *index_left);
                    let b = self.get_expression_rk_index(None, *index_right);
                    let c = self.get_expression_rk_index(None, right);
                    self.instructions.push(Instruction::SetTable(
                        a.r_index(),
                        b.rk_index(),
                        c.rk_index(),
                    ));
                }
            },
            LocalVariableDeclare(variable_name, expression) => {
                let a = self.add_variable(variable_name);
                self.set_expression_to_register(a, expression);
            }
            If(expression, then) => {
                let set_jmp_to = self.test_expression(true, None, expression, 1);
                self.push_statements(then);
                set_jmp_to(self);
            }
            While(expression, then) => {
                let pos = self.instructions.len();
                let set_jmp_to = self.test_expression(true, None, expression, 1);
                self.push_statements(then);
                self.instructions.push(Instruction::Jmp(
                    pos as i32 - self.instructions.len() as i32 - 1,
                ));
                set_jmp_to(self);
            }
            FunctionCallState(func) => {
                self.get_function_call(func, None);
            }
        }
    }
}
