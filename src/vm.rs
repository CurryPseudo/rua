mod table;
mod value;
pub use table::*;
pub use value::*;

use crate::ConstantValue::*;
use crate::*;
use std::{cell::RefCell, collections::HashMap, fmt::Debug, iter::once, rc::Rc};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum RuntimeError {
    #[error("runtime error: expect get a {1} value, but get {0}")]
    TypeError(Value, &'static str),
}

#[derive(Debug, Clone)]
pub enum Instruction {
    GetTabUp(u32, u32, i32),
    LoadK(u32, u32),
    Call(u32, u32, u32),
    Move(u32, u32),
    Add(u32, i32, i32),
    Mul(u32, i32, i32),
    Eq(u32, i32, i32),
    Lt(u32, i32, i32),
    Jmp(i32),
    LoadBool(u32, u32, u32),
    LoadNil(u32, u32),
    Return(u32, u32),
    Test(u32, u32),
    NewTable(u32),
    GetTable(u32, u32, i32),
    SetTable(u32, i32, i32),
}

#[derive(Debug, Default)]
pub struct VM {
    pub stack: Vec<CallInfo>,
    pub up_value: Value,
    tables: HashMap<usize, Table>,
    next_table_id: usize,
    function_infos: Vec<FunctionInfo>,
    gc_env: Rc<RefCell<GCEnv>>,
}

#[derive(Debug, Clone)]
pub struct FunctionInfo {
    register_count: usize,
    constants: Vec<ConstantValue>,
    instructions: Vec<Instruction>,
}
impl From<FunctionCompiler> for FunctionInfo {
    fn from(function_stack: FunctionCompiler) -> Self {
        FunctionInfo {
            register_count: function_stack.variable_count as usize,
            constants: function_stack.constants,
            instructions: function_stack.instructions,
        }
    }
}
#[derive(Debug)]
pub struct CallInfo {
    pc: usize,
    registers: Vec<Value>,
    function_info: FunctionInfo,
    up_values: Vec<Value>,
    gc_env: Rc<RefCell<GCEnv>>,
}
impl CallInfo {
    pub fn new(
        gc_env: Rc<RefCell<GCEnv>>,
        function_info: FunctionInfo,
        up_values: impl Iterator<Item = Value>,
    ) -> Self {
        Self {
            pc: 0,
            registers: vec![Nil.into(); function_info.register_count],
            up_values: up_values.collect(),
            function_info,
            gc_env,
        }
    }
    pub fn run(&mut self) -> Result<bool, RuntimeError> {
        if self.pc >= self.function_info.instructions.len() {
            return Ok(false);
        }
        trace!("{:?}", self.function_info.instructions[self.pc]);
        match self.function_info.instructions[self.pc] {
            Instruction::GetTabUp(a, b, c) => {
                *self.r_register_mut(a) = self
                    .up_value(b)
                    .clone()
                    .expect_table()?
                    .get(&self.rk_register(c))
                    .clone();
            }
            Instruction::LoadK(a, bx) => {
                *self.r_register_mut(a) = self.k_register(bx).clone().into();
            }
            Instruction::Call(a, b, c) => {
                let func = self.r_register(a).clone().expect_function()?;
                let results = func.evaluate(
                    self.r_registers(a + 1, b - 1)
                        .into_iter()
                        .map(Clone::clone)
                        .collect(),
                )?;
                let mut i = 0;
                for result in results {
                    if i >= c - 1 {
                        break;
                    }
                    *self.r_register_mut(a + i) = result;
                    i += 1;
                }
                while i < c - 1 {
                    *self.r_register_mut(a + i) = Nil.into();
                    i += 1;
                }
            }
            Instruction::Return(_a, _b) => {
                return Ok(false);
            }
            Instruction::Move(a, b) => {
                *self.r_register_mut(a) = self.r_register(b).clone();
            }
            Instruction::Add(a, b, c) => {
                *self.r_register_mut(a) = &self.rk_register(b) + &self.rk_register(c);
            }
            Instruction::Mul(a, b, c) => {
                *self.r_register_mut(a) = &self.rk_register(b) * &self.rk_register(c);
            }
            Instruction::Eq(a, b, c) => {
                if (self.rk_register(b) == self.rk_register(c)) ^ (a == 1) {
                    self.pc += 1;
                }
            }
            Instruction::Lt(a, b, c) => {
                if (self.rk_register(b) < self.rk_register(c)) ^ (a == 1) {
                    self.pc += 1;
                }
            }
            Instruction::Jmp(s_bx) => {
                self.pc = (self.pc as i32 + s_bx) as usize;
            }
            Instruction::LoadBool(a, b, c) => {
                *self.r_register_mut(a) = Boolean(b == 1).into();
                if c == 1 {
                    self.pc += 1;
                }
            }
            Instruction::Test(a, c) => {
                if *self.r_register(a).as_ref() != (c == 1) {
                    self.pc += 1;
                }
            }
            Instruction::NewTable(a) => {
                let value = self.gc_env.borrow_mut().new_table();
                *self.r_register_mut(a) = value;
            }
            Instruction::GetTable(a, b, c) => {
                *self.r_register_mut(a) = self
                    .r_register(b)
                    .clone()
                    .expect_table()?
                    .get(&self.rk_register(c))
                    .clone();
            }
            Instruction::SetTable(a, b, c) => {
                let b = self.rk_register(b).clone();
                let c = self.rk_register(c).clone();
                let mut table = self.r_register_mut(a).clone().expect_table()?;
                table.set(b, c);
            }
            Instruction::LoadNil(a, b) => {
                for i in 0..b + 1 {
                    *self.r_register_mut(a + i) = Nil.into();
                }
            }
        }
        self.pc += 1;
        Ok(true)
    }
    fn r_registers(&self, index: u32, len: u32) -> &[Value] {
        &self.registers[index as usize..(index + len) as usize]
    }
    fn k_register(&self, index: u32) -> &ConstantValue {
        &self.function_info.constants[index as usize]
    }
    fn rk_register(&self, index: i32) -> Value {
        if index >= 0 {
            self.r_register(index as u32).clone()
        } else {
            self.k_register((-1 - index) as u32).clone().into()
        }
    }
    fn r_register(&self, index: u32) -> &Value {
        &self.registers[index as usize]
    }
    fn r_register_mut(&mut self, index: u32) -> &mut Value {
        &mut self.registers[index as usize]
    }
    fn up_value(&self, index: u32) -> Value {
        self.up_values[index as usize].clone()
    }
}

impl VM {
    pub fn new() -> Self {
        let mut r = Self::default();
        r.up_value = r.gc_env.borrow_mut().new_table();
        r
    }
    pub fn import_foreign(&mut self, foreign: Foreign) {
        let mut last_table = self.up_value.clone().expect_table().unwrap();
        for pre in &foreign.pre[0..foreign.pre.len() - 1] {
            let key = LuaString(pre.to_string()).into();
            match last_table.get(&key).clone().expect_table() {
                Ok(table) => {
                    last_table = table;
                }
                _ => {
                    last_table.set(key.clone(), self.gc_env.borrow_mut().new_table());
                    last_table = last_table.get(&key).clone().expect_table().unwrap();
                }
            }
        }
        let name = foreign.pre.last().unwrap();
        last_table.set(
            LuaString(name.to_string()).into(),
            Value::LuaFunction(foreign.func),
        );
    }
    pub fn import_builtin(&mut self) {
        for foreign in vec![
            foreign!(
                print = |args| {
                    let mut to_print = String::new();
                    if !args.is_empty() {
                        to_print.push_str(args[0].to_string().as_str())
                    }
                    for i in 1..args.len() {
                        to_print.push('\t');
                        to_print.push_str(args[i].to_string().as_str())
                    }
                    println!("{}", to_print);
                    Ok(Vec::new())
                }
            ),
            foreign!(
                math.sqrt = |args| {
                    let f = args[0].clone().expect_number()? as Float;
                    let r = f.sqrt() as Integer;
                    Ok(vec![Number(r).into()])
                }
            ),
        ] {
            self.import_foreign(foreign);
        }
    }
    pub fn run(&mut self) -> Result<bool, RuntimeError> {
        if let Some(last) = self.stack.last_mut() {
            let r = last.run()?;
            if !r {
                self.stack.pop();
            }
            Ok(r)
        } else {
            Ok(false)
        }
    }
}

impl VM {
    pub fn add_function(&mut self, function: FunctionInfo) {
        self.function_infos.push(function);
    }
    pub fn add_main_function(&mut self, function: FunctionInfo) {
        self.add_function(function.clone());
        self.stack.push(CallInfo::new(
            self.gc_env.clone(),
            function,
            once(self.up_value.clone()),
        ))
    }
}
