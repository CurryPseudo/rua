mod table;
mod value;
pub use table::*;
pub use value::*;

use crate::*;
use std::collections::HashMap;

#[derive(Debug)]
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
    pub constants: Vec<Value>,
    pub instructions: Vec<Instruction>,
    pub pc: usize,
    pub up_value: Vec<usize>,
    tables: HashMap<usize, Table>,
    next_table_id: usize,
}

#[derive(Debug)]
pub struct CallInfo {
    pub registers: Vec<Value>,
    pub constant_offset: usize,
    pub call_instruction: usize,
}

impl CallInfo {
    pub fn new(register_count: usize, constant_offset: usize, call_instruction: usize) -> Self {
        Self {
            registers: vec![Value::Nil; register_count],
            constant_offset,
            call_instruction,
        }
    }
}

impl VM {
    pub fn new() -> Self {
        let mut r = Self::default();
        let table = r.new_table();
        r.up_value.push(table);
        r
    }
    pub fn import_foreign(&mut self, foreign: Foreign) {
        let mut table_id = self.up_value[0];
        let mut last: Option<&'static str> = None;
        for pre in foreign.pre {
            if let Some(last) = last {
                let new_table = self.new_table();
                self.get_table_mut_from_id(table_id)
                    .set(Value::String(last.to_string()), Value::Table(new_table));
                table_id = new_table;
            }
            last = Some(pre)
        }
        self.get_table_mut_from_id(table_id).set(
            Value::String(last.unwrap().to_string()),
            Value::LuaFunction(foreign.func),
        );
    }
    pub fn import_builtin(&mut self) {
        for foreign in get_builtins() {
            self.import_foreign(foreign.clone());
        }
    }
    pub fn run(&mut self) -> bool {
        if self.pc >= self.instructions.len() {
            return false;
        }
        trace!("{:?}", self.instructions[self.pc]);
        trace!("{:#?}", self.stack);
        match self.instructions[self.pc] {
            Instruction::GetTabUp(a, b, c) => {
                *self.r_register_mut(a) = self.get_up_value(b).get(self.rk_register(c)).clone();
            }
            Instruction::LoadK(a, bx) => {
                *self.r_register_mut(a) = self.k_register(bx).clone();
            }
            Instruction::Call(a, b, c) => {
                let func = self.r_register(a);
                match func {
                    Value::LuaFunction(lua_function) => {
                        let results = lua_function.evaluate(self.r_registers(a + 1, b - 1));
                        let mut i = 0;
                        for result in results {
                            if i >= c - 1 {
                                break;
                            }
                            *self.r_register_mut(a + i) = result;
                            i += 1;
                        }
                        while i < c - 1 {
                            *self.r_register_mut(a + i) = Value::Nil;
                            i += 1;
                        }
                    }
                    _ => panic!("{:?} is not function", func),
                }
            }
            Instruction::Return(a, b) => {
                return false;
            }
            Instruction::Move(a, b) => {
                *self.r_register_mut(a) = self.r_register(b).clone();
            }
            Instruction::Add(a, b, c) => {
                *self.r_register_mut(a) = self.rk_register(b) + self.rk_register(c);
            }
            Instruction::Mul(a, b, c) => {
                *self.r_register_mut(a) = self.rk_register(b) * self.rk_register(c);
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
                *self.r_register_mut(a) = Value::Boolean(b == 1);
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
                *self.r_register_mut(a) = Value::Table(self.new_table());
            }
            Instruction::GetTable(a, b, c) => {
                *self.r_register_mut(a) = self
                    .get_table_from_value(self.r_register(b))
                    .get(self.rk_register(c))
                    .clone();
            }
            Instruction::SetTable(a, b, c) => {
                let b = self.rk_register(b).clone();
                let c = self.rk_register(c).clone();
                let table = self.get_table_mut_from_register(a);
                table.set(b, c);
            }
            Instruction::LoadNil(a, b) => {
                for i in 0..b + 1 {
                    *self.r_register_mut(a + i) = Value::Nil;
                }
            }
        }
        self.pc += 1;
        true
    }
    fn r_registers(&self, index: u32, len: u32) -> &[Value] {
        &self.stack.last().unwrap().registers[index as usize..(index + len) as usize]
    }
    fn k_register(&self, index: u32) -> &Value {
        &self.constants[self.stack.last().unwrap().constant_offset + index as usize]
    }
    fn rk_register(&self, index: i32) -> &Value {
        if index >= 0 {
            self.r_register(index as u32)
        } else {
            self.k_register((-1 - index) as u32)
        }
    }
    fn r_register(&self, index: u32) -> &Value {
        &self.stack.last().unwrap().registers[index as usize]
    }
    fn r_register_mut(&mut self, index: u32) -> &mut Value {
        &mut self.stack.last_mut().unwrap().registers[index as usize]
    }
    fn get_up_value(&self, index: u32) -> &Table {
        &self.tables[&self.up_value[self.up_value.len() - 1 - index as usize]]
    }
    fn new_table(&mut self) -> usize {
        let r = self.next_table_id;
        self.tables.insert(self.next_table_id, Table::new());
        self.next_table_id += 1;
        r
    }
    fn get_table_mut_from_register(&mut self, register: u32) -> &mut Table {
        if let Value::Table(id) = self.r_register(register) {
            let id = *id;
            self.get_table_mut_from_id(id)
        } else {
            panic!(
                "Attempt to index a {} value",
                self.r_register(register).type_name()
            );
        }
    }
    fn get_table_mut_from_id(&mut self, id: usize) -> &mut Table {
        self.tables.get_mut(&id).unwrap()
    }
    fn get_table_from_value(&self, value: &Value) -> &Table {
        if let Value::Table(id) = value {
            &self.tables[id]
        } else {
            panic!("Attempt to index a {} value", value.type_name());
        }
    }
}

impl VM {
    pub fn add_function(&mut self, function_stack: FunctionStack) {
        self.stack.push(CallInfo::new(
            function_stack.variable_count as usize,
            self.constants.len(),
            self.instructions.len(),
        ));
        self.constants.extend(function_stack.constants.into_iter());
        self.instructions
            .extend(function_stack.instructions.into_iter());
    }
}
