mod table;
mod value;
pub use table::*;
pub use value::*;

use crate::*;

#[derive(Debug)]
pub enum Instruction {
    GetTabUp(u32, u32, i32),
    LoadK(u32, u32),
    Call(u32, u32, u32),
    Move(u32, u32),
    ADD(u32, i32, i32),
    Eq(u32, i32, i32),
    Lt(u32, i32, i32),
    JMP(i32),
    LoadBool(u32, u32, u32),
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
    pub up_value: Vec<Table>,
    tables: Vec<Table>,
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
    pub fn import_builtin_function(&mut self) {
        let mut table = Table::new();
        for export_lua_function in get_builtin_functions() {
            table.set(
                Value::String(export_lua_function.name().to_string()),
                Value::LuaFunction(export_lua_function.clone()),
            );
        }
        self.up_value.push(table);
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
                        let result = lua_function.evaluate(self.r_registers(a + 1, b - 1));
                        for i in 0..c - 1 {
                            *self.r_register_mut(a + i) = result[i as usize].clone();
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
            Instruction::ADD(a, b, c) => {
                *self.r_register_mut(a) = self.rk_register(b) + self.rk_register(c);
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
            Instruction::JMP(s_bx) => {
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
                *self.r_register_mut(a) = Value::Table(self.tables.len());
                self.tables.push(Table::new());
            }
            Instruction::GetTable(a, b, c) => {
                *self.r_register_mut(a) = self
                    .get_table(self.r_register(b))
                    .get(self.rk_register(c))
                    .clone();
            }
            Instruction::SetTable(a, b, c) => {
                let b = self.rk_register(b).clone();
                let c = self.rk_register(c).clone();
                let table = self.get_table_mut(a);
                table.set(b, c);
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
        &self.up_value[self.up_value.len() - 1 - index as usize]
    }
    fn get_table_mut(&mut self, register: u32) -> &mut Table {
        if let Value::Table(i) = self.r_register(register) {
            let i = *i;
            &mut self.tables[i]
        } else {
            panic!(
                "Attempt to index a {} value",
                self.r_register(register).type_name()
            );
        }
    }
    fn get_table(&self, value: &Value) -> &Table {
        if let Value::Table(i) = value {
            &self.tables[*i]
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
