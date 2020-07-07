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
    Return(u32, u32),
}

#[derive(Debug)]
pub struct VM {
    pub stack: Vec<CallInfo>,
    pub constants: Vec<Value>,
    pub instructions: Vec<Instruction>,
    pub current_instruction: usize,
    pub up_value: Vec<Table>,
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
            registers: vec![Value::None; register_count],
            constant_offset,
            call_instruction,
        }
    }
}

impl VM {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            constants: Vec::new(),
            instructions: Vec::new(),
            current_instruction: 0,
            up_value: Vec::new(),
        }
    }
    pub fn import_builtin_function(&mut self) {
        let mut table = Table::new();
        let mut i = 0;
        for lua_function in get_lua_functions() {
            table.set(
                Value::String(String::from(lua_function.name())),
                Value::LuaFunction(i),
            );
            i += 1;
        }
        self.up_value.push(table);
    }
    pub fn run(&mut self) -> bool {
        if self.current_instruction >= self.instructions.len() {
            return false;
        }
        match self.instructions[self.current_instruction] {
            Instruction::GetTabUp(a, b, c) => {
                *self.r_register_mut(a) = self.get_up_value(b).get(self.rk_register(c)).clone();
            }
            Instruction::LoadK(a, bx) => {
                *self.r_register_mut(a) = self.k_register(bx).clone();
            }
            Instruction::Call(a, b, c) => {
                let func = self.r_register(a);
                match func {
                    Value::LuaFunction(i) => {
                        let result = get_lua_function(*i).evaluate(self.r_registers(a + 1, b - 1));
                        for i in 0..c - 1 {
                            *self.r_register_mut(a + i) = result[i as usize].clone();
                        }
                    }
                    _ => panic!(),
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
        }
        self.current_instruction += 1;
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
}

impl VM {
    pub fn add_function(&mut self, function_stack: FunctionStack) {
        self.stack.push(CallInfo::new(function_stack.variable_count as usize, self.constants.len(), self.instructions.len()));
        self.constants.extend(function_stack.constants.into_iter());
        self.instructions.extend(function_stack.instructions.into_iter());

    }
}
