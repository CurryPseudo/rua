use std::collections::HashMap;

use crate::ConstantValue::*;
use crate::Value;
use crate::Value::*;

#[derive(Default, Debug)]
pub struct GCEnv {
    tables: Vec<Table>,
}
impl GCEnv {
    pub fn new_table(&mut self) -> Value {
        self.tables.push(Table::new());
        Value::Table(self.tables.last_mut().unwrap().into())
    }
}

#[derive(Debug, Clone, Default)]
pub struct Table(pub(crate) HashMap<Value, Value>);
impl Table {
    pub fn new() -> Self {
        Self(HashMap::new())
    }
    pub fn get(&self, value: &Value) -> &Value {
        if let Some(value) = self.0.get(value) {
            value
        } else {
            &Constant(Nil)
        }
    }
    pub fn set(&mut self, key: Value, value: Value) {
        if let Constant(Nil) = value {
            self.0.remove(&key);
        } else {
            self.0.insert(key, value);
        }
    }
}
