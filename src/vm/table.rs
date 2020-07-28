use std::collections::HashMap;
use super::*;
#[derive(Debug)]
pub struct Table(
    HashMap<Value, Value>
);
impl Table {
    pub fn new() -> Self {
        Self(HashMap::new())
    }
    pub fn get(&self, value: &Value) -> &Value {
        if let Some(value) = self.0.get(value) {
            value
        }
        else {
            &Value::Nil
        }
    }
    pub fn set(&mut self, key: Value, value: Value) {
        if let Value::Nil = value {
            self.0.remove(&key);
        }
        else {
            self.0.insert(key, value);
        }
    }
}
