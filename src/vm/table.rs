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
        self.0.get(value).unwrap()
    }
    pub fn set(&mut self, key: Value, value: Value) {
        self.0.insert(key, value);
    }
}
