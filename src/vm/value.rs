use std::{
    fmt::Display,
    hash::{Hash, Hasher},
};

use crate::*;

#[derive(Clone)]
pub struct ExportLuaFunction {
    name: &'static str,
    func: fn(Vec<Value>) -> Result<Vec<Value>, RuntimeError>,
}

impl ExportLuaFunction {
    pub fn new(
        name: &'static str,
        func: fn(Vec<Value>) -> Result<Vec<Value>, RuntimeError>,
    ) -> Self {
        Self { name, func }
    }
    pub fn name(&self) -> &'static str {
        self.name
    }
    pub fn evaluate(&self, args: Vec<Value>) -> Result<Vec<Value>, RuntimeError> {
        (self.func)(args)
    }
}

impl PartialEq for ExportLuaFunction {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for ExportLuaFunction {}

impl std::fmt::Display for ExportLuaFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}
impl std::fmt::Debug for ExportLuaFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl std::hash::Hash for ExportLuaFunction {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Value {
    Number(Integer),
    String(String),
    Boolean(bool),
    LuaFunction(ExportLuaFunction),
    Table(*mut Table),
    Nil,
}

impl Default for Value {
    fn default() -> Self {
        Self::Nil
    }
}

impl Value {
    pub fn is_nil(&self) -> bool {
        match self {
            Self::Nil => true,
            _ => false,
        }
    }
    pub fn type_name(&self) -> &'static str {
        match self {
            Self::Number(_) => "number",
            Self::String(_) => "string",
            Self::Boolean(_) => "boolean",
            Self::LuaFunction(_) => "function",
            Self::Table(_) => "table",
            Self::Nil => "nil",
        }
    }
    pub fn expect_number(self) -> Result<Integer, RuntimeError> {
        match self {
            Self::Number(n) => Ok(n),
            _ => Err(RuntimeError::TypeError(self, "number")),
        }
    }
    pub fn expect_function(self) -> Result<ExportLuaFunction, RuntimeError> {
        match self {
            Self::LuaFunction(f) => Ok(f),
            _ => Err(RuntimeError::TypeError(self, "function")),
        }
    }
    pub fn expect_table<'a>(self) -> Result<&'a mut Table, RuntimeError> {
        match self {
            Self::Table(t) => Ok(unsafe { t.as_mut() }.unwrap()),
            _ => Err(RuntimeError::TypeError(self, "table")),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(x) => write!(f, "{}", x),
            Self::String(s) => write!(f, "{}", s),
            Self::Boolean(b) => {
                if *b {
                    write!(f, "true")
                } else {
                    write!(f, "false")
                }
            }
            Self::Table(table_ptr) => write!(f, "table {}", *table_ptr as usize),
            Self::Nil => write!(f, "nil"),
            Self::LuaFunction(func) => write!(f, "function {}", func),
        }
    }
}
impl AsRef<bool> for Value {
    fn as_ref(&self) -> &bool {
        if self.is_nil() {
            &false
        } else if let Value::Boolean(b) = self {
            b
        } else {
            &true
        }
    }
}

fn numeric_binary_op(
    lhs: &Value,
    rhs: &Value,
    op_name: &'static str,
    f: fn(&Integer, &Integer) -> Integer,
) -> Value {
    match lhs {
        Value::Number(x) => match rhs {
            Value::Number(y) => {
                return Value::Number(f(x, y));
            }
            _ => (),
        },
        _ => (),
    }
    panic!(
        "Attempt to {} a {:?} with {:?}",
        op_name,
        lhs.type_name(),
        rhs.type_name()
    );
}

impl std::ops::Add<&Value> for &Value {
    type Output = Value;
    fn add(self, rhs: &Value) -> Value {
        numeric_binary_op(self, rhs, "add", |x, y| x + y)
    }
}
impl std::ops::Mul<&Value> for &Value {
    type Output = Value;
    fn mul(self, rhs: &Value) -> Value {
        numeric_binary_op(self, rhs, "mul", |x, y| x * y)
    }
}
impl PartialOrd<Self> for Value {
    fn partial_cmp(&self, rhs: &Self) -> Option<std::cmp::Ordering> {
        match self {
            Value::Number(x) => match rhs {
                Value::Number(y) => {
                    return Some(x.cmp(&y));
                }
                _ => (),
            },
            Value::String(x) => match rhs {
                Value::String(y) => {
                    return Some(x.cmp(&y));
                }
                _ => (),
            },
            _ => (),
        }
        panic!(
            "Attempt to compare a {:?} with {:?}",
            self.type_name(),
            rhs.type_name()
        );
    }
}
