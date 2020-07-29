use crate::*;
use std::fmt::*;
use std::hash::*;

#[derive(Clone)]
pub struct ExportLuaFunction {
    name: &'static str,
    func: fn(&[Value]) -> Vec<Value>,
}

impl ExportLuaFunction {
    pub fn new(name: &'static str, func: fn(&[Value]) -> Vec<Value>) -> Self {
        Self { name, func }
    }
    pub fn name(&self) -> &'static str {
        self.name
    }
    pub fn evaluate(&self, args: &[Value]) -> Vec<Value> {
        (self.func)(args)
    }
}

impl PartialEq for ExportLuaFunction {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for ExportLuaFunction {}

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
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Value {
    Number(Integer),
    String(String),
    Boolean(bool),
    LuaFunction(ExportLuaFunction),
    Table(usize),
    Nil,
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
    pub fn as_number(&self) -> Integer {
        match self {
            Self::Number(n) => *n,
            _ => panic!("Attempt to do numberic operation on {}", self.type_name())
        }
    }
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Self::Number(x) => x.to_string(),
            Self::String(s) => s.clone(),
            Self::Boolean(b) => {
                if *b {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            Self::Table(id) => format!("table: {}", id),
            Self::Nil => "nil".to_string(),
            Self::LuaFunction(_) => "function".to_string(),
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

fn numeric_binary_op(lhs: &Value, rhs: &Value, op_name: &'static str, f: fn(&Integer, &Integer) -> Integer) -> Value {
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
