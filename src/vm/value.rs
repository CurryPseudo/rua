use crate::*;

pub type ExportLuaFunction = fn(Vec<Value>) -> Vec<Value>;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Value {
    Number(Integer),
    String(String),
    Boolean(bool),
    LuaFunction(ExportLuaFunction),
    Nil,
}
impl Value {
    pub fn is_nil(&self) -> bool {
        match self {
            Self::Nil => true,
            _ => false
        }
    }
    pub fn type_name(&self) -> &'static str {
        match self {
            Self::Number(_) => "number",
            Self::String(_) => "string",
            Self::Boolean(_) => "boolean",
            Self::LuaFunction(_) => "function",
            Self::Nil => "nil",
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
            },
            Self::Nil => "nil".to_string(),
            Self::LuaFunction(_) => "function".to_string()
        }
    }
}
impl AsRef<bool> for Value {
    fn as_ref(&self) -> &bool {
        if self.is_nil() {
            &false
        }
        else if let Value::Boolean(b) = self {
            b
        }
        else {
            &true
        }
    }
}

impl std::ops::Add<&Value> for &Value {
    type Output = Value;
    fn add(self, rhs: &Value) -> Value {
        match self {
            Value::Number(x) => match rhs {
                Value::Number(y) => {
                    return Value::Number(x + y);
                }
                _ => (),
            },
            _ => (),
        }
        panic!("try to add a {:?} with {:?}", self.type_name(), rhs.type_name());
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
            }
            Value::String(x) => match rhs {
                Value::String(y) => {
                    return Some(x.cmp(&y));
                }
                _ => (),
            }
            _ => ()
        }
        panic!("try to compare a {:?} with {:?}", self.type_name(), rhs.type_name());
    }
}
