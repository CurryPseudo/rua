#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Value {
    Number(i32),
    String(String),
    LuaFunction(usize),
    None,
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Self::Number(x) => x.to_string(),
            Self::String(s) => s.clone(),
            _ => unimplemented!()
        }
    }
}

impl std::ops::Add<&Value> for &Value {
    type Output = Value;
    fn add(self, rhs: &Value) -> Value {
        match self {
            Value::Number(x) => {
                match rhs {
                    Value::Number(y) => {
                        return Value::Number(x + y);
                    }
                    _ => ()
                }
            }
            Value::String(x) => {
                match rhs {
                    Value::String(y) => {
                        return Value::String(format!("{}{}", x, y));
                    }
                    _ => ()
                }
            }
            _ => ()
        }
        panic!("try to add a {:?} with {:?}", self, rhs);
    }
}
