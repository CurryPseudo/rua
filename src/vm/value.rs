#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Value {
    Number(i32),
    String(String),
    Boolean(bool),
    LuaFunction(usize),
    Nil,
}
impl Value {
    pub fn is_nil(&self) -> bool {
        match self {
            Nil => true,
            _ => false
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
            _ => unimplemented!(),
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
        panic!("try to add a {:?} with {:?}", self, rhs);
    }
}
