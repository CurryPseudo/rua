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
