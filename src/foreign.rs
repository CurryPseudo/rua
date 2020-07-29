use crate::*;
#[derive(Clone)]
pub struct Foreign {
    pub pre: Vec<&'static str>,
    pub func: ExportLuaFunction,
}

macro_rules! foreign {
    ($($pre:tt).+ = $func:expr ) => {
        {
            let pre = vec![$(stringify!($pre)),+];
            let name = pre.last().unwrap().clone();
            Foreign {
                pre: pre,
                func: ExportLuaFunction::new(name, $func)
            }
        }
    };
}
