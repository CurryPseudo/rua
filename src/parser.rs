use nom::sequence::delimited;
use crate::*;
use nom::bytes::complete::take_while1;
use nom::character::complete::char;
use nom::character::complete::line_ending;
use nom::multi::many0;
use nom::sequence::tuple;
use nom::IResult;
use std::collections::HashMap;
#[derive(Debug, PartialEq, Eq)]
struct FunctionParseResult<'a> {
    name: &'a str,
    args: i32,
}
fn number(input: &str) -> IResult<&str, i32> {
    let (input, x) = take_while1(|c| c <= '9' && c >= '0')(input)?;
    let mut sum = 0;
    for d in x.chars() {
        sum = sum * 10 + (d as i32 - '0' as i32);
    }
    Ok((input, sum))
}
fn space_and_line(input: &str) -> IResult<&str, ()> {
    let (input, _) = many0!(input, alt!(eof!() | tag!(" ") | line_ending))?;
    Ok((input, ()))
}
fn function(input: &str) -> IResult<&str, FunctionParseResult> {
    let name = take_while1(|c| c != '(');
    let args = delimited(char('('), number, char(')'));
    let (input, (_, name, args)) = tuple((space_and_line, name, args))(input)?;
    Ok((input, FunctionParseResult { name, args }))
}

#[test]
fn test_function() {
    assert_eq!(
        function("print(123)"),
        Ok((
            "",
            FunctionParseResult {
                name: "print",
                args: 123
            }
        ))
    );
}

#[derive(Default)]
pub struct FunctionStack {
    pub variable_count: u32,
    free_variable_index: u32,
    pub constants: Vec<Value>,
    pub instructions: Vec<Instruction>,
    constant_map: HashMap<Value, u32>,
}

impl FunctionStack {
    fn get_free_variable_index(&mut self) -> u32 {
        if self.free_variable_index <= self.variable_count {
            self.variable_count += 1;
        }
        let t = self.free_variable_index;
        self.free_variable_index += 1;
        t
    }
    fn get_constant_index(&mut self, value: &Value) -> u32 {
        if let Some(index) = self.constant_map.get(value) {
            *index
        } else {
            let index = self.constants.len() as u32;
            self.constant_map.insert(value.clone(), index);
            self.constants.push(value.clone());
            index
        }
    }
    fn get_constant_rk_index(&mut self, value: &Value) -> i32 {
        -1 - self.get_constant_index(value) as i32
    }
    fn add_statement(&mut self, function_parse_result: FunctionParseResult) {
        let name = Value::String(String::from(function_parse_result.name));
        let r0 = self.get_free_variable_index();
        let k0 = self.get_constant_rk_index(&name) as i32;
        self.instructions.push(Instruction::GetTabUp(r0, 0, k0));
        let r1 = self.get_free_variable_index();
        let k1 = self.get_constant_index(&Value::Number(function_parse_result.args));
        self.instructions.push(Instruction::LoadK(r1, k1));
        self.instructions.push(Instruction::Call(r0, 2, 1));
        self.free_variable_index -= 2;
    }
    pub fn from_statements(input: &str) -> Self {
        let (_, parse_results) = many0(function)(input).unwrap();
        let mut r = Self::default();
        for statement in parse_results {
            r.add_statement(statement);
        }
        r
    }
}
