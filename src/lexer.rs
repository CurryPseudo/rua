use logos::Lexer;
pub use logos::Logos;
use enum_as_inner::EnumAsInner;
use strum_macros::{IntoStaticStr, EnumVariantNames};

#[derive(Logos, Debug, PartialEq, EnumAsInner, IntoStaticStr, EnumVariantNames)]
#[allow(non_camel_case_types)]
pub enum Token {
    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*", same)]
    id(String),
    #[token(",")]
    comma,
    #[token("(")]
    left_bracket,
    #[token(")")]
    right_bracket,
    #[regex(r"[0-9]+", number)]
    number(i32),
    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    error
}

fn same(lex: &mut Lexer<Token>) -> String {
    String::from(lex.slice())
}

fn number(lex: &mut Lexer<Token>) -> i32 {
    let mut sum = 0;
    for c in lex.slice().bytes() {
        sum = sum * 10 + (c - b'0') as i32;
    }
    sum
}

#[test]
fn test_lexer() {
    let mut lex = Token::lexer("print(1)\nprint(2)");
    assert_eq!(lex.next(), Some(Token::id(String::from("print"))));
    assert_eq!(lex.next(), Some(Token::left_bracket));
    assert_eq!(lex.next(), Some(Token::number(1)));
    assert_eq!(lex.next(), Some(Token::right_bracket));
    assert_eq!(lex.next(), Some(Token::id(String::from("print"))));
    assert_eq!(lex.next(), Some(Token::left_bracket));
    assert_eq!(lex.next(), Some(Token::number(2)));
    assert_eq!(lex.next(), Some(Token::right_bracket));
}
