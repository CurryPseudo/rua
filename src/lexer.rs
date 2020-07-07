use logos::Lexer;
pub use logos::Logos;
use enum_as_inner::EnumAsInner;
use strum_macros::{IntoStaticStr, EnumVariantNames};

#[derive(Logos, Debug, PartialEq, EnumAsInner, IntoStaticStr, EnumVariantNames)]
#[allow(non_camel_case_types)]
pub enum Token {
    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*", same)]
    ID(String),
    #[token(",")]
    COMMA,
    #[token("(")]
    LEFT_BRACKET,
    #[token(")")]
    RIGHT_BRACKET,
    #[regex(r"[0-9]+", number)]
    NUMBER(i32),
    #[token("local")]
    LOCAL,
    #[token("=")]
    EQUAL,
    #[token("+")]
    ADD,
    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    ERROR
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
    assert_eq!(lex.next(), Some(Token::ID(String::from("print"))));
    assert_eq!(lex.next(), Some(Token::LEFT_BRACKET));
    assert_eq!(lex.next(), Some(Token::NUMBER(1)));
    assert_eq!(lex.next(), Some(Token::RIGHT_BRACKET));
    assert_eq!(lex.next(), Some(Token::ID(String::from("print"))));
    assert_eq!(lex.next(), Some(Token::LEFT_BRACKET));
    assert_eq!(lex.next(), Some(Token::NUMBER(2)));
    assert_eq!(lex.next(), Some(Token::RIGHT_BRACKET));
}
