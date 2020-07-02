use logos::Lexer;
use logos::Logos;

#[derive(Logos, Debug, PartialEq)]
pub enum Token {
    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*", same)]
    Id(String),
    #[token(",")]
    Comma,
    #[token("(")]
    LeftBracket,
    #[token(")")]
    RightBracket,
    #[regex(r"[0-9]+", number)]
    Number(i32),
    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Error
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
    assert_eq!(lex.next(), Some(Token::Id(String::from("print"))));
    assert_eq!(lex.next(), Some(Token::LeftBracket));
    assert_eq!(lex.next(), Some(Token::Number(1)));
    assert_eq!(lex.next(), Some(Token::RightBracket));
    assert_eq!(lex.next(), Some(Token::Id(String::from("print"))));
    assert_eq!(lex.next(), Some(Token::LeftBracket));
    assert_eq!(lex.next(), Some(Token::Number(2)));
    assert_eq!(lex.next(), Some(Token::RightBracket));
}
