use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Display;
use std::hash::Hash;
pub trait ToTerminalName {
    fn to_terminal_name(&self) -> &'static str;
}
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
enum Symbol {
    NonTerminal(usize),
    Terminal(usize),
}
use Symbol::*;
#[derive(Debug)]
struct Grammar {
    productions: Vec<Production>,
    non_terminal_to_production: Vec<Vec<usize>>,
    terminal_count: usize,
    non_terminal_count: usize,
    g: Vec<Vec<Item>>,
    g_map: HashMap<Vec<Item>, usize>,
    goto: HashMap<(usize, Symbol), usize>,
    goto_symbol: Vec<Vec<Symbol>>
}

#[derive(Clone, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
struct Item {
    production_index: usize,
    position: usize,
}
impl Item {
    fn new(production_index: usize, position: usize) -> Self {
        Self {
            production_index,
            position,
        }
    }
}

impl Grammar {
    fn new(
        split_productions: Vec<(usize, Vec<Vec<Symbol>>)>,
        terminal_count: usize,
        non_terminal_count: usize,
    ) -> Self {
        let mut productions = Vec::new();
        let mut non_terminal_to_production = Vec::new();
        for (left, rights) in split_productions {
            let mut non_terminal_map = Vec::new();
            for right in rights {
                non_terminal_map.push(productions.len());
                productions.push(Production { left, right });
            }
            non_terminal_to_production.push(non_terminal_map);
        }
        let mut r = Self {
            productions,
            non_terminal_to_production,
            terminal_count,
            non_terminal_count,
            g: Vec::new(),
            g_map: HashMap::new(),
            goto: HashMap::new(),
            goto_symbol: Vec::new()
        };
        let begin_production_closure = vec![Item::new(0, 0)];
        r.g_map.insert(begin_production_closure.clone(), 0);
        r.g.push(begin_production_closure.clone());
        r.goto_symbol.push(Vec::new());
        let mut new_adds = vec![(0, begin_production_closure)];
        while !new_adds.is_empty() {
            let mut temp = Vec::new();
            for (index, new_add) in new_adds {
                let c = r.closure(new_add);
                let mut goto = HashMap::new();
                for i in c {
                    if let Some(symbol) = r.get_symbol(&i) {
                        let v = goto.entry(symbol.clone()).or_insert(Vec::new());
                        v.push(Item::new(i.production_index, i.position + 1));
                    }
                }
                for (symbol, mut i) in goto {
                    i.sort();
                    let to = if let Some(to) = r.g_map.get(&i) {
                        *to
                    } else {
                        let to = r.g.len();
                        temp.push((to, i.clone()));
                        r.g_map.insert(i.clone(), to);
                        r.g.push(i);
                        r.goto_symbol.push(Vec::new());
                        to
                    };
                    r.goto.insert((index, symbol.clone()), to);
                    r.goto_symbol[index].push(symbol.clone());
                }
            }
            new_adds = temp;
        }
        r
    }
    fn get_symbol(&self, item: &Item) -> Option<&Symbol> {
        let production = &self.productions[item.production_index];
        if item.position < production.right.len() {
            Some(&production.right[item.position])
        } else {
            None
        }
    }
    fn closure(&self, items: Vec<Item>) -> Vec<Item> {
        let mut added = items.clone().into_iter().collect::<HashSet<_>>();
        let mut new_add = items;
        while !new_add.is_empty() {
            let mut temp = Vec::new();
            for x in new_add {
                if let Some(NonTerminal(y)) = self.get_symbol(&x) {
                    for z in &self.non_terminal_to_production[*y] {
                        let item = Item::new(*z, 0);
                        if !added.contains(&item) {
                            temp.push(item.clone());
                            added.insert(item);
                        }
                    }
                }
            }
            new_add = temp;
        }
        added.into_iter().collect()
    }
    fn kernel(&self, items: Vec<Item>) -> Vec<Item> {
        items
            .into_iter()
            .filter(|item| {
                if item.position != 0 {
                    true
                } else {
                    item.production_index == 0
                }
            })
            .collect()
    }
}
struct DisplayGrammar {
    terminals: Vec<&'static str>,
    non_terminals: Vec<&'static str>,
    grammar: Grammar,
}
impl DisplayGrammar {
    fn to_name(&self, symbol: &Symbol) -> &'static str {
        match symbol {
            NonTerminal(s) => self.non_terminals[*s],
            Terminal(s) => self.terminals[*s],
        }
    }
}
impl Display for DisplayGrammar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        for production in &self.grammar.productions {
            write!(f, "{} -> ", self.non_terminals[production.left],)?;
            for right in &production.right {
                write!(f, "{} ", self.to_name(right))?;
            }
            writeln!(f);
        }
        writeln!(f, "LR(0):");
        for i in 0..self.grammar.g.len() {
            let items = &self.grammar.g[i];
            writeln!(f, "I{}", i);
            for item in self.grammar.closure(items.clone()) {
                let production = &self.grammar.productions[item.production_index];
                write!(f, "{} -> ", self.non_terminals[production.left]);
                for j in 0..production.right.len() + 1 {
                    if j == item.position {
                        write!(f, ". ");
                    }
                    if j < production.right.len() {
                        write!(f, "{} ", self.to_name(&production.right[j]));
                    }
                }
                writeln!(f);
            }
            for symbol in &self.grammar.goto_symbol[i] {
                write!(f, "{} => ", self.to_name(symbol));
                writeln!(f, "I{}", self.grammar.goto.get(&(i, symbol.clone())).unwrap());
            }
        }
        Ok(())
    }
}
#[derive(Debug)]
struct Production {
    left: usize,
    right: Vec<Symbol>,
}
macro_rules! parser {
    (
     ParserName: $parser_name:tt;
     Terminals: $($terminals:tt),+;
     $($left:tt -> $($($right:tt),+)|+);+
     ) => {
        pub struct $parser_name {}
        {
            lazy_static! {
                static ref TERMINAL_MAP: HashMap<&'static str, usize> = {
                    let mut r = HashMap::new();
                    $({
                        let len = r.len() as usize;
                        r.insert(stringify!($terminals), len);
                      }
                    )+
                    r
                };
            }
            lazy_static! {
                static ref NON_TERMINAL_MAP: HashMap<&'static str, usize> = {
                    let mut r = HashMap::new();
                    $({
                        let len = r.len() as usize;
                        r.insert(stringify!($left), len + 1);
                      }
                    )+
                    r
                };
            }
            lazy_static! {
                static ref GRAMMAR: DisplayGrammar = {
                    DisplayGrammar {
                        terminals: vec![$(stringify!($terminals)),+],
                        non_terminals: vec!["S'", $(stringify!($left)),+],
                        grammar: Grammar::new(
                            vec![
                                    (
                                        0,
                                        vec![vec![NonTerminal(1)]]
                                    ),
                                $(
                                    (
                                        *NON_TERMINAL_MAP.get(stringify!($left)).unwrap(),
                                        vec![$(vec![$(
                                            name_to_symbol(stringify!($right)).unwrap()
                                        ),+]),+]
                                    )
                                ),+
                            ],
                            TERMINAL_MAP.len(),
                            NON_TERMINAL_MAP.len() + 1
                        )
                    }
                };
            }
            fn name_to_symbol(s: &str) -> Option<Symbol> {
                if let Some(non_terminal) = NON_TERMINAL_MAP.get(s) {
                    Some(NonTerminal(*non_terminal))
                } else if let Some(terminal) = TERMINAL_MAP.get(s) {
                    Some(Terminal(*terminal))
                }
                else {
                    None
                }
            }
            impl $parser_name {
                pub fn new() -> Self {
                    Self {}
                }
                pub fn grammar(&self) -> &DisplayGrammar {
                    &GRAMMAR
                }
            }
        }
    };
}
#[test]
fn test_parser() {
    //parser!(
    //    ParserName: LuaParser;
    //    Terminals: c, d;
    //    S -> C, C;
    //    C -> c, C | d
    //);
    parser!(
        ParserName: LuaParser;
        Terminals: id, comma, left_bracket, right_bracket, number;
        Function -> id, left_bracket, ParamList, right_bracket;
        ParamList -> number, comma, ParamList | number
    );
    let parser = LuaParser::new();
    println!("{}", parser.grammar());
}
