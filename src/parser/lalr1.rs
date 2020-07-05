use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
pub trait ToTerminalName {
    fn to_terminal_name(&self) -> &'static str;
}
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
enum Symbol {
    NonTerminal(usize),
    Terminal(usize),
}
use Symbol::*;
#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
enum TerminalSymbol {
    Normal(usize),
    End,
}
use TerminalSymbol::*;

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
enum Action {
    MoveIn(usize),
    Reduce(usize, usize),
    Finish,
    Error
}
use Action::*;

#[derive(Debug)]
struct Grammar {
    action: Vec<Vec<Action>>,
    goto: Vec<Vec<Option<usize>>>
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
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
    fn acc(self) -> Self {
        Self {
            production_index: self.production_index,
            position: self.position + 1,
        }
    }
}

impl Grammar {
    fn new(
        terminals: &[&'static str],
        non_terminals: &[&'static str],
        split_productions: Vec<(usize, Vec<Vec<Symbol>>)>,
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
        let mut g = Vec::new();
        let mut g_map = HashMap::new();
        let mut goto_symbol = Vec::new();
        let get_symbol = |item: &Item| -> Option<&Symbol> {
            let production = &productions[item.production_index];
            if item.position < production.right.len() {
                Some(&production.right[item.position])
            } else {
                None
            }
        };
        let to_name = |symbol: &Symbol| -> &'static str {
            match symbol {
                NonTerminal(s) => non_terminals[*s],
                Terminal(s) => terminals[*s],
            }
        };
        debug!("{}", str_join(terminals.iter().copied()));
        for production in &productions {
            debug!(
                "{} -> {}",
                non_terminals[production.left],
                str_join(production.right.iter().map(|right| to_name(right)))
            );
        }
        let closure = |items: Vec<Item>| -> Vec<Item> {
            let mut results = Vec::new();
            dfs(items, |item| {
                results.push(item);
                let mut nexts = Vec::new();
                if let Some(NonTerminal(y)) = get_symbol(&item) {
                    for z in &non_terminal_to_production[*y] {
                        nexts.push(Item::new(*z, 0));
                    }
                }
                nexts
            });
            results
        };
        let mut goto = HashMap::new();
        {
            let begin_production_closure = vec![Item::new(0, 0)];
            g_map.insert(begin_production_closure.clone(), 0);
            g.push(begin_production_closure.clone());
            goto_symbol.push(Vec::new());
            dfs(vec![(0, begin_production_closure)], |(index, items)| {
                let closure = closure(items);
                let mut current_goto = HashMap::new();
                for i in closure {
                    if let Some(symbol) = get_symbol(&i) {
                        let v = current_goto.entry(symbol).or_insert_with(Vec::new);
                        v.push(i.acc());
                    }
                }
                let mut result = Vec::new();
                for (symbol, mut i) in current_goto {
                    i.sort();
                    let to = if let Some(to) = g_map.get(&i) {
                        *to
                    } else {
                        let to = g.len();
                        result.push((to, i.clone()));
                        g_map.insert(i.clone(), to);
                        g.push(i);
                        goto_symbol.push(Vec::new());
                        to
                    };
                    goto.insert((index, *symbol), to);
                    goto_symbol[index].push(*symbol);
                }
                result
            });
        }
        let mut first = vec![HashSet::new(); non_terminals.len()];
        {
            let mut first_propagate_map = vec![HashSet::new(); non_terminals.len()];
            for production in &productions {
                if let Some(NonTerminal(s)) = production.right.first() {
                    first_propagate_map[*s].insert(production.left);
                }
            }
            dfs(
                {
                    let mut begins = Vec::new();
                    for production in &productions {
                        if let Some(Terminal(s)) = production.right.first() {
                            begins.push((production.left, *s));
                        }
                    }
                    begins
                },
                |(non_terminal, first_terminal)| {
                    first[non_terminal].insert(first_terminal);
                    first_propagate_map[non_terminal]
                        .iter()
                        .map(|to| (*to, first_terminal))
                        .collect()
                },
            );
        }
        let mut lalr_generated_terminal = vec![HashSet::new(); g.len()];
        let mut lalr_propagated_path = vec![HashSet::new(); g.len()];
        {
            let mut item_to_state = HashMap::new();
            for (i, g) in g.iter().enumerate() {
                for item in closure(g.clone()) {
                    item_to_state.entry(item).or_insert_with(Vec::new).push(i);
                }
            }
            for i in 0..g.len() {
                dfs(
                    g[i].iter().map(|item| (None, *item)).collect(),
                    |(option_terminals, item)| {
                        if let Some(symbol) = get_symbol(&item) {
                            let state = goto[&(i, *symbol)];
                            if let Some(terminal) = option_terminals {
                                lalr_generated_terminal[state].insert(terminal);
                            } else {
                                lalr_propagated_path[i].insert(state);
                            }
                        }
                        let mut next = Vec::new();
                        if let Some(NonTerminal(non_terminal)) = get_symbol(&item) {
                            let look_forward_symbols = if let Some(symbol) =
                                get_symbol(&item.clone().acc())
                            {
                                match symbol {
                                    NonTerminal(s) => first[*s].iter().map(|s| Some(*s)).collect(),
                                    Terminal(s) => vec![Some(*s)],
                                }
                            } else {
                                vec![option_terminals]
                            };
                            for look_forward_symbol in &look_forward_symbols {
                                for production in &non_terminal_to_production[*non_terminal] {
                                    next.push((*look_forward_symbol, Item::new(*production, 0)));
                                }
                            }
                        }
                        next
                    },
                );
            }
        }
        let mut look_forward_terminal = vec![HashSet::new(); g.len()];
        dfs(
            {
                let mut begin = Vec::new();
                for (i, generateds) in lalr_generated_terminal.iter().enumerate() {
                    for generated in generateds {
                        begin.push((i, Normal(*generated)));
                    }
                }
                begin.push((0, End));
                begin
            },
            |(i, terminal)| {
                look_forward_terminal[i].insert(terminal);
                lalr_propagated_path[i]
                    .iter()
                    .map(|propagated| (*propagated, terminal))
                    .collect()
            },
        );
        debug!("LR(0):");
        for i in 0..g.len() {
            let items = &g[i];
            debug!("I{}", i);
            let print_production = |item: &Item| {
                let production = &productions[item.production_index];
                format!(
                    "{} -> {}",
                    non_terminals[production.left],
                    str_join((0..production.right.len() + 1).map(|i| {
                        use std::cmp::Ordering::*;
                        match i.cmp(&item.position) {
                            Less => to_name(&production.right[i]),
                            Equal => ".",
                            Greater => to_name(&production.right[i - 1]),
                        }
                    }))
                )
            };
            for item in items {
                debug!("{}", print_production(item));
            }
            for item in closure(items.clone())
                .iter()
                .filter(|item| !items.iter().any(|x| &x == item))
            {
                debug!("* {}", print_production(item));
            }
            for symbol in &goto_symbol[i] {
                debug!(
                    "{} => I{}",
                    to_name(symbol),
                    goto.get(&(i, *symbol)).unwrap()
                );
            }
            debug!(
                "generated {}",
                str_join(
                    lalr_generated_terminal[i]
                        .iter()
                        .map(|terminal| terminals[*terminal])
                )
            );
            debug!(
                "propagated {}",
                str_join(
                    lalr_propagated_path[i]
                        .iter()
                        .map(|state| format!("I{}", state))
                )
            );
            debug!(
                "final {}",
                str_join(look_forward_terminal[i].iter().map(|terminal| {
                    match terminal {
                        End => "$",
                        Normal(t) => terminals[*t],
                    }
                }))
            );
        }
        for i in 0..first.len() {
            debug!(
                "first({}) = {}",
                non_terminals[i],
                str_join(first[i].iter().map(|first| terminals[*first]))
            );
        }
        let mut action_table = vec![vec![Error; terminals.len() + 1]; g.len()];
        let mut goto_table = vec![vec![None; non_terminals.len()]; g.len()];
        for i in 0..g.len() {
            for j in 0..terminals.len() {
                let mut has_goto = false;
                if let Some(k) = goto.get(&(i, Terminal(j))) {
                    has_goto = true;
                    action_table[i][j] = MoveIn(*k);
                }
                if look_forward_terminal[i].contains(&Normal(j)) {
                    let mut reduce = None;
                    for item in &g[i] {
                        let production = &productions[item.production_index];
                        if production.right.len() == item.position {
                            if reduce.is_none() {
                                reduce = Some(Reduce(production.left, production.right.len()));
                            }
                            else {
                                panic!("Reduce/reduce conflict");
                            }
                        }
                    }
                    if let Some(reduce) = reduce {
                        if has_goto {
                            panic!("Move-in/reduce conflict");
                        }
                        action_table[i][j] = reduce;
                    }
                }
            }
            for item in &g[i] {
                let production = &productions[item.production_index];
                if production.left == 0 && item.position == 1 {
                    action_table[i][terminals.len()] = Finish;
                    break;
                }
            }
            for j in 0..non_terminals.len() {
                if let Some(k) = goto.get(&(i, NonTerminal(j))) {
                    goto_table[i][j] = Some(*k);
                }
            }
       }
        Self {
            action: action_table,
            goto: goto_table
        }
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
                static ref GRAMMAR: Grammar = {
                    Grammar::new(
                            &[$(stringify!($terminals)),+],
                            &["S'", $(stringify!($left)),+],
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
                            ]
                        )
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
            fn grammar() -> &'static Grammar {
                &GRAMMAR
            }
            impl $parser_name {
                pub fn new() -> Self {
                    println!("{:#?}", grammar());
                    Self {}
                }
            }
        }
    };
}
fn str_join<I: Iterator<Item = S>, S: ToString>(mut iter: I) -> String {
    let mut r = String::new();
    if let Some(i) = iter.next() {
        r.push_str(&i.to_string());
    }
    for i in iter {
        r.push(' ');
        r.push_str(&i.to_string());
    }
    r
}
fn dfs<T: Hash + PartialEq + Eq + Clone, N: FnMut(T) -> Vec<T>>(begins: Vec<T>, mut n: N) {
    let mut added = HashSet::new();
    let mut to_addeds = begins;
    for to_added in &to_addeds {
        added.insert(to_added.clone());
    }
    while let Some(x) = to_addeds.pop() {
        let nexts = n(x);
        for next in nexts {
            if added.insert(next.clone()) {
                to_addeds.push(next);
            }
        }
    }
}
#[test]
fn test_parser() {
    parser!(
        ParserName: LuaParser;
        Terminals: *, id, =;
        S -> L, =, R | R;
        L -> *, R | id;
        R -> L
    );
    //parser!(
    //    ParserName: LuaParser;
    //    Terminals: c, d;
    //    S -> C, C;
    //    C -> c, C | d
    //);
    //parser!(
    //    ParserName: LuaParser;
    //    Terminals: id, comma, left_bracket, right_bracket, number;
    //    Function -> id, left_bracket, ParamList, right_bracket;
    //    ParamList -> number, comma, ParamList | number
    //);
    let _ = pretty_env_logger::init();
    let parser = LuaParser::new();
}
