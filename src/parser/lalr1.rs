use std::collections::HashMap;
use std::collections::HashSet;
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
        debug!("{}", str_join(terminals.iter().map(|s| *s)));
        for production in &productions {
            debug!(
                "{} -> {}",
                non_terminals[production.left],
                str_join(production.right.iter().map(|right| to_name(right)))
            );
        }
        let closure = |items: Vec<Item>| -> Vec<Item> {
            let mut added = items.clone().into_iter().collect::<HashSet<_>>();
            let mut new_add = items;
            while !new_add.is_empty() {
                let mut temp = Vec::new();
                for x in new_add {
                    if let Some(NonTerminal(y)) = get_symbol(&x) {
                        for z in &non_terminal_to_production[*y] {
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
        };
        let mut goto = HashMap::new();
        {
            let begin_production_closure = vec![Item::new(0, 0)];
            g_map.insert(begin_production_closure.clone(), 0);
            g.push(begin_production_closure.clone());
            goto_symbol.push(Vec::new());
            let mut new_adds = vec![(0, begin_production_closure)];
            while !new_adds.is_empty() {
                let mut temp = Vec::new();
                for (index, new_add) in new_adds {
                    let c = closure(new_add);
                    let mut current_goto = HashMap::new();
                    for i in c {
                        if let Some(symbol) = get_symbol(&i) {
                            let v = current_goto.entry(symbol.clone()).or_insert_with(Vec::new);
                            v.push(i.acc());
                        }
                    }
                    for (symbol, mut i) in current_goto {
                        i.sort();
                        let to = if let Some(to) = g_map.get(&i) {
                            *to
                        } else {
                            let to = g.len();
                            temp.push((to, i.clone()));
                            g_map.insert(i.clone(), to);
                            g.push(i);
                            goto_symbol.push(Vec::new());
                            to
                        };
                        goto.insert((index, symbol.clone()), to);
                        goto_symbol[index].push(symbol.clone());
                    }
                }
                new_adds = temp;
            }
        }
        let mut first = vec![HashSet::new(); non_terminal_count];
        {
            let mut first_propagate_map = vec![HashSet::new(); non_terminal_count];
            for production in &productions {
                if let Some(NonTerminal(s)) = production.right.first() {
                    first_propagate_map[*s].insert(production.left);
                }
            }
            let mut new_added = Vec::new();
            for production in &productions {
                if let Some(Terminal(s)) = production.right.first() {
                    new_added.push((production.left, *s));
                    first[production.left].insert(*s);
                }
            }
            while !new_added.is_empty() {
                let mut temp = Vec::new();
                for (non_terminal, first_terminal) in new_added {
                    for to in &first_propagate_map[non_terminal] {
                        if first[*to].insert(first_terminal) {
                            temp.push((*to, first_terminal));
                        }
                    }
                }
                new_added = temp;
            }
        }
        let mut lalr_generated_terminal = vec![HashSet::new(); g.len()];
        let mut lalr_propagated_path = vec![HashSet::new(); g.len()];
        {
            let mut item_to_state = HashMap::new();
            for (i, g) in g.iter().enumerate() {
                for item in &closure(g.clone()) {
                    item_to_state
                        .entry(item.clone())
                        .or_insert_with(Vec::new)
                        .push(i);
                }
            }
            for i in 0..g.len() {
                let mut added = HashSet::new();
                for item in &g[i] {
                    added.insert((None, item.clone()));
                    let mut new_added = vec![(None, item.clone())];
                    while !new_added.is_empty() {
                        let mut temp = HashSet::new();
                        for (option_terminals, item) in new_added {
                            if let Some(symbol) = get_symbol(&item) {
                                let state = goto[&(i, symbol.clone())];
                                if let Some(terminal) = option_terminals {
                                    lalr_generated_terminal[state].insert(terminal);
                                } else {
                                    lalr_propagated_path[i].insert(state);
                                }
                            }
                            //println!("{:?}", (&option_terminals, &item));
                            if let Some(NonTerminal(non_terminal)) = get_symbol(&item) {
                                let look_forward_symbols =
                                    if let Some(symbol) = get_symbol(&item.clone().acc()) {
                                        match symbol {
                                            NonTerminal(s) => {
                                                first[*s].iter().map(|s| Some(*s)).collect()
                                            }
                                            Terminal(s) => vec![Some(*s)],
                                        }
                                    } else {
                                        vec![option_terminals]
                                    };
                                //println!("{:?}", look_forward_symbols);
                                for look_forward_symbol in &look_forward_symbols {
                                    for production in &non_terminal_to_production[*non_terminal] {
                                        let to_add =
                                            (*look_forward_symbol, Item::new(*production, 0));
                                        if added.insert(to_add.clone()) {
                                            //println!("Add {:?}", &to_add);
                                            temp.insert(to_add);
                                        }
                                    }
                                }
                            }
                        }
                        new_added = temp.into_iter().collect();
                    }
                }
            }
        }
        debug!("LR(0):");
        for i in 0..g.len() {
            let items = &g[i];
            debug!("I{}", i);
            for item in closure(items.clone()) {
                let production = &productions[item.production_index];
                let right = str_join((0..production.right.len() + 1).map(|i| {
                    use std::cmp::Ordering::*;
                    match i.cmp(&item.position) {
                        Less => to_name(&production.right[i]),
                        Equal => ".",
                        Greater => to_name(&production.right[i - 1])
                    }
                }));
                if items.iter().any(|x| x == &item) {
                    debug!("{} -> {}", non_terminals[production.left], right);
                } else {
                    debug!("* {} -> {}", non_terminals[production.left], right);
                }
            }
            for symbol in &goto_symbol[i] {
                debug!(
                    "{} => I{}",
                    to_name(symbol),
                    goto.get(&(i, symbol.clone())).unwrap()
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
        }
        for i in 0..first.len() {
            debug!(
                "first({}) = {}",
                non_terminals[i],
                str_join(first[i].iter().map(|first| terminals[*first]))
            );
        }
        Self {}
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
                            ],
                            NON_TERMINAL_MAP.len() + 1
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
                    println!("{:?}", grammar());
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
