use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::hash::Hash;
pub trait ToTerminalName {
    fn to_terminal_name(&self) -> &'static str;
    fn all_terminal_names() -> &'static [&'static str];
}
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub enum Symbol {
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
    Reduce(usize, usize, usize, usize),
    Finish,
    Error,
}
use Action::*;

type ASTBuilder<T, A> = Box<dyn Sync + Fn(VecDeque<T>, VecDeque<A>) -> A>;
pub struct Grammar<T, A> {
    terminal_map: HashMap<&'static str, usize>,
    action: Vec<Vec<Action>>,
    goto: Vec<Vec<Option<usize>>>,
    debug_info: GrammarDebugInfo,
    ast_builders: Vec<ASTBuilder<T, A>>,
}

#[derive(Debug)]
struct GrammarDebugInfo {
    terminals: Vec<&'static str>,
    non_terminals: Vec<&'static str>,
    productions: Vec<Production>,
    g: Vec<Vec<Item>>,
}

impl GrammarDebugInfo {
    fn print_item(&self, item: &Item) -> String {
        let production = &self.productions[item.production_index];
        format!(
            "{} -> {}",
            self.non_terminals[production.left],
            str_join(
                (0..production.right.len() + 1).map(|i| {
                    use std::cmp::Ordering::*;
                    match i.cmp(&item.position) {
                        Less => self.to_name(&production.right[i]),
                        Equal => ".",
                        Greater => self.to_name(&production.right[i - 1]),
                    }
                }),
                " "
            )
        )
    }
    fn print_production(&self, production_index: usize) -> String {
        let production = &self.productions[production_index];
        format!(
            "{} -> {}",
            self.non_terminals[production.left],
            str_join(
                production.right.iter().map(|right| self.to_name(right)),
                " "
            )
        )
    }
    fn print_state_items(&self, state: usize) -> Vec<String> {
        self.g[state]
            .iter()
            .map(|item| self.print_item(item))
            .collect()
    }
    fn to_name(&self, symbol: &Symbol) -> &'static str {
        match symbol {
            NonTerminal(s) => &self.non_terminals[*s],
            Terminal(s) => {
                if *s < self.terminals.len() {
                    &self.terminals[*s]
                } else {
                    "$"
                }
            }
        }
    }
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

impl<T: ToTerminalName, A> Grammar<T, A> {
    pub fn new(
        terminal_map: HashMap<&'static str, usize>,
        terminals: Vec<&'static str>,
        non_terminals: Vec<&'static str>,
        split_productions: Vec<(usize, Vec<Vec<Symbol>>)>,
        ast_builders: Vec<ASTBuilder<T, A>>,
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
        let debug_info = GrammarDebugInfo {
            terminals,
            non_terminals,
            g,
            productions: productions.clone(),
        };
        debug!("{}", str_join(debug_info.terminals.iter().copied(), " "));
        for production in 0..debug_info.productions.len() {
            debug!("{}", debug_info.print_production(production));
        }
        debug!("LR(0):");
        for i in 0..debug_info.g.len() {
            let items = &debug_info.g[i];
            debug!("I{}", i);
            for item in items {
                debug!("{}", debug_info.print_item(item));
            }
            for item in closure(items.clone())
                .iter()
                .filter(|item| !items.iter().any(|x| &x == item))
            {
                debug!("* {}", debug_info.print_item(item));
            }
            for symbol in &goto_symbol[i] {
                debug!(
                    "{} => I{}",
                    debug_info.to_name(symbol),
                    goto.get(&(i, *symbol)).unwrap()
                );
            }
            debug!(
                "generated [{}]",
                str_join(
                    lalr_generated_terminal[i]
                        .iter()
                        .map(|terminal| debug_info.terminals[*terminal]),
                    ","
                )
            );
            debug!(
                "propagated [{}]",
                str_join(
                    lalr_propagated_path[i]
                        .iter()
                        .map(|state| format!("I{}", state)),
                    ","
                )
            );
            debug!(
                "final [{}]",
                str_join(
                    look_forward_terminal[i].iter().map(|terminal| {
                        match terminal {
                            End => "$",
                            Normal(t) => debug_info.terminals[*t],
                        }
                    }),
                    ","
                )
            );
        }
        for i in 0..first.len() {
            debug!(
                "first({}) = [{}]",
                debug_info.non_terminals[i],
                str_join(
                    first[i].iter().map(|first| debug_info.terminals[*first]),
                    ","
                )
            );
        }
        let mut action_table = vec![vec![Error; debug_info.terminals.len() + 1]; debug_info.g.len()];
        let mut goto_table = vec![vec![None; debug_info.non_terminals.len()]; debug_info.g.len()];
        for i in 0..debug_info.g.len() {
            for j in 0..debug_info.terminals.len() + 1 {
                let mut has_goto = false;
                if j != debug_info.terminals.len() {
                    if let Some(k) = goto.get(&(i, Terminal(j))) {
                        has_goto = true;
                        action_table[i][j] = MoveIn(*k);
                    }
                }
                let terminal = if j == debug_info.terminals.len() {
                    End
                } else {
                    Normal(j)
                };
                if look_forward_terminal[i].contains(&terminal) {
                    let mut reduce = None;
                    for item in &debug_info.g[i] {
                        let production = &debug_info.productions[item.production_index];
                        if production.right.len() == item.position {
                            if reduce.is_none() {
                                if production.left == 0 && j == debug_info.terminals.len() {
                                    reduce = Some(Finish);
                                } else {
                                    let mut terminal_count = 0;
                                    let mut non_terminal_count = 0;
                                    for symbol in &production.right {
                                        if let Terminal(_) = symbol {
                                            terminal_count += 1;
                                        } else {
                                            non_terminal_count += 1;
                                        }
                                    }
                                    reduce = Some(Reduce(
                                        item.production_index,
                                        production.left,
                                        terminal_count,
                                        non_terminal_count,
                                    ));
                                }
                            } else {
                                panic!("Reduce/reduce conflict");
                            }
                        }
                    }
                    if let Some(reduce) = reduce {
                        if has_goto {
                            error!("In state productions:");
                            for production in debug_info.print_state_items(i) {
                                error!("{}", production);
                            }
                            if let MoveIn(next) = action_table[i][j] {
                                error!("Move by [{}] to state:", debug_info.to_name(&Terminal(j)));
                                for production in debug_info.print_state_items(next) {
                                    error!("{}", production);
                                }
                            }
                            if let Reduce(
                                production_index,
                                _,
                                _,
                                _,
                            ) = reduce
                            {
                                error!(
                                    "But need to reduce by [{}], with production [{}]",
                                    debug_info.to_name(&Terminal(j)),
                                    debug_info.print_production(production_index)
                                );
                            }
                            panic!("Move-in/reduce conflict");
                        }
                        action_table[i][j] = reduce;
                    }
                }
            }
            for j in 0..debug_info.non_terminals.len() {
                if let Some(k) = goto.get(&(i, NonTerminal(j))) {
                    goto_table[i][j] = Some(*k);
                }
            }
        }
        Self {
            terminal_map,
            action: action_table,
            goto: goto_table,
            debug_info,
            ast_builders,
        }
    }
    pub fn parse(&self, mut tokens: VecDeque<T>) -> A {
        let mut stack = vec![0];
        let mut token_stack = Vec::new();
        let mut ast_stack = Vec::new();
        let to_terminal = |token: &T| *self.terminal_map.get(token.to_terminal_name()).unwrap();
        while !stack.is_empty() {
            let terminal = if let Some(token) = tokens.front() {
                to_terminal(token)
            } else {
                self.action[0].len() - 1
            };
            let state = *stack.last().unwrap();
            match self.action[state][terminal] {
                MoveIn(next) => {
                    stack.push(next);
                    debug!("push {}", next);
                    token_stack.push(tokens.pop_front().unwrap());
                }
                Reduce(production_index, left, terminal_count, non_terminal_count) => {
                    for _ in 0..terminal_count + non_terminal_count {
                        debug!("pop {}", stack.last().unwrap());
                        stack.pop();
                    }
                    let tokens = token_stack
                        .drain(token_stack.len() - terminal_count..token_stack.len())
                        .collect();
                    let ast = ast_stack
                        .drain(ast_stack.len() - non_terminal_count..ast_stack.len())
                        .collect();
                    let current = *stack.last().unwrap();
                    let new_ast = self.ast_builders[production_index - 1](tokens, ast);
                    ast_stack.push(new_ast);
                    let next = self.goto[current][left].unwrap();
                    stack.push(next);
                    debug!("push {}", next);
                }
                Finish => {
                    return ast_stack.pop().unwrap();
                }
                Error => {
                    let state = *stack.last().unwrap();
                    error!("current state:");
                    for production in self.debug_info.print_state_items(state) {
                        error!("{}", production);
                    }
                    let mut expect = Vec::new();
                    for (i, action) in self.action[state].iter().enumerate() {
                        if match action {
                            Error => false,
                            _ => true,
                        } {
                            expect.push(i);
                        }
                    }
                    error!(
                        "expect token [{}], get [{}]",
                        str_join(
                            expect
                                .iter()
                                .map(|terminal| self.debug_info.to_name(&Terminal(*terminal))),
                            ","
                        ),
                        self.debug_info.to_name(&Terminal(terminal))
                    );
                    panic!();
                }
            }
        }
        unreachable!();
    }
}
#[derive(Debug, Clone)]
struct Production {
    left: usize,
    right: Vec<Symbol>,
}
#[allow(unused_macros)]
macro_rules! parser {
    (
     ParseFunctionName = $parser_name:ident;
     Token = $tokens_name:ident:$tokens_type:ty;
     AST = $ast_name:ident:$ast_type:ty;
     $($left:tt -> $($($right:tt),+ => $ast_builder:block)|+);+
     ) => {
        lazy_static! {
            static ref GRAMMAR: Grammar<$tokens_type, $ast_type> = {
                use std::collections::HashMap;
                let mut terminal_map = HashMap::new();
                for terminal in <$tokens_type>::all_terminal_names() {
                    let len = terminal_map.len() as usize;
                    terminal_map.insert(*terminal, len);
                }
                let mut non_terminal_map = HashMap::new();
                $({
                    let len = non_terminal_map.len() as usize;
                    non_terminal_map.insert(stringify!($left), len + 1);
                  }
                )+
                let name_to_symbol = |s| {
                    if let Some(non_terminal) = non_terminal_map.get(s) {
                        Some(Symbol::NonTerminal(*non_terminal))
                    } else if let Some(terminal) = terminal_map.get(s) {
                        Some(Symbol::Terminal(*terminal))
                    }
                    else {
                        None
                    }
                };
                let productions = vec![
                    (
                        0,
                        vec![vec![Symbol::NonTerminal(1)]]
                    ),
                    $(
                        (
                            *non_terminal_map.get(stringify!($left)).unwrap(),
                            vec![$(vec![$(
                                name_to_symbol(stringify!($right)).unwrap()
                            ),+]),+]
                        )
                    ),+
                ];
                #[allow(unused_mut)]
                #[allow(unused_variables)]
                Grammar::new(
                        terminal_map,
                        <$tokens_type>::all_terminal_names().iter().copied().collect(),
                        vec!["S'", $(stringify!($left)),+],
                        productions,
                        vec![$($(Box::new(|mut $tokens_name, mut $ast_name| $ast_builder)),+),+]
                )
            };
        }
        fn $parser_name(tokens: std::collections::VecDeque<$tokens_type>) -> $ast_type {
            GRAMMAR.parse(tokens)
        }
    };
}
fn str_join<I: Iterator<Item = S>, S: ToString>(mut iter: I, join_with: &str) -> String {
    let mut r = String::new();
    if let Some(i) = iter.next() {
        r.push_str(&i.to_string());
    }
    for i in iter {
        r.push_str(join_with);
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
