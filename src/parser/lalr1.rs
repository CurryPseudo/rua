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

impl TerminalSymbol {
    pub fn from_index(terminal_count: usize, index: usize) -> Self {
        if terminal_count == index {
            End
        } else {
            Normal(index)
        }
    }
    pub fn to_index(self, terminal_count: usize) -> usize {
        match self {
            Normal(i) => i,
            End => terminal_count,
        }
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
enum Action {
    MoveIn(usize),
    Reduce(usize, usize, usize, usize),
    Finish,
    Error,
}
use Action::*;

pub type ASTBuilder<T, A> = fn(SymbolVec<T>, SymbolVec<A>) -> A;
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
    fn print_state_item(&self, state: usize, item_index: usize) -> String {
        self.print_item(&self.g[state][item_index])
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
        unmerged_str_productions: Vec<Vec<(&'static str, Vec<&'static str>, ASTBuilder<T, A>)>>,
    ) -> Self {
        let mut productions = Vec::new();
        let mut terminal_map = HashMap::new();
        let mut non_terminal_map = HashMap::new();
        let mut non_terminals = Vec::new();
        let mut ast_builders = Vec::new();
        non_terminals.push("S'");
        for unmerged in &unmerged_str_productions {
            for (left_str, _, _) in unmerged {
                let len = non_terminal_map.len();
                if *non_terminal_map.entry(*left_str).or_insert_with(|| len + 1)
                    >= non_terminals.len()
                {
                    non_terminals.push(*left_str);
                }
            }
        }
        let mut non_terminal_to_production = vec![Vec::new(); non_terminal_map.len() + 1];
        let mut push_production = |production: Production| {
            let production_index = productions.len();
            non_terminal_to_production[production.left].push(production_index);
            productions.push(production);
        };
        push_production(Production {
            left: 0,
            right: vec![NonTerminal(1)],
        });
        let mut terminals = Vec::new();
        for terminal in T::all_terminal_names() {
            let len = terminal_map.len();
            if *terminal_map.entry(*terminal).or_insert_with(|| len) >= terminals.len() {
                terminals.push(*terminal);
            };
        }
        for unmerged in unmerged_str_productions {
            for (left_str, right_strs, ast_builder) in unmerged {
                let left = non_terminal_map[left_str];
                let right = right_strs
                    .into_iter()
                    .map(|s| {
                        if let Some(non_terminal) = non_terminal_map.get(s) {
                            Symbol::NonTerminal(*non_terminal)
                        } else if let Some(terminal) = terminal_map.get(s) {
                            Symbol::Terminal(*terminal)
                        } else {
                            panic!("Cant find symbol {}", s);
                        }
                    })
                    .collect();
                push_production(Production { left, right });
                ast_builders.push(ast_builder);
            }
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
        let item_to_index: Vec<_> = g
            .iter()
            .map(|items| {
                let mut map = HashMap::new();
                for (i, item) in items.iter().enumerate() {
                    map.insert(item.clone(), i);
                }
                map
            })
            .collect();
        let mut lalr_generated_terminal = create_item_symbol_container(&g, HashSet::new);
        let mut lalr_propagated_path = create_item_symbol_container(&g, HashSet::new);
        {
            for i in 0..g.len() {
                let mut begin = Vec::new();
                for (j, item) in g[i].iter().enumerate() {
                    begin.push((None, j, item.clone()));
                }
                dfs(begin, |(option_terminals, kernel_item_index, item)| {
                    let mut next = Vec::new();
                    if let Some(symbol) = get_symbol(&item) {
                        let next_state = goto[&(i, *symbol)];
                        let next_item_index = item_to_index[next_state][&item.acc()];
                        if let Some(terminal) = option_terminals {
                            lalr_generated_terminal[next_state][next_item_index].insert(terminal);
                        } else {
                            lalr_propagated_path[i][kernel_item_index]
                                .insert((next_state, next_item_index));
                        }
                        if let NonTerminal(non_terminal) = symbol {
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
                                    next.push((
                                        *look_forward_symbol,
                                        kernel_item_index,
                                        Item::new(*production, 0),
                                    ));
                                }
                            }
                        }
                    }
                    next
                });
            }
        }
        let mut look_forward_terminal = create_item_symbol_container(&g, HashSet::new);
        let mut propagated_chain =
            create_item_symbol_container(&g, || vec![Vec::new(); terminals.len() + 1]);
        dfs(
            {
                let mut begin = Vec::<(_, _, _, Option<(usize, usize)>)>::new();
                for (i, item_generateds) in lalr_generated_terminal.iter().enumerate() {
                    for (j, generateds) in item_generateds.iter().enumerate() {
                        for generated in generateds {
                            begin.push((i, j, Normal(*generated), None));
                        }
                    }
                }
                begin.push((0, 0, End, None));
                begin
            },
            |(i, j, terminal, from)| {
                if look_forward_terminal[i][j].insert(terminal) {
                    if let Some(from) = from {
                        let v = propagated_chain[from.0][from.1]
                            [terminal.to_index(terminals.len())]
                        .clone();
                        let target =
                            &mut propagated_chain[i][j][terminal.to_index(terminals.len())];
                        *target = v;
                        target.push(from)
                    }
                }
                lalr_propagated_path[i][j]
                    .iter()
                    .map(|(propagated_state, propagated_item)| {
                        (*propagated_state, *propagated_item, terminal, Some((i, j)))
                    })
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
            for (j, item) in items.iter().enumerate() {
                debug!("{}", debug_info.print_item(item));
                debug!(
                    "generated [{}]",
                    str_join(
                        lalr_generated_terminal[i][j]
                            .iter()
                            .map(|terminal| debug_info.terminals[*terminal]),
                        ","
                    )
                );
                debug!(
                    "propagated [{}]",
                    str_join(
                        lalr_propagated_path[i][j]
                            .iter()
                            .map(|(state, item_index)| format!(
                                "I{} {}",
                                state,
                                debug_info.print_item(&debug_info.g[*state][*item_index])
                            )),
                        ","
                    )
                );
                debug!(
                    "final [{}]",
                    str_join(
                        look_forward_terminal[i][j].iter().map(|terminal| {
                            match terminal {
                                End => "$",
                                Normal(t) => debug_info.terminals[*t],
                            }
                        }),
                        ","
                    )
                );
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
        let mut action_table =
            vec![vec![Error; debug_info.terminals.len() + 1]; debug_info.g.len()];
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
                let terminal = TerminalSymbol::from_index(debug_info.terminals.len(), j);
                let mut reduce = None;
                for (k, item) in debug_info.g[i].iter().enumerate() {
                    if look_forward_terminal[i][k].contains(&terminal) {
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
                        if let Some(reduce) = reduce {
                            if has_goto {
                                error!("In I{} productions:", i);
                                for production in debug_info.print_state_items(i) {
                                    error!("{}", production);
                                }
                                if let MoveIn(next) = action_table[i][j] {
                                    error!(
                                        "Move by [{}] to I{}:",
                                        debug_info.to_name(&Terminal(j)),
                                        next
                                    );
                                    for production in debug_info.print_state_items(next) {
                                        error!("{}", production);
                                    }
                                }
                                if let Reduce(
                                    production_index,
                                    _,
                                    terminal_count,
                                    non_terminal_count,
                                ) = reduce
                                {
                                    error!(
                                        "But need to reduce by [{}], with production [{}], by production chain [{}]",
                                        debug_info.to_name(&Terminal(j)),
                                        debug_info.print_production(production_index),
                                        str_join(propagated_chain[i][*item_to_index[i].get(&Item::new(production_index, terminal_count + non_terminal_count)).unwrap()][j].iter().map(|(i, j)| format!("I{} {}", i, debug_info.print_state_item(*i, *j))), ", ")
                                    );
                                }
                                panic!("Move-in/reduce conflict");
                            }
                            action_table[i][j] = reduce;
                        }
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
                debug!("accept terminal {}", token.to_terminal_name());
                to_terminal(token)
            } else {
                debug!("accept terminal $");
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
macro_rules! right {
    ($tokens_name:ident, $tokens_type:ty, $ast_name:ident, $ast_type:ty, ($($pre:tt),* + ($($($choose:tt),+)|+) + $($after:tt),* => $ast_builder:expr)) => {
        {
            let pre = vec![$(stringify!($pre)),+];
            let after = vec![$(stringify!($after)),+];
            let chooses = vec![$(vec![$(stringify!($choose)),+]),+];
            let mut r: Vec<(_, lalr1::ASTBuilder<$tokens_type, $ast_type>)> = Vec::new();
            for mut choose in chooses {
                let mut this_pre = pre.clone();
                let mut this_after = after.clone();
                this_pre.append(&mut choose);
                this_pre.append(&mut this_after);
                r.push((this_pre, |mut $tokens_name: lalr1::SymbolVec<$tokens_type>, mut $ast_name: lalr1::SymbolVec<$ast_type>| $ast_builder));
            }
            r
        }
    };
    ($tokens_name:ident, $tokens_type:ty, $ast_name:ident, $ast_type:ty, ($($right:tt),+ => $ast_builder:expr)) => {
        vec![(vec![$(stringify!($right)),+], |mut $tokens_name: lalr1::SymbolVec<$tokens_type>, mut $ast_name: lalr1::SymbolVec<$ast_type>| $ast_builder)]
    };
    ($tokens_name:ident, $tokens_type:ty, $ast_name:ident, $ast_type:ty, ($($right:tt),+)) => {
        vec![(vec![$(stringify!($right)),+], |mut $tokens_name: lalr1::SymbolVec<$tokens_type>, mut $ast_name: lalr1::SymbolVec<$ast_type>| $ast_name.get(0))]
    };
}
macro_rules! production {
    {$tokens_name:ident, $tokens_type:ty, $ast_name:ident, $ast_type:ty, ($left:tt -> $($right:ident!$args:tt),+)} => {
        {
            let mut r = Vec::new();
            $(
                let one: Vec<(_, lalr1::ASTBuilder<$tokens_type, $ast_type>)> = $right!($tokens_name, $tokens_type, $ast_name, $ast_type, $args);
                for (rights, ast_builder) in one {
                    r.push((stringify!($left), rights, ast_builder));
                }
            )+
            r
        }
    };
}
#[allow(unused_macros)]
macro_rules! parser {
    {
     $parser_name:ident = |$tokens_name:ident: $tokens_type:ty, $ast_name:ident: $ast_type:ty| $($product_macro:ident!$args:tt)+
    } => {
        lazy_static! {
            static ref GRAMMAR: lalr1::Grammar<$tokens_type, $ast_type> = {
                #[allow(unused_mut)]
                #[allow(unused_variables)]
                lalr1::Grammar::new(vec![$($product_macro!($tokens_name, $tokens_type, $ast_name, $ast_type, $args)),+])
            };
        }
        pub fn $parser_name(tokens: std::collections::VecDeque<$tokens_type>) -> $ast_type {
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
fn create_item_symbol_container<T, F: Fn() -> T>(g: &Vec<Vec<Item>>, create_t: F) -> Vec<Vec<T>> {
    g.iter()
        .map(|items| items.iter().map(|_| create_t()).collect::<Vec<_>>())
        .collect::<Vec<Vec<T>>>()
}
pub struct SymbolVec<T>(Vec<Option<T>>);

impl<T> std::iter::FromIterator<T> for SymbolVec<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self(iter.into_iter().map(|x| Some(x)).collect())
    }
}

impl<T> SymbolVec<T> {
    pub fn get(&mut self, i: usize) -> T {
        std::mem::replace(&mut self.0[i], None).unwrap()
    }
}
