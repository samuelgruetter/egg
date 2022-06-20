/// coquetier (french for egg server)

use egg::*;
use std::io;
use symbolic_expressions::*;

struct Rule {
    rulename: String,
    quantifiers: Vec<String>,
    sideconditions: Vec<Sexp>,
    conclusion: Sexp,
    triggers: Vec<Sexp>,
}

struct Server {
    runner: Runner<SymbolLang, ()>
}

impl Server {
    pub fn new() -> Self {
        Self { runner: Default::default() }
    }

    fn process_line(&mut self, line: Sexp) -> () {
        match line {
            Sexp::List(l) => {
                match &l[0] {
                    Sexp::String(command) => {
                        let c: &str = command;
                        match c {
                            "set-logic" => {/*ignore*/}
                            "set-option" => {/*ignore*/}
                            "declare-sort" => {/*ignore*/}
                            "declare-fun" => {/*ignore*/}
                            "assert" => { self.process_assert(l) }
                            _ => { panic!("unknown command {}", command); }
                        }
                    }
                    _ => panic!("First element of sexpr is not a command")
                }
            }
            _ => { panic!("Not an Sexp::List")}
        }
    }

    fn process_assert(&mut self, l: Vec<Sexp>) -> () {
        match &l[1] {
            Sexp::List(ll) => {
                match &ll[0] {
                    Sexp::String(s) => {
                        let kind: &str = s;
                        match kind {
                            "$initial" => { self.process_initial_expr(&ll[1]); }
                            "!" => { self.process_rule(ll); }
                            _ => { panic!("expected $initial or annotation, found {}", kind) }
                        }
                    }
                    _ => { panic!("head of arg to assert must be an atom") }
                }
            }
            _ => { panic!("assert expects list") }
        }

    }

    fn process_initial_expr(&mut self, se: &Sexp) -> () {
        // TODO can we avoid the round-trip?
        let expr: RecExpr<SymbolLang> = se.to_string().parse().unwrap();
        // TODO can we avoid inlining Runner.with_expr?
        //self.runner = self.runner.with_expr(&sy);
        let id = self.runner.egraph.add_expr(&expr);
        self.runner.roots.push(id);
    }

    fn process_rule(&mut self, _r: &Vec<Sexp>) -> Rule {
        Rule {
            rulename: Default::default(),
            quantifiers: Default::default(),
            sideconditions: Default::default(),
            conclusion: Default::default(),
            triggers: Default::default(),
        }
    }
}

fn main() {
    env_logger::init();
    let mut server = Server::new();

    #[allow(while_true)]
    while true {
        let mut buffer = String::new();
        io::stdin().read_line(&mut buffer).expect("failed to read line from stdin");
        let sexp = symbolic_expressions::parser::parse_str(&buffer).unwrap();
        server.process_line(sexp);
    }
}
