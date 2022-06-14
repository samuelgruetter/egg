#![allow(missing_docs)]
use crate::*;

pub fn print_eclasses<L: Language + std::fmt::Display, N: Analysis<L>>(eg: &EGraph<L, N>) -> () {
    let extractor = Extractor::new(eg, AstSize);
    let mut classes : Vec<&EClass<L, _>> = eg.classes().collect();
    classes.sort_by(|a, b| a.id.cmp(&b.id));
    for class in classes {
        let i = class.id;
        println!("\nClass {i}");
        for node in class.nodes.iter() {
            // The display() method implemented by define_language! macro happens to print only the op name
            // TODO is there a cleaner way to obtain the op name?
            let opname = format!("{}", node);
            let mut s: String = "".to_string();
            s.push_str(&opname);
            for child in node.children().iter() {
                let (_best_cost, best) = extractor.find_best(*child);
                s.push_str(&format!(" {}", best));
            }
            if node.children().is_empty() {
                println!("- {s}");
            } else {
                println!("- ({s})");
            }
        }
    }
    println!("");
}

pub fn why_exists<L: Language + language::FromOp + std::fmt::Display>(runner: &mut Runner<L, ()>, s: &str) -> () {
    println!("Explanation of why {s} exists:");
    let e: RecExpr<L> = s.parse::<RecExpr<L>>().unwrap();
    if runner.egraph.lookup_expr(&e).is_none() {
        println!("It actually doesn't exist.");
    } else {
        let expl = runner.explain_existance(&e).get_flat_sexps();
        for line in expl {
            println!("{}", line);
        }
    }
    println!("");
}

#[allow(dead_code)]
pub fn why_exists_uselessly_iterative(runner: &mut Runner<CoqSimpleLanguage, ()>, s: &str) -> () {
    let mut current: RecExpr<CoqSimpleLanguage> = s.parse().unwrap();
    for _i in 1..100 {
        println!("{current}");
        println!("exists because of");
        let expl = runner.explain_existance(&current).get_flat_sexps();
        let firstline = &expl[0];
        let first_s = format!("{}", firstline);
        println!("{first_s}");
        current = first_s.parse().unwrap();
    }
    println!("...\n");
}
