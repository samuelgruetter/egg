#![allow(missing_docs)]
use crate::*;
use std::fs::File;
use std::io::{BufWriter, Write};


pub fn fmt_subst<L: Language + std::fmt::Display, N: Analysis<L>>(
    eg: &EGraph<L, N>, 
    s: &Subst, 
    f: &mut std::fmt::Formatter<'_>
) -> std::fmt::Result {
    let len = s.vec.len();
    let extractor = Extractor::new(eg, AstSize);
    write!(f, "{{")?;
    for i in 0..len {
        let (var, id) = &s.vec[i];
        let (_best_cost, best) = extractor.find_best(*id);
        write!(f, "{}: {}", var, best)?;
        if i < len - 1 {
            write!(f, ", ")?;
        }
    }
    write!(f, "}}")
}

// TODO how to reuse above fmt_subst?
pub fn fmt_subst_to_str<L: Language + std::fmt::Display, N: Analysis<L>>(
    eg: &EGraph<L, N>, 
    s: &Subst, 
) -> String {
    let len = s.vec.len();
    let mut res: String = "{{".to_string();
    let extractor = Extractor::new(eg, AstSize);
    for i in 0..len {
        let (var, id) = &s.vec[i];
        let (_best_cost, best) = extractor.find_best(*id);
        res.push_str(&format!("{}: {}", var, best));
        if i < len - 1 {
            res.push_str(", ");
        }
    }
    res.push_str("}}");
    res
}

pub fn enode_to_best_expr<CF: CostFunction<L>, L: Language, N: Analysis<L>>(
    extractor: &Extractor<CF, L, N>,
    node: &L,
) -> RecExpr<L> {
    node.join_recexprs(|id| extractor.find_best(id).1)
}

pub fn enode_to_string<CF: CostFunction<L>, L: Language + std::fmt::Display, N: Analysis<L>>(
    extractor: &Extractor<CF, L, N>,
    node: &L,
) -> String {
    format!("{}", enode_to_best_expr(extractor, node))
}

#[allow(unused_must_use)]
pub fn print_eclasses_to_writer<W: Write, L: Language + std::fmt::Display, N: Analysis<L>>(
    eg: &EGraph<L, N>,
    w: &mut W
) -> () {
    let extractor = Extractor::new(eg, AstSize);
    let mut classes : Vec<&EClass<L, _>> = eg.classes().collect();
    classes.sort_by(|a, b| a.id.cmp(&b.id));
    for class in classes {
        let i = class.id;
        let mut reps: Vec<String> = vec![];
        for node in class.nodes.iter() {
            let ffn = &eg.ffn_of_enode(node).unwrap();
            reps.push(format!("- [{}] {}", ffn, enode_to_string(&extractor, node)));
        }
        writeln!(w, "\nClass {i}");
        reps.sort();
        for s in reps {
            writeln!(w, "{s}");
        }
    }
    writeln!(w, "");
    w.flush().expect("error flushing");
}

pub fn print_eclasses_to_file<L: Language + std::fmt::Display, N: Analysis<L>>(eg: &EGraph<L, N>, path: &str) -> () {
    let f = File::create(path).expect("unable to create file");
    let mut writer = BufWriter::new(f);
    print_eclasses_to_writer(eg, &mut writer);
    println!("Wrote egraph to {path}");
}


pub fn print_eclasses<L: Language + std::fmt::Display, N: Analysis<L>>(eg: &EGraph<L, N>) -> () {
    print_eclasses_to_writer(eg, &mut std::io::stdout());
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

/// returned boolean indicates whether ffn limit has been hit
#[allow(unused_must_use)]
pub fn print_max_ffn_explanation_to_writer<W: Write, L: Language + std::fmt::Display>(
    runner: &mut Runner<L, ()>,
    w: &mut W
) -> bool {
    let max_ffn = runner.ffn_limit;
    let extractor = Extractor::new(&runner.egraph, AstSize);

    // Note: this seemingly simpler way of looping through all ffn values also includes stale enodes
    // (which became equal to another enode because its children were unioned)
    // let oid: Option<Id> = runner.egraph.farfetchedness.iter().find(|(_id, &ffn)| ffn >= max_ffn).map(|(&id, _ffn)| id);
    
    let mut oexpr: Option<RecExpr<L>> = None;
    'outer: for class in runner.egraph.classes() {
        for node in class.nodes.iter() {
            let ffn = *runner.egraph.ffn_of_enode(node).unwrap();
            if ffn >= max_ffn {
                oexpr = Some(enode_to_best_expr(&extractor, node));
                break 'outer;
            }
        }
    }
    
    if let Some(expr) = oexpr {
        runner.egraph.rebuild();
        let expl = runner.explain_existance(&expr).get_flat_sexps();
        writeln!(w, "\nA node with max far-fetchedness ({max_ffn}) has been reached:");
        writeln!(w, "{}", expr);
        writeln!(w, "Here is why it exists:");
        for line in expl {
            writeln!(w, "{}", line);
        }
        writeln!(w, "");
        true
    } else {
        writeln!(w, "\nAll enodes have far-fetched-ness below {max_ffn}.\n");
        false
    }
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
