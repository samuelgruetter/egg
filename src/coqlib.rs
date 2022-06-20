use crate::*;
use symbolic_expressions::*;
use std::fs::File;
use std::io::{BufWriter, Write};

fn holify_aux(e: &Sexp) -> Sexp {
    match e {
        Sexp::String(s) => Sexp::String(s.replace("AT", "@").replace("DOT", ".")),
        Sexp::Empty => Sexp::Empty,
        Sexp::List(l) => {
            if l[0] == Sexp::String("Rewrite=>".to_string()) {
                Sexp::String("hole".to_string())
            } else if l[0] == Sexp::String("Rewrite<=".to_string()) {
                Sexp::String("hole".to_string())
            } else {
                Sexp::List(l.iter().map(holify_aux).collect())
            }
        }
    }
}

fn lemma_arity(s: &str) -> usize {
    match get_lemma_arity(s) {
        Some(a) => { return a; }
        None => { 
            match s.find('O') {
                Some(idx) => {  /* "optimization" */ return idx - 5; }
                None => { return 0; }
            }
        }
    }
}

fn add_arity_th_name(e: &Sexp) -> Sexp {
    match e {
        Sexp::String(s) => {
            // let-bound variables in context like "x := rhs : T"
            // were transformed into are rule named x$def saying "x => rhs", and will
            // now be translated back to (@eq_refl _ x)
            if s.ends_with("$def") {
                Sexp::List(vec![
                    Sexp::String("@eq_refl".to_string()),
                    Sexp::String("_".to_string()),
                    Sexp::String(s[..s.len()-4].to_string()),
                ])
            } else {
                let number = lemma_arity(s);
                if number == 0 {
                    Sexp::String(s.clone().replace("-rev", ""))
                } else {
                    let mut v = vec![e.clone()];
                    let arg_implicit_aux = ["_"].repeat(number);
                    let arg_implicit = arg_implicit_aux
                        .iter()
                        .map(|s| Sexp::String(s.to_string()))
                        .collect::<Vec<_>>();
                    v.extend(arg_implicit);
                    Sexp::List(v.clone())
                }
            }
        }
        _ => {
            panic!("not Sexp::String");
        }
    }
}

fn find_rw(e: &Sexp) -> Option<(bool, String, Sexp, Sexp)> {
    match e {
        Sexp::String(_s) => return None,
        Sexp::Empty => return None,
        Sexp::List(l) => {
            match &l[0] {
                Sexp::String(op) => {
                    if op.starts_with("Rewrite") {
                        let fw1 = op.starts_with("Rewrite=>");
                        match &l[1] {
                            Sexp::String(s) => {
                                let fw2 = !s.contains("-rev");
                                let fw = fw1 ^ fw2;
                                return Some((fw, s.to_string(), add_arity_th_name(&l[1]), l[2].clone()))
                            }
                            _ => { panic!("Expected rule name after Rewrite") }
                        }
                    }
                }
                _ => ()
            }
            // only executed if we have not yet returned:
            for i in l.iter() {
                match find_rw(i) {
                    None => {}
                    Some(a) => {
                        return Some(a);
                    }
                }
            }
            return None;
        }
    }
}

fn holify(e: &Sexp) -> (Sexp, bool, String, Sexp, Sexp) {
    match find_rw(e) {
        None => {
            panic!("There is no rewrite in the sexp")
        }
        Some((fw, name_th, applied_th, new)) => {
            return (holify_aux(e), fw, name_th, applied_th, holify_aux(&new));
        }
    }
}

/// parse an expression, simplify it using egg, and pretty print it back out
#[allow(dead_code, unused_must_use)]
pub fn simplify(s: &str, extra_s : Vec<&str>) -> () {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<CoqSimpleLanguage> = s.parse().unwrap();
    // let expr: RecExpr<SymbolLang> = s.parse().unwrap();

    let extra_exprs : Vec<RecExpr<CoqSimpleLanguage>> = extra_s.iter().map(|s| { s.parse::<RecExpr<CoqSimpleLanguage>>().unwrap()}).collect();
    // let extra_exprs : Vec<&RecExpr<CoqSimpleLanguage>> = extra_exprs1.iter().map(|x| &*x).collect();
    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_node_limit(1000)
        .with_expr(&expr)
        .with_ffn_limit(4)
        .with_exprs(extra_exprs.iter().map(|x| &*x).collect())
        .run(&make_rules());
    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    
    print_eclasses(&runner.egraph);
    // why_exists(&mut runner, "(@word.add 64 word x1 x1)");

    let explanations = runner.explain_equivalence(&expr, &best).get_flat_sexps();
    println!("Explanation length: {}", explanations.len());

    let path = get_proof_file_path();
    let f = File::create(path).expect("unable to create file");
    let mut writer = BufWriter::new(f);

    let mut explanation = explanations.iter();
    explanation.next();
    writeln!(writer, "unshelve (");
    for exp in explanation {
        let (holified, fw, name_th, applied_th, new) = holify(exp);
        let rw_lemma = if fw { "@rew_zoom_fw" } else { "@rew_zoom_bw" };
        let th = if is_eq(&name_th.to_string()).unwrap() { 
            format!("{applied_th}")
        } else { 
            format!("(prove_True_eq _ {applied_th})") 
        };
        writeln!(writer, "eapply ({rw_lemma} _ {new} _ {th} (fun hole => {holified}));");
    }
    writeln!(writer, "idtac).");
    writer.flush().expect("error flushing");
    println!("Wrote proof to {path}");

    println!("Simplified\n{}\nto\n{}\nwith cost {}", expr, best, best_cost);
    println!("Stop reason: {:?}", runner.stop_reason);
}

/* too hard to satisfy typechecker
fn write_explanation<W: Write>(&mut writer: &BufWriter<W>, explanations: &Vec<symbolic_expressions::Sexp>) -> () {
    let mut explanation = explanations.iter();
    explanation.next();
    writeln!(writer, "unshelve (");
    for exp in explanation {
        let (holified, fw, name_th, new) = holify(exp);
        let rw_lemma = if fw { "@rew_zoom_fw" } else { "@rew_zoom_bw" };
        writeln!(writer, "(eapply ({rw_lemma} _ {new} _  {name_th} (fun hole => {holified})) || ");
        writeln!(writer, "eapply ({rw_lemma} _ {new} _  (prove_True_eq _ {name_th}) (fun hole => {holified})));");
    }
    writeln!(writer, "idtac).");
}
*/

#[allow(dead_code, missing_docs)]
pub fn prove(s_l: &str, s_r: &str, extra_exprs: Vec<&str>) -> () {
    // parse the expression, the type annotation tells it which Language to use
    let expr_l: RecExpr<CoqSimpleLanguage> = s_l.parse().unwrap();
    // let expr_l: RecExpr<SymbolLang> = s_l.parse().unwrap();
    let expr_r: RecExpr<CoqSimpleLanguage> = s_r.parse().unwrap();
    // let expr_r: RecExpr<SymbolLang> = s_r.parse().unwrap();

    let extra_exprs_parsed : Vec<RecExpr<CoqSimpleLanguage>> = extra_exprs.iter().map(|s| s.parse::<RecExpr<CoqSimpleLanguage>>().unwrap()).collect();
    let mut extra_exprs_parsed2 : Vec<&RecExpr<CoqSimpleLanguage>> = vec![];
    for i in 0..extra_exprs_parsed.len() {
        extra_exprs_parsed2.push(&extra_exprs_parsed[i]);
    }

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr_l)
        .with_exprs(extra_exprs_parsed2)
        .run(&make_rules());
    // the Runner knows which e-class the expression given with `with_expr` is in
    let equivs = runner.egraph.equivs(&expr_l, &expr_r);
    if equivs.is_empty() {
        println!("(NotExplained)");
    } else {
        println!("{}", runner.explain_equivalence(&expr_l, &expr_r));
    }
}
