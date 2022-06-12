use egg::*;
use symbolic_expressions::*;

fn main() {
    //    run_simplifier(simplify,prove);
    run_simplifier(simplify);
    // simplify("(wadd x y)");
}

fn holify_aux(e: &Sexp) -> Sexp {
    match e {
        Sexp::String(s) => return Sexp::String(s.replace("AT", "@").replace("DOT", ".")),
        Sexp::Empty => return Sexp::Empty,
        Sexp::List(l) => {
            if l[0] == Sexp::String("Rewrite=>".to_string()) {
                return Sexp::String("hole".to_string());
            } else if l[0] == Sexp::String("Rewrite<=".to_string()) {
                return Sexp::String("hole".to_string());
            } else {
                return Sexp::List(l.iter().map(holify_aux).collect());
            }
        }
    }
}

fn add_arity_th_name(e: &Sexp) -> Sexp {
    match e {
        Sexp::String(s) => {
            match s.find('O') {
                None => {
                    return Sexp::String(s.clone().replace("-rev", ""));
                }
                Some(idx) => {
                    // optimization
                    let number = idx - 5;
                    let mut v = vec![e.clone()];
                    assert_eq!([1, 2].repeat(3), vec![1, 2, 1, 2, 1, 2]);

                    let arg_implicit_aux = ["_"].repeat(number);
                    let arg_implicit = arg_implicit_aux
                        .iter()
                        .map(|s| Sexp::String(s.to_string()))
                        .collect::<Vec<_>>();
                    v.extend(arg_implicit);
                    return Sexp::List(v.clone());
                }
            }
        }
        _ => {
            panic!("unexpected empty");
        }
    }
}
fn find_rw(e: &Sexp) -> Option<(bool, Sexp, Sexp)> {
    match e {
        Sexp::String(_s) => return None,
        Sexp::Empty => return None,
        Sexp::List(l) => {
            if l[0] == Sexp::String("Rewrite=>".to_string()) {
                match &l[1] {
                    Sexp::String(s) => {
                        if s.contains("-rev") {
                            return Some((true, add_arity_th_name(&l[1]), l[2].clone()));
                        } else {
                            return Some((false, add_arity_th_name(&l[1]), l[2].clone()));
                        }
                    }
                    _ => {
                        panic!("Absurd")
                    }
                }
            } else if l[0] == Sexp::String("Rewrite<=".to_string()) {
                return Some((true, add_arity_th_name(&l[1]), l[2].clone()));
            } else {
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
}
fn holify(e: &Sexp) -> (Sexp, bool, Sexp, Sexp) {
    match find_rw(e) {
        None => {
            panic!("There is no rewrite in the sexp")
        }
        Some((a, b, c)) => {
            return (holify_aux(e), a, b, holify_aux(&c));
        }
    }
}
/// parse an expression, simplify it using egg, and pretty print it back out
#[allow(dead_code)]
fn simplify(s: &str) -> () {
    // parse the expression, the type annotation tells it which Language to use
    // let expr: RecExpr<CoqSimpleLanguage> = s.parse().unwrap();
    let expr: RecExpr<SymbolLang> = s.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .run(&make_rules());
    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best) = extractor.find_best(root);
    let explanations = runner.explain_equivalence(&expr, &best).get_flat_sexps();
    let mut explanation = explanations.iter();
    explanation.next();
    for exp in explanation {
        let (holified, fw, name_th, new) = holify(exp);
        // println!("{}", exp.to_string());
        let rw_lemma = if fw { "@rew_zoom_fw" } else { "@rew_zoom_bw" };
        println!("eapply ({rw_lemma} _ {new} _  {name_th} (fun hole => {holified}));");
    }
    println!("idtac.")
}

#[allow(dead_code)]
fn prove(s_l: &str, s_r: &str) -> () {
    // parse the expression, the type annotation tells it which Language to use
    // let expr_l: RecExpr<CoqSimpleLanguage> = s_l.parse().unwrap();
    let expr_l: RecExpr<SymbolLang> = s_l.parse().unwrap();
    // let expr_r: RecExpr<CoqSimpleLanguage> = s_r.parse().unwrap();
    let expr_r: RecExpr<SymbolLang> = s_r.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr_l)
        .run(&make_rules());
    // the Runner knows which e-class the expression given with `with_expr` is in
    let equivs = runner.egraph.equivs(&expr_l, &expr_r);
    if equivs.is_empty() {
        println!("(NotExplained)");
    } else {
        println!("{}", runner.explain_equivalence(&expr_l, &expr_r));
    }
}
