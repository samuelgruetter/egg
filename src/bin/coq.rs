use egg::*;


fn main() {
    simplify("(wadd x y)");
}

/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<CoqSimpleLanguage> = s.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default().with_explanations_enabled().with_expr(&expr).run(&make_rules());
    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best) = extractor.find_best(root);
    println!("{}", runner.explain_equivalence(&expr, &best));
    best.to_string()
}

fn prove(s_l: &str, s_r : &str) -> () {
    // parse the expression, the type annotation tells it which Language to use
    let expr_l: RecExpr<CoqSimpleLanguage> = s_l.parse().unwrap();
    let expr_r: RecExpr<CoqSimpleLanguage> = s_r.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default().with_explanations_enabled().with_expr(&expr_l).run(&make_rules());
    // the Runner knows which e-class the expression given with `with_expr` is in
    let equivs = runner.egraph.equivs(&expr_l, &expr_r);
    if equivs.is_empty() {
        println!("(NotExplained)");
    }
    else {
        println!("{}", runner.explain_equivalence(&expr_l, &expr_r));
    }
}

