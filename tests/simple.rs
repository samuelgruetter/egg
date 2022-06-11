use egg::*;

define_language! {
    enum SimpleLanguage {
        Num(i32),
        // "+" = Add([Id; 2]),
        // "*" = Mul([Id; 2]),
        "le" = Le([Id; 2]),
        "eq" = Eq([Id; 2]),
        "abs" = Abs([Id;1]),
        Symbol(Symbol),
    }
}

fn make_rules() -> Vec<Rewrite<SimpleLanguage, ()>> {
    vec![
        // rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        // rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        // rewrite!("add-0"; "(+ ?a 0)" => "?a"),
        // rewrite!("mul-0"; "(* ?a 0)" => "0"),
        // rewrite!("mul-1"; "(* ?a 1)" => "?a"),
        rewrite!("le5-true"; "(le 0 5)" => "True"),
        // coq_rewrite!("context-transfer"; 
        //              "?foo = (abs ?yoo), ?posx = (le 0 ?yoo) = True" 
        //               =>
        //               "?yoo"),
        // coq_rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        coq_rewrite!("context-transfer"; 
                     "?foo = (abs ?yoo), ?posx = (le 0 ?yoo) = True" 
                      =>
                      "?yoo")
    ]
}


/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<SimpleLanguage> = s.parse().unwrap();
    let le5: RecExpr<SimpleLanguage> = "(le 0 5)".parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default().with_explanations_enabled().with_expr(&expr).with_expr(&le5).run(&make_rules());
    // let runner = Runner::default().with_expr(&expr).with_expr(&le5).run(&make_rules());


        // let exprx: RecExpr<SimpleLanguage> = "(tag x ctx1)".parse().unwrap();
        // let expry: RecExpr<SimpleLanguage> = "(tag y ctx1)".parse().unwrap();

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);

    let explanations = runner.explain_equivalence(&expr, &best).get_flat_string();
    println!("Simplified {} to {} with cost {}", expr, best, best_cost);
    println!("Explanation {} ", explanations);
    best.to_string()
}

#[test]
fn simple_tests() {
    assert_eq!(simplify("(abs 5)"), "5");
    // assert_eq!(simplify("(+ 0 (* 1 foo))"), "foo");
}
