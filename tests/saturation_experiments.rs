use egg::*;

define_language! {
    enum SimpleLanguage {
        Num(i32),
        "+" = Add([Id; 2]),
        "opp" = Neg([Id; 1]),
        Symbol(Symbol),
    }
}

fn simplify<'a>(rules: Vec<Rewrite<SimpleLanguage, ()>>, s: &str, extra_s : Vec<&str>) -> (String, StopReason) {
    env_logger::init();

    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<SimpleLanguage> = s.parse().unwrap();
    // let expr: RecExpr<SymbolLang> = s.parse().unwrap();

    let extra_exprs : Vec<RecExpr<SimpleLanguage>> = extra_s.iter().map(|s| { 
        s.parse::<RecExpr<SimpleLanguage>>().unwrap()
    }).collect();
    let mut runner = Runner::default()
        .with_explanations_enabled()
        //.with_node_limit(50)
        .with_iter_limit(2)
        .with_expr(&expr)
        .with_exprs(extra_exprs.iter().map(|x| &*x).collect())
        .run(&rules);
    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    
    print_eclasses(&runner.egraph);

    let best_str: String = format!("{best}");
    println!("Simplified\n{}\nto\n{}\nwith cost {}", expr, best_str.to_string(), best_cost);
    println!("Stop reason: {:?}", runner.stop_reason);
    why_exists(&mut runner, "(+ x x)");
    return (best_str, runner.stop_reason.unwrap());
}


#[test]
fn a_plus_b_minus_a_saturation() {
    let (res, reason) = simplify(vec![
        rewrite!("add_sub_sandwich"; "(+ (+ ?a ?b) (opp ?a))" => "?b"),
        rewrite!("add_comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add_to_left_assoc"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rewrite!("add_to_right_assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
    ], "(+ (+ x y) (opp x))", vec![
    ]);
    assert_eq!(res, "y");
    assert_eq!(std::mem::discriminant(&reason), std::mem::discriminant(&StopReason::Saturated));
}
