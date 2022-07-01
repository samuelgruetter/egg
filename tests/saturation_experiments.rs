use egg::*;

fn simplify<'a>(rules: Vec<Rewrite<SymbolLang, ()>>, s: &str, extra_s : Vec<&str>) -> (String, StopReason) {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<SymbolLang> = s.parse().unwrap();

    let extra_exprs : Vec<RecExpr<SymbolLang>> = extra_s.iter().map(|s| { 
        s.parse::<RecExpr<SymbolLang>>().unwrap()
    }).collect();
    let mut runner = Runner::default()
        .with_explanations_enabled()
        //.with_node_limit(50)
        //.with_iter_limit(2)
        .with_ffn_limit(6)
        .with_expr(&expr)
        .with_exprs(extra_exprs.iter().map(|x| &*x).collect())
        //.with_hook(|r| Ok(print_eclasses(&r.egraph)))
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
    why_exists(&mut runner, "(+ (+ x (+ x y)) (+ (opp x) (opp x)))");
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

#[test]
fn assoc_and_comm_1() {
    let (res, reason) = simplify(vec![
        rewrite!("add_0_l"; "(add zero ?x)" => "?x"),
        rewrite!("add_comm"; "(add ?a ?b)" => "(add ?b ?a)"),
        rewrite!("add_to_left_assoc"; "(add ?a (add ?b ?c))" => "(add (add ?a ?b) ?c)"),
        rewrite!("add_opp"; "(add ?a (neg ?a))" => "zero"),
    ], "(add (add x1 (add x2 (neg x1))) (neg x1))", vec![
        "zero"
    ]);
    assert!(res == "(add x2 (neg x1))" || res == "(add (neg x1) x2)");
    assert_eq!(std::mem::discriminant(&reason), std::mem::discriminant(&StopReason::Saturated));
}

#[test]
fn assoc_and_comm_2() {
    let (res, reason) = simplify(vec![
        rewrite!("add_0_l"; "(add zero ?x)" => "?x"),
        rewrite!("add_comm"; "(add ?a ?b)" => "(add ?b ?a)"),
        rewrite!("add_to_left_assoc"; "(add ?a (add ?b ?c))" => "(add (add ?a ?b) ?c)"),
        rewrite!("add_opp"; "(add ?a (neg ?a))" => "zero"),
        rewrite!("H"; "zero" => "zero"),
    ], "(@eq U (add x2 (neg x1)) (add (add x1 (add x2 (neg x1))) (neg x1)))", vec![
        "zero"
    ]);
    assert!(res == "(@eq U (add x2 (neg x1)) (add x2 (neg x1)))"
         || res == "(@eq U (add (neg x1) x2) (add (neg x1) x2))");
    assert_eq!(std::mem::discriminant(&reason), std::mem::discriminant(&StopReason::Saturated));
}

#[test]
fn multipattern_ffn_needs_to_consider_all_patterns() {
    let (res, reason) = simplify(vec![
        coq_rewrite!("Z_forget_mod_in_lt_l"; "?$hyp0 = &True = (&Z.le &0 ?a), ?$hyp1 = &True = (&Z.lt &0 ?m), ?$hyp2 = &True = (&Z.lt ?a ?b), ?$lhs = &True" => "(&Z.lt(&Z.modulo ?a ?m)?b)"),
        coq_rewrite!("Z_mod_nonneg"; "?$trigger0 = (&Z.modulo ?a ?m), ?$lhs = &True" => "(&Z.le &0 (&Z.modulo ?a ?m))"),
        rewrite!("H1"; "(&Z.le &0 va)" => "&True"),
        rewrite!("H2"; "(&Z.lt &0 vm)" => "&True"),
        rewrite!("H3"; "(&Z.lt va vb)" => "&True"),
    ], "(&Z.lt (&Z.modulo va vm) vb)", vec![
        "(&Z.le &0 va)",
        "(&Z.lt &0 vm)",
        "(&Z.lt va vb)",
    ]);
    assert_eq!(res, "&True");
    assert_eq!(std::mem::discriminant(&reason), std::mem::discriminant(&StopReason::Saturated));
}
