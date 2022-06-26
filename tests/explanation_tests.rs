use egg::*;

#[test]
fn explanation_test() {
    let rules: Vec<Rewrite<SymbolLang, ()>> = vec![
        rewrite!("decr_f"; "(h (Sf ?a))" => "(h ?a)"),
        rewrite!("decr_g"; "(h (Sg ?a))" => "(h ?a)"),
        rewrite!("H"; "x" => "y")
    ];
    let e1: RecExpr<SymbolLang> = "(h x)".parse().unwrap();
    let e2: RecExpr<SymbolLang> = "(h y)".parse().unwrap();
    let e3: RecExpr<SymbolLang> = "(h (Sf x))".parse().unwrap();
    let e4: RecExpr<SymbolLang> = "(h (Sg y))".parse().unwrap();
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&e1)
        .with_expr(&e2)
        .with_expr(&e3)
        .with_expr(&e4)
        .run(&rules);

    assert_eq!(runner.egraph.equivs(&e3, &e4).len(), 1);

    let explanations = runner.explain_equivalence(&e3, &e4).get_flat_sexps();
    for expl in explanations {
        println!("{expl}");
    }
}


#[test]
fn explanation_test_not_acutally_equal() {
    let rules: Vec<Rewrite<SymbolLang, ()>> = vec![
        rewrite!("H"; "x" => "y")
    ];
    let e1: RecExpr<SymbolLang> = "x".parse().unwrap();
    let e2: RecExpr<SymbolLang> = "y".parse().unwrap();
    let e3: RecExpr<SymbolLang> = "z".parse().unwrap();
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&e1)
        .with_expr(&e2)
        .with_expr(&e3)
        .run(&rules);

    assert_eq!(runner.egraph.equivs(&e1, &e2).len(), 1);
    assert_eq!(runner.egraph.equivs(&e2, &e3).len(), 0);

    // NOTE: if you accidentally ask for an explanation between two non-equal terms,
    // eg e2 and e3, you will get 'assertion failed: next_left != left || next_right != right'
    let explanations = runner.explain_equivalence(&e2, &e1).get_flat_sexps();
    for expl in explanations {
        println!("{expl}");
    }
}
