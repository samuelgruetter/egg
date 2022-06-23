
#![allow(missing_docs,non_camel_case_types)]
use crate ::*;
pub fn get_proof_file_path() -> &'static str {
  "/tmp/egg_proof.txt"
}
define_language! {
  pub enum CoqSimpleLanguage {
    "&Build_SModule" = IDBuild_SModule([Id; 2]),
    "&Prop" = IDProp([Id; 0]),
    "&x5" = IDx5([Id; 0]),
    "&option" = IDoption([Id; 1]),
    "&BlackHole" = IDBlackHole([Id; 1]),
    "&@alength" = IDATalength([Id; 2]),
    "&@eq" = IDATeq([Id; 3]),
    "&@default" = IDATdefault([Id; 2]),
    "&O" = IDO([Id; 0]),
    "&x9" = IDx9([Id; 0]),
    "&S" = IDS([Id; 1]),
    "&@aget" = IDATaget([Id; 3]),
    "&empty_Alog" = IDempty_Alog([Id; 1]),
    "&@fst" = IDATfst([Id; 3]),
    "&@Some" = IDATSome([Id; 2]),
    "&and" = IDand([Id; 2]),
    "&ge" = IDge([Id; 2]),
    "&x" = IDx([Id; 0]),
    "&x2" = IDx2([Id; 0]),
    "&@None" = IDATNone([Id; 1]),
    "&SModule" = IDSModule([Id; 0]),
    "&N0" = IDN0([Id; 0]),
    "&ToProve" = IDToProve([Id; 0]),
    "&prod" = IDprod([Id; 2]),
    "&empty_Vlog" = IDempty_Vlog([Id; 2]),
    "&arg_method" = IDarg_method([Id; 0]),
    "&xH" = IDxH([Id; 0]),
    "&N" = IDN([Id; 0]),
    "&False" = IDFalse([Id; 0]),
    "&nat" = IDnat([Id; 0]),
    "&@values" = IDATvalues([Id; 3]),
    "&mkpair" = IDmkpair([Id; 4]),
    "&myreg.read" = IDmyregDOTread([Id; 0]),
    "&Npos" = IDNpos([Id; 1]),
    "&True" = IDTrue([Id; 0]),
  }
}

pub fn symbol_metadata(name : &str) -> Option<(usize,bool)> {
  let v = vec![
    ("&Build_SModule", (2,true)),
    ("&Prop", (0,false)),
    ("&x5", (0,false)),
    ("&option", (1,false)),
    ("&BlackHole", (1,false)),
    ("&@alength", (2,false)),
    ("&@eq", (3,false)),
    ("&@default", (2,false)),
    ("&O", (0,true)),
    ("&x9", (0,false)),
    ("&S", (1,true)),
    ("&@aget", (3,false)),
    ("&empty_Alog", (1,false)),
    ("&@fst", (3,false)),
    ("&@Some", (2,true)),
    ("&and", (2,false)),
    ("&ge", (2,false)),
    ("&x", (0,false)),
    ("&x2", (0,false)),
    ("&@None", (1,true)),
    ("&SModule", (0,false)),
    ("&N0", (0,true)),
    ("&ToProve", (0,false)),
    ("&prod", (2,false)),
    ("&empty_Vlog", (2,false)),
    ("&arg_method", (0,false)),
    ("&xH", (0,true)),
    ("&N", (0,false)),
    ("&False", (0,false)),
    ("&nat", (0,false)),
    ("&@values", (3,false)),
    ("&mkpair", (4,false)),
    ("&myreg.read", (0,false)),
    ("&Npos", (1,true)),
    ("&True", (0,false)),
  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> {
  let v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![
    coq_rewrite!("H6"; "?$hyp0 = &True = (&and(&@eq &N &N0(&Npos &xH))(&@eq &N &x5 ?a)), ?$lhs = (&@None &N)" => "(&@Some &N ?a)"),
    coq_rewrite!("H5"; "?$hyp0 = (&@None &N) = (&@Some &N ?a), ?$lhs = &True" => "(&and(&@eq &N &N0(&Npos &xH))(&@eq &N &x5 ?a))"),
    rewrite!("H7"; "&N0" => "&N0"),
    rewrite!("H3"; "(&empty_Vlog &O &myreg.read)" => "(&@None &N)"),
    rewrite!("H"; "(&empty_Alog(&S &O))" => "(&@None(&prod &nat &N))"),
    rewrite!("H11"; "(&@aget &SModule &x &O)" => "(&Build_SModule &N(&Npos &xH))"),
    rewrite!("H10"; "(&@aget &SModule &x(&S &O))" => "(&Build_SModule &N &arg_method)"),
    rewrite!("H4"; "(&@default &SModule &x)" => "(&Build_SModule &nat &O)"),
    rewrite!("H2"; "(&@alength &SModule &x)" => "(&S(&S &O))"),
    coq_rewrite!("H1"; "?$hyp0 = &True = (&ge ?x(&@alength &SModule &x)), ?$lhs = (&@values &SModule &x ?x)" => "(&@default &SModule &x)"),
    rewrite!("H17"; "(&@aget &SModule &x &O)" => "(&Build_SModule &N &x9)"),
    rewrite!("H8"; "&x9" => "(&Npos &xH)"),
    rewrite!("H12"; "(&@aget &SModule &x(&S &O))" => "(&Build_SModule &N &x2)"),
    rewrite!("and_True_l"; "(&and &True ?P)" => "?P"),
    rewrite!("and_True_r"; "(&and ?P &True)" => "?P"),
    coq_rewrite!("reify_eq"; "?$hyp0 = &True = &True, ?$hyp1 = ?x = ?y, ?$lhs = (&@eq ?t ?x ?y)" => "&True"),
    coq_rewrite!("H0"; "?$hyp0 = (&Build_SModule ?t ?x) = (&Build_SModule ?t ?y), ?$lhs = ?x" => "?y"),
    coq_rewrite!("H9"; "?$hyp0 = (&@Some ?t ?x) = (&@Some ?t ?y), ?$lhs = ?x" => "?y"),
    rewrite!("H13"; "(&@fst ?A ?B(&mkpair ?A ?B ?f ?s))" => "?f"),
    coq_rewrite!("ExGoal"; "?$hyp0 = &True = (&and(&@eq &SModule(&Build_SModule(&option &N)(&@Some &N &arg_method))(&Build_SModule(&option &N)(&@Some &N ?n)))(&@eq &N &x2 ?n)), ?$lhs = &True" => "(&@fst &Prop &N(&mkpair &Prop &N &ToProve ?n))"),
    coq_rewrite!("rv_trigger1"; "?$hyp0 = &True = &True, ?$hyp1 = &arg_method = ?n, ?$lhs = &True" => "(&BlackHole(&and(&@eq &SModule(&Build_SModule(&option &N)(&@Some &N &arg_method))(&Build_SModule(&option &N)(&@Some &N ?n)))(&@eq &N &x2 ?n)))"),
  ];
  v
}

pub fn get_lemma_arity(name: &str) -> Option<usize> {
  let v = vec![
    ("H6", 2),
    ("H5", 2),
    ("H7", 0),
    ("H3", 0),
    ("H", 0),
    ("H11", 0),
    ("H10", 0),
    ("H4", 0),
    ("H2", 0),
    ("H1", 2),
    ("H17", 0),
    ("H8", 0),
    ("H12", 0),
    ("and_True_l", 1),
    ("and_True_r", 1),
    ("reify_eq", 5),
    ("H0", 4),
    ("H9", 4),
    ("H13", 4),
    ("ExGoal", 2),
    ("rv_trigger1", 3),
  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

pub fn is_eq(name: &str) -> Option<bool> {
  let v = vec![
    ("H6", true),
    ("H5", false),
    ("H7", true),
    ("H3", true),
    ("H", true),
    ("H11", true),
    ("H10", true),
    ("H4", true),
    ("H2", true),
    ("H1", true),
    ("H17", true),
    ("H8", true),
    ("H12", true),
    ("and_True_l", true),
    ("and_True_r", true),
    ("reify_eq", true),
    ("H0", true),
    ("H9", true),
    ("H13", true),
    ("ExGoal", false),
    ("rv_trigger1", false),
  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

#[allow(unused_variables)]
pub fn run_simplifier(f_simplify : fn(&str, Vec<&str>) -> (), f_prove : fn(&str, &str, Vec<&str>) -> ()) {
  let es = vec![
    "(&@aget &SModule &x &O)",
    "(&@None(&prod &nat &N))",
    "&N0",
    "(&@aget &SModule &x(&S &O))",
    "(&Npos &xH)",
    "(&Build_SModule &N &arg_method)",
    "(&Build_SModule &N(&Npos &xH))",
    "&arg_method",
    "(&Build_SModule &nat &O)",
    "(&empty_Vlog &O &myreg.read)",
    "&True",
    "(&Build_SModule &N &x9)",
    "(&@None &N)",
    "(&@alength &SModule &x)",
    "(&Build_SModule &N &x2)",
    "(&empty_Alog(&S &O))",
    "&x9",
    "(&S(&S &O))",
    "(&@default &SModule &x)",
  ];
  let st : &str = "(&@eq &Prop &ToProve &True)";
  f_simplify(st, es);
}
