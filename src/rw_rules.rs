
#![allow(missing_docs,non_camel_case_types)]
use crate ::*;
define_language! {
  pub enum CoqSimpleLanguage {
    Num(i32),
    "wadd" = wadd([Id; 2]),
    "@eq" = ATeq([Id; 3]),
    "Z.pow" = ZDOTpow([Id; 2]),
    "@length" = ATlength([Id; 2]),
    "Z.div" = ZDOTdiv([Id; 2]),
    "wslu" = wslu([Id; 2]),
    "wsub" = wsub([Id; 2]),
    "Z.mul" = ZDOTmul([Id; 2]),
    "wopp" = wopp([Id; 1]),
    "Z.lt" = ZDOTlt([Id; 2]),
    "ZToWord" = ZToWord([Id; 1]),
    "not" = not([Id; 1]),
    "unsigned" = unsigned([Id; 1]),
    "wsru" = wsru([Id; 2]),
    "and" = and([Id; 2]),
    "Z.of_nat" = ZDOTof_nat([Id; 1]),
    "Z.modulo" = ZDOTmodulo([Id; 2]),
    "Z.le" = ZDOTle([Id; 2]),
    Symbol(Symbol),
  }
}

pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> {
  let v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![
    rewrite!("wadd_0_l"; "(wadd (ZToWord 0) ?a)" => "?a"),
    rewrite!("wadd_0_r"; "(wadd ?a (ZToWord 0))" => "?a"),
    rewrite!("wadd_comm"; "(wadd ?a ?b)" => "(wadd ?b ?a)"),
    rewrite!("wadd_to_left_assoc"; "(wadd ?a (wadd ?b ?c))" => "(wadd (wadd ?a ?b) ?c)"),
    rewrite!("wadd_to_right_assoc"; "(wadd (wadd ?a ?b) ?c)" => "(wadd ?a (wadd ?b ?c))"),
    rewrite!("wadd_opp"; "(wadd ?a (wopp ?a))" => "(ZToWord 0)"),
    rewrite!("wsub_def"; "(wsub ?a ?b)" => "(wadd ?a (wopp ?b))"),
    coq_rewrite!("unsigned_of_Z"; "?hyp$0 = (and (Z.le 0 ?a) (Z.lt ?a (Z.pow 2 32))) = True, ?lhs$ = (unsigned (ZToWord ?a))" => "?a"),
    coq_rewrite!("unsigned_nonneg"; "?trigger$0 = (unsigned ?x), ?lhs$ = True" => "(Z.le 0 (unsigned ?x))"),
    coq_rewrite!("unsigned_sru_to_div_pow2"; "?hyp$0 = (and (Z.le 0 ?a) (Z.lt ?a 32)) = True, ?lhs$ = (unsigned (wsru ?x (ZToWord ?a)))" => "(Z.div (unsigned ?x) (Z.pow 2 ?a))"),
    coq_rewrite!("unsigned_slu_to_mul_pow2"; "?hyp$0 = (and (Z.le 0 ?a) (Z.lt ?a 32)) = True, ?lhs$ = (unsigned (wslu ?x (ZToWord ?a)))" => "(Z.modulo (Z.mul (unsigned ?x) (Z.pow 2 ?a)) (Z.pow 2 32))"),
    rewrite!("H"; "(unsigned (wsub x2 x1))" => "(Z.mul 8 (Z.of_nat (@length word x)))"),
    rewrite!("H-rev"; "(Z.mul 8 (Z.of_nat (@length word x)))" => "(unsigned (wsub x2 x1))"),
    rewrite!("H0"; "(not (@eq Z (unsigned (wsub x2 x1)) 0))" => "True"),
    rewrite!("H0-rev"; "True" => "(not (@eq Z (unsigned (wsub x2 x1)) 0))"),
    rewrite!("C1"; "(and (Z.le 0 8) (Z.lt 8 (Z.pow 2 32)))" => "True"),
    rewrite!("C1-rev"; "True" => "(and (Z.le 0 8) (Z.lt 8 (Z.pow 2 32)))"),
    rewrite!("C2"; "(and (Z.le 0 3) (Z.lt 3 32))" => "True"),
    rewrite!("C2-rev"; "True" => "(and (Z.le 0 3) (Z.lt 3 32))"),
    rewrite!("C3"; "(and (Z.le 0 4) (Z.lt 4 32))" => "True"),
    rewrite!("C3-rev"; "True" => "(and (Z.le 0 4) (Z.lt 4 32))"),
    rewrite!("C4"; "(Z.le 0 (Z.pow 2 3))" => "True"),
    rewrite!("C4-rev"; "True" => "(Z.le 0 (Z.pow 2 3))"),
    rewrite!("C5"; "(Z.lt 0 (Z.pow 2 4))" => "True"),
    rewrite!("C5-rev"; "True" => "(Z.lt 0 (Z.pow 2 4))"),
    rewrite!("C6"; "(Z.lt 0 (Z.pow 2 32))" => "True"),
    rewrite!("C6-rev"; "True" => "(Z.lt 0 (Z.pow 2 32))"),
    rewrite!("C7"; "(Z.lt 0 (Z.pow 2 3))" => "True"),
    rewrite!("C7-rev"; "True" => "(Z.lt 0 (Z.pow 2 3))"),
    rewrite!("C8"; "(Z.lt (Z.pow 2 3) (Z.pow 2 4))" => "True"),
    rewrite!("C8-rev"; "True" => "(Z.lt (Z.pow 2 3) (Z.pow 2 4))"),
    coq_rewrite!("Z_forget_mod_in_lt_l"; "?hyp$0 = (Z.le 0 ?a) = True, ?hyp$1 = (Z.lt 0 ?m) = True, ?hyp$2 = (Z.lt ?a ?b) = True, ?lhs$ = (Z.lt (Z.modulo ?a ?m) ?b)" => "True"),
    coq_rewrite!("Z_mul_le"; "?hyp$0 = (Z.le 0 ?e1) = True, ?hyp$1 = (Z.le 0 ?e2) = True, ?trigger$0 = (Z.mul ?e1 ?e2), ?lhs$ = True" => "(Z.le 0 (Z.mul ?e1 ?e2))"),
    coq_rewrite!("Z_div_pos"; "?hyp$0 = (Z.le 0 ?a) = True, ?hyp$1 = (Z.lt 0 ?b) = True, ?trigger$0 = (Z.div ?a ?b), ?lhs$ = True" => "(Z.le 0 (Z.div ?a ?b))"),
    coq_rewrite!("Z_div_mul_lt"; "?hyp$0 = (Z.lt 0 ?x) = True, ?hyp$1 = (Z.lt 0 ?d1) = True, ?hyp$2 = (Z.lt ?d1 ?d2) = True, ?lhs$ = True" => "(Z.lt (Z.mul (Z.div ?x ?d2) ?d1) ?x)"),
    coq_rewrite!("Z_lt_from_le_and_neq"; "?hyp$0 = (Z.le ?x ?y) = True, ?hyp$1 = (not (@eq Z ?x ?y)) = True, ?lhs$ = True" => "(Z.lt ?x ?y)"),
    rewrite!("H_eq_eq_sym"; "(@eq ?A ?x ?y)" => "(@eq ?A ?y ?x)"),
  ];
  v
}

pub fn get_lemma_arity(name: &str) -> Option<usize> {
  let v = vec![
    ("C4", 0),
    ("C3", 0),
    ("Z_forget_mod_in_lt_l", 6),
    ("unsigned_slu_to_mul_pow2", 3),
    ("wadd_comm", 2),
    ("C6", 0),
    ("unsigned_nonneg", 1),
    ("H", 0),
    ("unsigned_of_Z", 2),
    ("wadd_to_left_assoc", 3),
    ("Z_lt_from_le_and_neq", 4),
    ("wsub_def", 2),
    ("wadd_opp", 1),
    ("Z_div_mul_lt", 6),
    ("C7", 0),
    ("unsigned_sru_to_div_pow2", 3),
    ("C5", 0),
    ("H_eq_eq_sym", 3),
    ("Z_div_pos", 4),
    ("wadd_to_right_assoc", 3),
    ("C2", 0),
    ("C1", 0),
    ("wadd_0_r", 1),
    ("Z_mul_le", 4),
    ("wadd_0_l", 1),
    ("H0", 0),
    ("C8", 0),
  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

#[allow(unused_variables)]
pub fn run_simplifier(f_simplify : fn(&str, Vec<&str>) -> (), f_prove : fn(&str, &str, Vec<&str>) -> ()) {
  let st : &str = "(Z.lt (unsigned (wsub (wadd x1 (wslu (wsru (wsub x2 x1) (ZToWord 4)) (ZToWord 3))) x1)) (Z.mul (unsigned (ZToWord 8)) (Z.of_nat (@length word x))))";
  let es = vec![
    //"(ZToWord 0)", // allows decreasing far-fetchedness limit from 4 to 3
    "(Z.le 0 (Z.pow 2 3))",
    "True",
    "(Z.lt (Z.pow 2 3) (Z.pow 2 4))",
    "(Z.lt 0 (Z.pow 2 3))",
    "(and (Z.le 0 8) (Z.lt 8 (Z.pow 2 32)))",
    "(Z.mul 8 (Z.of_nat (@length word x)))",
    "(not (@eq Z (unsigned (wsub x2 x1)) 0))",
    "(unsigned (wsub x2 x1))",
    "(Z.lt 0 (Z.pow 2 4))",
    "(and (Z.le 0 4) (Z.lt 4 32))",
    "(and (Z.le 0 3) (Z.lt 3 32))",
    "(Z.lt 0 (Z.pow 2 32))",
  ];
  f_simplify(st, es);
}

