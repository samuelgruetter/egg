
#![allow(missing_docs,non_camel_case_types)]
use crate ::*;
define_language! {
  pub enum CoqSimpleLanguage {
    Num(i32),
    "@Datatypes.length" = ATDatatypesDOTlength([Id; 2]),
    "@eq" = ATeq([Id; 3]),
    "Z.pow" = ZDOTpow([Id; 2]),
    "@word.sru" = ATwordDOTsru([Id; 4]),
    "Z.div" = ZDOTdiv([Id; 2]),
    "Z.mul" = ZDOTmul([Id; 2]),
    "@word.slu" = ATwordDOTslu([Id; 4]),
    "@word.of_Z" = ATwordDOTof_Z([Id; 3]),
    "@word.add" = ATwordDOTadd([Id; 4]),
    "Z.lt" = ZDOTlt([Id; 2]),
    "@word.opp" = ATwordDOTopp([Id; 3]),
    "not" = not([Id; 1]),
    "@word.rep" = ATwordDOTrep([Id; 2]),
    "and" = and([Id; 2]),
    "Z.modulo" = ZDOTmodulo([Id; 2]),
    "Z.of_nat" = ZDOTof_nat([Id; 1]),
    "Z.le" = ZDOTle([Id; 2]),
    "@word.unsigned" = ATwordDOTunsigned([Id; 3]),
    "@word.sub" = ATwordDOTsub([Id; 4]),
    Symbol(Symbol),
  }
}

pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> {
  let v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![
    rewrite!("length_rep"; "(@word.unsigned 64 word (@word.sub 64 word x2 x1))" => "(Z.mul 8 (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)))"),
    rewrite!("length_rep-rev"; "(Z.mul 8 (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)))" => "(@word.unsigned 64 word (@word.sub 64 word x2 x1))"),
    rewrite!("H4"; "(not (@eq Z (@word.unsigned 64 word (@word.sub 64 word x2 x1)) 0))" => "True"),
    rewrite!("H4-rev"; "True" => "(not (@eq Z (@word.unsigned 64 word (@word.sub 64 word x2 x1)) 0))"),
    rewrite!("C1"; "(and (Z.le 0 8) (Z.lt 8 (Z.pow 2 64)))" => "True"),
    rewrite!("C1-rev"; "True" => "(and (Z.le 0 8) (Z.lt 8 (Z.pow 2 64)))"),
    rewrite!("C2"; "(and (Z.le 0 3) (Z.lt 3 64))" => "True"),
    rewrite!("C2-rev"; "True" => "(and (Z.le 0 3) (Z.lt 3 64))"),
    rewrite!("C3"; "(and (Z.le 0 4) (Z.lt 4 64))" => "True"),
    rewrite!("C3-rev"; "True" => "(and (Z.le 0 4) (Z.lt 4 64))"),
    rewrite!("C4"; "(Z.le 0 (Z.pow 2 3))" => "True"),
    rewrite!("C4-rev"; "True" => "(Z.le 0 (Z.pow 2 3))"),
    rewrite!("C5"; "(Z.lt 0 (Z.pow 2 4))" => "True"),
    rewrite!("C5-rev"; "True" => "(Z.lt 0 (Z.pow 2 4))"),
    rewrite!("C6"; "(Z.lt 0 (Z.pow 2 64))" => "True"),
    rewrite!("C6-rev"; "True" => "(Z.lt 0 (Z.pow 2 64))"),
    rewrite!("C7"; "(Z.lt 0 (Z.pow 2 3))" => "True"),
    rewrite!("C7-rev"; "True" => "(Z.lt 0 (Z.pow 2 3))"),
    rewrite!("C8"; "(Z.lt (Z.pow 2 3) (Z.pow 2 4))" => "True"),
    rewrite!("C8-rev"; "True" => "(Z.lt (Z.pow 2 3) (Z.pow 2 4))"),
    rewrite!("wadd_0_l"; "(@word.add 64 word (@word.of_Z 64 word 0) ?x)" => "?x"),
    rewrite!("wadd_0_r"; "(@word.add 64 word ?x (@word.of_Z 64 word 0))" => "?x"),
    rewrite!("wadd_comm"; "(@word.add 64 word ?a ?b)" => "(@word.add 64 word ?b ?a)"),
    rewrite!("wadd_to_left_assoc"; "(@word.add 64 word ?a (@word.add 64 word ?b ?c))" => "(@word.add 64 word (@word.add 64 word ?a ?b) ?c)"),
    rewrite!("wadd_to_right_assoc"; "(@word.add 64 word (@word.add 64 word ?a ?b) ?c)" => "(@word.add 64 word ?a (@word.add 64 word ?b ?c))"),
    rewrite!("wadd_opp"; "(@word.add 64 word ?a (@word.opp 64 word ?a))" => "(@word.of_Z 64 word 0)"),
    rewrite!("wsub_def"; "(@word.sub 64 word ?a ?b)" => "(@word.add 64 word ?a (@word.opp 64 word ?b))"),
    coq_rewrite!("wunsigned_of_Z_nowrap"; "?hyp$0 = (and (Z.le 0 ?x) (Z.lt ?x (Z.pow 2 64))) = True, ?lhs$ = (@word.unsigned 64 word (@word.of_Z 64 word ?x))" => "?x"),
    coq_rewrite!("wunsigned_nonneg"; "?trigger$0 = (@word.unsigned 64 word ?x), ?lhs$ = True" => "(Z.le 0 (@word.unsigned 64 word ?x))"),
    coq_rewrite!("wunsigned_sru_to_div_pow2"; "?hyp$0 = (and (Z.le 0 ?a) (Z.lt ?a 64)) = True, ?lhs$ = (@word.unsigned 64 word (@word.sru 64 word ?x (@word.of_Z 64 word ?a)))" => "(Z.div (@word.unsigned 64 word ?x) (Z.pow 2 ?a))"),
    coq_rewrite!("wunsigned_slu_to_mul_pow2"; "?hyp$0 = (and (Z.le 0 ?a) (Z.lt ?a 64)) = True, ?lhs$ = (@word.unsigned 64 word (@word.slu 64 word ?x (@word.of_Z 64 word ?a)))" => "(Z.modulo (Z.mul (@word.unsigned 64 word ?x) (Z.pow 2 ?a)) (Z.pow 2 64))"),
    coq_rewrite!("Z_forget_mod_in_lt_l"; "?hyp$0 = (Z.le 0 ?a) = True, ?hyp$1 = (Z.lt 0 ?m) = True, ?hyp$2 = (Z.lt ?a ?b) = True, ?lhs$ = (Z.lt (Z.modulo ?a ?m) ?b)" => "True"),
    coq_rewrite!("Z_mul_nonneg"; "?hyp$0 = (Z.le 0 ?e1) = True, ?hyp$1 = (Z.le 0 ?e2) = True, ?trigger$0 = (Z.mul ?e1 ?e2), ?lhs$ = True" => "(Z.le 0 (Z.mul ?e1 ?e2))"),
    coq_rewrite!("Z_div_pos"; "?hyp$0 = (Z.le 0 ?a) = True, ?hyp$1 = (Z.lt 0 ?b) = True, ?trigger$0 = (Z.div ?a ?b), ?lhs$ = True" => "(Z.le 0 (Z.div ?a ?b))"),
    coq_rewrite!("Z_div_mul_lt"; "?hyp$0 = (Z.lt 0 ?x) = True, ?hyp$1 = (Z.lt 0 ?d1) = True, ?hyp$2 = (Z.lt ?d1 ?d2) = True, ?lhs$ = True" => "(Z.lt (Z.mul (Z.div ?x ?d2) ?d1) ?x)"),
    coq_rewrite!("Z_lt_from_le_and_neq"; "?hyp$0 = (Z.le ?x ?y) = True, ?hyp$1 = (not (@eq Z ?x ?y)) = True, ?lhs$ = True" => "(Z.lt ?x ?y)"),
    rewrite!("H_eq_eq_sym"; "(@eq ?A ?x ?y)" => "(@eq ?A ?y ?x)"),
  ];
  v
}

pub fn get_lemma_arity(name: &str) -> Option<usize> {
  let v = vec![
    ("wunsigned_slu_to_mul_pow2", 3),
    ("C4", 0),
    ("C3", 0),
    ("Z_forget_mod_in_lt_l", 6),
    ("wunsigned_nonneg", 1),
    ("wadd_comm", 2),
    ("length_rep", 0),
    ("C6", 0),
    ("Z_mul_nonneg", 4),
    ("wunsigned_of_Z_nowrap", 2),
    ("wadd_to_left_assoc", 3),
    ("Z_lt_from_le_and_neq", 4),
    ("wsub_def", 2),
    ("wadd_opp", 1),
    ("H4", 0),
    ("Z_div_mul_lt", 6),
    ("C7", 0),
    ("C5", 0),
    ("H_eq_eq_sym", 3),
    ("Z_div_pos", 4),
    ("wadd_to_right_assoc", 3),
    ("C2", 0),
    ("wunsigned_sru_to_div_pow2", 3),
    ("wadd_0_r", 1),
    ("C1", 0),
    ("wadd_0_l", 1),
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
  let st : &str = "(Z.lt (@word.unsigned 64 word (@word.sub 64 word (@word.add 64 word x1 (@word.slu 64 word (@word.sru 64 word (@word.sub 64 word x2 x1) (@word.of_Z 64 word 4)) (@word.of_Z 64 word 3))) x1)) (Z.mul (@word.unsigned 64 word (@word.of_Z 64 word 8)) (Z.of_nat (@Datatypes.length (@word.rep 64 word) x))))";
  let es = vec![
    "(Z.le 0 (Z.pow 2 3))",
    "(and (Z.le 0 3) (Z.lt 3 64))",
    "True",
    "(Z.mul 8 (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)))",
    "(Z.lt (Z.pow 2 3) (Z.pow 2 4))",
    "(Z.lt 0 (Z.pow 2 64))",
    "(Z.lt 0 (Z.pow 2 3))",
    "(@word.unsigned 64 word (@word.sub 64 word x2 x1))",
    "(and (Z.le 0 4) (Z.lt 4 64))",
    "(Z.lt 0 (Z.pow 2 4))",
    "(and (Z.le 0 8) (Z.lt 8 (Z.pow 2 64)))",
    "(not (@eq Z (@word.unsigned 64 word (@word.sub 64 word x2 x1)) 0))",
  ];
  f_simplify(st, es);
}

