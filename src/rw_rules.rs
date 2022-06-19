
#![allow(missing_docs,non_camel_case_types)]
use crate ::*;
pub fn get_proof_file_path() -> &'static str {
  "/tmp/egg_proof.txt"
}
define_language! {
  pub enum CoqSimpleLanguage {
    Num(i32),
    "Syntax.cmd.cond" = SyntaxDOTcmdDOTcond([Id; 3]),
    "@Datatypes.length" = ATDatatypesDOTlength([Id; 2]),
    "@eq" = ATeq([Id; 3]),
    "Z.pow" = ZDOTpow([Id; 2]),
    "@nil" = ATnil([Id; 1]),
    "@cons" = ATcons([Id; 3]),
    "Z.div" = ZDOTdiv([Id; 2]),
    "@word.sru" = ATwordDOTsru([Id; 4]),
    "@pair.mk" = ATpairDOTmk([Id; 4]),
    "String" = String([Id; 2]),
    "@map.put" = ATmapDOTput([Id; 6]),
    "Z.mul" = ZDOTmul([Id; 2]),
    "Syntax.cmd.set" = SyntaxDOTcmdDOTset([Id; 2]),
    "Z.divide" = ZDOTdivide([Id; 2]),
    "@word.of_Z" = ATwordDOTof_Z([Id; 3]),
    "@word.slu" = ATwordDOTslu([Id; 4]),
    "Z.lt" = ZDOTlt([Id; 2]),
    "@word.add" = ATwordDOTadd([Id; 4]),
    "@word.opp" = ATwordDOTopp([Id; 3]),
    "Syntax.expr.literal" = SyntaxDOTexprDOTliteral([Id; 1]),
    "not" = not([Id; 1]),
    "@reconstruct" = ATreconstruct([Id; 5]),
    "Syntax.expr.var" = SyntaxDOTexprDOTvar([Id; 1]),
    "@word.rep" = ATwordDOTrep([Id; 2]),
    "Syntax.expr.load" = SyntaxDOTexprDOTload([Id; 2]),
    "and" = and([Id; 2]),
    "Syntax.expr.op" = SyntaxDOTexprDOTop([Id; 3]),
    "Z.modulo" = ZDOTmodulo([Id; 2]),
    "Z.of_nat" = ZDOTof_nat([Id; 1]),
    "Z.le" = ZDOTle([Id; 2]),
    "Ascii.Ascii" = AsciiDOTAscii([Id; 8]),
    "@word.unsigned" = ATwordDOTunsigned([Id; 3]),
    "@word.sub" = ATwordDOTsub([Id; 4]),
    Symbol(Symbol),
  }
}

pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> {
  let v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![
    rewrite!("c$def"; "c" => "(Syntax.cmd.cond(Syntax.expr.op Syntax.bopname.ltu(Syntax.expr.load Syntax.access_size.word(Syntax.expr.var(String(Ascii.Ascii true false true true false true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii false false true false false true true false)EmptyString)))))(Syntax.expr.var(String(Ascii.Ascii false false true false true true true false)(String(Ascii.Ascii true false false false false true true false)(String(Ascii.Ascii false true false false true true true false)(String(Ascii.Ascii true true true false false true true false)(String(Ascii.Ascii true false true false false true true false)(String(Ascii.Ascii false false true false true true true false)EmptyString))))))))(Syntax.cmd.set(String(Ascii.Ascii false false true true false true true false)(String(Ascii.Ascii true false true false false true true false)(String(Ascii.Ascii false true true false false true true false)(String(Ascii.Ascii false false true false true true true false)EmptyString))))(Syntax.expr.op Syntax.bopname.add(Syntax.expr.var(String(Ascii.Ascii true false true true false true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii false false true false false true true false)EmptyString))))(Syntax.expr.literal 8)))(Syntax.cmd.set(String(Ascii.Ascii false true false false true true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii true true true false false true true false)(String(Ascii.Ascii false false false true false true true false)(String(Ascii.Ascii false false true false true true true false)EmptyString)))))(Syntax.expr.var(String(Ascii.Ascii true false true true false true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii false false true false false true true false)EmptyString))))))"),
    rewrite!("H0"; "(@word.unsigned 64 word(@word.sub 64 word right left))" => "(Z.mul 8(Z.of_nat(@Datatypes.length(@word.rep 64 word)xs)))"),
    rewrite!("length_rep"; "(@word.unsigned 64 word(@word.sub 64 word x2 x1))" => "(Z.mul 8(Z.of_nat(@Datatypes.length(@word.rep 64 word)x)))"),
    rewrite!("H3"; "(@Datatypes.length(@word.rep 64 word)x)" => "v"),
    rewrite!("H4"; "True" => "(not(@eq Z(@word.unsigned 64 word(@word.sub 64 word x2 x1))0))"),
    rewrite!("mid$def"; "mid" => "(@word.add 64 word x1(@word.slu 64 word(@word.sru 64 word(@word.sub 64 word x2 x1)(@word.of_Z 64 word 4))(@word.of_Z 64 word 3)))"),
    rewrite!("l$def"; "l" => "(@map.put string(@word.rep 64 word)locals localsmap(String(Ascii.Ascii true false true true false true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii false false true false false true true false)EmptyString)))mid)"),
    rewrite!("C1"; "True" => "(and(Z.le 0 8)(Z.lt 8(Z.pow 2 64)))"),
    rewrite!("C2"; "True" => "(and(Z.le 0 3)(Z.lt 3 64))"),
    rewrite!("C3"; "True" => "(and(Z.le 0 4)(Z.lt 4 64))"),
    rewrite!("C4"; "True" => "(Z.le 0(Z.pow 2 3))"),
    rewrite!("C5"; "True" => "(Z.lt 0(Z.pow 2 4))"),
    rewrite!("C6"; "True" => "(Z.lt 0(Z.pow 2 64))"),
    rewrite!("C7"; "True" => "(Z.lt 0(Z.pow 2 3))"),
    rewrite!("C8"; "True" => "(Z.lt(Z.pow 2 3)(Z.pow 2 4))"),
    rewrite!("C9"; "(Z.pow 2 3)" => "8"),
    rewrite!("C10"; "True" => "(Z.divide(Z.pow 2 3)(Z.pow 2 64))"),
    rewrite!("wadd_0_l"; "(@word.add 64 word(@word.of_Z 64 word 0)?x)" => "?x"),
    rewrite!("wadd_0_r"; "(@word.add 64 word ?x(@word.of_Z 64 word 0))" => "?x"),
    rewrite!("wadd_comm"; "(@word.add 64 word ?a ?b)" => "(@word.add 64 word ?b ?a)"),
    rewrite!("wadd_to_left_assoc"; "(@word.add 64 word ?a(@word.add 64 word ?b ?c))" => "(@word.add 64 word(@word.add 64 word ?a ?b)?c)"),
    rewrite!("wadd_to_right_assoc"; "(@word.add 64 word(@word.add 64 word ?a ?b)?c)" => "(@word.add 64 word ?a(@word.add 64 word ?b ?c))"),
    rewrite!("wadd_opp"; "(@word.add 64 word ?a(@word.opp 64 word ?a))" => "(@word.of_Z 64 word 0)"),
    rewrite!("wsub_def"; "(@word.sub 64 word ?a ?b)" => "(@word.add 64 word ?a(@word.opp 64 word ?b))"),
    coq_rewrite!("wunsigned_of_Z_nowrap"; "?$hyp0 = True = (and(Z.le 0 ?x)(Z.lt ?x(Z.pow 2 64))), ?$lhs = (@word.unsigned 64 word(@word.of_Z 64 word ?x))" => "?x"),
    coq_rewrite!("wunsigned_nonneg"; "?$trigger0 = (@word.unsigned 64 word ?x), ?$lhs = True" => "(Z.le 0(@word.unsigned 64 word ?x))"),
    coq_rewrite!("wunsigned_sru_to_div_pow2"; "?$hyp0 = True = (and(Z.le 0 ?a)(Z.lt ?a 64)), ?$lhs = (@word.unsigned 64 word(@word.sru 64 word ?x(@word.of_Z 64 word ?a)))" => "(Z.div(@word.unsigned 64 word ?x)(Z.pow 2 ?a))"),
    coq_rewrite!("wunsigned_slu_to_mul_pow2"; "?$hyp0 = True = (and(Z.le 0 ?a)(Z.lt ?a 64)), ?$lhs = (@word.unsigned 64 word(@word.slu 64 word ?x(@word.of_Z 64 word ?a)))" => "(Z.modulo(Z.mul(@word.unsigned 64 word ?x)(Z.pow 2 ?a))(Z.pow 2 64))"),
    coq_rewrite!("Z_forget_mod_in_lt_l"; "?$hyp0 = True = (Z.le 0 ?a), ?$hyp1 = True = (Z.lt 0 ?m), ?$hyp2 = True = (Z.lt ?a ?b), ?$lhs = True" => "(Z.lt(Z.modulo ?a ?m)?b)"),
    coq_rewrite!("Z_mul_nonneg"; "?$hyp0 = True = (Z.le 0 ?e1), ?$hyp1 = True = (Z.le 0 ?e2), ?$trigger0 = (Z.mul ?e1 ?e2), ?$lhs = True" => "(Z.le 0(Z.mul ?e1 ?e2))"),
    coq_rewrite!("Z_div_nonneg"; "?$hyp0 = True = (Z.le 0 ?a), ?$hyp1 = True = (Z.lt 0 ?b), ?$trigger0 = (Z.div ?a ?b), ?$lhs = True" => "(Z.le 0(Z.div ?a ?b))"),
    coq_rewrite!("Z_div_mul_lt"; "?$hyp0 = True = (Z.lt 0 ?x), ?$hyp1 = True = (Z.lt 0 ?d1), ?$hyp2 = True = (Z.lt ?d1 ?d2), ?$lhs = True" => "(Z.lt(Z.mul(Z.div ?x ?d2)?d1)?x)"),
    coq_rewrite!("Z_lt_from_le_and_neq"; "?$hyp0 = True = (Z.le ?x ?y), ?$hyp1 = True = (not(@eq Z ?x ?y)), ?$lhs = True" => "(Z.lt ?x ?y)"),
    coq_rewrite!("Z_remove_inner_mod"; "?$hyp0 = True = (Z.lt 0 ?n), ?$hyp1 = True = (Z.lt 0 ?m), ?$hyp2 = True = (Z.divide ?n ?m), ?$lhs = (Z.modulo(Z.modulo ?a ?m)?n)" => "(Z.modulo ?a ?n)"),
    rewrite!("Z__mod_mult"; "(Z.modulo(Z.mul ?a ?b)?b)" => "0"),
    rewrite!("H_eq_eq_sym"; "(@eq ?A ?x ?y)" => "(@eq ?A ?y ?x)"),
    rewrite!("H_eq_same_True"; "(@eq ?A ?a ?a)" => "True"),
  ];
  v
}

pub fn get_lemma_arity(name: &str) -> Option<usize> {
  let v = vec![
    ("c$def", 0),
    ("H0", 0),
    ("length_rep", 0),
    ("H3", 0),
    ("H4", 0),
    ("mid$def", 0),
    ("l$def", 0),
    ("C1", 0),
    ("C2", 0),
    ("C3", 0),
    ("C4", 0),
    ("C5", 0),
    ("C6", 0),
    ("C7", 0),
    ("C8", 0),
    ("C9", 0),
    ("C10", 0),
    ("wadd_0_l", 1),
    ("wadd_0_r", 1),
    ("wadd_comm", 2),
    ("wadd_to_left_assoc", 3),
    ("wadd_to_right_assoc", 3),
    ("wadd_opp", 1),
    ("wsub_def", 2),
    ("wunsigned_of_Z_nowrap", 2),
    ("wunsigned_nonneg", 1),
    ("wunsigned_sru_to_div_pow2", 3),
    ("wunsigned_slu_to_mul_pow2", 3),
    ("Z_forget_mod_in_lt_l", 6),
    ("Z_mul_nonneg", 4),
    ("Z_div_nonneg", 4),
    ("Z_div_mul_lt", 6),
    ("Z_lt_from_le_and_neq", 4),
    ("Z_remove_inner_mod", 6),
    ("Z__mod_mult", 2),
    ("H_eq_eq_sym", 3),
    ("H_eq_same_True", 2),
  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

pub fn is_eq(name: &str) -> Option<bool> {
  let v = vec![
    ("c$def", true),
    ("H0", true),
    ("length_rep", true),
    ("H3", true),
    ("H4", false),
    ("mid$def", true),
    ("l$def", true),
    ("C1", false),
    ("C2", false),
    ("C3", false),
    ("C4", false),
    ("C5", false),
    ("C6", false),
    ("C7", false),
    ("C8", false),
    ("C9", true),
    ("C10", false),
    ("wadd_0_l", true),
    ("wadd_0_r", true),
    ("wadd_comm", true),
    ("wadd_to_left_assoc", true),
    ("wadd_to_right_assoc", true),
    ("wadd_opp", true),
    ("wsub_def", true),
    ("wunsigned_of_Z_nowrap", true),
    ("wunsigned_nonneg", false),
    ("wunsigned_sru_to_div_pow2", true),
    ("wunsigned_slu_to_mul_pow2", true),
    ("Z_forget_mod_in_lt_l", false),
    ("Z_mul_nonneg", false),
    ("Z_div_nonneg", false),
    ("Z_div_mul_lt", false),
    ("Z_lt_from_le_and_neq", false),
    ("Z_remove_inner_mod", true),
    ("Z__mod_mult", true),
    ("H_eq_eq_sym", true),
    ("H_eq_same_True", true),
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
    "True",
    "(Z.lt 0(Z.pow 2 4))",
    "v",
    "8",
    "(and(Z.le 0 4)(Z.lt 4 64))",
    "l",
    "(Z.lt(Z.pow 2 3)(Z.pow 2 4))",
    "(Z.divide(Z.pow 2 3)(Z.pow 2 64))",
    "(Z.pow 2 3)",
    "(not(@eq Z(@word.unsigned 64 word(@word.sub 64 word x2 x1))0))",
    "(@Datatypes.length(@word.rep 64 word)x)",
    "mid",
    "(Z.mul 8(Z.of_nat(@Datatypes.length(@word.rep 64 word)x)))",
    "(Z.mul 8(Z.of_nat(@Datatypes.length(@word.rep 64 word)xs)))",
    "(Z.lt 0(Z.pow 2 3))",
    "(@word.unsigned 64 word(@word.sub 64 word x2 x1))",
    "(Z.lt 0(Z.pow 2 64))",
    "(Syntax.cmd.cond(Syntax.expr.op Syntax.bopname.ltu(Syntax.expr.load Syntax.access_size.word(Syntax.expr.var(String(Ascii.Ascii true false true true false true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii false false true false false true true false)EmptyString)))))(Syntax.expr.var(String(Ascii.Ascii false false true false true true true false)(String(Ascii.Ascii true false false false false true true false)(String(Ascii.Ascii false true false false true true true false)(String(Ascii.Ascii true true true false false true true false)(String(Ascii.Ascii true false true false false true true false)(String(Ascii.Ascii false false true false true true true false)EmptyString))))))))(Syntax.cmd.set(String(Ascii.Ascii false false true true false true true false)(String(Ascii.Ascii true false true false false true true false)(String(Ascii.Ascii false true true false false true true false)(String(Ascii.Ascii false false true false true true true false)EmptyString))))(Syntax.expr.op Syntax.bopname.add(Syntax.expr.var(String(Ascii.Ascii true false true true false true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii false false true false false true true false)EmptyString))))(Syntax.expr.literal 8)))(Syntax.cmd.set(String(Ascii.Ascii false true false false true true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii true true true false false true true false)(String(Ascii.Ascii false false false true false true true false)(String(Ascii.Ascii false false true false true true true false)EmptyString)))))(Syntax.expr.var(String(Ascii.Ascii true false true true false true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii false false true false false true true false)EmptyString))))))",
    "(@word.unsigned 64 word(@word.sub 64 word right left))",
    "c",
    "(and(Z.le 0 8)(Z.lt 8(Z.pow 2 64)))",
    "(and(Z.le 0 3)(Z.lt 3 64))",
    "(@word.add 64 word x1(@word.slu 64 word(@word.sru 64 word(@word.sub 64 word x2 x1)(@word.of_Z 64 word 4))(@word.of_Z 64 word 3)))",
    "(Z.le 0(Z.pow 2 3))",
    "(@map.put string(@word.rep 64 word)locals localsmap(String(Ascii.Ascii true false true true false true true false)(String(Ascii.Ascii true false false true false true true false)(String(Ascii.Ascii false false true false false true true false)EmptyString)))mid)",
  ];
  let st : &str = "(Z.lt(@word.unsigned 64 word(@word.sub 64 word mid x1))(Z.mul(@word.unsigned 64 word(@word.of_Z 64 word 8))(Z.of_nat(@Datatypes.length(@word.rep 64 word)x))))";
  f_simplify(st, es);
}
