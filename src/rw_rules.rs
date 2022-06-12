
#![allow(missing_docs,non_camel_case_types)]
use crate ::*;
define_language! {
  pub enum CoqSimpleLanguage {
    Num(i32),
    "eq" = eq([Id; 3]),
    "wadd" = wadd([Id; 2]),
    "Z.pow" = ZDOTpow([Id; 2]),
    "Z.div" = ZDOTdiv([Id; 2]),
    "wslu" = wslu([Id; 2]),
    "wsub" = wsub([Id; 2]),
    "Z.mul" = ZDOTmul([Id; 2]),
    "length" = length([Id; 2]),
    "wopp" = wopp([Id; 1]),
    "Z.lt" = ZDOTlt([Id; 2]),
    "ZToWord" = ZToWord([Id; 1]),
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
  let mut v : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![
    // universally quantified <=>
    rewrite!("wadd_assoc"; "(wadd ?a (wadd ?b ?c))" <=> "(wadd (wadd ?a ?b) ?c)"),

    // equalities
    rewrite!("H"; "(unsigned (wsub x2 x1))" <=> "(Z.mul 8 (Z.of_nat (length word x)))"),
    rewrite!("H0"; "(eq Z (unsigned (wsub x2 x1)) 0)" <=> "False"),
    rewrite!("C1"; "(and (Z.le 0 8) (Z.lt 8 (Z.pow 2 32)))" <=> "True"),
    rewrite!("C2"; "(and (Z.le 0 3) (Z.lt 3 32))" <=> "True"),
    rewrite!("C3"; "(and (Z.le 0 4) (Z.lt 4 32))" <=> "True"),
    rewrite!("C4"; "(Z.le 0 (Z.pow 2 3))" <=> "True"),
    rewrite!("C5"; "(Z.lt 0 (Z.pow 2 4))" <=> "True"),
    rewrite!("C6"; "(Z.lt 0 (Z.pow 2 32))" <=> "True"),
    rewrite!("C7"; "(Z.lt 0 (Z.pow 2 3))" <=> "True"),
    rewrite!("C8"; "(Z.lt (Z.pow 2 3) (Z.pow 2 4))" <=> "True"),
  ].concat();

  v.extend(vec![
    // universally quantified =>
    rewrite!("wadd_0_l"; "(wadd (ZToWord 0) ?a)" => "?a"),
    rewrite!("wadd_0_r"; "(wadd ?a (ZToWord 0))" => "?a"),
    rewrite!("wadd_comm"; "(wadd ?a ?b)" => "(wadd ?b ?a)"),
    rewrite!("wadd_opp"; "(wadd ?a (wopp ?a))" => "(ZToWord 0)"),
    rewrite!("wsub_def"; "(wsub ?a ?b)" => "(wadd ?a (wopp ?b))"),
    rewrite!("unsigned_nonneg"; "(Z.le 0 (unsigned ?x))" => "True"),
    rewrite!("word_sub_add_l_same_l"; "(wsub (wadd ?x ?y) ?x)" => "?y"),
    rewrite!("H_eq_eq_sym"; "(eq ?A ?x ?y)" => "(eq ?A ?y ?x)"),

    coq_rewrite!("unsigned_nonneg_triggering_more";
       "?trigger = (unsigned ?x), ?lhs = True"
       => "(Z.le 0 (unsigned ?x))"),

    // with sideconditions
    coq_rewrite!("unsigned_of_Z"; 
      "?hyp1 = (and (Z.le 0 ?a) (Z.lt ?a (Z.pow 2 32))) = True, ?lhs = (unsigned (ZToWord ?a))"
       => "?a"),
    coq_rewrite!("unsigned_sru_to_div_pow2"; 
      "?hyp1 = (and (Z.le 0 ?a) (Z.lt ?a 32)) = True, ?lhs = (unsigned (wsru ?x (ZToWord ?a)))"
       => "(Z.div (unsigned ?x) (Z.pow 2 ?a))"),   
    coq_rewrite!("unsigned_slu_to_mul_pow2"; 
      "?hyp1 = (and (Z.le 0 ?a) (Z.lt ?a 32)) = True, ?lhs = (unsigned (wslu ?x (ZToWord ?a)))"
      => "(Z.modulo (Z.mul (unsigned ?x) (Z.pow 2 ?a)) (Z.pow 2 32))"),

    coq_rewrite!("ZT_forget_mod_in_lt_l";
      "?hyps = (Z.le 0 ?a) = (Z.lt 0 ?m) = (Z.lt ?a ?b) = True, ?lhs = (Z.lt (Z.modulo ?a ?m) ?b)"
      => "True"),
    coq_rewrite!("ZT_mul_le"; 
      "?hyps = (Z.le 0 ?e1) = (Z.le 0 ?e2) = True, ?trigger = (Z.mul ?e1 ?e2), ?lhs = True"
      => "(Z.le 0 (Z.mul ?e1 ?e2))"),
    coq_rewrite!("ZT_div_pos"; 
      "?hyps = (Z.le 0 ?a) = (Z.lt 0 ?b) = True, ?trigger = (Z.div ?a ?b), ?lhs = True"
      => "(Z.le 0 (Z.div ?a ?b))"),
    coq_rewrite!("ZT_div_mul_lt"; 
      "?hyps = (Z.lt 0 ?x) = (Z.lt 0 ?d1) = (Z.lt ?d1 ?d2) = True, ?trigger = (Z.mul (Z.div ?x ?d2) ?d1), ?lhs = True"
       => "(Z.lt (Z.mul (Z.div ?x ?d2) ?d1) ?x)"),
    coq_rewrite!("ZT_lt_from_le_and_neq"; 
      "?hyp1 = (Z.le ?x ?y) = True, ?hyp2 = (eq Z ?x ?y) = False, ?lhs = True"
       => "(Z.lt ?x ?y)"),
   ]);
  v
}

#[allow(unused_variables)]
pub fn run_simplifier(f_simplify : fn(&str, Vec<&str>) -> (), f_prove : fn(&str, &str, Vec<&str>) -> ()) {
  let st : &str = "(eq Prop (Z.lt (unsigned (wsub (wadd x1 (wslu (wsru (wsub x2 x1) (ZToWord 4)) (ZToWord 3))) x1)) (Z.mul (unsigned (ZToWord 8)) (Z.of_nat (length word x)))) True)";
  let es = vec![
    // all lhs's and rhs's of the equalities above:
    "(unsigned (wsub x2 x1))" , "(Z.mul 8 (Z.of_nat (length word x)))",
    "(eq Z (unsigned (wsub x2 x1)) 0)" , "False",
    "(and (Z.le 0 8) (Z.lt 8 (Z.pow 2 32)))" , "True",
    "(and (Z.le 0 3) (Z.lt 3 32))" , "True",
    "(and (Z.le 0 4) (Z.lt 4 32))" , "True",
    "(Z.le 0 (Z.pow 2 3))" , "True",
    "(Z.lt 0 (Z.pow 2 4))" , "True",
    "(Z.lt 0 (Z.pow 2 32))" , "True",
    "(Z.lt 0 (Z.pow 2 3))" , "True",
    "(Z.lt (Z.pow 2 3) (Z.pow 2 4))" , "True",
  ];
  f_simplify(st, es);
  // (eq Prop (Z.lt (unsigned (wslu (wsru (wsub x2 x1) (ZToWord 4)) (ZToWord 3))) (unsigned (wsub x2 x1))) True)
}

/*
#![allow(missing_docs,non_camel_case_types)]
use crate ::*;
define_language! {
pub enum CoqSimpleLanguage {
        // Template starts here, add symbols, both functions and constants 
        Num(i32),"ATwadd" = ATwadd([Id; 2]),
"ATf" = ATf([Id; 1]),
"ATg" = ATg([Id; 1]),
"ATZToWord" = ATZToWord([Id; 1]),
"ATand" = ATand([Id; 2]),
"ATListDOTfirstn" = ATListDOTfirstn([Id; 3]),
"ATMySuc" = ATMySuc([Id; 1]),
"ATcons" = ATcons([Id; 3]),
"ATeq" = ATeq([Id; 3]),
"ATunsigned" = ATunsigned([Id; 1]),
"ATZDOTto_nat" = ATZDOTto_nat([Id; 1]),
"ATmydiv" = ATmydiv([Id; 2]),
"ATapp" = ATapp([Id; 3]),
"ATnil" = ATnil([Id; 1]),
"ATListDOTskipn" = ATListDOTskipn([Id; 3]),
"ATwopp" = ATwopp([Id; 1]),
"ATsep" = ATsep([Id; 3]),
"ATword_array" = ATword_array([Id; 2]),
 Symbol(Symbol),
    }
}
pub fn run_simplifier(f : fn(&str) -> ()) {
    let st : &str = " (ATand (ATeq word (ATf (ATwadd b a)) (ATg b)) (ATand (ATsep R (ATword_array a (ATcons word v0 (ATcons word w1 (ATcons word w2 (ATnil word))))) m) (ATeq word (ATf (ATwadd b a)) (ATf (ATwadd a b))))) ";
    f(&st);
}
// pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> { let mut v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![rewrite!("EGGTHSSOwadd_comm"; /* a0 b0 : word */ "(ATwadd ?a0 ?b0)"=>"(ATwadd ?b0 ?a0)"),
pub fn make_rules() -> Vec<Rewrite<SymbolLang, ()>> { let mut v  : Vec<Rewrite<SymbolLang, ()>> = vec![rewrite!("EGGTHSSOwadd_comm"; /* a0 b0 : word */ "(ATwadd ?a0 ?b0)"=>"(ATwadd ?b0 ?a0)"),
rewrite!("EGGTHSOwadd_0_l"; /* a0 : word */ "(ATwadd (ATZToWord 0) ?a0)"=>"?a0"),
rewrite!("EGGTHSOwadd_0_r"; /* a0 : word */ "(ATwadd ?a0 (ATZToWord 0))"=>"?a0"),
rewrite!("EGGTHSOand_True_l"; /* P : Prop */ "(ATand True ?P)"=>"?P"),
rewrite!("EGGTHSSSOfirstn_cons"; /* (n : nat) (a0 : word) (l : list word) */                       "(ATListDOTfirstn word (ATMySuc ?n) (ATcons word ?a0 ?l))"=>"                       (ATcons word ?a0 (ATListDOTfirstn word ?n ?l))"),
rewrite!("EGGTHSOand_True_r"; /* P : Prop */ "(ATand ?P True)"=>"?P"),
rewrite!("EGGTHSSSOwadd_assoc"; /* a0 b0 c : word */                      "(ATwadd ?a0 (ATwadd ?b0 ?c))"=>"                      (ATwadd (ATwadd ?a0 ?b0) ?c)"),
rewrite!("EGGTHSOeq_eq_True"; /* a0 : word */ "(ATeq word ?a0 ?a0)"=>"True"),
rewrite!("EGGTHSOapp_nil_l"; /* l : list word */ "(ATapp word (ATnil word) ?l)"=>"?l"),
rewrite!("EGGTHSOapp_nil_r"; /* l : list word */ "(ATapp word ?l (ATnil word))"=>"?l"),
rewrite!("EGGTHSSSOskipn_cons"; /* (n : nat) (a0 : word) (l : list word) */                      "(ATListDOTskipn word (ATMySuc ?n) (ATcons word ?a0 ?l))"=>"                      (ATListDOTskipn word ?n ?l)"),
rewrite!("EGGTHSSSOapp_cons"; /* (x y : list word) (a0 : word) */                    "(ATcons word ?a0 (ATapp word ?x ?y))"=>"                    (ATapp word (ATcons word ?a0 ?x) ?y)"),
rewrite!("EGGTHSOwadd_opp"; /* a0 : word */ "(ATwadd ?a0 (ATwopp ?a0))"=>"(ATZToWord 0)"),
rewrite!("EGGTHSOfirstn_O"; /* l : list word */                  "(ATListDOTfirstn word MyO ?l)"=>"(ATnil word)"),
rewrite!("EGGTHSOskipn_O"; /* l : list word */ "(ATListDOTskipn word MyO ?l)"=>"?l"),
rewrite!("EGGTHSSSOour_wadd_assoc"; /* a0 b0 c : word */                          "(ATwadd (ATwadd ?a0 ?b0) ?c)"=>"                          (ATwadd ?a0 (ATwadd ?b0 ?c))"),
rewrite!("EGGTHSSSOour_app_cons"; /* (x y : list word) (a0 : word) */                        "(ATapp word (ATcons word ?a0 ?x) ?y)"=>"                        (ATcons word ?a0 (ATapp word ?x ?y))"),
rewrite!("EGGTHSSSOsep_comm"; /* (P Q : mem_pred) (m0 : mem) */                    "(ATsep ?P ?Q ?m0)"=>"(ATsep ?Q ?P ?m0)")];v.extend(vec![rewrite!("EGGHYPhyp_missing"; "(ATf (ATwadd a b))"<=>"(ATg b)"),
rewrite!("EGGHYPA1"; "(ATunsigned (ATZToWord 8))"<=>"8"),
rewrite!("EGGHYPC1"; "(ATZDOTto_nat (ATmydiv 8 4))"<=>"(ATMySuc (ATMySuc MyO))"),
rewrite!("EGGHYPH"; "(ATsep           (ATword_array a           (ATapp word           (ATListDOTfirstn word           (ATZDOTto_nat           (ATmydiv (ATunsigned (ATwadd (ATwadd a (ATZToWord 8)) (ATwopp a))) 4))           (ATapp word           (ATListDOTfirstn word (ATMySuc MyO)           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))           (ATapp word (ATcons word w1 (ATnil word))           (ATListDOTskipn word (ATMySuc (ATMySuc MyO))           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word))))))))           (ATapp word (ATcons word w2 (ATnil word))           (ATListDOTskipn word           (ATMySuc           (ATZDOTto_nat           (ATmydiv (ATunsigned (ATwadd (ATwadd a (ATZToWord 8)) (ATwopp a))) 4)))           (ATapp word           (ATListDOTfirstn word (ATMySuc MyO)           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))           (ATapp word (ATcons word w1 (ATnil word))           (ATListDOTskipn word (ATMySuc (ATMySuc MyO))           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))))))))           R m)"<=>"True"),
].concat()); v}
*/
