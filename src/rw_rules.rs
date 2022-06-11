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
}pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> { let mut v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![rewrite!("EGGTHSSOwadd_comm"; /* a0 b0 : word */ "(ATwadd ?a0 ?b0)"=>"(ATwadd ?b0 ?a0)"),
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
rewrite!("EGGHYPH"; "(ATsep           (ATword_array a           (ATapp word           (ATListDOTfirstn word           (ATZDOTto_nat           (ATmydiv (ATunsigned (ATwadd (ATwadd a (ATZToWord 8)) (ATwopp a))) 4))           (ATapp word           (ATListDOTfirstn word (ATMySuc MyO)           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))           (ATapp word (ATcons word w1 (ATnil word))           (ATListDOTskipn word (ATMySuc (ATMySuc MyO))           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word))))))))           (ATapp word (ATcons word w2 (ATnil word))           (ATListDOTskipn word           (ATMySuc           (ATZDOTto_nat           (ATmydiv (ATunsigned (ATwadd (ATwadd a (ATZToWord 8)) (ATwopp a))) 4)))           (ATapp word           (ATListDOTfirstn word (ATMySuc MyO)           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))           (ATapp word (ATcons word w1 (ATnil word))           (ATListDOTskipn word (ATMySuc (ATMySuc MyO))           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))))))))           R m)"<=>"True")].concat()); v}