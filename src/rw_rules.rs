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
"ATmylt" = ATmylt([Id; 2]),
"ATSome" = ATSome([Id; 2]),
"ATmyabs" = ATmyabs([Id; 1]),
 Symbol(Symbol),
    }
}
pub fn run_simplifier(f : fn(&str, Vec<&str>) -> ()) {
    let st : &str = " (ATeq Z (ATmyabs (ATunsigned b)) 3) ";
    let extra_st : Vec<&str> = vec!["  (ATf (ATwadd a b))","(ATg b)","  (ATunsigned (ATZToWord 8))","8","  (ATZDOTto_nat (ATmydiv 8 4))","(ATMySuc (ATMySuc MyO))","  (ATsep           (ATword_array a           (ATapp word           (ATListDOTfirstn word           (ATZDOTto_nat           (ATmydiv (ATunsigned (ATwadd (ATwadd a (ATZToWord 8)) (ATwopp a))) 4))           (ATapp word           (ATListDOTfirstn word (ATMySuc MyO)           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))           (ATapp word (ATcons word w1 (ATnil word))           (ATListDOTskipn word (ATMySuc (ATMySuc MyO))           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word))))))))           (ATapp word (ATcons word w2 (ATnil word))           (ATListDOTskipn word           (ATMySuc           (ATZDOTto_nat           (ATmydiv (ATunsigned (ATwadd (ATwadd a (ATZToWord 8)) (ATwopp a))) 4)))           (ATapp word           (ATListDOTfirstn word (ATMySuc MyO)           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))           (ATapp word (ATcons word w1 (ATnil word))           (ATListDOTskipn word (ATMySuc (ATMySuc MyO))           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))))))))           R m)","True"," (ATmylt 2 3)"," (ATmylt 0 2)","  (ATSome Z (ATunsigned b))","(ATSome Z 3)"];
    f(&st, extra_st);
}pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, ()>> { let mut v  : Vec<Rewrite<CoqSimpleLanguage, ()>> = vec![rewrite!("EGGTHSSOwadd_comm";"   (ATwadd ?a0 ?b0)"=>"(ATwadd ?b0 ?a0)"),
rewrite!("EGGTHSOwadd_0_l";"   (ATwadd (ATZToWord 0) ?a0)"=>"?a0"),
rewrite!("EGGTHSOwadd_0_r";"   (ATwadd ?a0 (ATZToWord 0))"=>"?a0"),
rewrite!("EGGTHSOand_True_l";"   (ATand True ?P)"=>"?P"),
rewrite!("EGGTHSSSOfirstn_cons";"                         (ATListDOTfirstn word (ATMySuc ?n) (ATcons word ?a0 ?l))"=>"                       (ATcons word ?a0 (ATListDOTfirstn word ?n ?l))"),
rewrite!("EGGTHSOand_True_r";"   (ATand ?P True)"=>"?P"),
rewrite!("EGGTHSSSOwadd_assoc";"                        (ATwadd ?a0 (ATwadd ?b0 ?c))"=>"                      (ATwadd (ATwadd ?a0 ?b0) ?c)"),
rewrite!("EGGTHSOeq_eq_True";"   (ATeq word ?a0 ?a0)"=>"True"),
rewrite!("EGGTHSOapp_nil_l";"   (ATapp word (ATnil word) ?l)"=>"?l"),
rewrite!("EGGTHSOapp_nil_r";"   (ATapp word ?l (ATnil word))"=>"?l"),
rewrite!("EGGTHSSSOskipn_cons";"                        (ATListDOTskipn word (ATMySuc ?n) (ATcons word ?a0 ?l))"=>"                      (ATListDOTskipn word ?n ?l)"),
rewrite!("EGGTHSSSOapp_cons";"                      (ATcons word ?a0 (ATapp word ?x ?y))"=>"                    (ATapp word (ATcons word ?a0 ?x) ?y)"),
rewrite!("EGGTHSOwadd_opp";"   (ATwadd ?a0 (ATwopp ?a0))"=>"(ATZToWord 0)"),
rewrite!("EGGTHSOfirstn_O";"                    (ATListDOTfirstn word MyO ?l)"=>"(ATnil word)"),
rewrite!("EGGTHSOskipn_O";"   (ATListDOTskipn word MyO ?l)"=>"?l"),
rewrite!("EGGTHSSSOour_wadd_assoc";"                            (ATwadd (ATwadd ?a0 ?b0) ?c)"=>"                          (ATwadd ?a0 (ATwadd ?b0 ?c))"),
rewrite!("EGGTHSSSOour_app_cons";"                          (ATapp word (ATcons word ?a0 ?x) ?y)"=>"                        (ATcons word ?a0 (ATapp word ?x ?y))"),
rewrite!("EGGTHSSSOsep_comm";"                      (ATsep ?P ?Q ?m0)"=>"(ATsep ?Q ?P ?m0)"),
coq_rewrite!("EGGTHSSSSSOH";"                ?CHENIL0 = (ATmylt ?n ?m0) = True ,               ?CHENIL1 = (ATmylt ?m0 ?p) = True ,               ?CHENIL2 = True " => " (ATmylt ?n ?p) " ),
coq_rewrite!("EGGTHSSSSOH0";"                ?CHENIL0 = (ATSome ?A ?x) = (ATSome ?A ?y),               ?CHENIL1 = ?x " => " ?y " ),
coq_rewrite!("EGGTHSSOH3";"              ?CHENIL0 = (ATmylt 0 ?x) = True ,             ?CHENIL1 = (ATmyabs ?x) " => " ?x " )];v.extend(vec![rewrite!("EGGHYPhyp_missing";"  (ATf (ATwadd a b))"<=>"(ATg b)"),
rewrite!("EGGHYPA1";"  (ATunsigned (ATZToWord 8))"<=>"8"),
rewrite!("EGGHYPC1";"  (ATZDOTto_nat (ATmydiv 8 4))"<=>"(ATMySuc (ATMySuc MyO))"),
rewrite!("EGGHYPH";"  (ATsep           (ATword_array a           (ATapp word           (ATListDOTfirstn word           (ATZDOTto_nat           (ATmydiv (ATunsigned (ATwadd (ATwadd a (ATZToWord 8)) (ATwopp a))) 4))           (ATapp word           (ATListDOTfirstn word (ATMySuc MyO)           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))           (ATapp word (ATcons word w1 (ATnil word))           (ATListDOTskipn word (ATMySuc (ATMySuc MyO))           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word))))))))           (ATapp word (ATcons word w2 (ATnil word))           (ATListDOTskipn word           (ATMySuc           (ATZDOTto_nat           (ATmydiv (ATunsigned (ATwadd (ATwadd a (ATZToWord 8)) (ATwopp a))) 4)))           (ATapp word           (ATListDOTfirstn word (ATMySuc MyO)           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))           (ATapp word (ATcons word w1 (ATnil word))           (ATListDOTskipn word (ATMySuc (ATMySuc MyO))           (ATcons word v0 (ATcons word v1 (ATcons word v2 (ATnil word)))))))))))           R m)"<=>"True"),
rewrite!("EGGHYPH1";"True " <=> " (ATmylt 2 3)"),
rewrite!("EGGHYPH2";"True " <=> " (ATmylt 0 2)"),
rewrite!("EGGHYPlol_hyp";"  (ATSome Z (ATunsigned b))"<=>"(ATSome Z 3)")].concat()); v}