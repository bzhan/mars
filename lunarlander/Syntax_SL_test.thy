section {* Abstract syntax for Logic. *}

theory Syntax_SL_test 
  imports  Main HOL.Real
begin

(*Constants*)
datatype val = Real real     ("Real _" 76)
             | String string ("String _" 76)
             | Bool bool     ("Bool _" 76)
| Err
(*Expressions of HCSP language.*)
datatype exp = Con val ("Con _" 75)
             | RVar string   ("RVar _" 75 )
             | SVar string   ("SVar _" 75)
             | BVar string   ("BVar _" 75)
             | Add exp exp   (infixr "[+]" 70)
             | Sub exp exp   (infixl  "[-]" 70)
             | Mul exp exp   (infixr "[*]" 71)
(*to complete all related to divide in  following functions.*)
             | Div exp exp   (infixr "[**]" 71) 
ML {*
@{term "Real a"}
*}

ML{*
@{term "RVar a"}

*}


ML{*
@{term "a [+] b"}

*}


(*Type declarations to be used in {*proc*}*)
datatype typeid = R | S | B
(*States*)
type_synonym state = "string * typeid => val"

(*Evaluation of expressions*)
primrec evalE :: "exp \<Rightarrow> state => val" where
"evalE (Con y) f = y" |
"evalE (RVar (x)) f = f (x, R)" |
"evalE (SVar (x)) f = f (x, S)" |
"evalE (BVar (x)) f = f (x, B)" |
"evalE (e1 [+] e2) f = (case (evalE e1 f) of Real (x) =>
                                         (case (evalE e2 f) of Real (y) => Real (x + y) |
                                                                          _    => Err)|
                                                              _ => Err)" |
"evalE (e1 [-] e2) f = (case (evalE e1 f) of  Real (x) =>
                                         (case (evalE e2 f) of  Real (y) =>  Real (x - y) |
                                                                          _    => Err)|
                                                              _ => Err)" |
"evalE (e1 [*] e2) f = (case (evalE e1 f) of  Real (x) =>
                                         (case (evalE e2 f) of Real (y) =>  Real (x * y) |
                                                                          _    => Err)|
                                                              _ => Err)"




section{*FOL operators*}
type_synonym fform = "state  \<Rightarrow> bool"
definition fTrue:: "fform" where " fTrue == \<lambda> s. True"
definition fFalse:: "fform" where "fFalse == \<lambda> s. False"
definition fEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[=]_" 69) where
"e [=] f == \<lambda> s. evalE e s = evalE f s"
definition fLess :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[<]_" 69) where
"e [<] f == \<lambda> s. (case (evalE e s) of Real c \<Rightarrow> (case (evalE f s) of Real d \<Rightarrow> (c<d)
                                                                    |  _ \<Rightarrow> False)
                                       |  _ \<Rightarrow> False )" 

definition fAnd :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixl "[&]"  65) where
"P [&] Q == \<lambda> s. P s \<and> Q s"
definition fOr :: "fform\<Rightarrow> fform \<Rightarrow> fform"  (infixl "[|]" 65) where
"P [|] Q == \<lambda> s. P s \<or> Q s"
definition fNot :: "fform \<Rightarrow> fform"  ("[\<not>]_" 67) where
"[\<not>]P == \<lambda> s. \<not> P s"
definition fImp :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixl "[\<longrightarrow>]" 65) where
"P [\<longrightarrow>] Q == \<lambda> s. P s \<longrightarrow> Q s"

definition fLessEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[\<le>]_" 69) where
"e [\<le>] f == (e [=] f) [|] (e [<] f)"
definition fGreaterEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[\<ge>]_" 69) where
"e [\<ge>] f == [\<not>](e [<] f)"
definition fGreater :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[>]_" 69) where
"e [>] f == [\<not>](e [\<le>] f)"

(*For substitution*)
definition fSubForm :: "fform \<Rightarrow> exp \<Rightarrow> string \<Rightarrow> typeid \<Rightarrow> fform" ("_[_,_,_]" 70) where
"P [e, a, b] == (\<lambda>s. P (\<lambda> (x, r). (if (x = a \<and> r = b) then (evalE e s)
                                                            else (s (x, r)))))"
 
(*close() extends the formula with the boundary, used for continuous evolution.*)
consts close :: "fform \<Rightarrow> fform"

axiomatization where
Lessc[simp]: "close (e [<] f) = e [\<le>] f" and
Greatc[simp]: "close (e [>] f) = e [\<ge>] f" and
Equalc[simp]: "close (e [=] f) = e [=] f" and
GreatEqual[simp] : "close ( e [\<ge>] f) =  e [\<ge>] f" and
Andc[simp]: "close (P [&] Q) = close (P) [&] close (Q)" and
Orc[simp]: "close (P [|] Q) = close (P) [|] close (Q)"

 
lemma notLess : "close ([\<not>] e [<] f) = e [\<ge>] f"
apply (subgoal_tac "[\<not>] e [<] f == e [\<ge>] f", auto)
apply (simp add:fGreaterEqual_def fOr_def fNot_def fLess_def fEqual_def fGreater_def)
done


declare fTrue_def [simp]
declare fFalse_def [simp]
     
(*Types for defining HCSP*)
type_synonym cname = string
type_synonym time = real

(*Communication processes of HCSP*)
datatype comm
= Send "cname" "exp"         ("_!!_" [110,108] 100)      
| Receive "cname" "exp"    ("_??_" [110,108] 100) 

(*HCSP processes*)
datatype proc
= Cm comm
| "Skip"
| Ass "exp" "exp"          ("_ := _" [99, 95] 94)   
| Seq "proc" "proc"                   ("_; _"        [91,90 ] 90)
| Cond "fform" "proc"                 ("IF _ _"   [95,94]93)
| CondG "fform" "proc" "proc"                 ("IFELSE _ _ _"   [95,94,94]93)
| Pref   "comm" "proc"                  ("_\<rightarrow>_"   [95,94]93)           
| join "proc" "proc"                   (infixr "[[" 90)
| meet "proc" "proc"                  ("_<<_" [90,90] 90)
(*Repetition is annotated with invariant*)
| Rep    "proc" "fform"                              ("_*&&_"[91] 90)
| RepN  "proc" "nat"   ("_* NUM _"[91, 90] 90)
(*Continuous evolution is annotated with invariant.*)
| Cont  "(string * typeid) list" "exp list" "fform" "fform"               ("<_:_&&_&_>" [95,95,96]94)
| Interp   "proc" "proc" ("_[[>_"[95,94]94)

(*We assume parallel  composition only occurs in  the topmost level.*)
datatype procP = Par    "proc" "proc"                  (infixr "||" 89)

end

