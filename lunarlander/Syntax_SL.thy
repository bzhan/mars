section \<open>Abstract syntax for Logic\<close>

theory Syntax_SL 
  imports Main HOL.Real
begin

text \<open>Expressions of HCSP language. \<close>
datatype exp = Real real ("Real _" [75] 75)
             | RVar string   ("RVar _" [75] 75)
             | Add exp exp   (infixl "[+]" 70)
             | Sub exp exp   (infixl "[-]" 70)
             | Mul exp exp   (infixl "[*]" 71)
             | Div exp exp   (infixl "[div]" 71)
             | Pow exp nat   (infixl "[**]" 72)

 
text \<open>States\<close>
type_synonym state = "string  \<Rightarrow> real"

text \<open>Evaluation of expressions\<close>
primrec evalE :: "exp \<Rightarrow> state \<Rightarrow> real" where
  "evalE (Real y) f = y"
| "evalE (RVar (x)) f = f x"
| "evalE (e1 [+] e2) f = (evalE e1 f + evalE e2 f)"
| "evalE (e1 [-] e2) f = (evalE e1 f - evalE e2 f)"
| "evalE (e1 [*] e2) f = (evalE e1 f * evalE e2 f)"
| "evalE (e1 [div] e2) f = (evalE e1 f / evalE e2 f)"
| "evalE (e1 [**] n) f = (evalE e1 f  ^ n)"

subsection \<open>FOL operators\<close>

type_synonym fform = "state \<Rightarrow> bool"

definition fTrue :: fform where "fTrue \<equiv> \<lambda>s. True"
definition fFalse :: fform where "fFalse \<equiv> \<lambda>s. False"

definition fEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  (infixl "[=]" 50) where
  "e [=] f \<equiv> \<lambda>s. evalE e s = evalE f s"

definition fLess :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("(_/ [<] _)"  [51, 51] 50) where
  "e [<] f \<equiv> \<lambda>s. (evalE e s < evalE f s)"

definition fAnd :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixr "[&]" 35) where
  "P [&] Q \<equiv> \<lambda>s. P s \<and> Q s"

definition fOr :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixr "[|]" 30) where
  "P [|] Q \<equiv> \<lambda>s. P s \<or> Q s"

definition fNot :: "fform \<Rightarrow> fform"  ("[\<not>]_" [40] 40) where
  "[\<not>]P \<equiv> \<lambda>s. \<not> P s"

definition fImp :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixr "[\<longrightarrow>]" 25) where
  "P [\<longrightarrow>] Q \<equiv> \<lambda>s. P s \<longrightarrow> Q s"

definition fLessEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("(_/ [\<le>] _)"  [51, 51] 50) where
  "e [\<le>] f \<equiv> (e [=] f) [|] (e [<] f)"

definition fGreaterEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"   ("(_/ [\<ge>] _)"  [51, 51] 50) where
  "e [\<ge>] f \<equiv> \<lambda>s. ((evalE e s \<ge> evalE f s))"

definition fGreater :: "exp \<Rightarrow> exp \<Rightarrow> fform"   ("(_/ [>] _)"  [51, 51] 50) where
  "e [>] f == [\<not>](e [\<le>] f)"


text \<open>Evaluate on state after assigning value of expression e to (a, b).\<close>
definition fSubForm :: "fform \<Rightarrow> exp \<Rightarrow> string \<Rightarrow> fform" ("_\<lbrakk>_,_\<rbrakk>" [71,71] 70) where
  "P \<lbrakk>e, a\<rbrakk> \<equiv> (\<lambda>s. P (\<lambda> x. if x = a then evalE e s else s x))"


text \<open>The @{term close} operation extends the formula with the boundary,
  used for continuous evolution.\<close>
axiomatization close :: "fform \<Rightarrow> fform" where
  Lessc[simp]: "close (e [<] f) = (e [\<le>] f)" and
  Greatc[simp]: "close (e [>] f) = (e [\<ge>] f)" and
  Equalc[simp]: "close (e [=] f) = (e [=] f)" and
  LessEqual[simp]: "close (e [\<le>] f) = (e [\<le>] f)" and
  GreatEqual[simp] : "close (e [\<ge>] f) = (e [\<ge>] f)" and
  Andc[simp]: "close (P [&] Q) = (close (P) [&] close (Q))" and
  Orc[simp]: "close (P [|] Q) = (close (P) [|] close (Q))" and
  notLessc[simp]: "close ([\<not>] e [<] f) = (e [\<ge>] f)"

declare fTrue_def [simp]
declare fFalse_def [simp]
     
text \<open>Types for defining HCSP\<close>
type_synonym cname = string
type_synonym time = real

text \<open>Communication processes of HCSP\<close>
datatype comm =
  Send cname exp         ("_!!_" [110,108] 100)
  | Receive cname exp      ("_??_" [110,108] 100)



text \<open>HCSP processes\<close>
datatype proc =
  Cm comm
| Skip
| Ass exp exp             ("_ := _" [99,95] 94)
| Seq proc proc           ("_; _" [91,90] 90)
| Cond fform proc         ("IF _ _" [95,94] 93)
| CondG fform proc proc   ("IFELSE _ _ _" [95,94,94] 93)
| Pref comm proc          ("_\<rightarrow>_" [95,94] 93)
| join proc proc          (infixr "[[" 90)
| meet proc proc          ("_<<_" [90,90] 90)
\<comment> \<open>Repetition is annotated with invariant\<close>
| Rep proc fform          ("_*&&_" [91] 90)
| RepN proc nat           ("_* NUM _" [91, 90] 90)
\<comment> \<open>Continuous evolution is annotated with invariant.\<close>
| Cont "string list" "exp list" fform fform  ("<_:_&&_&_>" [95,95,96] 94)
| Interp proc proc        ("_[[>_" [95,94] 94)

text \<open>We assume parallel composition only occurs in the topmost level.\<close>
datatype procP = Par proc proc  (infixr "||" 89)

end
