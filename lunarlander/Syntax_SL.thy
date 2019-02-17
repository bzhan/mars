section \<open>Abstract syntax for Logic\<close>

theory Syntax_SL 
  imports Main HOL.Real
begin

text \<open>Constants\<close>
datatype val = Real real     ("Real _" 76)
             | String string ("String _" 76)
             | Bool bool     ("Bool _" 76)
             | Err

text \<open>Expressions of HCSP language. Rules for division still to be added.\<close>
datatype exp = Con val ("Con _" 75)
             | RVar string   ("RVar _" 75 )
             | SVar string   ("SVar _" 75)
             | BVar string   ("BVar _" 75)
             | Add exp exp   (infixr "[+]" 70)
             | Sub exp exp   (infixl "[-]" 70)
             | Mul exp exp   (infixr "[*]" 71)
             | Div exp exp   (infixr "[**]" 71)

text \<open>Type declarations to be used in proc\<close>
datatype typeid = R | S | B

text \<open>States\<close>
type_synonym state = "string * typeid \<Rightarrow> val"

text \<open>Evaluation of expressions\<close>
primrec evalE :: "exp \<Rightarrow> state \<Rightarrow> val" where
  "evalE (Con y) f = y"
| "evalE (RVar (x)) f = f (x, R)"
| "evalE (SVar (x)) f = f (x, S)"
| "evalE (BVar (x)) f = f (x, B)"
| "evalE (e1 [+] e2) f =
   (case evalE e1 f of Real x \<Rightarrow> (case evalE e2 f of Real y \<Rightarrow> Real (x + y) | _ \<Rightarrow> Err) | _ => Err)"
| "evalE (e1 [-] e2) f =
   (case evalE e1 f of Real x \<Rightarrow> (case evalE e2 f of Real y \<Rightarrow> Real (x - y) | _ \<Rightarrow> Err) | _ \<Rightarrow> Err)"
| "evalE (e1 [*] e2) f =
   (case evalE e1 f of Real x \<Rightarrow> (case evalE e2 f of Real y \<Rightarrow> Real (x * y) | _ \<Rightarrow> Err) | _ \<Rightarrow> Err)"
| "evalE (e1 [**] e2) f = undefined"

subsection \<open>FOL operators\<close>

type_synonym fform = "state \<Rightarrow> bool"

definition fTrue :: fform where "fTrue \<equiv> \<lambda>s. True"
definition fFalse :: fform where "fFalse \<equiv> \<lambda>s. False"

definition fEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  (infix "[=]" 69) where
  "e [=] f \<equiv> \<lambda>s. evalE e s = evalE f s"

definition fLess :: "exp \<Rightarrow> exp \<Rightarrow> fform"  (infix "[<]" 69) where
  "e [<] f \<equiv> \<lambda>s. (case evalE e s of
      Real c \<Rightarrow> (case evalE f s of Real d \<Rightarrow> (c < d) | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

definition fAnd :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixl "[&]" 65) where
  "P [&] Q \<equiv> \<lambda>s. P s \<and> Q s"

definition fOr :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixl "[|]" 65) where
  "P [|] Q \<equiv> \<lambda>s. P s \<or> Q s"

definition fNot :: "fform \<Rightarrow> fform"  ("[\<not>]_" 67) where
  "[\<not>]P \<equiv> \<lambda>s. \<not> P s"

definition fImp :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixl "[\<longrightarrow>]" 65) where
  "P [\<longrightarrow>] Q \<equiv> \<lambda>s. P s \<longrightarrow> Q s"

definition fLessEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  (infix "[\<le>]" 69) where
  "e [\<le>] f \<equiv> (e [=] f) [|] (e [<] f)"

definition fGreaterEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  (infix "[\<ge>]" 69) where
  "e [\<ge>] f \<equiv> \<lambda>s. (case evalE e s of
      Real c \<Rightarrow> (case (evalE f s) of Real d \<Rightarrow> (c \<ge> d) | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

definition fGreater :: "exp \<Rightarrow> exp \<Rightarrow> fform"  (infix "[>]" 69) where
  "e [>] f == [\<not>](e [\<le>] f)"


text \<open>Evaluate on state after assigning value of expression e to (a, b).\<close>
definition fSubForm :: "fform \<Rightarrow> exp \<Rightarrow> string \<Rightarrow> typeid \<Rightarrow> fform" ("_\<lbrakk>_,_,_\<rbrakk>" 70) where
  "P \<lbrakk>e, a, b\<rbrakk> \<equiv> (\<lambda>s. P (\<lambda> (x, r). if x = a \<and> r = b then evalE e s else s (x, r)))"


text \<open>The @{term close} operation extends the formula with the boundary,
  used for continuous evolution.\<close>
axiomatization close :: "fform \<Rightarrow> fform" where
  Lessc[simp]: "close (e [<] f) = e [\<le>] f" and
  Greatc[simp]: "close (e [>] f) = e [\<ge>] f" and
  Equalc[simp]: "close (e [=] f) = e [=] f" and
  GreatEqual[simp] : "close (e [\<ge>] f) = e [\<ge>] f" and
  Andc[simp]: "close (P [&] Q) = close (P) [&] close (Q)" and
  Orc[simp]: "close (P [|] Q) = close (P) [|] close (Q)" and
  notLessc[simp]: "close ([\<not>] e [<] f) = e [\<ge>] f"

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
| Cont "(string * typeid) list" "exp list" fform fform  ("<_:_&&_&_>" [95,95,96] 94)
| Interp proc proc        ("_[[>_" [95,94] 94)

text \<open>We assume parallel composition only occurs in the topmost level.\<close>
datatype procP = Par proc proc  (infixr "||" 89)

end
