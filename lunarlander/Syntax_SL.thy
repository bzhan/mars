section \<open>Abstract syntax for Logic\<close>

theory Syntax_SL 
  imports 
    Main HOL.Real
    Ordinary_Differential_Equations.ODE_Analysis
begin

text \<open>Expressions of HCSP language. \<close>
datatype 'a exp = Real real ("Real _" [75] 75)
             | RVar 'a   ("RVar _" [75] 75)
             | DVar 'a ("DVar _" [75] 75)
             | Add "'a exp" "'a exp"   (infixl "[+]" 70)
             | Sub "'a exp" "'a exp"   (infixl "[-]" 70)
             | Mul "'a exp" "'a exp"   (infixl "[*]" 71)
             | Diff "'a exp"  ("Diff _" [73] 73) 



text \<open>States\<close>
type_synonym 'a eval = "real^('a :: finite)"
type_synonym 'a state = "'a eval"
text \<open>A pair of states for recording variables and differential variables\<close>
type_synonym 'a pair_state = "'a state \<times> 'a state"

definition Vagree :: "('a :: finite) pair_state \<Rightarrow> 'a pair_state \<Rightarrow> 'a set \<Rightarrow> bool"
  where "Vagree u v V ==
     (\<forall> i. i \<in> V \<longrightarrow> fst u $ i = fst v $ i \<and> snd u $ i = snd v $ i)"

lemma Vagree_eq: "Vagree \<nu> \<omega> UNIV \<Longrightarrow> \<nu> = \<omega>"
  unfolding Vagree_def 
  by (simp add: vec_eq_iff prod.expand)

text \<open>Differential-free expressions\<close>
primrec DE_free :: "('a :: finite) exp \<Rightarrow> bool" 
  where
  "DE_free (Real y)  = True"
| "DE_free (RVar (x))  = True"
| "DE_free (DVar (x))  = False"
| "DE_free (e1 [+] e2)  = (DE_free e1  \<and> DE_free e2)"
| "DE_free (e1 [-] e2)  = (DE_free e1  \<and> DE_free e2)"
| "DE_free (e1 [*] e2)  = (DE_free e1  \<and> DE_free e2)"
| "DE_free (Diff e)  = False" 

text \<open>Evaluation of differential-free expressions\<close>
primrec evalE_df :: "('a :: finite) exp \<Rightarrow> 'a state \<Rightarrow> real" 
  where
  "evalE_df (Real y) f = y"
| "evalE_df (RVar (x)) f = f $ x"
| "evalE_df (DVar (x)) f = undefined"
| "evalE_df (e1 [+] e2) f = (evalE_df e1 f + evalE_df e2 f)"
| "evalE_df (e1 [-] e2) f = (evalE_df e1 f - evalE_df e2 f)"
| "evalE_df (e1 [*] e2) f = (evalE_df e1 f * evalE_df e2 f)"
| "evalE_df (Diff e) f = undefined"  

primrec frechet :: "'a :: finite exp \<Rightarrow> 'a state => 'a state => real"
  where
  "frechet (Real y) v = (\<lambda> v'. 0)"
| "frechet (RVar x) v = (\<lambda> v'. v' \<bullet> axis x 1)"
| "frechet (DVar x) v = undefined"
| "frechet (e1 [+] e2) v = (\<lambda> v' . frechet e1 v v' + frechet e2 v v')"
| "frechet (e1 [-] e2) v = (\<lambda> v' . frechet e1 v v' - frechet e2 v v')"
| "frechet (e1 [*] e2) v = (\<lambda> v' . (evalE_df e1 v * frechet e2 v v' + frechet e1 v v' * evalE_df e2 v))"
| "frechet (Diff e) v = undefined"


text \<open>Evaluation of all expressions\<close>
primrec evalE :: "'a :: finite exp \<Rightarrow> 'a pair_state \<Rightarrow> real" where
  "evalE (Real y) f = y"
| "evalE (RVar (x)) f = (fst f) $ x"
| "evalE (DVar (x)) f = (snd f) $ x"
| "evalE (e1 [+] e2) f = (evalE e1 f + evalE e2 f)"
| "evalE (e1 [-] e2) f = (evalE e1 f - evalE e2 f)"
| "evalE (e1 [*] e2) f = (evalE e1 f * evalE e2 f)"
| "evalE (Diff e) f = (frechet e (fst f) (snd f))"

lemma DE_free_evalE: 
 "DE_free e \<Longrightarrow> evalE e f = evalE_df e (fst f)"
  by (induct e, auto)

subsection \<open>FOL operators\<close>

type_synonym 'a fform = "'a pair_state \<Rightarrow> bool"

definition fTrue :: "'a fform" where "fTrue \<equiv> \<lambda>s. True"
definition fFalse :: "'a fform" where "fFalse \<equiv> \<lambda>s. False"

definition fEqual :: "'a :: finite exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"  (infixl "[=]" 50) where
  "e [=] f \<equiv> \<lambda>s. evalE e s = evalE f s"

definition fLess :: "'a :: finite exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"  ("(_/ [<] _)"  [51, 51] 50) where
  "e [<] f \<equiv> \<lambda>s. (evalE e s < evalE f s)"

definition fAnd :: "'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a fform"  (infixr "[&]" 35) where
  "P [&] Q \<equiv> \<lambda>s. P s \<and> Q s"

definition fOr :: "'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a fform"  (infixr "[|]" 30) where
  "P [|] Q \<equiv> \<lambda>s. P s \<or> Q s"

definition fNot :: "'a fform \<Rightarrow> 'a fform"  ("[\<not>]_" [40] 40) where
  "[\<not>]P \<equiv> \<lambda>s. \<not> P s"

definition fImp :: "'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a fform"  (infixr "[\<longrightarrow>]" 25) where
  "P [\<longrightarrow>] Q \<equiv> \<lambda>s. P s \<longrightarrow> Q s"

definition fLessEqual :: "'a :: finite exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"  ("(_/ [\<le>] _)"  [51, 51] 50) where
  "e [\<le>] f \<equiv> (e [=] f) [|] (e [<] f)"

definition fGreaterEqual :: "'a :: finite exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"   ("(_/ [\<ge>] _)"  [51, 51] 50) where
  "e [\<ge>] f \<equiv> \<lambda>s. ((evalE e s \<ge> evalE f s))"

definition fGreater :: "'a :: finite exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"   ("(_/ [>] _)"  [51, 51] 50) where
  "e [>] f == [\<not>](e [\<le>] f)"


text \<open>Evaluate on state after assigning value of expression e to RVar a.\<close>
definition fSubForm :: "'a :: finite fform \<Rightarrow> 'a exp \<Rightarrow> 'a \<Rightarrow> 'a fform" ("_\<lbrakk>_,_\<rbrakk>" [71,71] 70) where
  "P \<lbrakk>e, a\<rbrakk> \<equiv> (\<lambda>s. P (\<chi> x. if x = a then evalE e s else (fst s) $ x, snd s))"

text \<open>Evaluate on state after assigning value of expression e to DVar a.\<close>
definition fSubFormD :: "'a :: finite fform \<Rightarrow> 'a exp \<Rightarrow> 'a \<Rightarrow> 'a fform" ("_\<lbrakk>_,_\<rbrakk>\<^sub>D" [71,71] 70) where
  "P \<lbrakk>e, a\<rbrakk>\<^sub>D \<equiv> (\<lambda>s. P (fst s, \<chi> x. if x = a then evalE e s else (snd s) $ x))"

text \<open>The @{term close} operation extends the formula with the boundary,
  used for continuous evolution.\<close>
axiomatization close :: "'a :: finite fform \<Rightarrow> 'a fform" where
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
type_synonym var = string

text \<open>Communication processes of HCSP\<close>
datatype 'a comm =
  Send cname "'a exp"   ("_[!]_" [110,108] 100)
| Receive cname 'a      ("_[?]_" [110,108] 100)

datatype 'a ODE =
  ODEOne 'a "'a exp"  ("odeone _ _" [110,108] 100)
| ODEPar "'a ODE" "'a ODE"  ("odes _, _" [100,100] 90)

fun ODE_vars :: "'a ODE \<Rightarrow> 'a set" where
  "ODE_vars (odeone x e) = { x }"
| "ODE_vars (odes ode1, ode2) = ODE_vars ode1 \<union> ODE_vars ode2"
 
fun wf_ODE :: "'a ODE \<Rightarrow> bool" where
  "wf_ODE (odeone x e) = True"
| "wf_ODE (odes ode1, ode2) = (ODE_vars ode1 \<inter> ODE_vars ode2 = {})"
  
text \<open>HCSP processes\<close>
datatype 'a proc =
  Cm "'a comm"
| Skip
| Ass 'a "'a exp"             ("_ := _" [99,95] 94)
| DAss 'a "'a exp"      
| Seq "'a proc" "'a proc"           ("_; _" [91,90] 90)
| Cond "'a fform" "'a proc"         ("IF _ _" [95,94] 93)
(*| Pref comm proc          ("_\<rightarrow>_" [95,94] 93)*)
| IChoice "'a proc" "'a proc"          (infixr "\<sqinter>" 90)
| EChoice "'a comm" "'a proc" "'a comm" "'a proc"          ("_ \<rightarrow> _ [] _ \<rightarrow> _" [92,91,92,91] 90)
\<comment> \<open>Repetition is annotated with invariant\<close>
| Rep "'a proc" "'a fform"          ("_*&&_" [91] 90)
| RepN "'a proc" nat           ("_* NUM _" [91, 90] 90)
\<comment> \<open>Continuous evolution is annotated with invariant.\<close>
| Cont "'a ODE" "'a fform" "'a fform"  ("<_&&_&_>" [95,95,96] 94)
| Interr "'a proc" "'a comm" "'a proc"       ("_[]_\<rightarrow>_" [95,94,94] 94)

text \<open>We assume parallel composition only occurs in the topmost level.\<close>
datatype 'a procP = Par "'a proc" "'a proc"  (infixr "||" 89)

end
