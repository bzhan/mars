section \<open>Abstract syntax for Logic\<close>

theory syntax_sl
  imports 
    Main HOL.Real
    Ordinary_Differential_Equations.ODE_Analysis
begin

text \<open>States\<close>

type_synonym 'a eval = "real^('a :: finite)"

type_synonym 'a state = "'a eval"

definition update :: "'a :: finite state \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a state"
  where "update u a r = (\<chi> i. if i = a then r else  u $ i)"


definition Vagree :: "('a :: finite) state \<Rightarrow> 'a state \<Rightarrow> 'a set \<Rightarrow> bool"
  where "Vagree u v V == 
     (\<forall> i.  i \<in> V \<longrightarrow>  u $ i =  v $ i)"


lemma Vagree_eq:"Vagree \<nu> \<omega> UNIV \<Longrightarrow> \<nu> = \<omega>"
  unfolding Vagree_def 
  by (simp add: vec_eq_iff prod.expand)


type_synonym 'a exp = "'a state \<Rightarrow> real"


text \<open>first-order formulas\<close>
type_synonym 'a fform = "'a state => bool"
definition fTrue :: "'a fform" where "fTrue \<equiv> \<lambda>s. True"
definition fFalse :: "'a fform" where "fFalse \<equiv> \<lambda>s. False"
declare fTrue_def [simp]
declare fFalse_def [simp]

definition fEqual :: "'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"  (infixl "[=]" 50) where
  "e [=] f \<equiv> \<lambda>s. e s = f s"

definition fLess :: "'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"  ("(_/ [<] _)"  [51, 51] 50) where
  "e [<] f \<equiv> \<lambda>s. (e s < f s)"

definition fAnd :: "'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a fform"  (infixr "[&]" 35) where
  "P [&] Q \<equiv> \<lambda>s. P s \<and> Q s"

definition fOr :: "'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a fform"  (infixr "[\<or>]" 30) where
  "P [\<or>] Q \<equiv> \<lambda>s. P s \<or> Q s"

definition fNot :: "'a fform \<Rightarrow> 'a fform"  ("[\<not>]_" [40] 40) where
  "[\<not>]P \<equiv> \<lambda>s. \<not> P s"

definition fImp :: "'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a fform"  (infixr "[\<longrightarrow>]" 25) where
  "P [\<longrightarrow>] Q \<equiv> \<lambda>s. P s \<longrightarrow> Q s"

definition fLessEqual :: "'a  exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"  ("(_/ [\<le>] _)"  [51, 51] 50) where
  "e [\<le>] f \<equiv> (e [=] f) [\<or>] (e [<] f)"

definition fGreaterEqual :: "'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"   ("(_/ [\<ge>] _)"  [51, 51] 50) where
  "e [\<ge>] f \<equiv> \<lambda>s. (e s \<ge> f s)"

definition fGreater :: "'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a fform"   ("(_/ [>] _)"  [51, 51] 50) where
  "e [>] f == [\<not>](e [\<le>] f)"


text \<open>Types for defining HCSP\<close>
type_synonym cname = string
type_synonym time = real
type_synonym var = string

text \<open>Communication processes of HCSP\<close>
datatype 'a comm =
  Send cname "'a exp"         ("_[!]_" [110,108] 100)
  | Receive cname 'a      ("_[?]_" [110,108] 100)

datatype 'a ODE =
  ODE "'a set" "'a \<Rightarrow> 'a exp"

fun ODE_vars :: "'a ODE \<Rightarrow> 'a set" where
  "ODE_vars (ODE S f) = S"
  
text \<open>HCSP processes\<close>
datatype 'a proc =
  Cm "'a comm"
| Skip
| Ass 'a "'a exp"             ("_ ::= _" [99,95] 94)    
| Seq "'a proc" "'a proc"           ("_; _" [91,90] 90)
| Cond "'a fform" "'a proc"         ("IF _ _" [95,94] 93)
| IFELSE "'a fform" "'a proc" "'a proc"     ("IFELSE _ _ _" [95,94] 93)
(*| Pref comm proc          ("_\<rightarrow>_" [95,94] 93)*)
| IChoice "'a proc" "'a proc"          (infixr "\<sqinter>" 90)
| EChoice "'a comm" "'a proc" "'a comm" "'a proc"          ("_ \<rightarrow>  _ [] _ \<rightarrow> _" [92,91,92,91] 90)
\<comment> \<open>Repetition is annotated with invariant\<close>
| Rep "'a proc" "'a fform"          ("_*&&_" [91] 90)
| RepN "'a proc" nat           ("_* NUM _" [91, 90] 90)
\<comment> \<open>Continuous evolution is annotated with invariant.\<close>
| Cont "'a ODE" "'a fform" "'a fform"  ("<_&&_&_>" [95,95,96] 94)
| InterOne "'a proc" "'a comm" "'a proc"       ("_ |> _ \<rightarrow> _" [95,94,94] 94)
| InterTwo "'a proc" "'a comm" "'a proc" "'a comm" "'a proc"         ("_ |>> _ \<rightarrow> _, _ \<rightarrow> _" [95,94,94,94,94] 94)

text \<open>We assume parallel composition only occurs in the topmost level.\<close>
datatype 'a procP = Par "'a proc"  "'a proc"  (infixr "||" 89)


type_synonym now = real


type_synonym 'a history = "time \<Rightarrow> 'a state"
fun extend_history :: "'a::finite history \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a history" where
  "extend_history f a d = (\<lambda> t. if t > a \<and> t \<le> a + d then f a else f t)"


subsection \<open>Five kinds of events for HCSP processes\<close>
datatype event =
  Tau
| In cname real
| Out cname real 
| IO cname real 
| Delay time

subsection \<open>Auxiliary functions needed to be introduced first.\<close>

text \<open>Two events are compatible if they are In-Out pairs.\<close>
primrec compat :: "event \<Rightarrow> event \<Rightarrow> bool" where
  "compat Tau ev = False"
| "compat (In ch val) ev = (if ev = Out ch val then True else False)"
| "compat (Out ch val) ev = (if ev = In ch val then True else False)"
| "compat (IO ch val) ev = False"
| "compat (Delay d) ev = False"

text \<open>handshake between an In-Out pair is an IO event.\<close>
primrec handshake :: "event \<Rightarrow> event \<Rightarrow> event" where
  "handshake Tau ev = Tau"
| "handshake (In ch val) ev = (if ev = Out ch val then IO ch val else Tau)"
| "handshake (Out ch val) ev = (if ev = In ch val then IO ch val else Tau)"
| "handshake (IO ch val) ev = Tau"
| "handshake (Delay d) ev = Tau"

text \<open>Set of channels of a procedure\<close>
primrec chansetC :: "'a comm => string set" where 
  "chansetC (ch[!]e) = {ch}"
| "chansetC (ch[?]e) = {ch}"

primrec chanset :: "'a proc \<Rightarrow> string set" where
  "chanset (Cm r) = chansetC r"
| "chanset Skip = {}"
| "chanset (e ::= f) = {}"
| "chanset (P; Q) = chanset P \<union> chanset Q"
| "chanset (IF b P) = chanset P"
| "chanset (IFELSE b P Q) = chanset P \<union> chanset Q"
| "chanset (P \<sqinter> Q) = chanset P \<union> chanset Q"
| "chanset (c \<rightarrow> P [] d \<rightarrow> Q) = chansetC c  \<union> chansetC d  \<union> chanset P \<union> chanset Q"
| "chanset (P *&& Inv) = chanset P"
| "chanset (P * NUM n) = chanset P"
| "chanset (<ODEs && Inv & b>) = {}"
| "chanset (P |> c \<rightarrow> Q) = chanset P \<union> chanset Q \<union> chansetC c"
| "chanset (P |>> c \<rightarrow> Q, d \<rightarrow> F) = chanset P \<union> chanset Q \<union> chansetC c \<union> chansetC d \<union> chanset F"

subsection \<open>Definitions for ODEs\<close>

text \<open>the value of vector field\<close>
fun ODE2Vec :: "('a :: finite) ODE \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "ODE2Vec (ODE S f) s = (\<chi> a. if a \<in> S then f a s else 0)"

definition ODEsol :: "('a :: finite) ODE \<Rightarrow> (real \<Rightarrow> 'a state) \<Rightarrow>real \<Rightarrow> bool" where
  "ODEsol ode p d = ((d\<ge>0) \<and> ((p has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {0 .. d}))"


definition ODEstate :: "('a :: finite) ODE \<Rightarrow> real \<Rightarrow> 'a state \<Rightarrow> 'a state \<Rightarrow> bool" where
  "ODEstate ode d u v = (d\<ge>0 \<and> (\<exists> f . ODEsol ode f d \<and> u = f 0 \<and> v = f d ))"

lemma veclim:"((\<lambda>y. v y) \<longlongrightarrow> 0) (at t within D) \<Longrightarrow> ((\<lambda>y. v y $ i) \<longlongrightarrow> 0) (at t within D)"
  using tendsto_vec_nth by fastforce


lemma proj:
  assumes "(p has_vector_derivative q t) (at t within D) "
  shows "((\<lambda>t. p t $ i) has_vector_derivative q t $ i) (at t within D) "
  using assms unfolding has_vector_derivative_def has_derivative_def 
  apply (simp add: bounded_linear_scaleR_left)
  using veclim by fastforce
  
lemma mvt_real_eq:
  fixes p :: "real \<Rightarrow>real"
 assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
  and "d\<ge>0"
  and "\<forall>t\<in>{0 .. d}. \<forall>s. q t s = 0"
  and "x\<in>{0 .. d}"
  shows "p 0 = p x" 
proof-
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by force
qed


lemma mvt_real_ge:
  fixes p :: "real \<Rightarrow>real"
 assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
  and "d\<ge>0"
  and "\<forall>t\<in>{0 .. d}. \<forall>s\<ge>0. q t s \<ge> 0"
  and "x\<in>{0 .. d}"
  shows "p 0 \<le> p x "
  proof-
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by (smt atLeastAtMost_iff greaterThanLessThan_iff)
qed

lemma mvt_real_le:
  fixes p :: "real \<Rightarrow>real"
 assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
  and "d\<ge>0"
  and "\<forall>t\<in>{0 .. d}. \<forall>s\<ge>0 . q t s \<le> 0"
    and "x\<in>{0 .. d}"
  shows "p 0 \<ge> p x "
  proof-
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by (smt atLeastAtMost_iff greaterThanLessThan_iff)
qed

lemma mvt_vector:
  fixes p :: "real \<Rightarrow> ('a :: finite) state"
  assumes "\<forall>t\<in>{0 .. d}. ((p has_vector_derivative q t) (at t within {0 .. d}) \<and> q t $ i = 0)"
  and "d\<ge>0"
  shows "p 0 $ i = p d $ i"
proof-
  have step1:"\<forall>t\<in>{0 .. d}. ((\<lambda>t. p t $ i) has_vector_derivative q t $ i) (at t within {0 .. d})" 
    using assms proj by blast
  have step2:"\<forall>t\<in>{0 .. d}. q t $ i = 0" 
    using assms by auto
  show ?thesis
    using assms step1 step2 unfolding has_vector_derivative_def 
    using mvt_simple [where f="(\<lambda>t. p t $ i)" and f'="(\<lambda>t. \<lambda> x. x *\<^sub>R q t $ i)" and a="0" and b="d"]
    by force
qed


lemma odeVagree:
  assumes "ODEstate (ODE S f) d u v "
  shows "Vagree u v (-S)"
proof -
  from assms obtain p  where ode_sol: "ODEsol (ODE S f) p d" "u = p 0" "v = p d" "d\<ge>0"
    using ODEstate_def by blast
  have "u $ i = v $ i" if cond:"i \<notin> S" for i
    using ode_sol cond 
    unfolding ODEsol_def has_vderiv_on_def 
    using mvt_vector[where p="p" and i="i"  and d="d" and q="\<lambda>x. ODE2Vec (ODE S f) (p x)"]
    by auto
  then show ?thesis
    unfolding Vagree_def by auto
qed



  term "Deriv.has_vector_derivative"
  term "at x within (S::real set)"


lemma chainrule:
  assumes "\<forall> x. ((g :: ('a :: finite) exp ) has_derivative g' x ) (at x within UNIV)"
      and "ODEsol ode p d"
      and "t\<in>{0 .. d}"
    shows "((\<lambda>t. g (p t)) has_derivative (\<lambda>s. g'(p t) (s*\<^sub>R(ODE2Vec ode (p t))))) (at t within {0 .. d}) "
proof-
  have step1:"(\<And>x. x \<in> UNIV \<Longrightarrow> (g has_derivative g' x) (at x))"
    using assms(1) by auto
  have step2:"0 \<le> t \<and> t \<le> d"
    using assms(3) by auto
  have step3:"(p has_derivative (\<lambda>s. s *\<^sub>R ODE2Vec ode (p t))) (at t within {0..d})"
    using step2 assms(2) unfolding ODEsol_def has_vderiv_on_def has_vector_derivative_def by auto
  show ?thesis
  using step1 step2 step3 has_derivative_in_compose2[of UNIV g g' p "{0 .. d}" t "\<lambda>s. (s*\<^sub>R(ODE2Vec ode(p t)))"]
  by auto
qed

lemma derivconst:"\<forall>x. ((\<lambda>t. c) has_derivative (\<lambda>t. 0)) (at x)"
  unfolding has_derivative_def by auto
lemma derivcoord:"\<forall>x. ((\<lambda>t. t$i) has_derivative (\<lambda>t. t$i)) (at x)"
  unfolding has_derivative_def by auto



definition INV :: " ('a :: finite) fform  \<Rightarrow> (real \<Rightarrow> 'a state) \<Rightarrow> real \<Rightarrow> bool" where
"INV Inv p d  \<equiv>  ((d \<ge> 0) \<and> (\<forall>t. 0\<le>t\<and>t\<le>d \<longrightarrow> Inv (p t)))"

subsection \<open>Big-step semantics\<close>

text \<open>Continuous evolution domain: assume b is an open formula, otherwise
the escaping point cannot be found.\<close>

inductive semB :: "'a :: finite proc \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> bool" where
  skipB: "semB Skip now f now f"
| assignB: "semB (x ::= e) now f 
    now (\<lambda>t. if t = now then update (f t) x ( e (f t)) else f t)"
| continuous: "d \<ge> 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall> t. (t \<ge> 0 \<and> t < d \<longrightarrow> b (p t))) \<Longrightarrow> \<not> b (p d) \<Longrightarrow> f now = p 0 \<Longrightarrow>
    semB (<ode && Inv&b>) now f 
      (now + d) (\<lambda>t. if t \<le> now + d \<and> t \<ge> now then
                       p (t-now)
                     else f t)"
| sequenceB: "semB P now f now' f' \<and> semB Q now' f' now'' f'' \<Longrightarrow> semB (P; Q) now f now'' f''"
| conditionBT: " b (f now) \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (IF b P) now f now_d f_d"
| conditionBF: "\<not>b (f now) \<Longrightarrow> semB (IF b P) now f now f"
| IFELSET: " b (f now) \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (IFELSE b P Q) now f now_d f_d"
| IFELSEF: "\<not>b (f now) \<Longrightarrow> semB Q now f now_d f_d \<Longrightarrow> semB (IFELSE b P Q) now f now_d f_d"
| IChoiceBL: "semB P now f now' f' \<Longrightarrow> semB (P \<sqinter> Q) now f now' f'"
| IChoiceBR: "semB Q now f now' f' \<Longrightarrow> semB (P \<sqinter> Q) now f now' f'"
| EChoiceL: "d \<ge> 0 \<Longrightarrow> semB P (now + d) (extend_history f now d) now' f' \<Longrightarrow>
             semB (ch [!] e \<rightarrow> P [] dh [?] x \<rightarrow> Q) now f now' f'"
| EChoiceR: "d \<ge> 0 \<Longrightarrow> semB (x ::= (\<lambda>_. c); Q) (now + d) (extend_history f now d) now' f' \<Longrightarrow>
             semB (ch [!] e \<rightarrow> P [] dh [?] x \<rightarrow> Q) now f now' f'"
| repetitionN0B: "N = (0::nat) \<Longrightarrow> semB (P * NUM N) now f now f"
| repetitionNkB: "N > (0::nat) \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (P * NUM (N-1)) now_d f_d now_dd f_dd \<Longrightarrow>
                  semB (P * NUM N) now f now_dd f_dd" 
| repetitionB: "\<exists>N. semB (P * NUM N) now f now_dd f_dd \<Longrightarrow> semB (P*&&Inv) now f now_dd f_dd"
(*| outputBC: "d\<ge>0 \<Longrightarrow> semB (Cm (ch[!]e)) now f (now+d) (extend_history f now d)"
| inputBC: "d\<ge>0 \<Longrightarrow> semB (Cm (ch[?]x)) now f (now + d)
            (\<lambda>t. if t < now + d \<and> t > now then f now
                 else if t = now + d then update (f now) x c
                 else f t)"
*)
(*Notice: no real meaning of c in the inputBC. It will not be used actually without a synchronized output.*)

 
inductive_cases SkipE[elim!]:
  "semB Skip now f now' f'"
inductive_cases AssignE[elim!]:
  "semB (x ::= e) now f now' f'"
inductive_cases SeqE[elim!]:
  "semB (P; Q) now f now' f'"
inductive_cases CondE[elim!]:
  "semB (IF b P) now f  now' f'"
inductive_cases IFELSEE[elim!]:
  "semB (IFELSE b P Q) now f  now' f'"
inductive_cases IChE[elim!]:
  "semB (P \<sqinter> Q) now f now' f'"
inductive_cases ContE[elim!]:
  "semB (<ode && Inv&b>) now f now' f'"
inductive_cases RepE[elim!]:
  "semB (P*&&Inv) now f now' f'"
inductive_cases RepNE[elim!]:
  "semB (P* NUM N) now f now' f'"
thm ContE

text \<open>There are four cases for semantics of parallel composition.\<close>
inductive semBP :: "'a::finite procP \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> bool" where
  parallelB1: "semB P nowp fp nowp' fp' \<Longrightarrow> semB Q nowq fq nowq' fq' \<Longrightarrow> chanset P = {} \<and> chanset Q = {} \<Longrightarrow>
               semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'"
| parallelB2: "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
               semB U nowp' fp' nowu' fu' \<Longrightarrow> semB V nowq' fq' nowv' fv' \<Longrightarrow> chanset P \<noteq> {} \<and> chanset Q \<noteq> {} \<Longrightarrow>
               chanset U = {} \<and> chanset V = {} \<Longrightarrow>
               semBP ((P; U) || (Q; V)) nowp fp nowq fq  nowu' fu' nowv' fv'"
(*B3 and B4 are symmetric*)
| parallelB3: "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
               semBP (P; Cm (ch[?]x) || Q; Cm (ch[!]e)) nowp fp nowq fq
               (max nowp' nowq')
               (\<lambda>t. if nowp' < t \<and> t < max nowp' nowq' then fp' nowp'
                    else if t = max nowp' nowq' then update (fp' nowp') x ( e (fp' nowp')) 
                    else fp' t)
               (max nowp' nowq')
               (\<lambda>t. if nowq' < t \<and> t \<le> max nowp' nowq' then fq' nowq' else fq' t)"
| parallelB4: "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
               semBP (P; Cm (ch[!]e) || Q; Cm (ch[?]x)) nowp fp nowq fq
               (max nowp' nowq')
               (\<lambda>t. if nowp' < t \<and> t \<le> max nowp' nowq' then fp' nowp' else fp' t)
               (max nowp' nowq')
               (\<lambda>t. if nowq' < t \<and> t < max nowp' nowq' then fq' nowq'
                    else if t = max nowp' nowq' then update (fq' nowq') x ( e (fq' nowq'))
                    else fq' t)"
(*P terminates after Q, so ode is not executed*)
| parallelB5:  "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp' \<ge> nowq' \<Longrightarrow>
               semBP (((P; (<ode&&Inv&b>)|> ch[!]e \<rightarrow> E)) || (Q; Cm (ch[?]x))) nowp fp nowq fq
               nowp' fp' nowp'
               (\<lambda>t. if nowq' < t \<and> t < nowp' then fq' nowq'
                    else if t = nowp' then update (fq' nowq') x (e (fp' nowp'))
                    else fq' t)"
(*P terminates earlier than Q and b is true when the communication is ready to occur, so E will be executed*)
| parallelB6: "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp' < nowq' \<Longrightarrow>
                d = (nowq' - nowp') \<Longrightarrow>
               ODEsol ode sol d \<Longrightarrow> ((\<forall> t. (t \<ge> 0 \<and> t \<le> d \<longrightarrow> b (sol t)))) \<Longrightarrow>
               semB E nowq' (\<lambda>t. if nowp' < t \<and> t \<le> nowq' then sol (t - nowp') 
                    else fp' t) nowp'' fp'' \<Longrightarrow>
               semBP (((P; (<ode&&Inv&b>)|> ch[!]e \<rightarrow> E)) || (Q; Cm (ch[?]x))) nowp fp nowq fq
               nowp'' fp''
               nowq' (\<lambda>t. if t = nowq' then update (fq' nowq') x (e (sol d))
                    else fq' t)"
(*P terminates earlier than Q and b turns false before the communication becomes ready.*)
| parallelB7: "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp' < nowq' \<Longrightarrow>
                d \<ge> 0 \<Longrightarrow> d < (nowq' - nowp') \<Longrightarrow>
               ODEsol ode sol d \<Longrightarrow> ((\<forall> t. (t \<ge> 0 \<and> t < d \<longrightarrow> b (sol t)))) \<Longrightarrow> \<not>b (sol d) \<Longrightarrow>
               semBP (((P; (<ode&&Inv&b>)|> ch[!]e \<rightarrow> E)) || (Q; Cm (ch[?]x))) nowp fp nowq fq
               (nowp'+ d) (\<lambda>t. if nowp' < t \<and> t \<le> nowp'+d then sol (t - nowp') 
                    else fp' t)
               nowq' fq'"
(*The following three rules are symmetric with the above B5, B6 and B7*)
(*P terminates after Q, so ode is not executed*)
| parallelB8:  "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp' \<ge> nowq' \<Longrightarrow>
               semBP (((P; (<ode&&Inv&b>)|> ch[?]x \<rightarrow> E)) || (Q; Cm (ch[!]e))) nowp fp nowq fq
               nowp' (\<lambda>t. if t = nowp' then update (fp' nowp') x (e (fq' nowq'))
                      else fp' t) 
               nowp' (\<lambda>t. if nowq' < t \<and> t \<le> nowp' then fq' nowq'
                      else fq' t)"
(*P terminates earlier than Q and b is true when the communication is ready to occur, so E will be executed*)
| parallelB9: "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp' < nowq' \<Longrightarrow>
                d = (nowq' - nowp') \<Longrightarrow>
               ODEsol ode sol d \<Longrightarrow> ((\<forall> t. (t \<ge> 0 \<and> t \<le> d \<longrightarrow> b (sol t)))) \<Longrightarrow>
               semB E nowq' (\<lambda>t. if nowp' < t \<and> t < nowq' then sol (t - nowp') 
                    else if t = nowq' then update (sol d) x (e (fq' nowq'))
                    else fp' t) nowp'' fp'' \<Longrightarrow>
               semBP (((P; (<ode&&Inv&b>)|> ch[?]x \<rightarrow> E)) || (Q; Cm (ch[!]e))) nowp fp nowq fq
               nowp'' fp''
               nowq' fq'"
(*P terminates earlier than Q and b turns false before the communication becomes ready.*)
| parallelB10: "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp' < nowq' \<Longrightarrow>
                d \<ge> 0 \<Longrightarrow> d < (nowq' - nowp') \<Longrightarrow>
               ODEsol ode sol d \<Longrightarrow> ((\<forall> t. (t \<ge> 0 \<and> t < d \<longrightarrow> b (sol t)))) \<Longrightarrow> \<not>b (sol d) \<Longrightarrow>
               semBP (((P; (<ode&&Inv&b>)|> ch[?]x \<rightarrow> E)) || (Q; Cm (ch[!]e))) nowp fp nowq fq
               (nowp'+d) (\<lambda>t. if nowp' < t \<and> t \<le> nowp'+d then sol (t - nowp') 
                    else fp' t)
               nowq' fq'"

inductive_cases ParaE[elim!]:
  "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'"


lemma sem1:
  "semB P now f now' f' \<Longrightarrow> now \<le> now'"
  by (induct rule: semB.induct, auto)


lemma semB1:
  "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp \<le> nowp' \<and> nowq \<le> nowq'"
proof (induct rule: semBP.induct)
  case (parallelB1 P nowp fp nowp' fp' Q nowq fq nowq' fq')
  then show ?case  using sem1 by blast
next
  case (parallelB2 P Q nowp fp nowq fq nowp' fp' nowq' fq' U nowu' fu' V nowv' fv')
  then show ?case  by (metis order_trans sem1)
next
  case (parallelB3 P Q nowp fp nowq fq nowp' fp' nowq' fq' ch x e)
  then show ?case
    by linarith
next
  case (parallelB4 P Q nowp fp nowq fq nowp' fp' nowq' fq' ch e x)
  then show ?case 
    by linarith
next
  case (parallelB5 P Q nowp fp nowq fq nowp' fp' nowq' fq' ode Inv b ch e E x)
  then show ?case
    by auto
next
  case (parallelB6 P Q nowp fp nowq fq nowp' fp' nowq' fq' d ode sol b E nowp'' fp'' Inv ch e x)
  then show ?case 
    by (smt sem1)
next
  case (parallelB7 P Q nowp fp nowq fq nowp' fp' nowq' fq' d ode sol b Inv ch e E x)
  then show ?case
    by linarith

next
  case (parallelB8 P Q nowp fp nowq fq nowp' fp' nowq' fq' ode Inv b ch x E e)
  then show ?case by auto
next
  case (parallelB9 P Q nowp fp nowq fq nowp' fp' nowq' fq' d ode sol b E x e nowp'' fp'' Inv ch)
then show ?case by (smt sem1)
next
  case (parallelB10 P Q nowp fp nowq fq nowp' fp' nowq' fq' d ode sol b Inv ch e E x)
  then show ?case by linarith
qed
  

lemma sem2:
  "semB P now f now' f' \<Longrightarrow> \<forall>t. t < now \<or> t > now' \<longrightarrow> f t = f' t"
proof (induct rule: semB.induct)
   case (sequenceB P now f now' f' Q now'' f'')
  then show ?case by (metis (full_types) le_less_trans not_le sem1)
next
   case (EChoiceL d P now f now' f' ch e dh x Q)
  then show ?case 
    by (smt extend_history.simps sem1)
next
  case (EChoiceR d x c Q now f now' f' ch e P dh)
  then show ?case by (smt extend_history.simps sem1)
next
  case (repetitionNkB N P now f now_d f_d now_dd f_dd)
  then show ?case  by (metis (full_types) le_less_trans less_eq_real_def sem1)
qed auto
 
lemma semB2:
  "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
    (\<forall>t. t < nowp \<or> t > nowp' \<longrightarrow> (fp t = fp' t)) \<and>
    (\<forall>t. t < nowq \<or> t > nowq' \<longrightarrow> (fq t = fq' t))"
proof (induct rule: semBP.induct)
  case (parallelB1 P nowp fp nowp' fp' Q nowq fq nowq' fq')
  then show ?case  
    using sem2 by blast
next
  case (parallelB2 P Q nowp fp nowq fq nowp' fp' nowq' fq' U nowu' fu' V nowv' fv')
  then show ?case  by (smt sem1 sem2 semB1)
next
  case (parallelB3 P Q nowp fp nowq fq nowp' fp' nowq' fq' ch x e)
  then show ?case by (smt semB1)
next
  case (parallelB4 P Q nowp fp nowq fq nowp' fp' nowq' fq' ch e x)
  then show ?case by (smt semB1)
next
  case (parallelB5 P Q nowp fp nowq fq nowp' fp' nowq' fq' ode Inv b ch e E x)
  then show ?case sorry
next
  case (parallelB6 P Q nowp fp nowq fq nowp' fp' nowq' fq' d ode sol b E nowp'' fp'' Inv ch e x)
  then show ?case sorry
next
  case (parallelB7 P Q nowp fp nowq fq nowp' fp' nowq' fq' d ode sol b Inv ch e E x)
  then show ?case sorry
next
  case (parallelB8 P Q nowp fp nowq fq nowp' fp' nowq' fq' ode Inv b ch x E e)
  then show ?case sorry
next
  case (parallelB9 P Q nowp fp nowq fq nowp' fp' nowq' fq' d ode sol b E x e nowp'' fp'' Inv ch)
  then show ?case sorry
next
  case (parallelB10 P Q nowp fp nowq fq nowp' fp' nowq' fq' d ode sol b Inv ch x E e)
  then show ?case sorry
qed

lemma semB3:
  "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
   chanset P = {} \<and> chanset Q = {} \<Longrightarrow>
   semB P nowp fp nowp' fp' \<and> semB Q nowq fq nowq' fq'"
  by (induct rule: semBP.cases; simp add: chanset_def)
 
text \<open>history formulas\<close>
type_synonym now_dash = real
type_synonym 'a dform = "'a history \<Rightarrow> now \<Rightarrow> now_dash \<Rightarrow> bool"


text \<open>The dform formula is only decided by the interval between now and now_dash\<close>
definition well_DC :: "'a dform \<Rightarrow> bool" where
"well_DC df == (\<forall> now now' h h'. (now \<le> now' \<and> (\<forall>t. t > now \<and> t < now' \<longrightarrow> h t = h' t)) \<longrightarrow> df h now now' = df h' now now')" 
 

subsection \<open>Duration Calculus operators and lemmas proved\<close>
text \<open>almost P, P holds everywhere except for the rightmost point, not almost everywhere, over the interval.
The reason is that, for continuous evolution, it escapes whenever a violation is met.
A special case is that, if using almost everywhere, the differential cut rule will not hold anymore.\<close>
definition almost :: "'a fform \<Rightarrow> 'a dform"  where 
"almost P \<equiv> \<lambda>h n nd. (nd-n > 0) \<and> (\<forall>t. t \<ge> n \<and> t < nd \<longrightarrow> P (h (t)))"

definition chop :: "'a dform \<Rightarrow> 'a dform \<Rightarrow> 'a dform"  (infixr "[^]" 40) where
  "H [^] M \<equiv> \<lambda>h n nd. \<exists>nm. nm \<ge> n \<and> nm \<le> nd \<and> H h n nm \<and> M h nm nd"

text \<open>The length of the interval l is equal to, greater than, less than T.\<close>
definition elE :: "real \<Rightarrow> 'a dform" where
  "elE T \<equiv> \<lambda>h n nd. (nd-n) = T"
definition elG :: "real \<Rightarrow> 'a dform" where
  "elG T \<equiv> \<lambda>h n nd. (nd-n) > T"
definition elL :: "real \<Rightarrow> 'a dform" where
  "elL T \<equiv> \<lambda>h n nd. (nd-n) < T"

definition dAnd :: "'a dform \<Rightarrow> 'a dform \<Rightarrow> 'a dform"  (infixr "[[&]]" 35) where
  "P [[&]] Q \<equiv> \<lambda>h n m. P h n m \<and> Q h n m"
definition dOr :: "'a dform \<Rightarrow> 'a dform \<Rightarrow> 'a dform"  (infixr "[[\<or>]]" 30) where
  "P [[\<or>]] Q \<equiv> \<lambda>h n m. P h n m \<or> Q h n m"
definition dNot :: "'a dform \<Rightarrow> 'a dform"  ("[[\<not>]]_" 40) where
  "[[\<not>]]P \<equiv> \<lambda>h n m. \<not> P h n m"
definition dImp :: "'a dform \<Rightarrow> 'a dform \<Rightarrow> 'a dform"  (infixr "[[\<longrightarrow>]]" 25) where
  "P [[\<longrightarrow>]] Q \<equiv> \<lambda>h n m. P h n m \<longrightarrow> Q h n m"

declare almost_def [simp]
declare chop_def [simp]
declare elE_def [simp]
declare elG_def [simp]
declare elL_def [simp]


text \<open>True holds almost everywhere\<close>
lemma almostf:
  "\<forall>h n nd. nd - n \<le> 0 \<or> almost fTrue h n nd"
  apply simp
  by (metis dense not_le)

text \<open>almost P \<Leftrightarrow> chop almost P almost P\<close>
lemma chopfb:
  "chop (almost P) (almost P) h n nd \<Longrightarrow> almost P h n nd"
  unfolding chop_def almost_def
  apply (rule conjI, auto)
  by (metis (poly_guards_query) less_eq_real_def less_trans not_less)

text \<open>chop (almost P \/ l = 0) (almost P \/ l = 0) ==> almost P \/ l = 0 \<close>
lemma chopfor:
  "chop (elE 0 [[\<or>]] almost P) (elE 0 [[\<or>]] almost P) h n nd \<Longrightarrow> (elE 0 [[\<or>]] almost P) h n nd"
  unfolding dOr_def
  apply (rule disjCI, auto)
  by (metis less_eq_real_def less_trans not_less)

lemma chopf:
  "almost P h n nd \<Longrightarrow> chop (almost P) (almost P) h n nd"
  unfolding almost_def chop_def
  apply (rule exI[where x = "(n+nd)/2"])
  by auto

lemma chop0L: "chop (almost P) (elE 0) h n nd \<Longrightarrow> almost P h n nd"
  by auto

lemma chop0R: "almost P h n nd \<Longrightarrow> chop (almost P) (elE 0) h n nd"
  by auto

lemma chop_well_DC: "well_DC Ha \<Longrightarrow> well_DC Hb \<Longrightarrow> well_DC (Ha [^] Hb)"
  unfolding chop_def well_DC_def
  apply auto
  apply smt
  apply smt
  done 
 
text \<open>Monotonicity: s \<Rightarrow> t \<Longrightarrow> almost s \<Rightarrow> almost t\<close>
lemma almostmono:
  "\<forall>s. P s \<longrightarrow> Q s \<Longrightarrow> \<forall>h n nd. almost P h n nd \<longrightarrow> almost Q h n nd"
  by auto
  
 
lemma almostint:
  "now < nowf \<Longrightarrow> \<forall>t. (t\<ge>now \<and> t<nowf) \<longrightarrow> P (f t) \<Longrightarrow> almost P f now nowf"
  by auto

end