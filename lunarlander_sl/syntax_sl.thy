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



type_synonym 'a fform = "'a state => bool"
definition fTrue :: "'a fform" where "fTrue \<equiv> \<lambda>s. True"
definition fFalse :: "'a fform" where "fFalse \<equiv> \<lambda>s. False"
declare fTrue_def [simp]
declare fFalse_def [simp]
definition fAnd :: "'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a fform"  (infixr "[&]" 35) where
  "P [&] Q \<equiv> \<lambda>s. P s \<and> Q s"

definition fOr :: "'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a fform"  (infixr "[|]" 30) where
  "P [|] Q \<equiv> \<lambda>s. P s \<or> Q s"

definition fNot :: "'a fform \<Rightarrow> 'a fform"  ("[\<not>]_" [40] 40) where
  "[\<not>]P \<equiv> \<lambda>s. \<not> P s"

definition fImp :: "'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a fform"  (infixr "[\<longrightarrow>]" 25) where
  "P [\<longrightarrow>] Q \<equiv> \<lambda>s. P s \<longrightarrow> Q s"



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
(*| Pref comm proc          ("_\<rightarrow>_" [95,94] 93)*)
| IChoice "'a proc" "'a proc"          (infixr "\<sqinter>" 90)
| EChoice "'a comm" "'a proc" "'a comm" "'a proc"          ("_ \<Rightarrow> _ [] _ \<Rightarrow> _" [92,91,92,91] 90)
\<comment> \<open>Repetition is annotated with invariant\<close>
| Rep "'a proc" "'a fform"          ("_*&&_" [91] 90)
| RepN "'a proc" nat           ("_* NUM _" [91, 90] 90)
\<comment> \<open>Continuous evolution is annotated with invariant.\<close>
| Cont "'a ODE" "'a fform" "'a fform"  ("<_&&_&_>" [95,95,96] 94)
| Interr "'a proc" "'a comm" "'a proc"       ("_ [] _ \<Rightarrow> _" [95,94,94] 94)

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
| "chanset (P \<sqinter> Q) = chanset P \<union> chanset Q"
| "chanset (c \<Rightarrow> P [] d \<Rightarrow> Q) = chansetC c  \<union> chansetC d  \<union> chanset P \<union> chanset Q"
| "chanset (P *&& Inv) = chanset P"
| "chanset (P * NUM n) = chanset P"
| "chanset (<ODEs && Inv & b>) = {}"
| "chanset (P [] c \<Rightarrow> Q) = chanset P \<union> chanset Q \<union> chansetC c"

subsection \<open>Definitions for ODEs\<close>

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
| IChoiceBL: "semB P now f now' f' \<Longrightarrow> semB (P \<sqinter> Q) now f now' f'"
| IChoiceBR: "semB Q now f now' f' \<Longrightarrow> semB (P \<sqinter> Q) now f now' f'"
| EChoiceL: "d \<ge> 0 \<Longrightarrow> semB P (now + d) (extend_history f now d) now' f' \<Longrightarrow>
             semB (ch [!] e \<Rightarrow> P [] dh [?] x \<Rightarrow> Q) now f now' f'"
| EChoiceR: "d \<ge> 0 \<Longrightarrow> semB (x ::= (\<lambda>_. c); Q) (now + d) (extend_history f now d) now' f' \<Longrightarrow>
             semB (ch [!] e \<Rightarrow> P [] dh [?] x \<Rightarrow> Q) now f now' f'"
| repetitionN0B: "N = (0::nat) \<Longrightarrow> semB (P * NUM N) now f now f"
| repetitionNkB: "N > (0::nat) \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (P * NUM (N-1)) now_d f_d now_dd f_dd \<Longrightarrow>
                  semB (P * NUM N) now f now_dd f_dd" 
| repetitionB: "\<exists>N. semB (P * NUM N) now f now_dd f_dd \<Longrightarrow> semB (P*&&Inv) now f now_dd f_dd"
| outputBC: "d\<ge>0 \<Longrightarrow> semB (Cm (ch[!]e)) now f (now+d) (extend_history f now d)"
| inputBC: "d\<ge>0 \<Longrightarrow> semB (Cm (ch[?]x)) now f (now + d)
            (\<lambda>t. if t < now + d \<and> t > now then f now
                 else if t = now + d then update (f now) x c
                 else f t)"
(*Notice: no real meaning of c in the inputBC. It will not be used actually without a synchronized output.*)

inductive_cases SkipE[elim!]:
  "semB Skip now f now' f'"
inductive_cases AssignE[elim!]:
  "semB (x ::= e) now f now' f'"
inductive_cases SeqE[elim!]:
  "semB (P; Q) now f now' f'"
inductive_cases CondE[elim!]:
  "semB (IF b P) now f  now' f'"
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

inductive_cases ParaE[elim!]:
  "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'"


lemma sem1:
  "semB P now f now' f' \<Longrightarrow> now \<le> now'"
  by (induct rule: semB.induct, auto)


lemma semB1:
  "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp \<le> nowp' \<and> nowq \<le> nowq'"
proof (induct rule: semBP.induct)
  case (parallelB1 P nowp fp nowp' fp' Q nowq fq nowq' fq')
  then show ?case  
    using sem1 by blast
next
  case (parallelB2 P Q nowp fp nowq fq nowp' fp' nowq' fq' U nowu' fu' V nowv' fv')
  then show ?case by (metis order_trans sem1)
qed (metis le_max_iff_disj)+

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
qed

lemma semB3:
  "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
   chanset P = {} \<and> chanset Q = {} \<Longrightarrow>
   semB P nowp fp nowp' fp' \<and> semB Q nowq fq nowq' fq'"
  by (induct rule: semBP.cases; simp add: chanset_def)
 

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
definition dOr :: "'a dform \<Rightarrow> 'a dform \<Rightarrow> 'a dform"  (infixr "[[|]]" 30) where
  "P [[|]] Q \<equiv> \<lambda>h n m. P h n m \<or> Q h n m"
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
  "chop (elE 0 [[|]] almost P) (elE 0 [[|]] almost P) h n nd \<Longrightarrow> (elE 0 [[|]] almost P) h n nd"
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

subsection \<open>Inference rules for Hybrid CSP: Hybrid Hoare Logic rules\<close>

text \<open>Specification\<close>
definition Valid :: "'a :: finite fform \<Rightarrow> 'a proc \<Rightarrow> 'a fform \<Rightarrow> 'a dform \<Rightarrow> bool" ("\<Turnstile> {_}_{_; _}" 80) where
  "\<Turnstile> {p} c {q; H} \<longleftrightarrow> (\<forall>now h now' h'. semB c now h now' h' \<longrightarrow> p (h now) \<longrightarrow> (q (h' now') \<and> H h' now now'))"

definition ValidP :: "'a :: finite fform \<Rightarrow> 'a fform \<Rightarrow> 'a procP \<Rightarrow> 'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a dform \<Rightarrow> 'a dform \<Rightarrow> bool"
  ("\<Turnstile> {_, _}_{_, _; _, _}" 80) where
  "\<Turnstile> {pa, pb} c {qa, qb; Ha, Hb} \<longleftrightarrow> (\<forall>nowp nowq fp fq nowp' nowq' fp' fq'.
    semBP c nowp fp nowq fq nowp' fp' nowq' fq'  \<longrightarrow> 
    pa (fp(nowp)) \<longrightarrow> pb (fq(nowq)) \<longrightarrow> 
    qa (fp'(nowp')) \<and> qb (fq'(nowq')) \<and> (Ha fp' nowp nowp') \<and> (Hb fq' nowq nowq'))"

text \<open>HHLlrule\<close>

lemma SkipR:
  assumes "\<forall> s h now now'. (p s \<longrightarrow> q s) \<and> ((elE 0) h now now'\<longrightarrow> H h now now') "
  shows "\<Turnstile> {p} Skip {q; H}"
  using assms
  unfolding Valid_def  elE_def by auto

lemma AssignR:
  assumes"(\<forall> s. p s \<longrightarrow> (q (update s x ( e s))))
               \<and> (\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')) " 
  shows "\<Turnstile> {p} (x ::= e) {q; H}"
  using assms
  unfolding Valid_def elE_def by auto

lemma SeqR:
  assumes "\<Turnstile> {p} P {m; H} " 
  and "\<Turnstile> {m} Q {q; G}"
  and "well_DC H"
shows "\<Turnstile> {p} P;  Q {q; H[^]G}"
proof-
   have "semB (P; Q) now h now' h' \<longrightarrow> p (h now) \<longrightarrow> 
    q (h' now') \<and> (\<exists>nm\<ge>now. nm \<le> now' \<and> H h' now nm \<and> G h' nm now')" for now h now' h'
   proof-
   {
     assume pq:"semB (P; Q) now h now' h'"
     and pre:"p (h now)"
     obtain now'' h'' where p:"semB P now h now'' h''" and q:"semB Q now'' h'' now' h'"using pq by auto 
     have step1:"m (h'' now'')"using p pre assms unfolding Valid_def by auto  
     have step2:"H h'' now now''" using p pre assms unfolding Valid_def by auto
     have step3:"q (h' now')" using step1 q assms unfolding Valid_def by auto 
     have step4:"G h' now'' now'" using step1 q assms unfolding Valid_def by auto
     have step5: "(now'' \<le> now' \<and> (\<forall>t. t < now'' \<or> t > now' \<longrightarrow> h'' t = h' t))"
       using q by (simp add: sem1 sem2)
     have step6:"(\<forall>t. now < t \<and> t < now'' \<longrightarrow> h'' t = h' t)" using step5 by auto
     have step7:"now \<le> now''" using p sem1 by metis
     have step8:"H h' now now''" using assms(3) step2 step6 step7 unfolding well_DC_def by auto
     have step9:"q (h' now') \<and> (\<exists>nm\<ge>now. nm \<le> now' \<and> H h' now nm \<and> G h' nm now')" using step3 step4 step8 step5 step7 by blast
   }
   then show ?thesis by auto
 qed
  then show ?thesis 
    unfolding Valid_def chop_def by blast
qed

lemma CondTR: 
  assumes"\<forall> s. p s \<longrightarrow> ( b s)"
      and"\<Turnstile> {p} P {q; H} "
    shows"\<Turnstile> {p} IF b P {q; H}"
  using assms unfolding Valid_def by auto


lemma CondFR: 
  assumes"\<forall> s. p s \<longrightarrow> (q s \<and> (\<not> b s))" 
      and"\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')"
    shows"\<Turnstile> {p} IF b P {q; H}"
  using assms
  unfolding elE_def Valid_def by auto

lemma IChoiceR: 
  assumes"\<Turnstile> {p} P {m; H} "
      and"\<Turnstile> {p} Q {q; G}"
    shows"\<Turnstile> {p} P \<sqinter> Q {m [|] q; H [[|]] G}"
  using assms
  unfolding Valid_def fOr_def dOr_def by auto

lemma repetitionNR: 
  assumes "\<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m "
      and "\<Turnstile> {I}P{I; H}"
      and "well_DC H "
    shows "\<Turnstile> {I}(P* NUM N) {I; H [[|]] elE 0}"
  unfolding Valid_def
  apply (induction N) 
  apply clarify
  subgoal  premises pre1 for now h now' h'
  proof-
    {
      assume cond1:"semB (P* NUM 0) now h now' h'"
         and cond2:"I (h now)"
        have step1:"now' = now" and "h' = h"
          using cond1 by auto
        then have step2:"I (h' now')" using cond2 by auto
        have step3:"elE 0 h' now now'"
          using step1 unfolding elE_def by auto
        have step4:"I (h' now') \<and> (H [[|]] elE 0) h' now now'"
          using step2 step3 unfolding dOr_def by auto
    }
    then show ?thesis using pre1 by auto 
  qed
  apply clarify
  subgoal premises pre2 for N nowa ha now'a h'a
  proof-
    {
      assume cond1:" \<forall>now h now' h'.
          semB (P* NUM N) now h now' h' \<longrightarrow> I (h now) \<longrightarrow> I (h' now') \<and> (H [[|]] elE 0) h' now now' "
         and cond2:" semB (P* NUM Suc N) nowa ha now'a h'a"
         and cond3:"I (ha nowa)"
      have step1:"Suc N >0" by auto
      obtain nowd and hd where PR:"semB P nowa ha nowd hd" and PNR:"semB (P* NUM  N ) nowd hd now'a h'a"
        using cond2 step1 
        using RepNE [where P="P" and now="nowa" and f="ha" and now'= "now'a" and f'="h'a" and N="Suc N" and Pa="thesis"]
        by simp
      have step2:"I (hd nowd)" using cond3 PR assms(2) unfolding Valid_def by auto
      have step3:"H hd nowa nowd" using cond3 PR assms(2) unfolding Valid_def by auto
      have step4:"I (h'a now'a)" using PNR step2 cond1  by metis
      have step5:"(H [[|]] elE 0) h'a nowd now'a" using PNR step2 cond1  by metis
      have step6:"H h'a nowa nowd" using PR PNR sem1 sem2 step3 assms(3) unfolding well_DC_def by metis
      have step7:"H h'a nowa now'a" using step5 step6 assms(1) unfolding dOr_def chop_def elE_def
        by (metis PNR PR eq_iff_diff_eq_0 sem1)
      have step8:"I (h'a now'a) \<and> (H [[|]] elE 0) h'a nowa now'a" using step4 step7 unfolding dOr_def by auto
    }
    then show ?thesis using pre2 by auto
  qed
  done

lemma  repetR: 
  assumes "\<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m "
      and "\<Turnstile> {I}P{I; H}"
      and "well_DC H "
    shows "\<Turnstile> {I} P*&&I {I; (H [[|]] (elE 0))}"
  apply(subgoal_tac"\<forall>N. \<Turnstile> {I}(P* NUM N) {I; H [[|]] elE 0}")
  subgoal
    unfolding Valid_def  by force
  using repetitionNR assms by metis

lemma continTR: 
  assumes"\<forall> s. (Inv [&][\<not>]b) s \<longrightarrow> q s "
     and "\<forall> tr d. ((ODEsol ode tr d \<and> p (tr 0))\<longrightarrow> INV Inv tr d) " 
     and "\<forall> h now now'. (almost (Inv [&]  b) [[|]] elE 0) h now now' \<longrightarrow>H h now now' " 
   shows "\<Turnstile> {p} <ode && Inv&b> {q; H}"
  unfolding Valid_def 
  apply auto
  subgoal
    using assms unfolding fAnd_def fNot_def INV_def ODEsol_def apply auto
    done
  subgoal premises pre for now h d pa
  proof-
    {
      assume cond1:"0 \<le> d " 
      and cond2:"ODEsol ode pa d " 
      and cond3:"\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (pa t) "
      and cond4:"\<not> b (pa d) " 
      and cond5:"h now = pa 0 " 
      and cond6:"p (pa 0) "
      then have step1:"(almost (Inv [&]  b) [[|]] elE 0) (\<lambda>t. if t \<le> now + d \<and> now \<le> t then pa (t - now) else h t) now (now + d)"
        using assms(2) unfolding dOr_def almost_def fAnd_def elE_def INV_def by force 
      then have step2:" H (\<lambda>t. if t \<le> now + d \<and> now \<le> t then pa (t - now) else h t) now (now + d)"
        using assms(3) by blast
    }
    then show ?thesis using pre by auto
  qed
  done

lemma diffCut: 
  assumes "\<Turnstile> {p} <ode && Inv&b> {I; almost I [[|]] elE 0} " 
      and "\<Turnstile> {p} <ode && Inv&(b[&]I)> {q; H} " 
    shows "\<Turnstile> {p} <ode && Inv&b> {q; H}" 
proof (simp add:Valid_def) 
  have step1:"\<forall>now h now' h'. semB (<ode&&Inv&b>) now h now' h' \<longrightarrow> p (h now) 
    \<longrightarrow> I (h' now') \<and> (almost I [[|]] elE 0) h' now now'"
    using assms(1) unfolding Valid_def by auto
  have step2: "semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> I (h' now')"
    for now h now' h'
    using step1 by auto
  have step3: "semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> (almost I [[|]] elE 0) h' now now'"
    for now h now' h'
    using step1 by auto
  have step4: "semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> semB (<ode&&Inv&(b [&] I)>) now h now' h'"
    for now h now' h'
    using step2 [of now h now' h'] step3 [of now h now' h'] 
    unfolding almost_def dOr_def elE_def apply simp
    apply (ind_cases "semB (<ode&&Inv&b>) now h now' h'") 
    apply auto
    subgoal premises pre1 for d pa
    proof-
      {
        assume cond1:"p (pa 0) " 
           and cond2:"I (pa d)"
           and cond3:"now' = now + d " 
           and cond4:"h' = (\<lambda>t. if t \<le> now + d \<and> now \<le> t then pa (t - now) else h t) "
           and cond5:"ODEsol ode pa d " 
           and cond6:" \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (pa t) " 
           and cond7:"\<not> b (pa d) " 
           and cond8:"h now = pa 0 "
           and cond9:"0 < d" 
           and cond10:"\<forall>t. now \<le> t \<and> t < now + d \<longrightarrow> I (pa (t - now))"
        have step1:"d\<ge>0" using cond9 by auto
        have step2:" \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> (b [&] I) (pa t) " unfolding fAnd_def using cond6 cond10 by smt
        have step3:" \<not> (b [&] I) (pa d) " unfolding fAnd_def using cond7 by auto
        have step4:"0 \<le> d \<and> ODEsol ode pa d \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> (b [&] I) (pa t)) \<and>
    \<not> (b [&] I) (pa d) \<and> h now = pa 0 "
          using step1 step2 step3 cond5 cond8 by auto

      }
      then show ?thesis using pre1 continuous[of d ode pa "b [&] I" h now Inv ] by auto
    qed
    subgoal premises pre2 for pa
    proof-
      {
        assume cond1:"p (pa 0)"
           and cond2:"I (pa 0)" 
           and cond3:"now' = now"
           and cond4:"h' = (\<lambda>t. if t \<le> now \<and> now \<le> t then pa (t - now) else h t)"
           and cond5:"ODEsol ode pa 0"
           and cond6:"\<forall>t. 0 \<le> t \<and> t < 0 \<longrightarrow> b (pa t)"
           and cond7:"\<not> b (pa 0)"
           and cond8:"h now = pa 0"
        have step1:"\<forall>t. 0 \<le> t \<and> t < 0 \<longrightarrow> (b [&] I) (pa t)" by auto
        have step2:" \<not> (b [&] I) (pa 0)" unfolding fAnd_def using cond7 by auto
        have step3:"(0 :: real) \<le> 0" by auto 
        have step4:"(0 :: real) \<le> 0 \<and> ODEsol ode pa 0 \<and>(\<forall>t. 0 \<le> t \<and> t < 0 \<longrightarrow> (b [&] I) (pa t)) \<and>\<not> (b [&] I) (pa 0) \<and> h now = pa 0 "
          using step1 step2 step3 cond5 cond8 by auto
      }
      then show ?thesis using  pre2 continuous[of 0 ode pa "b [&] I" h now Inv ] by auto
    qed
    done
    have step5:"semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> q (h' now') \<and> H h' now now'"
    for now h now' h'
    using assms(2) step4 unfolding Valid_def by meson
    then show "\<forall>now h now' h'. semB (<ode&&Inv&b>) now h now' h' \<longrightarrow> p (h now) \<longrightarrow> q (h' now') \<and> H h' now now'"
    by auto
qed 

lemma diffWeak: 
  assumes "\<forall> h now now'. (almost b [[|]] elE 0) h now now' \<longrightarrow> H h now now' " 
    shows "\<Turnstile> {p} <ode && Inv&b> {[\<not>]b; H}"
  unfolding Valid_def apply clarify 
  unfolding fNot_def apply simp
  subgoal for now h  d pa
    apply (subgoal_tac "(almost b [[|]] elE 0)(\<lambda>t. if t \<le> now + d \<and> now \<le> t then pa (t - now) else h t) now (now + d)")
    using assms(1) apply auto
    unfolding almost_def dOr_def elE_def by auto
  done




end