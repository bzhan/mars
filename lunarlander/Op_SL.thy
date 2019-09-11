section \<open>Operation semantics of HCSP.\<close>

theory Op_SL
  imports Syntax_SL
begin

type_synonym now = real
type_synonym 'a history = "time \<Rightarrow> 'a pair_state"

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
| "chanset (e := f) = {}"
| "chanset (P; Q) = chanset P \<union> chanset Q"
| "chanset (IF b P) = chanset P"
| "chanset (P \<sqinter> Q) = chanset P \<union> chanset Q"
| "chanset (c \<rightarrow> P [] d \<rightarrow> Q) = chansetC c  \<union> chansetC d  \<union> chanset P \<union> chanset Q"
| "chanset (P *&& Inv) = chanset P"
| "chanset (P * NUM n) = chanset P"
| "chanset (<ODEs && Inv & b>) = {}"
| "chanset (P [] c \<rightarrow> Q) = chanset P \<union> chanset Q \<union> chansetC c"

subsection \<open>Definitions for ODEs\<close>
 
text \<open>The semantics of an ODE is the value of the vector field.\<close>
fun ODE_sem :: "'a::finite ODE \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "ODE_sem (odeone x e) = (\<lambda> s. (\<chi> i. if i = x then evalE_df e s else 0))"
| "ODE_sem (odes ode1, ode2) = (\<lambda> s. ODE_sem ode1 s + ODE_sem ode2 s)"

definition ODE_pair_state :: "'a::finite ODE \<Rightarrow> 'a state \<Rightarrow> 'a pair_state" where
  "ODE_pair_state ode u = (u, ODE_sem ode u)"

text \<open>From a pair-state \<nu> and a state u, obtain a new state \<omega> by replacing
the part of \<nu> specified by the differential equation with the differential
equation evaluated on u.\<close>
definition execute_ODE :: "'a::finite ODE \<Rightarrow> 'a pair_state \<Rightarrow> 'a state \<Rightarrow> 'a pair_state" where
  "execute_ODE ode \<nu> u = 
    (THE \<omega>. Vagree \<omega> \<nu> (- ODE_vars ode) \<and> Vagree \<omega> (ODE_pair_state ode u) (ODE_vars ode))"

text \<open>Construct a concrete solution for the ODE.\<close>
definition concrete_sol :: "'a::finite ODE \<Rightarrow> 'a pair_state \<Rightarrow> 'a state \<Rightarrow> 'a pair_state" where
  "concrete_sol ode \<nu> u = 
     (\<chi> i. (if i \<in> ODE_vars ode then u else fst \<nu>) $ i,
      \<chi> i. (if i \<in> ODE_vars ode then ODE_sem ode u else snd \<nu>) $ i)"

lemma execute_ODE_exists: 
  "\<exists> \<omega>. Vagree  \<omega> \<nu> (- ODE_vars ode) \<and> (Vagree \<omega> (ODE_pair_state ode u) (ODE_vars ode))"
  by(rule exI[where x="(concrete_sol ode \<nu> u)"],
     auto simp add: concrete_sol_def ODE_pair_state_def Vagree_def)

lemma execute_ODE_agree:
  "Vagree (execute_ODE ode \<nu> u) \<nu> (- ODE_vars ode) \<and>
   Vagree (execute_ODE ode \<nu> u) (ODE_pair_state ode u) (ODE_vars ode)"
  unfolding execute_ODE_def Let_def
  apply (rule theI[where a = "concrete_sol ode \<nu> u"], auto)
  apply (simp add:concrete_sol_def ODE_pair_state_def Vagree_def Let_def)+
  using exE[OF execute_ODE_exists, of \<nu> ode u]
  by (auto simp add: concrete_sol_def ODE_pair_state_def Vagree_def vec_eq_iff)

lemma execute_ODE_concrete:
  "execute_ODE ode \<nu> u = concrete_sol ode \<nu> u"
  apply (simp add:concrete_sol_def)
  apply (rule Vagree_eq)
  using execute_ODE_agree[of ode \<nu> u]
  unfolding Vagree_def ODE_pair_state_def by auto


text \<open>The solution of ode at time interval {0..t} with respect to initial state \<nu>\<close>
definition ODE_solution :: "'a::finite ODE \<Rightarrow> real \<Rightarrow> 'a pair_state \<Rightarrow> (real \<Rightarrow> 'a state) \<Rightarrow> bool" where
  "ODE_solution ode t \<nu> v \<longleftrightarrow>
    (v has_vderiv_on (\<lambda>t. ODE_sem ode (v t))) {0..t} \<and> v 0 = fst \<nu>" 

definition ODE_solution_in_dom :: "'a::finite ODE \<Rightarrow> real \<Rightarrow> 'a pair_state \<Rightarrow> 'a fform \<Rightarrow> (real \<Rightarrow> 'a state) \<Rightarrow> bool" where
  "ODE_solution_in_dom ode t \<nu> b v \<longleftrightarrow>
    (v solves_ode (\<lambda>_. ODE_sem ode)) {0..t} {x. b (execute_ODE ode \<nu> x)} \<and> v 0 = fst \<nu>"

text \<open>\<nu> is the initial state, b is the domain, and i is the invariant\<close>
definition ODE_inv_in_dom :: "'a :: finite ODE \<Rightarrow>'a pair_state \<Rightarrow> 'a fform \<Rightarrow> 'a fform \<Rightarrow> bool" where
  "ODE_inv_in_dom ode \<nu> b i \<longleftrightarrow> (\<forall> d \<ge> 0. \<forall> sol.
    ODE_solution ode d \<nu> sol \<longrightarrow>
    (\<forall> t. t \<ge> 0 \<and> t < d \<longrightarrow> b (execute_ODE ode \<nu> (sol t))) \<longrightarrow>
    (\<forall> t. t \<ge> 0 \<and> t \<le> d \<longrightarrow> i (execute_ODE ode \<nu> (sol t))))"

(*
text \<open>With a change of differential variables in the second state\<close>
definition the_first_state :: "'a :: finite ODE \<Rightarrow>'a pair_state \<Rightarrow> 'a pair_state"
  where "the_first_state ode \<nu> = execute_ODE ode \<nu> (ODE_solution ode 0 \<nu> 0)"
*)

fun update_fst :: "'a::finite pair_state \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a pair_state" where
  "update_fst u a r = ((\<chi> i. if i = a then r else fst u $ i), snd u)"

fun update_snd :: "'a::finite pair_state \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a pair_state" where
  "update_snd u a r = (fst u, (\<chi> i. if i = a then r else snd u $ i))"

text \<open>Update the value of f between a and a+d to f a.\<close>
fun extend_history :: "'a::finite history \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a history" where
  "extend_history f a d = (\<lambda> t. if t > a \<and> t \<le> a + d then f a else f t)"


subsection \<open>Small step semantics for HCSP\<close>

text \<open>semP P t h (e, P2, t2, h2) means a single step starting at program P changes
the program to P2, changes time t to t2, and history h to h2, while outputting event e.\<close>
inductive semP :: "'a::finite proc \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> (event \<times> 'a proc \<times> now \<times> 'a history) \<Rightarrow> bool" where
  skip: "semP Skip now f (Tau, Skip, now, f)"
| assign: "semP (x := e) now f
    (Tau, Skip, now, (\<lambda>t. if t = now then update_fst (f t) x (evalE e (f t)) else f t))"
| Dassign: "semP (DAss x e) now f 
    (Tau, Skip, now, (\<lambda>t. if t = now then update_snd (f t) x (evalE e (f t)) else f t))"
\<comment> \<open>Finish execution of an ODE\<close>
| continuousF: "([\<not>]b) (execute_ODE ode (f now) (fst (f now))) \<Longrightarrow>
    semP (<ode && Inv&b>) now f (Tau, Skip, now, (\<lambda>t. if t = now then execute_ODE ode (f now) (fst (f now)) else f t))"
\<comment> \<open>Partial execution of an ODE\<close>
| continuousT: "d > 0 \<Longrightarrow> ODE_solution_in_dom ode d (f now) b sol \<Longrightarrow>
    semP (<ode && Inv&b>) now f (Delay d, <ode && Inv&b>, now+d,
       (\<lambda>t. if t \<le> now+d \<and> t > now then
              execute_ODE ode (f now) (sol (t-now))
            else f t))"
| sequenceL: "semP P now f (ev, P', now', f') \<and> P' \<noteq> Skip \<Longrightarrow>
              semP (P; Q) now f (ev, P'; Q, now', f')"
| sequenceR: "semP P now f (ev, P', now', f') \<and> P' = Skip \<Longrightarrow>
              semP (P; Q) now f (ev, Q, now', f')"
| conditionT: " b (f now) \<Longrightarrow> semP (IF b P) now f (Tau, P, now, f)"
| conditionF: "\<not>b (f now) \<Longrightarrow> semP (IF b P) now f (Tau, Skip, now, f)"
| IChoiceL: "semP (P \<sqinter> Q) now f (Tau, P, now, f)"
| IChoiceR: "semP (P \<sqinter> Q) now f (Tau, Q, now, f)"
| EChoiceL: "semP (ch [!] e \<rightarrow> P [] dh [?] x \<rightarrow> Q) now f (Out ch (evalE e (f now)), P, now, f)"
| EChoiceR: "semP (ch [!] e \<rightarrow> P [] dh [?] x \<rightarrow> Q) now f (In dh c, (x := (Real c); P), now, f)"
| EChoiceW: "d\<ge>0 \<Longrightarrow> semP (ch [!] e \<rightarrow> P [] dh [?] x \<rightarrow> Q) now f 
              (Delay d, (ch [!] e \<rightarrow> P [] dh [?] x \<rightarrow> Q), now + d, extend_history f now d)"
| repetition0: "semP (P *&& Inv) now f (Tau, Skip, now, f)"
| repetitionk: "semP P now f (ev, P', now', f') \<and> P' \<noteq> Skip \<Longrightarrow>
                semP (P *&& Inv) now f (ev, (P'; P *&& Inv), now', f')"
| repetitionk1: "semP P now f (ev, P', now', f') \<and> P' = Skip \<Longrightarrow>
                 semP (P *&& Inv) now f (ev, P *&& Inv, now',f')"
| outputC : "semP (Cm (ch[!]e)) now f (Out ch (evalE e (f now)), Skip, now, f)"
| outputW : "d\<ge>0 \<Longrightarrow> semP (Cm (ch[!]e)) now f
            (Delay d, Cm (ch[!]e), now + d, extend_history f now d)"
| inputC : "semP (Cm (ch[?]x)) now f (In ch c, x := (Real c), now, f)"
| inputW : "d\<ge>0 \<Longrightarrow> semP (Cm (ch[?]x)) now f
            (Delay d, Cm (ch[?]x), now + d, extend_history f now d)"


inductive semPP :: "'a::finite procP \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> 'a history \<Rightarrow>
                    (event \<times> 'a procP \<times> now \<times> 'a history \<times> 'a history) \<Rightarrow> bool" where
\<comment> \<open>Swap\<close>
  parallel0: "semPP (P||Q) now f g (eve, P'||Q', now', f', g') \<Longrightarrow> semPP (Q||P) now g f (eve, Q'||P', now', g', f')"
\<comment> \<open>Handshake on the two sides\<close>
| parallel1: "semP P now f (evp, P', now, f') \<and> semP Q now g (evq, Q', now, g') \<and> compat evp evq \<Longrightarrow>
              semPP (P||Q) now f g (handshake evp evq, P'||Q', now, f', g')"
\<comment> \<open>Execution on P only\<close>
| parallel2 : "semP P now f (evp, P', now', f')
             \<and> ((evp = Tau) \<or>
                (\<exists>ch c. evp = Out ch c \<and> \<not>(ch \<in> chanset P \<inter> chanset Q)) \<or>
                (\<exists>ch c. evp = In ch c \<and> \<not>(ch \<in> chanset P \<inter> chanset Q)) \<or>
                (\<exists>ch c. evp = IO ch c \<and> \<not>(ch \<in> chanset P \<inter> chanset Q))) \<Longrightarrow>
             semPP (P||Q) now f g (evp, P'||Q, now', f', g)"
\<comment> \<open>Delay on both sides\<close>
| parallel3 : "semP P now f (Delay d, P', now + d, f')
              \<and> semP Q now g (Delay d, Q', now + d, g') \<Longrightarrow>
             semPP (P||Q) now f g (Delay d, P'||Q', now + d, (\<lambda>t. if t \<le> now + d \<and> t \<ge> now then f' t else f t),
                (\<lambda>t. if t \<le> now + d \<and> t \<ge> now then g' t else g t))"

subsection \<open>Big-step semantics\<close>

text \<open>Continuous evolution domain: assume b is an open formula, otherwise
the escaping point cannot be found.\<close>

inductive semB :: "'a :: finite proc \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> now \<Rightarrow> 'a history \<Rightarrow> bool" where
  skipB: "semB Skip now f now f"
| assignB: "semB (x := e) now f 
    now (\<lambda>t. if t = now then update_fst (f t) x (evalE e (f t)) else f t)"
| DassignB: "semB (DAss x e) now f 
    now (\<lambda>t. if t = now then update_snd (f t) x (evalE e (f t)) else f t)"
(*| continuousBF: "let sol = ODE_solution ode 0 (f now) in
      ([\<not>]b) (execute_ODE ode (f now) (sol 0)) \<Longrightarrow> semB (<ode && Inv&b>) now f 
    now (\<lambda>t. if t = now then (execute_ODE ode (f now) ((ODE_solution ode 0 (f now)) 0))  else f t)"
*)
| continuous: "d \<ge> 0 \<Longrightarrow> ODE_solution ode d (f now) sol \<Longrightarrow>
    (\<forall> t. t \<ge> 0 \<and> t < d \<longrightarrow> b (execute_ODE ode (f now) (sol t))) \<Longrightarrow> \<not> b (execute_ODE ode (f now) (sol d)) \<Longrightarrow>
    semB (<ode && Inv&b>) now f 
      (now + d) (\<lambda>t. if t \<le> now + d \<and> t \<ge> now then
                       execute_ODE ode (f now) (sol (t-now))
                     else f t)"
| sequenceB: "semB P now f now' f' \<and> semB Q now' f' now'' f'' \<Longrightarrow> semB (P; Q) now f now'' f''"
| conditionBT: " b (f now) \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (IF b P) now f now_d f_d"
| conditionBF: "\<not>b (f now) \<Longrightarrow> semB (IF b P) now f now f"
| IChoiceBL: "semB P now f now' f' \<Longrightarrow> semB (P \<sqinter> Q) now f now' f'"
| IChoiceBR: "semB Q now f now' f' \<Longrightarrow> semB (P \<sqinter> Q) now f now' f'"
| EChoiceL: "d \<ge> 0 \<Longrightarrow> semB P (now + d) (extend_history f now d) now' f' \<Longrightarrow>
             semB (ch [!] e \<rightarrow> P [] dh [?] x \<rightarrow> Q) now f now' f'"
| EChoiceR: "d \<ge> 0 \<Longrightarrow> semB (x := (Real c); Q) (now + d) (extend_history f now d) now' f' \<Longrightarrow>
             semB (ch [!] e \<rightarrow> P [] dh [?] x \<rightarrow> Q) now f now' f'"
| repetitionN0B: "N = (0::nat) \<Longrightarrow> semB (P * NUM N) now f now f"
| repetitionNkB: "N > (0::nat) \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (P * NUM (N-1)) now_d f_d now_dd f_dd \<Longrightarrow>
                  semB (P * NUM N) now f now_dd f_dd" 
| repetitionB: "\<exists>N. semB (P * NUM N) now f now_dd f_dd \<Longrightarrow> semB (P*&&Inv) now f now_dd f_dd"
| outputBC: "d\<ge>0 \<Longrightarrow> semB (Cm (ch[!]e)) now f (now+d) (extend_history f now d)"
| inputBC: "d\<ge>0 \<Longrightarrow> semB (Cm (ch[?]x)) now f (now + d)
            (\<lambda>t. if t < now + d \<and> t > now then f now
                 else if t = now + d then update_fst (f now) x c
                 else f t)"
(*Notice: no real meaning of c in the inputBC. It will not be used actually without a synchronized output.*)

 
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
                    else if t = max nowp' nowq' then update_fst (fp' nowp') x (evalE e (fp' nowp')) 
                    else fp' t)
               (max nowp' nowq')
               (\<lambda>t. if nowq' < t \<and> t \<le> max nowp' nowq' then fq' nowq' else fq' t)"
| parallelB4: "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
               semBP (P; Cm (ch[!]e) || Q; Cm (ch[?]x)) nowp fp nowq fq
               (max nowp' nowq')
               (\<lambda>t. if nowp' < t \<and> t \<le> max nowp' nowq' then fp' nowp' else fp' t)
               (max nowp' nowq')
               (\<lambda>t. if nowq' < t \<and> t < max nowp' nowq' then fq' nowq'
                    else if t = max nowp' nowq' then update_fst (fq' nowq') x (evalE e (fq' nowq'))
                    else fq' t)"

inductive_cases [elim!]:
  "semB Skip now f now' f'"
  "semB (DAss x e) now f now' f'"
  "semB (x := e) now f now' f'"
  "semB (P; Q) now f now' f'"
  "semB (IF b P) now f  now' f'"
  "semB (P \<sqinter> Q) now f now' f'"
  "semB (<ode && Inv&b>) now f now' f'"
  "semB (P*&&Inv) now f now' f'"
  "semB (P* NUM N) now f now' f'"

inductive_cases [elim!]:
  "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'"
 
 

subsection \<open>Properties related to semantics\<close>

lemma sem1:
  "semB P now f now' f' \<Longrightarrow> now \<le> now'"
  by (induct rule: semB.induct, auto)

lemma semDass:
  "semB (DAss x e) now f now' f' \<Longrightarrow> now' = now \<and> f' = (\<lambda>t. if t = now then update_snd (f t) x (evalE e (f t)) else f t)"
  using semB.DassignB[of x e now f] by auto 

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
 
end
