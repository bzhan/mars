section \<open>Operation semantics of HCSP.\<close>

theory Op_SL
  imports State_SL
begin

text \<open>Five kinds of events for HCSP processes\<close>
datatype event = Tau | In cname val | Out cname val | IO cname val | Delay time
type_synonym now = real

text \<open>Continuous evolution\<close>

datatype flow = Flow "(string * typeid) list" "exp list"
text \<open>Explicit solution\<close>
consts Solution :: "flow \<Rightarrow> state \<Rightarrow> real \<Rightarrow> val"

consts evalP :: "proc \<Rightarrow> now \<Rightarrow> history \<Rightarrow> event * proc * now * history"
consts evalPP :: "procP \<Rightarrow> now \<Rightarrow> history \<Rightarrow> history \<Rightarrow> event * procP * now * history * history"

 
text \<open>Parallel composition\<close>

text \<open>Auxiliary functions needed to be introduced first.\<close>

primrec compat :: "event \<Rightarrow> event \<Rightarrow> bool" where
  "compat Tau ev = False"
| "compat (In ch val) ev = (if ev = Out ch val then True else False)"
| "compat (Out ch val) ev = (if ev = In ch val then True else False)"
| "compat (IO ch val) ev = False"
| "compat (Delay d) ev = False"

primrec handshake :: "event \<Rightarrow> event \<Rightarrow> event" where
  "handshake Tau ev = Tau"
| "handshake (In ch val) ev = (if ev = Out ch val then IO ch val else Tau)"
| "handshake (Out ch val) ev = (if ev = In ch val then IO ch val else Tau)"
| "handshake (IO ch val) ev = Tau"
| "handshake (Delay d) ev = Tau"

text \<open>Set of channels of a procedure\<close>
primrec chansetC :: "comm => string set" where 
  "chansetC (ch!!e) = {ch}"
| "chansetC (ch??e) = {ch}"
                            
primrec chanset :: "proc \<Rightarrow> string set" where
  "chanset (Cm r) = chansetC r"
| "chanset Skip = {}"
| "chanset (e := f) = {}"
| "chanset (P; Q) = chanset P \<union> chanset Q"
| "chanset (IF b P) = chanset P"
| "chanset (C \<rightarrow> P) = chansetC C \<union> chanset P"
| "chanset (P [[ Q) = chanset P \<union> chanset Q"
| "chanset (P << Q) = chanset P \<union> chanset Q"
  (*"chanset (P || Q) = chanset P \<union> chanset Q" |*)
| "chanset (P *&& Inv) = chanset P"
| "chanset (<vl : el && Inv & b>) = {}"
| "chanset (P [[> Q) = chanset P \<union> chanset Q"


text \<open>Small step semantics for HCSP.\<close>

inductive semP :: "proc \<Rightarrow> now \<Rightarrow> history \<Rightarrow> (event * proc * now * history) \<Rightarrow> bool" where
  skip: "semP Skip now f (Tau, Skip, now, f)"
| assignR: "semP ((RVar x) := e) now f
    (Tau, Skip, now, (\<lambda>t. if t = now then (\<lambda>(y, i). if y=x \<and> i=R then evalE e (f t) else f t (y, i)) else f t))"
| assignS: "semP ((SVar x) := e) now f
    (Tau, Skip, now, (\<lambda>t. if t = now then (\<lambda>(y, i). if y=x & i=S then evalE e (f t) else f t (y, i)) else f t))"
| assignB: "semP ((BVar x) := e) now f
    (Tau, Skip, now, (\<lambda>t. if t = now then (\<lambda>(y, i). if y=x & i=B then evalE e (f t) else f t (y, i)) else f t))"
| continuousF: "([\<not>]b) (f now) \<Longrightarrow>
    semP (<[s]:E&&Inv&b>) now f (Tau, Skip, now, f)"
| continuousT: "d\<ge>0 \<Longrightarrow>
       let f' = (\<lambda>t. if t \<le> now+d \<and> t > now then
                       (\<lambda>(y, i). if y=fst s \<and> i=snd s then Solution (Flow [s] E) (f now) (t-now) else f now (y, i))
                     else f t)
       in \<forall>m. m \<le> now+d \<and> m \<ge> now \<longrightarrow> b (f' m) \<Longrightarrow>
    semP (<[s]:E&&Inv&b>) now f
      (Delay d, <[s]:E&&Inv&b>, now+d,
       (\<lambda>t. if t \<le> now+d \<and> t > now then
              (\<lambda>(y, i). if y=fst s \<and> i=snd s then Solution (Flow [s] E) (f now) (t-now) else f now (y, i))
            else f t))"
| sequenceL: "semP P now f (ev, P', now', f') \<and> P'\<noteq>Skip \<Longrightarrow>
              semP (P; Q) now f (ev, P';Q, now', f')"
| sequenceR: "semP P now f (ev, P', now', f') \<and> P'=Skip \<Longrightarrow>
              semP (P; Q) now f (ev, Q, now', f')"
| conditionT: " b (f now) \<Longrightarrow> semP (IF b P) now f (Tau, P, now, f)"
| conditionF: "\<not>b (f now) \<Longrightarrow> semP (IF b P) now f (Tau, Skip, now, f)"
| joinL: "semP (P[[Q) now f (Tau, P, now, f)"
| joinR: "semP (P[[Q) now f (Tau, Q, now, f)"
| repetition0: "semP (P*&&Inv) now f (Tau, Skip, now, f)"
| repetitionk: "semP P now f (ev, P', now', f') \<and> P'\<noteq>Skip \<Longrightarrow>
                semP (P*&&Inv) now f (ev, (P'; P*&&Inv), now', f')"
| repetitionk1: "semP P now f (ev, P', now', f') \<and> P'=Skip \<Longrightarrow>
                  semP (P*&&Inv) now f (ev, P*&&Inv, now',f')"
| outputC : "semP (Cm (ch!!e)) now f (Out ch (evalE e (f now)), Skip, now, f)"
| outputW : "d\<ge>0 \<Longrightarrow> semP (Cm (ch!!e)) now f
            (Delay d, Cm (ch!!e), now+d, \<lambda>t. if t \<le> now+d \<and> t > now then f now else f t)"
| inputC : "semP (Cm (ch??x)) now f (In ch c, x := (Con c), now, f)"
| inputW : "d\<ge>0 \<Longrightarrow> semP (Cm (ch??x)) now f
            (Delay d, Cm (ch??x), now+d, \<lambda>t. if t \<le> now+d \<and> t > now then f now else f t)"

inductive semPP :: "procP \<Rightarrow> now \<Rightarrow> history \<Rightarrow> history \<Rightarrow> (event * procP * now * history * history) \<Rightarrow> bool" where
  parallel0: "semPP (P||Q) now f g (eve, P'||Q', now', f', g') \<Longrightarrow> semPP (Q||P) now g f (eve, Q'||P', now', g', f')"
| parallel1: "semP P now f (evp, P', now, f') \<and> semP Q now g (evq, Q', now, g') \<and> compat evp evq \<Longrightarrow>
              semPP (P||Q) now f g (handshake evp evq, P'||Q', now, f', g')"
| parallel2 : "semP P now f (evp, P', now', f')
             \<and> ((evp = Tau) \<or>
                (\<exists>ch c. evp = Out ch c \<and> \<not>(ch \<in> chanset P \<inter> chanset Q)) \<or>
                (\<exists>ch c. evp = In ch c \<and> \<not>(ch \<in> chanset P \<inter> chanset Q)) \<or>
                (\<exists>ch c. evp = IO ch c \<and> \<not>(ch \<in> chanset P \<inter> chanset Q))) \<Longrightarrow>
             semPP (P||Q) now f g (evp, P'||Q, now', f', g)"
| parallel3 : "semP P now f (Delay d, P', now+d, f')
              \<and> semP Q now g (Delay d, Q', now+d, g') \<Longrightarrow>
             semPP (P||Q) now f g (Delay d, P'||Q', now+d, (\<lambda>t. if t \<le> now+d \<and> t \<ge> now then f' t else f t),
                   (\<lambda>t. if t \<le> now+d \<and> t \<ge> now then g' t else g t))"
(*| parallel4: "semP (Skip||Skip) now f (Tau, Skip, now, f)"*)


text \<open>Big-step semantics\<close>

inductive semB :: "proc \<Rightarrow> now \<Rightarrow> history \<Rightarrow> now \<Rightarrow> history \<Rightarrow> bool" where
  skipB: "semB Skip now f now f"
| assignBR: "semB ((RVar x) := e) now f 
    now (\<lambda>t. if t = now then (\<lambda>(y, i). if y=x \<and> i=R then evalE e (f t) else f t (y, i)) else f t)"
| assignBS: "semB ((SVar x) := e) now f
    now (\<lambda>t. if t = now then (\<lambda>(y, i). if y=x \<and> i=S then evalE e (f t) else f t (y, i)) else f t)"
| assignBB: "semB ((BVar x) := e) now f
    now (\<lambda>t. if t = now then (\<lambda>(y, i). if y=x \<and> i=B then evalE e (f t) else f t (y, i)) else f t)"
| continuousBF: "([\<not>]b) (f now) \<Longrightarrow> semB (<[s]:E&&Inv&b>) now f now f"
| continuousBT: "d>0 \<Longrightarrow> 
       let f' = (\<lambda>t. if t \<le> now+d \<and> t > now then
                       (\<lambda>(y, i). if y=fst s \<and> i=snd s then (Solution (Flow [s] E) (f now) (t-now)) else f now (y, i))
                     else f t)
       in (\<forall>m. m < now+d \<and> m \<ge> now \<longrightarrow> b (f' m)) \<and> ([\<not>]b) (f' (now+d)) \<Longrightarrow>
    semB (<[s]:E&&Inv&b>) now f (now+d)
      (\<lambda>t. if t \<le> now+d \<and> t > now then
             (\<lambda>(y, i). if y=fst s \<and> i=snd s then (Solution (Flow [s] E) (f now) (t-now)) else f now (y, i))
           else f t)"
| sequenceB: "semB P now f now' f' \<and> semB Q now' f' now'' f'' \<Longrightarrow> semB (P; Q) now f now'' f''"
| conditionBT: " b (f now) \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (IF b P) now f now_d f_d"
| conditionBF: "\<not>b (f now) \<Longrightarrow> semB (IF b P) now f now f"
| conditionGBT: " b (f now) \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (IFELSE b P Q) now f now_d f_d"
| conditionGBF: "\<not>b (f now) \<Longrightarrow> semB Q now f now_d f_d \<Longrightarrow> semB (IFELSE b P Q) now f now_d f_d"
| joinBL: "semB P now f now_d f_d \<Longrightarrow> semB (P[[Q) now f now_d f_d"
| joinBR: "semB Q now f now_d f_d \<Longrightarrow> semB (P[[Q) now f now_d f_d"
| repetitionB: "\<exists>N. semB (P * NUM N) now f now_dd f_dd \<Longrightarrow> semB (P*&&Inv) now f now_dd f_dd"
| repetitionN0B: "N = (0::nat) \<Longrightarrow> semB (P * NUM N) now f now f"
| repetitionNkB: "N > (0::nat) \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (P * NUM (N-1)) now_d f_d now_dd f_dd \<Longrightarrow>
                  semB (P * NUM N) now f now_dd f_dd"
| outputBC: "d\<ge>0 \<Longrightarrow> semB (Cm (ch!!e)) now f (now+d) (\<lambda>t. if t \<le> now+d \<and> t > now then f now else f t)"
| inputBC: "d\<ge>0 \<Longrightarrow> semB (Cm (ch??(RVar x))) now f (now + d)
            (\<lambda>t. if t < now+d \<and> t > now then f now
                 else if t = now+d then \<lambda>(y, i). if y=x \<and> i=R then c else f now (y, i)
                 else f t)"
 
text \<open>There are four cases for semantics of parallel composition.\<close>
inductive semBP :: "procP \<Rightarrow> now \<Rightarrow> history \<Rightarrow> now \<Rightarrow> history \<Rightarrow> now \<Rightarrow> history \<Rightarrow> now \<Rightarrow> history \<Rightarrow> bool" where
  parallelB1: "semB P nowp fp nowp' fp' \<Longrightarrow> semB Q nowq fq nowq' fq' \<Longrightarrow> chanset P = {} \<and> chanset Q = {} \<Longrightarrow>
               semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'"
| parallelB2: "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
               semB U nowp' fp' nowu' fu' \<Longrightarrow> semB V nowq' fq' nowv' fv' \<Longrightarrow> chanset P \<noteq> {} \<and> chanset Q \<noteq> {} \<Longrightarrow>
               chanset U = {} \<and> chanset V = {} \<Longrightarrow>
               semBP ((P; U) || (Q; V)) nowp fp nowq fq  nowu' fu' nowv' fv'"
| parallelB3:
 "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
  semBP (P; Cm (ch??(RVar x)) || Q; Cm (ch!!e)) nowp fp nowq fq (max nowp' nowq')
   (\<lambda>t. if nowp' < t \<and> t < max nowp' nowq' then fp' nowp'
         else if t = max nowp' nowq' then \<lambda>(y, i). if y = x \<and> i = R then evalE e (fp' nowp') else fp' nowp' (y, i)
              else fp' t)
   (max nowp' nowq') (\<lambda>t. if nowq' < t \<and> t \<le> max nowp' nowq' then fq' nowq' else fq' t)"
| parallelB4:
 "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
  semBP (P; Cm (ch!!e) || Q; Cm (ch??(RVar x))) nowp fp nowq fq (max nowp' nowq')
   (\<lambda>t. if nowp' < t \<and> t \<le> max nowp' nowq' then fp' nowp' else fp' t) (max nowp' nowq')
   (\<lambda>t. if nowq' < t \<and> t < max nowp' nowq' then fq' nowq'
         else if t = max nowp' nowq' then \<lambda>(y, i). if y = x \<and> i = R then evalE e (fq' nowq') else fq' nowq' (y, i)
              else fq' t)"

inductive_cases [elim!]:
  "semB Skip now f now' f'"
  "semB ((RVar x) := e) now f now' f'"
  "semB ((SVar x) := e) now f now' f'"
  "semB ((BVar x) := e) now f now' f'"
  "semB (P; Q) now f now' f'"
  "semB (IF be P) now f  now' f'"
  "semB (IFELSE be P Q) now f now' f'"
  "semB (P[[Q) now f now' f'"
  "semB (<[s]:E&&Inv&b>) now f now' f'"
  "semB (P*&&Inv) now f now' f'"
  "semB (P* NUM N) now f now' f'"
  "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'"


subsection \<open>Continuous evolution\<close>

(*Differential invariant: Now the invariant is annotated in the equation directly.*)
(*consts Invariant :: "proc \<Rightarrow> fform"*)

text \<open>exeFlow defines the execution of a continuous process from a state satisfying a given property\<close>
definition exeFlow :: "proc \<Rightarrow> fform \<Rightarrow> fform" where
  "exeFlow P p s \<equiv> (\<exists>now f now' f'. semB P now f now' f' \<and> p (f now) \<and> (\<exists>t. t \<le> now' \<and> t \<ge> now \<and> f' t = s))"


subsection \<open>Properties related to semantics\<close>

lemma sem1:
  "semB P now f now' f' \<Longrightarrow> now \<le> now'"
  by (induct rule: semB.induct, auto)

lemma semB1:
  "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp \<le> nowp' \<and> nowq \<le> nowq'"
proof (induct rule: semBP.induct)
  case (parallelB1 P nowp fp nowp' fp' Q nowq fq nowq' fq')
  then show ?case by (auto intro: sem1)
next
  case (parallelB2 P Q nowp fp nowq fq nowp' fp' nowq' fq' U nowu' fu' V nowv' fv')
  then show ?case by (metis order_trans sem1)
qed (metis le_max_iff_disj)+

lemma sem2:
  "semB P now f now' f' \<Longrightarrow> \<forall>t. t < now \<or> t > now' \<longrightarrow> f t = f' t"
proof (induct rule: semB.induct)
  case (sequenceB P now f now' f' Q now'' f'')
  then show ?case
    by (metis (full_types) le_less_trans not_le sem1)
next
  case (repetitionNkB N P now f now_d f_d now_dd f_dd)
  then show ?case
    by (metis (full_types) le_less_trans less_eq_real_def sem1)
qed auto

lemma semB2:
  "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
    (\<forall>t. t < nowp \<or> t > nowp' \<longrightarrow> (fp t = fp' t)) \<and>
    (\<forall>t. t < nowq \<or> t > nowq' \<longrightarrow> (fq t = fq' t))"
proof (induct rule: semBP.induct)
  case (parallelB1 P nowp fp nowp' fp' Q nowq fq nowq' fq')
  then show ?case by (auto simp add: sem2)
next
  case (parallelB2 P Q nowp fp nowq fq nowp' fp' nowq' fq' U nowu' fu' V nowv' fv')
  then show ?case by (smt sem1 sem2 semB1)
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
