theory Op_SL
imports State_SL
(*This file defines the operation semantics of HCSP.*)

begin



(*Five kinds of events for HCSP processes*)
datatype event = Tau | In cname val | Out cname val | IO cname val | Delay time
type_synonym now = real 

(* continuous evolution*)
(*Explicit solution*)
consts Solution :: "proc \<Rightarrow> state \<Rightarrow> real => val"

consts evalP :: "proc => now => history => event * proc * now * history"
consts evalPP :: "procP => now => history => history   => event * procP * now  * history * history"

 
(*parallel composition*)
(*Auxiliary functions needed to be introduced first.*)
(*chanset returns the channel set of a procecure, while varset the variable set of a 
procedure.*)
primrec compat :: "event => event => bool" where
"compat Tau ev = False" |
"compat (In ch val) ev = (if (ev = Out ch val) then True else False)" |
"compat (Out ch val) ev = (if (ev = In ch val) then True else False)" |
"compat (IO ch val) ev = False" |
"compat (Delay d) ev = False"

primrec handshake :: "event => event => event" where
"handshake Tau ev = Tau" |
"handshake (In ch val) ev = (if (ev = Out ch val) then (IO ch val) else Tau)" |
"handshake (Out ch val) ev = (if (ev = In ch val) then (IO ch val) else Tau)" |
"handshake (IO ch val) ev =Tau" |
"handshake (Delay d) ev =Tau"

primrec chansetC :: "comm => string set" where 
"chansetC (ch!!e) = {ch} "|
"chansetC (ch??e) = {ch}"
                            
primrec chanset :: "proc => string set" where
"chanset (Cm r) = chansetC r" |
"chanset Skip = {}" |
"chanset (e := f) = {}" |
"chanset (P; Q) = chanset P \<union> chanset Q" |
"chanset (IF b P) = chanset P" |
"chanset (C \<rightarrow> P) = chansetC C \<union> chanset P" |
"chanset (P [[ Q) = chanset P \<union> chanset Q" |
"chanset (P << Q) = chanset P \<union> chanset Q" | 
(*"chanset (P || Q) = chanset P \<union> chanset Q" |*)
"chanset (P*&&Inv) = chanset P" |
"chanset (<vl:el&&Inv&b>) = {}"|
"chanset (P [[> Q) = chanset P \<union> chanset Q"


(*The operational semantics of HCSP.*)
(*small step*)
inductive semP :: "proc => now => history => (event * proc * now * history) \<Rightarrow> bool" 
where
  skip : "semP Skip now f (Tau, Skip, now, f)"
| assignR : "semP ((RVar (x)) := e) now f 
   (Tau, Skip, now, (%t. if t = now then (%(y, i). if y=x & i=R then (evalE e (f(t))) else (f(t)(y, i))) else f(t)))"
| assignS :"semP ((SVar (x)) := e) now f (Tau, 
   Skip, now, (%t. if t = now then  (%(y, i). if y=x & i=S then (evalE e (f(t))) else (f(t)(y, i))) else f(t)))"
| assignB :"semP  ((BVar (x)) := e) now f (Tau, 
   Skip, now, (%t. if t = now then  (%(y, i). if y=x & i=B then (evalE e (f(t))) else (f(t)(y, i))) else f(t)))"
| continuousF : "([\<not>]b) (f(now)) ==> semP (<[s]:E&&Inv&b>)  now f  (Tau, Skip, now, f)"
| continuousT : "d\<ge>0 \<Longrightarrow> (
                     (let f'= (%t. if t <= now+d & t > now then
                       (%(y, i). if y=fst (s) & i=snd (s) then (Solution (<[s]:E&&Inv&b>) (f(now)) (t-now)) else f(now)(y, i)) else f(t)) in 
                    \<forall> m.  m <= now+d & m \<ge> now --> (b) (f'(m))))
    ==> semP (<[s]:E&&Inv&b>) now f  
       (Delay d, <[s]:E&&Inv&b>, now+d, (%t. if t <= now+d & t > now then
       (%(y, i). if y=fst (s) & i=snd (s) then (Solution (<[s]:E&&Inv&b>) (f(now)) (t-now)) else f(now)(y, i)) else f(t)))"
| sequenceL : "semP P now f (ev, P', now', f') \<and> ~ (P'= Skip)
               ==> semP (P; Q) now f  (ev, P';Q, now', f')"
| sequenceR : "semP P now f (ev, P', now', f') \<and> (P'= Skip)
   ==> semP (P; Q) now f (ev, Q, now', f')"
| conditionT : " be (f(now)) ==> semP (IF be P) now f  (Tau, P, now, f)"  
| conditionF : "~be (f(now)) ==> semP (IF be P) now f (Tau, Skip, now, f)" 
| joinL : "semP (P[[Q) now f (Tau, P, now, f)"
| joinR : "semP (P[[Q) now f (Tau, Q, now, f)"
| repetition0 : "semP (P*&&Inv) now f  (Tau, Skip, now, f)"
| repetitionk : "semP P now f (ev, P', now', f') \<and> ~(P'= Skip) ==>
                semP (P*&&Inv) now f (ev, (P'; P*&&Inv), now',f')" 
| repetitionk1 : "semP P now f (ev, P', now', f') \<and> (P'= Skip) ==>
                  semP (P*&&Inv) now f  (ev, P*&&Inv, now',f')"
| outputC : "semP (Cm (ch!!e)) now f  ((Out ch (valE e f(now))), Skip, now, f)" 
| outputW : "d\<ge>0 \<Longrightarrow> semP (Cm (ch!!e)) now f ((Delay d), Cm (ch!!e), now+d, 
            (%t. if t <= now+d & t > now then f(now) else f(t)))"
| inputC : "semP (Cm (ch??x)) now f ((In ch c), x:= (Con c), now, f)"
| inputW : "d\<ge>0 \<Longrightarrow> semP (Cm (ch??x)) now f ((Delay d), Cm (ch??x), now+d, 
            (%t. if t <= now+d & t > now then f(now) else f(t)))"

inductive semPP :: "procP => now => history \<Rightarrow> history => (event * procP * now * history * history) \<Rightarrow> bool" 
where
  parallel0 : "semPP (P||Q) now f g (eve, P'||Q', now', f', g') \<Longrightarrow> semPP (Q||P) now g f (eve, Q'||P', now', g', f')" 
| parallel1 : "semP P now f (evp, P', now, f) \<and> semP Q now g (evq, Q', now, g') \<and> compat evp evq
             ==> semPP (P||Q) now f  g  (handshake evp evq, P'||Q', now, f', g')" 
| parallel2 : "semP P now f  (evp, P', now', f')
             \<and> ((evp = Tau) | (EX ch c. evp = Out ch c & ~(ch \<in> chanset P \<inter> chanset Q))
             \<or> (EX ch c. evp = In ch c & ~(ch \<in> chanset P \<inter> chanset Q))
             \<or>(EX ch c. evp = IO ch c & ~(ch \<in> chanset P \<inter> chanset Q)))
            ==> semPP (P||Q) now f g (evp, P'||Q, now', f', g)" 
| parallel3 : "semP P now f   (Delay d, P', now+d, f')
              \<and> semP Q now g (Delay d, Q', now+d, g')
               ==> semPP (P||Q) now f g (Delay d, P'||Q', now+d, (%t. if t <= now+d & t >= now then f'(t) else f(t)),
                   (%t. if t <= now+d & t >= now then g'(t) else g(t)))"  
(*| parallel4: "semP (Skip||Skip) now f (Tau, Skip, now, f)"*)


(*Big-step semantics*)
inductive semB :: "proc => now => history => now \<Rightarrow> history \<Rightarrow> bool" 
where
  skipB : "semB Skip now f now f"
| assignBR : "semB ((RVar (x)) := e) now f 
    now  (%t. if t = now then (%(y, i). if y=x & i=R then (evalE e (f(t))) else (f(t)(y, i))) else f(t))"
| assignBS :"semB ((SVar (x)) := e) now f  
  now (%t. if t = now then  (%(y, i). if y=x & i=S then (evalE e (f(t))) else (f(t)(y, i))) else f(t))"
| assignBB :"semB  ((BVar (x)) := e) now f  
  now (%t. if t = now then  (%(y, i). if y=x & i=B then (evalE e (f(t))) else (f(t)(y, i))) else f(t))"
| continuousBF : "([\<not>]b) (f(now)) ==> semB (<[s]:E&&Inv&b>)  now f   now  f "
| continuousBT : "d>0 \<Longrightarrow> (
                     (let f'= (%t. if t <= now+d & t > now then
                       (%(y, i). if y=fst (s) & i=snd (s) then (Solution (<[s]:E&&Inv&b>) (f(now)) (t-now)) else f(now)(y, i)) else f(t)) in 
                   ( \<forall> m.  m < now+d & m \<ge> now --> (b) (f'(m))) \<and> ([\<not>]b) (f'(now+d))))
    ==> semB (<[s]:E&&Inv&b>) now f  
         (now+d) (%t. if t <= now+d & t > now then
       (%(y, i). if y=fst (s) & i=snd (s) then (Solution (<[s]:E&&Inv&b>) (f(now)) (t-now)) else f(now)(y, i)) else f(t))"
| sequenceB : "semB P now f now' f' \<and> semB Q now' f' now'' f''
               ==> semB (P; Q) now f now'' f''"
| conditionBT : "be (f(now)) ==> semB (P) now f  now_d f_d \<Longrightarrow> semB (IF be P) now f  now_d f_d"  
| conditionBF : "\<not>be (f(now)) ==> semB (IF be P) now f  now  f " 
| conditionGBT : "be (f(now)) ==> semB (P) now f  now_d f_d \<Longrightarrow> semB (IFELSE be P Q) now f  now_d f_d"  
| conditionGBF : "\<not>be (f(now)) ==> semB (Q) now f  now_d f_d \<Longrightarrow> semB (IFELSE be P Q) now f  now_d f_d" 
| joinBL : " semB (P) now f  now_d f_d \<Longrightarrow> semB (P[[Q) now f  now_d f_d"
| joinBR : " semB (Q) now f  now_d f_d \<Longrightarrow> semB (P[[Q) now f  now_d f_d"
| repetitionB : "\<exists> N. semB (P* NUM N) now f  now_dd f_dd \<Longrightarrow> semB (P*&&Inv) now f  now_dd f_dd"
| repetitionN0B : "N = (0::nat) \<Longrightarrow>  semB (P* NUM N) now f now f" 
| repetitionNkB : "N >0 \<Longrightarrow> semB P now f now_d f_d \<Longrightarrow> semB (P* NUM (N-(1::nat))) now_d f_d  now_dd f_dd ==>
                semB (P* NUM N) now f  now_dd f_dd" 
| outputBC : "d\<ge>0 \<Longrightarrow> semB (Cm (ch!!e)) now f (now+d)  (%t. if t <= now+d & t > now then f(now) else f(t))"
| inputBC : "d\<ge> 0 \<Longrightarrow> semB (Cm (ch??(RVar (x)))) now f (now + d)  
            (%t. if t < now+d & t > now then f(now) else (if t = now+d then (%(y, i). if y=x & i=R then (c) else (f(now)(y, i))) else f(t)))"
 
(*There are four cases for semantics of parallel  composition.*)
inductive semBP :: "procP => now => history \<Rightarrow> now \<Rightarrow> history \<Rightarrow>  now \<Rightarrow> history \<Rightarrow> now \<Rightarrow> history \<Rightarrow> bool" 
where
 parallelB1 : "semB P nowp fp nowp' fp' \<Longrightarrow> semB Q nowq fq nowq' fq' \<Longrightarrow> chanset P = {} \<and> chanset Q = {}  \<Longrightarrow>
   semBP (P||Q) nowp fp nowq fq nowp' fp' nowq'  fq'"
| parallelB2 : "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'  \<Longrightarrow> 
                semB U nowp' fp' nowu' fu' \<Longrightarrow> semB V nowq' fq' nowv' fv'  \<Longrightarrow> chanset P \<noteq> {} \<and> chanset Q \<noteq> {} \<Longrightarrow> 
                chanset U = {} \<and> chanset V = {} \<Longrightarrow> 
   semBP ((P; U) || (Q; V)) nowp fp nowq fq  nowu' fu' nowv' fv'"
| parallelB3: "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'
  \<Longrightarrow> semBP ((P;Cm (ch??(RVar (x))))||(Q; (Cm (ch!!e)))) nowp fp nowq fq (max nowp' nowq') 
      (%t. if t>nowp'\<and> t< max nowp' nowq' then fp'(nowp') else
             (if t =max nowp' nowq' then (%(y, i). 
                   if  y=x & i=R then (evalE e (fp'(nowp'))) else (fp'(nowp')(y, i))) else fp'(t)))
(max nowp' nowq') 
 (%t. if t>nowq'\<and> t\<le> max nowp' nowq' then fq'(nowq') else fq'(t))"
| parallelB4: "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'
  \<Longrightarrow> semBP(((P; (Cm (ch!!e))))||(Q; Cm (ch??(RVar (x))))) nowp fp nowq fq (max nowp' nowq') 
      (%t. if t>nowp'\<and> t\<le> max nowp' nowq' then fp'(nowp') else fp'(t))
(max nowp' nowq') 
 (%t. if t>nowq'\<and> t< max nowp' nowq' then fq'(nowq') else
             (if t =max nowp' nowq' then (%(y, i). 
                   if  y=x & i=R then (evalE e (fq'(nowq'))) else (fq'(nowq')(y, i))) else fq'(t)))"
 
 
inductive_cases [elim!]:
  "semB Skip now f now' f'" "semB ((RVar (x)) := e) now f now' f' "
"semB ((SVar (x)) := e) now f now' f' " "semB ((BVar (x)) := e) now f now' f' "
"semB (P; Q) now f now' f'" "semB (IF be P) now f  now'  f'" "semB (IFELSE be P Q) now f  now'  f'"
" semB (P[[Q) now f  now' f'" "semB (<[s]:E&&Inv&b>)  now f   now'  f'"
"semB (P*&&Inv) now f now' f'"
" semB (P* NUM N) now f now' f'"
"semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq'"  


subsection{*Continuous evolution*}
(*Differential invariant: Now the invariant is annotated in the equation directly.*)
(*consts Invariant :: "proc \<Rightarrow> fform"*)
(*exeFlow defines the execution of a continuous process from a state satisfying a given property*)
definition exeFlow :: "proc \<Rightarrow> fform \<Rightarrow> fform" where
"exeFlow P p s \<equiv> (\<exists>  now f now' f'. (  (semB (P) now f now' f') \<and> p (f(now)) \<and> 
(\<exists> t. t\<le> now' \<and> t\<ge> now \<and> f'(t) = s)))"
 
 
subsection{*Properties related to semantics*}
lemma sem1 : "semB P now f now' f' \<Longrightarrow> now \<le> now'"
apply (erule semB.induct)
apply auto
done

lemma semB1 : "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> nowp \<le> nowp' \<and> nowq \<le> nowq'"
apply (erule semBP.induct) 
apply (rule conjI) 
apply (rule sem1, simp) 
apply (rule sem1, simp) 
apply (metis order_trans sem1)
apply (metis le_max_iff_disj)+
done

lemma sem2 : "semB P now f now' f' \<Longrightarrow> ( \<forall> t. t< now \<or> t> now' \<longrightarrow> f t = f' t)"
apply (erule semB.induct)
apply simp+
apply (subgoal_tac "now \<le> now' \<and> now' \<le> now''")
apply (metis (poly_guards_query) antisym_conv3 le_less_trans less_not_sym)
apply (rule conjI)
apply (cut_tac P = "P" and now = now and  now'=now' and f = "f" and f' = "f'" in sem1, simp)
apply metis
apply (cut_tac P = "Q" and now = now' and  now'=now'' and f = "f'" and f' = "f''" in sem1, simp)
apply metis+
apply (subgoal_tac "now \<le> now_d \<and> now_d \<le> now_dd")
apply (metis (poly_guards_query) antisym_conv3 le_less_trans less_not_sym)
apply (rule conjI)
apply (cut_tac P = "P" and now = now and  now'=now_d and f = "f" and f' = "f_d" in sem1, simp)
apply metis
apply (cut_tac P = "P* NUM (N - 1)" and now = now_d and  now'=now_dd and f = "f_d" and f' = "f_dd" in sem1, simp)
apply metis
   apply (metis less_not_sym not_le)
 by auto


lemma semB2 : "semBP (P||Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow> 
  ( \<forall> t. t< nowp \<or> t> nowp' \<longrightarrow> (fp t = fp' t))
\<and>  ( \<forall> t. t< nowq \<or> t> nowq' \<longrightarrow> (fq t = fq' t))"
apply (erule semBP.induct)
apply (metis sem2)
apply (subgoal_tac "nowp \<le> nowp'\<and> nowq \<le> nowq'\<and> nowp'\<le> nowu'\<and> nowq'\<le> nowv'")
apply (subgoal_tac "(\<forall>t. t < nowp' \<or> nowu' < t \<longrightarrow> fp' t = fu' t) \<and> (\<forall>t. t < nowq' \<or> nowv' < t \<longrightarrow> fq' t = fv' t)")
apply simp
apply (simp add: sem2)
apply (simp add: sem1 semB1)
apply (rule conjI)
apply (metis less_irrefl less_max_iff_disj max_def not_le semB1)
apply (metis less_irrefl less_max_iff_disj max_def not_le semB1)
apply (rule conjI)
apply (metis less_irrefl less_max_iff_disj max_def not_le semB1)
apply (metis less_irrefl less_max_iff_disj max_def not_le semB1)
done



lemma semB3 : " semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' 
                  \<Longrightarrow> chanset P = {} \<and> chanset Q = {}
                  \<Longrightarrow> semB P nowp fp nowp' fp' \<and> semB Q nowq fq nowq' fq'"
apply (ind_cases "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq'", simp)
apply (simp add:chanset_def)+
  done
    

 
end
 