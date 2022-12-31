theory task1
  imports testvalid
begin

type_synonym tid = real

datatype status =
  WAIT | READY | RUNNING

datatype estate =
  Sch (pool:"(real \<times> tid) list") (run_now:tid) (run_prior:real)
| Task (status:status) (entered:nat) (task_prior:real)
| None

definition req_ch :: "tid \<Rightarrow> string" where
  "req_ch tid = (
    if tid = 1 then ''reqProcessor1''
    else if tid = 2 then ''reqProcessor2''
    else undefined)"

definition preempt_ch :: "tid \<Rightarrow> string" where
  "preempt_ch tid = (
    if tid = 1 then ''preempt1''
    else if tid = 2 then ''preempt2''
    else undefined)"

definition run_ch :: "tid \<Rightarrow> string" where
  "run_ch tid = (
    if tid = 1 then ''run1''
    else if tid = 2 then ''run2''
    else undefined)"

definition free_ch :: "tid \<Rightarrow> string" where
  "free_ch tid = (
    if tid = 1 then ''free1''
    else if tid = 2 then ''free2''
    else undefined)"


definition exit_ch :: "tid \<Rightarrow> string" where
  "exit_ch tid = (
    if tid = 1 then ''exit1''
    else if tid = 2 then ''exit2''
    else undefined)"

definition T :: char where "T = CHR ''t''"

definition C :: char where "C = CHR ''c''"

definition F :: char where "F = CHR ''F''"

fun ent_assign :: "nat \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate" where
"ent_assign n (Task st nt p) s = (Task st n p)"

fun wait_assign :: "estate \<Rightarrow> state \<Rightarrow> estate" where
"wait_assign (Task st nt p) s = (Task WAIT nt p)"

fun ready_assign :: "estate \<Rightarrow> state \<Rightarrow> estate" where
"ready_assign (Task st nt p) s = (Task READY nt p)"

fun run_assign :: "estate \<Rightarrow> state \<Rightarrow> estate" where
"run_assign (Task st nt p) s = (Task RUNNING nt p)"

definition T1 :: "estate proc" where
"T1 = IF (\<lambda>(a,s) . status a = WAIT) 
        THEN (Wait (\<lambda>(a,s). 0.045 - s T);T ::= (\<lambda>_. 0); Basic (ent_assign 0);Basic (ready_assign)) 
      ELSE 
      (IF(\<lambda>(a,s) . status a = READY) 
        THEN (Cm ((req_ch 1)[!](\<lambda>(a,s). task_prior a)); 
             (Interrupt (ODE ((\<lambda> _ _ . 0)(T := (\<lambda> _ .1)))) (\<lambda> s. s T < 0.045) [(run_ch 1[?]F,Basic run_assign)]); 
             (IF (\<lambda>(a,s) . status a = READY \<and> s T = 0.045) THEN (EChoice[(run_ch 1[?]F,Basic run_assign),(exit_ch 1[!](\<lambda>_.0),Basic wait_assign)]) ELSE Skip FI))  
      ELSE 
      (IF(\<lambda>(a,s) . entered a = 0) THEN 
             (C ::= (\<lambda>_ . 0); Basic (ent_assign 1)) ELSE Skip FI; 
        (Interrupt (ODE ((\<lambda> _ _ . 0)(T := (\<lambda> _ .1),C := (\<lambda>_ .1)))) (\<lambda> s. s T < 0.045 \<and> s C < 0.01) [(preempt_ch 1[?]F,Basic ready_assign)]); 
        IF (\<lambda>(a,s) . status a = RUNNING) THEN (EChoice[(preempt_ch 1[?]F,Basic wait_assign),(free_ch 1[!](\<lambda>_.0),Basic wait_assign)]) ELSE Skip FI) 
      FI) FI"


fun T1_tr:: "nat \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "T1_tr k (Sch v va vb) s = false\<^sub>A"
| "T1_tr k None s = false\<^sub>A"
| "T1_tr 0 (Task st ent tp) s = emp\<^sub>t"
| "T1_tr (Suc k) (Task WAIT ent tp) s = 
   (wait_tassn (0.045 - s T) (\<lambda>_ . EState(Task WAIT ent tp,s)) ({},{}) @\<^sub>t T1_tr k (Task READY 0 tp) (s(T:=0)))"
| "T1_tr (Suc k) (Task READY ent tp) s =
  (((out_tassn (req_ch 1) tp) @\<^sub>t 
     ((\<exists>\<^sub>t \<tau> v. \<up>(\<tau>\<in>{0..<0.045- s T}) \<and>\<^sub>t (wait_assn \<tau> (\<lambda> t. EState(Task READY ent tp,s(T := s T + t))) ({}, {run_ch 1}) @\<^sub>t in_tassn (run_ch 1) v @\<^sub>t T1_tr k (Task RUNNING ent tp) (s(T := s T + \<tau>, F := v)))) 
  \<or>\<^sub>t (wait_assn (0.045- s T) (\<lambda> t. EState(Task READY ent tp,s(T := s T + t))) ({}, {run_ch 1}) @\<^sub>t ((\<exists>\<^sub>t v. in_tassn (run_ch 1) v @\<^sub>t T1_tr k (Task RUNNING ent tp) (s(T := 0.045, F := v)))
                                                                                   \<or>\<^sub>t(out_tassn (exit_ch 1) 0 @\<^sub>t T1_tr k (Task WAIT ent tp) (s(T := 0.045)))
                                                                                   \<or>\<^sub>t(\<exists>\<^sub>t \<tau> . \<up>(\<tau>\<in>{0<..}) \<and>\<^sub>t wait_tassn \<tau> (\<lambda>_. EState(Task READY ent tp,s(T := 0.045))) ({exit_ch 1},{run_ch 1}) @\<^sub>t true\<^sub>A)))))
   \<or>\<^sub>t ((\<exists>\<^sub>t \<tau> . \<up>(\<tau>\<in>{0<..}) \<and>\<^sub>t (wait_assn \<tau> (\<lambda>_ . EState(Task READY ent tp,s)) ({req_ch 1}, {}))) @\<^sub>t true\<^sub>A))"
| "T1_tr (Suc k) (Task RUNNING ent tp) s =
  (let c = (if ent = 0 then 0 else s C) in 
  (\<exists>\<^sub>t \<tau> v. \<up>(\<tau>\<in>{0..<min (0.045- s T) (0.01 - c)}) \<and>\<^sub>t (wait_assn \<tau> (\<lambda> t. EState(Task RUNNING 1 tp,s(T := s T + t,C := c + t))) ({}, {preempt_ch 1}) @\<^sub>t in_tassn (preempt_ch 1) v @\<^sub>t T1_tr k (Task READY 1 tp) (s(T := s T + \<tau>, C := c + \<tau>,F := v))))
\<or>\<^sub>t(wait_assn (min (0.045- s T) (0.01 - c)) (\<lambda> t. EState(Task RUNNING 1 tp,s(T := s T + t,C := c + t))) ({}, {preempt_ch 1}) @\<^sub>t ((\<exists>\<^sub>t v. in_tassn (preempt_ch 1) v @\<^sub>t T1_tr k (Task WAIT 1 tp) (s(T := s T + (min (0.045- s T) (0.01 - c)),C := c+(min (0.045- s T) (0.01 - c)),  F := v)))
                                                                                                                              \<or>\<^sub>t(out_tassn (free_ch 1) 0 @\<^sub>t T1_tr k (Task WAIT 1 tp) (s(T := s T + (min (0.045- s T) (0.01 - c)),C := c+(min (0.045- s T) (0.01 - c)))))
                                                                                                                              \<or>\<^sub>t(\<exists>\<^sub>t \<tau> . \<up>(\<tau>\<in>{0<..}) \<and>\<^sub>t wait_tassn \<tau> (\<lambda>_. EState(Task RUNNING 1 tp,s(T := s T + (min (0.045- s T) (0.01 - c)),C := c+(min (0.045- s T) (0.01 - c))))) ({exit_ch 1},{run_ch 1}) @\<^sub>t true\<^sub>A))))"


lemma T1_Valid_WAIT:
"\<Turnstile> {\<lambda>s t. s = (Task WAIT ent tp,ss) \<and> P s t}
   T1
    {\<lambda> s t. s = (Task READY 0 tp,ss(T:=0)) \<and> (P (Task WAIT ent tp,ss) @\<^sub>t Wait\<^sub>t (9 / 200 - ss T) (\<lambda>_. EState (Task WAIT ent tp, ss)) ({}, {})) t}"
  unfolding T1_def
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_cond_sp)
    apply(rule Valid_seq)
     apply(rule Valid_wait_sp1)
    apply(rule Valid_seq)
  apply(rule Valid_assign_sp1)
    apply(rule Valid_seq)
     apply(rule Valid_basic_sp1)
    apply simp
    apply(rule Valid_basic_sp1)
  unfolding entails_def
   apply simp
   apply(rule Valid_weaken_pre[where P'="\<lambda> s t. False"])
  unfolding entails_def
    apply auto[1]
   apply(rule Valid_False)
  apply(auto simp add: pure_assn_def conj_assn_def)
  done


lemma T1_Valid_READY:
"\<Turnstile> {\<lambda>s t. s = (Task READY ent tp,ss) \<and> P s t}
   T1
    {\<lambda> s t. Q}"
unfolding T1_def
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_cond_sp)
  apply(rule Valid_weaken_pre[where P'="\<lambda> s t. False"])
unfolding entails_def
    apply auto[1]
  apply(rule Valid_False)
  apply(rule Valid_cond_sp)
  prefer 2
apply(rule Valid_weaken_pre[where P'="\<lambda> s t. False"])
unfolding entails_def
    apply auto[1]
  apply(rule Valid_False)
  apply(rule Valid_seq)
  apply(rule Valid_send_sp)
  apply(rule Valid_seq)
  apply(rule Valid_interrupt_In_sp)


