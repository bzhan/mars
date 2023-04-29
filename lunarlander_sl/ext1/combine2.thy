theory combine2
  imports combine1
begin

definition proper' :: "estate \<Rightarrow> bool " where
"proper' schs = ((properp (run_now schs) (run_prior schs)) \<and> (pool schs) = [])"

definition propc' :: "nat \<Rightarrow> estate \<Rightarrow> estate \<Rightarrow> bool" where
"propc' k schs task_es = (k>0 \<longrightarrow>(status task_es = RUNNING \<longleftrightarrow> run_now schs = 2))"



fun combine2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> estate ext_state \<Rightarrow> estate ext_state \<Rightarrow> estate ext_state \<Rightarrow> estate tassn" where
  "combine2 0 k1 k2 (Sch p rn rp,ss) (Task st1 ent1 tp1,ts1) (Task st2 ent2 tp2,ts2) = emp\<^sub>t"
| "combine2 (Suc k) 0 0 (Sch p rn rp, ss) (Task st1 ent1 tp1, ts1) (Task st2 ent2 tp2, ts2)  = false\<^sub>A"
| "combine2 (Suc k) 0 (Suc k2) (Sch p rn rp, ss) (Task st1 ent1 tp1, ts1) (Task WAIT ent2 tp2, ts2) = 
   (\<up> (9 / 200 - ts2 T = 0) \<and>\<^sub>t combine2 (Suc k) 0 k2 (Sch p rn rp, ss) (Task st1 ent1 tp1, ts1) (Task READY ezero tp2, ts2(T:=0)))"
| "combine2 (Suc k) 0 (Suc k2) (Sch p rn rp, ss) (Task st1 ent1 tp1, ts1) (Task READY ent2 tp2, ts2) = (
     (\<up> (rn = -1) \<and>\<^sub>t (combine2 k 0 k2 (Sch p 2 1, ss(Pr := 1)) (Task st1 ent1 tp1, ts1) (Task RUNNING ent2 tp2, ts2(T := ts2 T, F := 0))))
  \<or>\<^sub>t (\<up> (k > 0 \<and> 9 / 200 - ts2 T = 0) \<and>\<^sub>t (combine2 (k-1) 0 k2 (Sch p rn rp, ss(Pr := 1, G := 0)) (Task st1 ent1 tp1, ts1) (Task WAIT ent2 tp2, ts2(T := 9 / 200)))))"
| "combine2 (Suc k) 0 (Suc k2) (Sch p rn rp, ss) (Task st1 ent1 tp1, ts1) (Task RUNNING ent2 tp2, ts2) = 
     combine2 k 0 k2 (Sch [] (- 1) (- 1), ss(G := 0)) (Task st1 ent1 tp1, ts1) (Task WAIT eone tp2, ts2(C := C_upd ent2 (ts2 C)))"
| "combine2 (Suc k) (Suc k1) 0 (Sch p rn rp, ss) (Task WAIT ent1 tp1, ts1) (Task st2 ent2 tp2, ts2) = 
   (\<up> (9 / 200 - ts1 T = 0) \<and>\<^sub>t combine2 (Suc k) k1 0 (Sch p rn rp, ss) (Task READY ezero tp1, ts1(T:=0)) (Task st2 ent2 tp2, ts2))"
| "combine2 (Suc k) (Suc k1) 0 (Sch p rn rp, ss) (Task READY ent1 tp1, ts1) (Task st2 ent2 tp2, ts2) = 
   (\<up> (rn = -1) \<and>\<^sub>t combine2 k k1 0 (Sch p 1 2, ss(Pr := 2)) (Task RUNNING ent1 tp1, ts1(F := 0)) (Task st2 ent2 tp2, ts2))"
| "combine2 (Suc k) (Suc k1) 0 (Sch p rn rp, ss) (Task RUNNING ent1 tp1, ts1) (Task st2 ent2 tp2, ts2) = 
     combine2 k k1 0 (Sch [] (- 1) (- 1), ss(G := 0)) (Task WAIT eone tp1, ts1(C := C_upd ent1 (ts1 C))) (Task st2 ent2 tp2, ts2)"
| "combine2 (Suc k) (Suc k1) (Suc k2) (Sch p rn rp, ss) (Task WAIT ent1 tp1, ts1) (Task WAIT ent2 tp2, ts2) = (
  (\<up> (ts1 T = ts2 T) \<and>\<^sub>t Wait\<^sub>t (9 / 200 - ts1 T)
      (\<lambda>t. ParState (ParState (EState (Sch p rn rp, ss))
              (EState (Task WAIT ent1 tp1, ts1(T := ts1 T + t))))
              (EState (Task WAIT ent2 tp2, ts2(T := ts2 T + t))))
      ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t
      (combine2 (Suc k) k1 k2 (Sch p rn rp, ss) (Task READY ezero tp1, ts1(T := 0)) (Task READY ezero tp2, ts2(T := 0))))
\<or>\<^sub>t (\<up> (ts2 T < ts1 T) \<and>\<^sub>t Wait\<^sub>t (9 / 200 - ts1 T)
     (\<lambda>t. ParState (ParState (EState (Sch p rn rp, ss))
              (EState (Task WAIT ent1 2, ts1(T := ts1 T + t))))
              (EState (Task WAIT ent2 1, ts2(T := ts2 T + t))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t
      (combine2 (Suc k) k1 (Suc k2) (Sch p rn rp, ss) (Task READY ezero 2, ts1(T := 0)) (Task WAIT ent2 tp2, ts2(T:=ts2 T + (0.045 - ts1 T)))))
\<or>\<^sub>t (\<up> (ts1 T < ts2 T) \<and>\<^sub>t Wait\<^sub>t (9 / 200 - ts2 T)
     (\<lambda>t. ParState (ParState (EState (Sch p rn rp, ss))
             (EState (Task WAIT ent1 2, ts1(T := ts1 T + t))))
             (EState (Task WAIT ent2 1, ts2(T := ts2 T + t))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t
    (combine2 (Suc k) (Suc k1) k2 (Sch p rn rp, ss) (Task WAIT ent1 tp1, ts1(T:=ts1 T + (0.045 - ts2 T))) (Task READY ezero tp2, ts2(T := 0))))
)"
| "combine2 (Suc k) (Suc k1) (Suc k2) (Sch p rn rp, ss) (Task WAIT ent1 tp1, ts1) (Task READY ent2 tp2, ts2) = (
  (\<up> (9 / 200 - ts1 T = 0) \<and>\<^sub>t (combine2 (Suc k) k1 (Suc k2) (Sch p rn rp, ss) (Task READY ezero tp1, ts1(T := 0)) (Task READY ent2 tp2, ts2)))
\<or>\<^sub>t(\<up> (9 / 200 - ts1 T > 0) \<and>\<^sub>t (combine2 k (Suc k1) k2 (Sch p 2 1, ss(Pr := 1)) (Task WAIT ent1 tp1, ts1) (Task RUNNING ent2 tp2, ts2(F := 0))))
)"
| "combine2 (Suc k) (Suc k1) (Suc k2) (Sch p rn rp, ss) (Task WAIT ent1 tp1, ts1) (Task RUNNING ent2 tp2, ts2) = (
  (\<up> (min (45 / 10 ^ 3 - ts2 T) (2 / 10\<^sup>2 - C_upd ent2 (ts2 C)) \<ge> (9 / 200 - ts1 T))
   \<and>\<^sub>t  Wait\<^sub>t (9 / 200 - ts1 T)
        (\<lambda>t. ParState (ParState (EState (Sch p rn rp, ss))
                (EState (Task WAIT ent1 tp1, ts1(T := ts1 T + t))))
                (EState (Task RUNNING eone tp2, ts2(T := ts2 T + t, C := C_upd ent2 (ts2 C) + t))))
        ({},{preempt_ch 2, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1,exit_ch 2}) @\<^sub>t 
    combine2 (Suc k) k1 (Suc k2) (Sch p rn rp, ss) (Task READY ezero tp1, ts1(T := 0)) (Task RUNNING eone tp2, ts2(T:= ts2 T + (9 / 200 - ts1 T), C:= C_upd ent2 (ts2 C) + (9 / 200 - ts1 T))))
\<or>\<^sub>t(\<up> (min (45 / 10 ^ 3 - ts2 T) (2 / 10\<^sup>2 - C_upd ent2 (ts2 C)) < (9 / 200 - ts1 T))
   \<and>\<^sub>t  Wait\<^sub>t (min (9 / 200 - ts2 T) (1 / 50 - C_upd ent2 (ts2 C)))
     (\<lambda>t. ParState(ParState (EState (Sch p rn rp, ss))
             (EState (Task WAIT ent1 tp1, ts1(T := ts1 T + t))))
             (EState(Task RUNNING eone tp2, ts2(T := ts2 T + t, C := C_upd ent2 (ts2 C) + t))))
     ({},{preempt_ch 2, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t 
    (combine2 k (Suc k1) k2 (Sch [] (- 1) (- 1), ss(G := 0)) 
     (Task WAIT ent1 tp1, ts1(T := ts1 T + min (9 / 200 - ts2 T) (1 / 50 - C_upd ent2 (ts2 C))))
     (Task WAIT eone tp2, ts2(T := ts2 T + min (9 / 200 - ts2 T) (1 / 50 - C_upd ent2 (ts2 C)),
         C := C_upd ent2 (ts2 C) + min (9 / 200 - ts2 T) (1 / 50 - C_upd ent2 (ts2 C))))))
)"
| "combine2 (Suc k) (Suc k1) (Suc k2) (Sch p rn rp, ss) (Task READY ent1 tp1, ts1) (Task WAIT ent2 tp2, ts2) = (
  (\<up> (9 / 200 - ts2 T = 0) \<and>\<^sub>t (combine2 (Suc k) (Suc k1) k2 (Sch p rn rp, ss) (Task READY ent1 tp1, ts1) (Task READY ezero tp2, ts2(T := 0))))
\<or>\<^sub>t(\<up> (9 / 200 - ts2 T > 0) \<and>\<^sub>t (combine2 k k1 (Suc k2) (Sch p 1 2, ss(Pr := 2)) (Task RUNNING ent1 tp1, ts1(F := 0)) (Task WAIT ent2 tp2, ts2)))
)"
| "combine2 (Suc k) (Suc k1) (Suc k2) (Sch p rn rp, ss) (Task READY ent1 tp1, ts1) (Task READY ent2 tp2, ts2) = (
   combine2 k k1 (Suc k2) (Sch p 1 2, ss(Pr := 2)) (Task RUNNING ent1 tp1, ts1(F := 0)) (Task READY ent2 tp2, ts2)
\<or>\<^sub>t combine2 k (Suc k1) k2 (Sch p 2 1, ss(Pr := 1)) (Task READY ent1 tp1, ts1) (Task RUNNING ent2 tp2, ts2(F := 0))
)"
| "combine2 (Suc k) (Suc k1) (Suc k2) (Sch p rn rp, ss) (Task READY ent1 tp1, ts1) (Task RUNNING ent2 tp2, ts2) = (
  (combine2 k k1 k2 (Sch p 1 2, ss(Pr := 2)) (Task RUNNING ent1 tp1, ts1(F := 0)) (Task READY eone tp2, ts2(C := C_upd ent2 (ts2 C), F := 0)))
\<or>\<^sub>t(\<up> (min (9 / 200 - ts2 T) (1 / 50 - C_upd ent2 (ts2 C)) = 0) \<and>\<^sub>t
    combine2 k k1 k2 (Sch p 1 2, ss(Pr := 2)) (Task RUNNING ent1 tp1, ts1(F := 0))(Task WAIT eone tp2, ts2(C := C_upd ent2 (ts2 C), F := 0)))
\<or>\<^sub>t(\<up> (min (9 / 200 - ts2 T) (1 / 50 - C_upd ent2 (ts2 C)) = 0) \<and>\<^sub>t    
    combine2 k (Suc k1) k2 (Sch [] (- 1) (- 1), ss(G := 0)) (Task READY ent1 tp1, ts1) (Task WAIT eone tp2, ts2(C := C_upd ent2 (ts2 C))))
)"
| "combine2 (Suc k) (Suc k1) (Suc k2) (Sch p rn rp, ss) (Task RUNNING ent1 tp1, ts1) (Task WAIT ent2 tp2, ts2) = (
  (\<up> (min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)) \<ge> (9 / 200 - ts2 T)) 
        \<and>\<^sub>t Wait\<^sub>t (9 / 200 - ts2 T)
     (\<lambda>t. ParState(ParState (EState (Sch p rn rp, ss))
             (EState(Task RUNNING eone tp1, ts1(T := ts1 T + t, C := C_upd ent1 (ts1 C) + t))))
             (EState (Task WAIT ent2 tp2, ts2(T := ts2 T + t))))
     ({},{preempt_ch 1, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t
   combine2 (Suc k) (Suc k1) k2 (Sch p rn rp, ss) (Task RUNNING eone tp1, ts1(T:= ts1 T + (9 / 200 - ts2 T), C:= C_upd ent1 (ts1 C) + (9 / 200 - ts2 T))) (Task READY ezero tp2, ts2(T := 0)))
\<or>\<^sub>t(\<up> ((9 / 200 - ts2 T) > min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C))) 
        \<and>\<^sub>t Wait\<^sub>t (min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)))
     (\<lambda>t. ParState(ParState (EState (Sch p rn rp, ss))
             (EState(Task RUNNING eone tp1, ts1(T := ts1 T + t, C := C_upd ent1 (ts1 C) + t))))
             (EState (Task WAIT ent2 tp2, ts2(T := ts2 T + t))))
     ({},{preempt_ch 1, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t
(combine2 k k1 (Suc k2) (Sch [] (- 1) (- 1), ss(G := 0))
       (Task WAIT eone tp1, ts1(T := ts1 T + min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)),
         C := C_upd ent1 (ts1 C) + min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C))))
       (Task WAIT ent2 tp2, ts2(T:= ts2 T + min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C))))))
)"
| "combine2 (Suc k) (Suc k1) (Suc k2) (Sch p rn rp, ss) (Task RUNNING ent1 tp1, ts1) (Task READY ent2 tp2, ts2) = (
   (\<up> (min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)) = 0) \<and>\<^sub>t
       (combine2 k k1 (Suc k2) (Sch [] (- 1) (- 1), ss(G := 0)) (Task WAIT eone tp1, ts1(C := C_upd ent1 (ts1 C))) (Task READY ent2 tp2, ts2)))
\<or>\<^sub>t (\<up> (min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)) \<le> 9 / 200 - ts2 T \<and> k > 0) \<and>\<^sub>t
    Wait\<^sub>t (min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)))
     (\<lambda>t. ParState(ParState (EState (Sch [(1, 2)] 1 2, ss(Pr := 1)))
             (EState (Task RUNNING eone tp1, ts1(T := ts1 T + t, C := C_upd ent1 (ts1 C) + t))))
             (EState (Task READY ent2 tp2, ts2(T := ts2 T + t))))
     ({}, {run_ch 2, preempt_ch 1, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t 
     (combine2 (k-1) k1 k2 (Sch [] 2 1, ss(Pr := 1, G := 0))
       (Task WAIT eone tp1, ts1
        (T := ts1 T + min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)),
         C := C_upd ent1 (ts1 C) + min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C))))
       (Task RUNNING ent2 tp2, ts2(T := ts2 T + min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)), F := 0))))
\<or>\<^sub>t (\<up> (min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)) \<ge> 9 / 200 - ts2 T \<and> k > 0) \<and>\<^sub>t
    Wait\<^sub>t (9 / 200 - ts2 T)
     (\<lambda>t. ParState
           (ParState (EState (Sch [(1, 2)] 1 2, ss(Pr := 1)))
             (EState (Task RUNNING eone tp1, ts1(T := ts1 T + t, C := C_upd ent1 (ts1 C) + t))))
           (EState (Task READY ent2 tp2, ts2(T := ts2 T + t))))
     ({}, {run_ch 2, preempt_ch 1, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t
     (combine2 (k-1) (Suc k1) k2 (Sch [] 1 2, ss(Pr := 1, G := 0))
       (Task RUNNING eone tp1, ts1(T := ts1 T + (9 / 200 - ts2 T), C := C_upd ent1 (ts1 C) + (9 / 200 - ts2 T)))
       (Task WAIT ent2 tp2, ts2(T := 9 / 200))))
)"
| "combine2 (Suc k) (Suc k1) (Suc k2) (Sch p rn rp, ss) (Task RUNNING ent1 tp1, ts1) (Task RUNNING ent2 tp2, ts2) = false\<^sub>A"


lemma combine_assn_in0_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (in_0assn ch v @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_0assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_in0_wait:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (in_0assn ch v @\<^sub>t P) (wait_assn d p rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   \<up>(d\<le>0) \<and>\<^sub>t combine_assn chs (in_0assn ch v @\<^sub>t P) Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:in_0assn.cases[of ch v])
     apply auto
    apply(cases rule:wait_assn.cases[of d p rdy])
      apply auto
    subgoal by (auto elim: sync_elims)
    apply(rule exI[where x="(InBlock ch v # tr2a)"])
    by auto
  done

lemma combine_assn_in0_out:
"ch1\<in>chs \<and> ch2\<in>chs \<Longrightarrow>
combine_assn chs (in_0assn ch1 v1 @\<^sub>t P) (out_assn s ch2 v2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
\<up>(ch1=ch2 \<and> v1 =v2) \<and>\<^sub>t combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: in_0assn.cases[of ch1 v1 tr1a])
     apply auto
    apply(cases rule: out_assn.cases[of s ch2 v2 tr1b])
      apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    by (auto elim: sync_elims)
  done

lemma combine_assn_in0_outrdy:
"ch1\<in>chs \<and> ch2\<in>chs \<Longrightarrow>
combine_assn chs (in_0assn ch1 v1 @\<^sub>t P) (outrdy_assn s ch2 v2 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
\<up>(ch1=ch2 \<and> v1 =v2) \<and>\<^sub>t combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: in_0assn.cases[of ch1 v1 tr1a])
     apply auto
    apply(cases rule: outrdy_assn.cases[of s ch2 v2 rdy tr1b])
      apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    by (auto elim: sync_elims)
  done

lemma combine_assn_in0_inrdy:
"ch1\<in>chs \<and> ch2\<in>chs \<Longrightarrow>
combine_assn chs (in_0assn ch1 v1 @\<^sub>t P) (inrdy_assn s ch2 v2 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: in_0assn.cases[of ch1 v1 tr1a])
     apply auto
    apply(cases rule: inrdy_assn.cases[of s ch2 v2 rdy tr1b])
      apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    by (auto elim: sync_elims)
  done


lemma combine_assn_in0_waitin:
"ch1\<in>chs \<and> ch2\<in>chs \<Longrightarrow>
combine_assn chs (in_0assn ch1 v1 @\<^sub>t P) (waitin_assn d p ch2 v2 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: in_0assn.cases[of ch1 v1 tr1a])
     apply auto
    apply(cases rule: waitin_assn.cases[of d p ch2 v2 rdy tr1b])
      apply auto
    subgoal
      by (auto elim: sync_elims)
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    done
  done

lemma combine_assn_out0_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (out_0assn ch v @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_0assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_out0_inrdy:
"ch1\<in>chs \<and> ch2\<in>chs \<Longrightarrow>
combine_assn chs (out_0assn ch1 v1 @\<^sub>t P) (inrdy_assn s ch2 v2 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
\<up>(ch1=ch2 \<and> v1 =v2) \<and>\<^sub>t combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: out_0assn.cases[of ch1 v1 tr1a])
     apply auto
    apply(cases rule: inrdy_assn.cases[of s ch2 v2 rdy tr1b])
      apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    by (auto elim: sync_elims)
  done


lemma combine_assn_out0_outrdy:
"ch1\<in>chs \<and> ch2\<in>chs \<Longrightarrow>
combine_assn chs (out_0assn ch1 v1 @\<^sub>t P) (outrdy_assn s ch2 v2 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: out_0assn.cases[of ch1 v1 tr1a])
     apply auto
    apply(cases rule: outrdy_assn.cases[of s ch2 v2 rdy tr1b])
      apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    by (auto elim: sync_elims)
  done

lemma combine_assn_out0_waitin:
"ch1\<in>chs \<and> ch2\<in>chs \<Longrightarrow>
combine_assn chs (out_0assn ch1 v1 @\<^sub>t P) (waitin_assn d p ch2 v2 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
  \<up>(ch1=ch2 \<and> v1 =v2 \<and> d\<le>0) \<and>\<^sub>t combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: out_0assn.cases[of ch1 v1 tr1a])
     apply auto
    apply(cases rule: waitin_assn.cases[of d p ch2 v2 rdy tr1b])
      apply auto
    subgoal
      by (auto elim: sync_elims)
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    done
  done


lemma combine_assn_wait_wait2:
"compat_rdy rdy1 rdy2 \<and> d1 = d2 \<and> d1\<ge>0 \<Longrightarrow>
combine_assn chs (wait_assn d1 p1 rdy1 @\<^sub>t P) (wait_assn d2 p2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
wait_assn d1 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P Q"
unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_assn.cases[of d2 p1 rdy1 tr1a])
      apply auto
    subgoal
     apply(cases rule:wait_assn.cases[of d2 p2 rdy2 tr1b])
        apply auto
      apply(elim combine_blocks_waitE2)
       apply auto
      apply(rule exI[where x="[WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
      apply auto
      apply(rule) by auto
    by(auto simp add:emp_assn_def)
  done


lemma combine_assn_wait_wait3:
"compat_rdy rdy1 rdy2 \<and> d1 < d2 \<and> d1\<ge>0 \<Longrightarrow>
combine_assn chs (wait_assn d1 p1 rdy1 @\<^sub>t P) (wait_assn d2 p2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
wait_assn d1 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P (wait_assn (d2-d1) (\<lambda> t. p2(t+d1)) rdy2 @\<^sub>t Q)"
unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_assn.cases[of d1 p1 rdy1 tr1a])
      apply auto
    subgoal
     apply(cases rule:wait_assn.cases[of d2 p2 rdy2 tr1b])
        apply auto
      subgoal
      apply(elim combine_blocks_waitE3)
       apply auto
      apply(rule exI[where x="[WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
      apply auto
         apply(rule) 
         apply auto
        apply(rule exI[where x= tr2a])
        apply auto
        apply(rule exI[where x="(WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2b)"])
        apply auto
        apply(rule exI[where x="[WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2]"])
        apply auto
        apply(rule) by auto
      done
    by(auto simp add:emp_assn_def)
  done

lemma combine_assn_wait_wait3':
"compat_rdy rdy1 rdy2 \<and> d1 \<le> d2 \<and> d1\<ge>0 \<Longrightarrow>
combine_assn chs (wait_assn d1 p1 rdy1 @\<^sub>t P) (wait_assn d2 p2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
wait_assn d1 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P (wait_assn (d2-d1) (\<lambda> t. p2(t+d1)) rdy2 @\<^sub>t Q)"
  apply(cases "d1=d2")
  subgoal 
    apply auto
    apply(rule combine_assn_wait_wait2)
    by auto
  apply(rule combine_assn_wait_wait3)
  by auto


lemma combine_assn_wait_wait4:
"compat_rdy rdy1 rdy2 \<and> d1 > d2 \<and> d2\<ge>0 \<Longrightarrow>
combine_assn chs (wait_assn d1 p1 rdy1 @\<^sub>t P) (wait_assn d2 p2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
wait_assn d2 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs (wait_assn (d1-d2) (\<lambda> t. p1(t+d2)) rdy1 @\<^sub>t P) Q"
unfolding combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_assn.cases[of d2 p2 rdy2 tr1b])
      apply auto
    subgoal
     apply(cases rule:wait_assn.cases[of d1 p1 rdy1 tr1a])
        apply auto
      subgoal
      apply(elim combine_blocks_waitE4)
       apply auto
      apply(rule exI[where x="[WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
      apply auto
         apply(rule) 
         apply auto
        apply(rule exI[where x="(WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr2a)"])
        apply auto
         apply(rule exI[where x="[WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1]"])
        apply auto
        apply(rule) by auto
      done
    by(auto simp add:emp_assn_def)
  done

lemma combine_assn_wait_wait4':
"compat_rdy rdy1 rdy2 \<and> d1 \<ge> d2 \<and> d2\<ge>0 \<Longrightarrow>
combine_assn chs (wait_assn d1 p1 rdy1 @\<^sub>t P) (wait_assn d2 p2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
wait_assn d2 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs (wait_assn (d1-d2) (\<lambda> t. p1(t+d2)) rdy1 @\<^sub>t P) Q"
  apply(cases "d1=d2")
  subgoal
    apply auto
    apply(rule combine_assn_wait_wait2)
    by auto
  apply(rule combine_assn_wait_wait4)
  by auto

lemma combine_assn_wait_wait5:
"compat_rdy rdy1 rdy2 \<and> d1 \<ge> 0 \<and> d2\<ge> 0 \<Longrightarrow>
combine_assn chs (wait_assn d1 p1 rdy1 @\<^sub>t P) (wait_assn d2 p2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (\<up>(d1=d2) \<and>\<^sub>t wait_assn d1 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P Q)
\<or>\<^sub>t (\<up>(d1<d2) \<and>\<^sub>t wait_assn d1 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P (wait_assn (d2-d1) (\<lambda> t. p2(t+d1)) rdy2 @\<^sub>t Q))
\<or>\<^sub>t (\<up>(d1>d2) \<and>\<^sub>t wait_assn d2 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs (wait_assn (d1-d2) (\<lambda> t. p1(t+d2)) rdy1 @\<^sub>t P) Q)"
  apply(cases "d1>d2")
  subgoal apply auto
    apply(rule entails_tassn_disjI2)
    apply(rule entails_tassn_disjI2)
    apply(rule combine_assn_wait_wait4)
    by auto
  apply(cases "d1<d2")
  subgoal apply auto
    apply(rule entails_tassn_disjI2)
    apply(rule entails_tassn_disjI1)
    apply(rule combine_assn_wait_wait3)
    by auto
  apply auto
  apply(rule entails_tassn_disjI1)
  apply(rule combine_assn_wait_wait2)
  by auto

lemma combine_assn_waitin_wait:
  assumes "ch \<in> chs \<and> compat_rdy rdy1 rdy2 \<and> d1\<ge>0 \<and> d2\<ge>0"
  shows "combine_assn chs (waitin_assn d1 p1 ch v rdy1 @\<^sub>t P)(Wait\<^sub>t d2 p2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
      \<up>(d2\<le>d1) \<and>\<^sub>t   Wait\<^sub>t d2 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) 
                @\<^sub>t (combine_assn chs (waitin_assn (d1-d2) (\<lambda> t. p1(t+d2)) ch v rdy1 @\<^sub>t P) Q)"
  unfolding combine_assn_def
  using assms
  apply (auto simp add: entails_tassn_def join_assn_def)
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: waitin_assn.cases[of d1 p1 ch v rdy1 tr1a])
      apply auto
    subgoal
      apply(cases rule: wait_assn.cases[of d2 p2 rdy2 tr1b])
        apply auto
        subgoal using assms
        apply(cases "d2<d1")
        subgoal
          apply (auto elim!: combine_blocks_waitE4)
          apply(rule exI[where x="[WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
          apply auto
          subgoal apply rule by auto
          apply(rule exI[where x="(WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # InBlock ch v # tr2a)"])
          apply auto
          apply(rule exI[where x="WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # [InBlock ch v]"])
          apply auto
          apply(rule )
          by auto
        apply(cases "d2>d1")
        subgoal
          apply (auto elim!: combine_blocks_waitE3)
          by (auto elim:combine_blocks_pairE2)
        apply(cases "d2=d1")
        subgoal
          apply (auto elim!: combine_blocks_waitE2)
          apply(rule exI[where x="[WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
          apply auto
          subgoal apply(rule) by auto
          apply(rule exI[where x="(InBlock ch v # tr2a)"])
          apply auto
          apply(rule exI[where x="[InBlock ch v]"])
          apply auto
          apply(rule)
          by auto
        by auto
      subgoal
        apply(auto simp add:emp_assn_def)
        apply(rule exI[where x="(WaitBlk d1 p1 rdy1 # InBlock ch v # tr2a)"])
        by auto
      done
    subgoal
      apply(cases rule: wait_assn.cases[of d2 p2 rdy2 tr1b])
        apply auto
      subgoal
        by (auto elim: sync_elims)
      subgoal
        apply(auto simp add:emp_assn_def)
        apply(rule exI[where x="(InBlock ch v # tr2a)"])
        by auto
      done
    done
  done

lemma combine_assn_wait_waitin:
  assumes "ch \<in> chs \<and> compat_rdy rdy2 rdy1 \<and> d1\<ge>0 \<and> d2\<ge>0"
  shows "combine_assn chs (Wait\<^sub>t d2 p2 rdy2 @\<^sub>t Q) (waitin_assn d1 p1 ch v rdy1 @\<^sub>t P) \<Longrightarrow>\<^sub>t 
      \<up>(d2\<le>d1) \<and>\<^sub>t   Wait\<^sub>t d2 (\<lambda> t. ParState (p2 t) (p1 t)) (merge_rdy rdy2 rdy1) 
                @\<^sub>t (combine_assn chs Q (waitin_assn (d1-d2) (\<lambda> t. p1(t+d2)) ch v rdy1 @\<^sub>t P))"
  unfolding combine_assn_def
  using assms
  apply (auto simp add: entails_tassn_def join_assn_def)
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: waitin_assn.cases[of d1 p1 ch v rdy1 tr1b])
      apply auto
    subgoal
      apply(cases rule: wait_assn.cases[of d2 p2 rdy2 tr1a])
        apply auto
        subgoal using assms
        apply(cases "d2<d1")
        subgoal
          apply (auto elim!: combine_blocks_waitE3)
          apply(rule exI[where x="[WaitBlk d2 (\<lambda>t. ParState (p2 t) (p1 t)) (merge_rdy rdy2 rdy1)]"])
          apply auto
          subgoal apply rule by auto
          apply(rule exI[where x=tr2a])
          apply auto
          apply(rule exI[where x="(WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # InBlock ch v # tr2b)"])
          apply auto
          apply(rule exI[where x="WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # [InBlock ch v]"])
          apply auto
          apply(rule )
          by auto
        apply(cases "d2>d1")
        subgoal
          apply (auto elim!: combine_blocks_waitE4)
          by (auto elim:combine_blocks_pairE2')
        apply(cases "d2=d1")
        subgoal
          apply (auto elim!: combine_blocks_waitE2)
          apply(rule exI[where x="[WaitBlk d1 (\<lambda>t. ParState (p2 t) (p1 t)) (merge_rdy rdy2 rdy1)]"])
          apply auto
          subgoal apply(rule) by auto
          apply(rule exI[where x=tr2a])
          apply auto
          apply(rule exI[where x="(InBlock ch v # tr2b)"])
          apply auto
          apply(rule exI[where x="[InBlock ch v]"])
          apply auto
          apply(rule)
          by auto
        by auto
      subgoal
        apply(auto simp add:emp_assn_def)
        apply(rule exI[where x="tr2a"])
        apply auto
        apply(rule exI[where x="(WaitBlk d1 p1 rdy1 # InBlock ch v # tr2b)"])
        by auto
      done
    subgoal
      apply(cases rule: wait_assn.cases[of d2 p2 rdy2 tr1a])
        apply auto
      subgoal
        by (auto elim: sync_elims)
      subgoal
        apply(auto simp add:emp_assn_def)
        apply(rule exI[where x="tr2a"])
        apply auto
        apply(rule exI[where x="(InBlock ch v # tr2b)"])
        by auto
      done
    done
  done


lemma combine_assn_wait_out:
  assumes "ch\<in>chs \<and> ch \<in> snd rdy"
  shows "combine_assn chs (wait_assn d p rdy @\<^sub>t P) (out_assn s ch v @\<^sub>t Q)
      \<Longrightarrow>\<^sub>t \<up>(d\<le>0) \<and>\<^sub>t combine_assn chs P (out_assn s ch v @\<^sub>t Q)"
  unfolding combine_assn_def
  using assms
  apply (auto simp add: entails_tassn_def join_assn_def)
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: wait_assn.cases[of d p rdy tr1a])
      apply auto
    apply(cases rule:out_assn.cases[of s ch v tr1b])
      apply auto
    subgoal
      by (auto elim: sync_elims)
    apply(elim combine_blocks_waitE1)
    apply(cases rdy)
    by auto
  done

lemma combine_assn_wait_outrdy:
  assumes "ch\<in>chs \<and> \<not> compat_rdy rdy rdy'"
  shows "combine_assn chs (wait_assn d p rdy @\<^sub>t P) (outrdy_assn s ch v rdy'@\<^sub>t Q)
      \<Longrightarrow>\<^sub>t \<up>(d\<le>0) \<and>\<^sub>t combine_assn chs P (outrdy_assn s ch v rdy' @\<^sub>t Q)"
  unfolding combine_assn_def
  using assms
  apply (auto simp add: entails_tassn_def join_assn_def)
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: wait_assn.cases[of d p rdy tr1a])
      apply auto
    apply(cases rule:outrdy_assn.cases[of s ch v rdy' tr1b])
      apply auto
    subgoal
      by (auto elim: sync_elims)
    apply(elim combine_blocks_waitE1)
    by auto
  done

lemma combine_assn_wait_inrdy:
  assumes "ch\<in>chs \<and> \<not> compat_rdy rdy rdy'"
  shows "combine_assn chs (wait_assn d p rdy @\<^sub>t P) (inrdy_assn s ch v rdy'@\<^sub>t Q)
      \<Longrightarrow>\<^sub>t \<up>(d\<le>0) \<and>\<^sub>t combine_assn chs P (inrdy_assn s ch v rdy' @\<^sub>t Q)"
  unfolding combine_assn_def
  using assms
  apply (auto simp add: entails_tassn_def join_assn_def)
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: wait_assn.cases[of d p rdy tr1a])
      apply auto
    apply(cases rule:inrdy_assn.cases[of s ch v rdy' tr1b])
      apply auto
    subgoal
      by (auto elim: sync_elims)
    apply(elim combine_blocks_waitE1)
    by auto
  done

lemma combine_assn_waitin_out:
  assumes "ch\<in>chs \<and> ch \<in> snd rdy"
  shows "combine_assn chs (waitin_assn d p ch v rdy @\<^sub>t P) (out_assn s' ch v' @\<^sub>t Q) \<Longrightarrow>\<^sub>t
           \<up>(v=v' \<and> d\<le>0) \<and>\<^sub>t combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:waitin_assn.cases[of d p ch v rdy tr1a])
      apply auto
    subgoal 
      apply(cases rule:out_assn.cases[of s' ch v' tr1b])
      apply auto
      subgoal
        by(auto elim:combine_blocks_pairE2')
      subgoal for d
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        by auto
      done
    subgoal
      apply(cases rule:out_assn.cases[of s' ch v' tr1b])
        apply auto
      subgoal
        apply (auto elim!: combine_blocks_pairE)
        by blast
      subgoal for d
        by(auto elim:combine_blocks_pairE2)
      done
    done
  done


lemma combine_assn_waitin_out'':
  assumes "ch1\<in>chs \<and> ch2\<in>chs \<and> ch1\<noteq>ch2"
  shows "combine_assn chs (waitin_assn d p ch1 v rdy @\<^sub>t P) (out_assn s' ch2 v' @\<^sub>t Q) \<Longrightarrow>\<^sub>t
           R"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:waitin_assn.cases[of d p ch1 v rdy tr1a])
      apply auto
      subgoal 
        apply(cases rule:out_assn.cases[of s' ch2 v' tr1b])
        apply auto
        subgoal
          by (auto elim!: sync_elims)
        subgoal for d2
          apply(cases "\<not> compat_rdy rdy ({ch2}, {})")
          subgoal by (auto elim!: sync_elims)
          apply(cases "d<d2")
          subgoal
            apply(elim combine_blocks_waitE3)
            by (auto elim!: sync_elims)
          apply(cases "d>d2")
          subgoal
            apply(elim combine_blocks_waitE4)
            by (auto elim!: sync_elims)
          apply auto
          apply(elim combine_blocks_waitE2)
          by (auto elim!: combine_blocks_pairE)
        done
      subgoal
      apply(cases rule:out_assn.cases[of s' ch2 v' tr1b])
        apply auto
        subgoal
          by (auto elim!: combine_blocks_pairE)
        subgoal
          by (auto elim!: sync_elims)
        done
      done
    done


lemma combine_assn_out0_waitin1:
  assumes "ch2\<in>chs \<and> ch1\<in>chs"
  shows "combine_assn chs (out_0assn ch2 v2 @\<^sub>t P)(waitin_assn d p ch1 v1 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         \<up>(ch1 = ch2 \<and> v1 = v2 \<and> d\<le>0) \<and>\<^sub>t combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch2 v2 tr1a])
     apply auto
    apply(cases rule:waitin_assn.cases[of d p ch1 v1 rdy tr1b])
      apply auto
    subgoal 
      by(auto elim!: combine_blocks_pairE2)
    subgoal
      apply(auto elim!: combine_blocks_pairE)
      by blast
    done
  done


lemma combine_assn_waitp_waitin':
  assumes "ch1\<in>chs \<and> \<not>compat_rdy rdy1 rdy2"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P)(waitin_assn d p ch1 v1 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         R"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    subgoal for dd pp
      apply(cases rule:waitin_assn.cases[of d p ch1 v1 rdy2 tr1b])
        apply auto
      subgoal
        apply(elim combine_blocks_waitE1)
        by auto
      subgoal
        by (auto elim!: sync_elims)
    done
  done
  done


lemma combine_assn_waitin_waitin:
  assumes "ch1\<in>chs \<and> ch2\<in>chs"
  shows "combine_assn chs (waitin_assn d1 p1 ch1 v1 rdy1 @\<^sub>t P) (waitin_assn d2 p2 ch2 v2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:waitin_assn.cases[of d1 p1 ch1 v1 rdy1])
      apply auto
    subgoal 
      apply(cases rule:waitin_assn.cases[of d2 p2 ch2 v2 rdy2])
        apply auto
      subgoal 
        apply(cases "\<not> compat_rdy rdy1 rdy2")
        subgoal by (auto elim!: sync_elims)
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          by (auto elim!: sync_elims)
        apply auto
        apply(elim combine_blocks_waitE2)
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        by (auto elim!: sync_elims)
      done
      subgoal
      apply(cases rule:waitin_assn.cases[of d2 p2 ch2 v2 rdy2])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      done
      done
    done



lemma combine_assn_waitin_outrdy:
  assumes "ch1\<in>chs \<and> ch2\<in>chs \<and> \<not>compat_rdy rdy1 rdy2"
  shows "combine_assn chs (waitin_assn d p ch1 v1 rdy1 @\<^sub>t P)(outrdy_assn s2 ch2 v2 rdy2 @\<^sub>t Q)
         \<Longrightarrow>\<^sub>t \<up>(ch1 = ch2 \<and> v1= v2 \<and> d \<le> 0) \<and>\<^sub>t combine_assn chs P Q"
  unfolding entails_tassn_def combine_assn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:waitin_assn.cases[of d p ch1 v1 rdy1 tr1a])
      apply auto
    subgoal
      apply(cases rule:outrdy_assn.cases[of s2 ch2 v2 rdy2 tr1b])
        apply auto
      by (auto elim!: sync_elims)
    subgoal
      apply(cases rule:outrdy_assn.cases[of s2 ch2 v2 rdy2 tr1b])
        apply auto
      subgoal
        apply(auto elim!: combine_blocks_pairE)
        by blast
      by (auto elim!: sync_elims)
    done
  done


lemma combine_assn_waitin_inrdy:
  assumes "ch1\<in>chs \<and> ch2\<in>chs"
  shows "combine_assn chs (waitin_assn d1 p1 ch1 v1 rdy1 @\<^sub>t P) (inrdy_assn s ch2 v2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:waitin_assn.cases[of d1 p1 ch1 v1 rdy1])
      apply auto
    subgoal 
      apply(cases rule:inrdy_assn.cases[of s ch2 v2 rdy2])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d2
        apply(cases "\<not> compat_rdy rdy1 rdy2")
        subgoal by (auto elim!: sync_elims)
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          by (auto elim!: sync_elims)
        apply auto
        apply(elim combine_blocks_waitE2)
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      done
      subgoal
      apply(cases rule:inrdy_assn.cases[of s ch2 v2 rdy2 tr1b])
          apply auto
        subgoal
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        by (auto elim!: sync_elims)
      done
      done
    done


lemma combine_SCH_T1_T2:
"propc k1 (Sch p rn rp) (Task st1 ent1 2) \<Longrightarrow>
 propc' k2 (Sch p rn rp) (Task st2 ent2 1) \<Longrightarrow>
   proper' (Sch p rn rp) \<Longrightarrow>
   inv_s ts1 \<Longrightarrow>
   inv_s' ts2 \<Longrightarrow>
 combine_assn {req_ch 2, preempt_ch 2, run_ch 2, free_ch 2, exit_ch 2} 
 (combine1 k k1 (Sch p rn rp,ss) (Task st1 ent1 2,ts1)) (T2_tr k2 (Task st2 ent2 1,ts2)) \<Longrightarrow>\<^sub>t
 combine2 k k1 k2 (Sch p rn rp,ss) (Task st1 ent1 2,ts1) (Task st2 ent2 1,ts2)"
proof(induction " k+k1+k2"  arbitrary: k1 k2 k p rn rp ss ts1 st1 ent1 ts2 st2 ent2 rule: less_induct)
  case less
  then show ?case 
    apply(cases k)
    subgoal
      apply(cases k1)
      subgoal
        apply(cases k2)
        subgoal
          by auto
        subgoal for k2'
          apply auto
          apply(cases st2)
            apply simp
            subgoal premises pre
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_emp_wait')
              apply(rule entails_tassn_trans[where Q ="combine2 0 0 k2' (Sch p rn rp,ss) (Task st1 ent1 2,ts1) (Task READY ezero 1, ts2(T := 0))"])
              apply(rule entails_tassn_trans)
               prefer 2
               apply(rule pre(1))
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) unfolding propc'_def by auto
              subgoal using pre(4) unfolding proper'_def by auto
              subgoal using pre(5) unfolding inv_s_def by auto
              subgoal using pre(6) unfolding inv_s'_def by auto
              by auto
            apply simp
            subgoal premises pre
              apply(rule combine_or_right)
              subgoal
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                by(simp add:combine_assn_emp_out)
              by(simp add:combine_assn_emp_out)
            apply simp
            subgoal premises pre
              apply(rule combine_or_right)
              subgoal
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                apply(simp add: combine_assn_emp_waitin)
                done
              subgoal
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_emp_wait')
                apply(rule combine_or_right)
                subgoal
                  by(simp add: combine_assn_emp_outrdy)
                apply(rule combine_assn_ex_pre_right')
                by(simp add: combine_assn_emp_inrdy)
              done
            done
          done
        subgoal for k1'
          apply(cases k2)
          subgoal
            apply(cases st1)
              apply simp
            subgoal premises pre
              apply(rule entails_tassn_trans[where Q="combine2 0 k1' 0 (Sch p rn rp, ss) (Task READY ezero 2, ts1(T := 0)) (Task st2 ent2 1,ts2)"])
              apply(rule entails_tassn_trans)
               prefer 2
               apply(rule pre(1))
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) unfolding propc'_def by auto
              subgoal using pre(4) unfolding proper'_def by auto
              subgoal using pre(5) unfolding inv_s_def by auto
              subgoal using pre(6) unfolding inv_s'_def by auto
              by auto
             apply simp
            subgoal premises pre
              by(auto simp add: combine_assn_def entails_tassn_def false_assn_def)
            apply simp
            subgoal premises pre
              by(auto simp add: combine_assn_def entails_tassn_def false_assn_def)
            done
          subgoal for k2'
            apply simp
            apply(cases st1)
            subgoal
              apply(cases st2)
                apply simp
              subgoal premises pre
                apply(cases k1')
                subgoal apply auto
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_emp_wait')
                  apply(rule entails_tassn_trans[where Q="combine2 0 k1' k2' (Sch p rn rp, ss) (Task READY ezero 2, ts1(T := 0)) (Task READY ezero 1, ts2(T := 0))"])
                   apply(rule entails_tassn_trans)
                    prefer 2
                    apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto
                  subgoal using pre(4) unfolding proper'_def by auto
                  subgoal using pre(5) unfolding inv_s_def by auto
                using pre(6) unfolding inv_s'_def by auto
              subgoal for k1''
                by (auto simp add:combine_assn_def entails_tassn_def false_assn_def)
              done
             apply simp
            subgoal premises pre
              apply(cases "k1'")
              subgoal apply simp
                apply(rule combine_or_right)
                subgoal
                 apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                  by(simp add: combine_assn_emp_out)
                by(simp add: combine_assn_emp_out)
              subgoal for nt1''
                apply simp
                by (auto simp add:combine_assn_def entails_tassn_def false_assn_def)
              done
            apply simp
            subgoal premises pre
              apply(cases k1')
              subgoal apply simp
                apply(rule combine_or_right)
                subgoal
                apply(rule combine_assn_ex_pre_right')+
                  apply(rule combine_assn_pure_pre_right')
                  apply(simp add: combine_assn_emp_waitin)
                  done
                subgoal
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_emp_wait')
                  apply(rule combine_or_right)
                  subgoal
                    by(simp add: combine_assn_emp_outrdy)
                  apply(rule combine_assn_ex_pre_right')
                  by(simp add: combine_assn_emp_inrdy)
                done
              subgoal for nt1''
                apply simp
                by (auto simp add:combine_assn_def entails_tassn_def false_assn_def)
              done
            done
          apply simp
          subgoal
            by (auto simp add:combine_assn_def entails_tassn_def false_assn_def)
          apply simp
          subgoal
            by (auto simp add:combine_assn_def entails_tassn_def false_assn_def)
          done
        done
      done
    subgoal for k'
      apply(cases k1)
      subgoal
        apply(cases k2)
        subgoal
         apply(simp only:combine1.simps T2_tr.simps)
          subgoal premises pre
            apply(rule combine_or_left)
            subgoal
              by(simp add: combine_assn_in0_emp)
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')+
              apply(rule combine_assn_pure_pre_left')
              by(simp add: combine_assn_in0_emp)
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')+
              by(simp add: combine_assn_in0_emp)
            subgoal
              apply(rule combine_assn_ex_pre_left')+
              by(simp add: combine_assn_in0_emp)
            done
          done
        subgoal for k2'
          apply(simp only:combine1.simps)
          apply(cases st2)
            apply(simp only:T2_tr.simps)
          subgoal premises pre
            apply(rule combine_or_left)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_wait)
              subgoal by auto
              unfolding combine2.simps
              apply(rule entails_tassn_conj)
              subgoal
                apply auto
                using pre(6) unfolding inv_s'_def by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule entails_tassn_trans)
               prefer 2
              apply(rule pre(1))
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) unfolding propc'_def by auto
              subgoal using pre(4) unfolding proper'_def by auto
              subgoal using pre(5) unfolding inv_s_def by auto
              subgoal using pre(6) unfolding inv_s'_def by auto
              apply(rule combine_assn_left_tran)
              unfolding combine1.simps
              apply(rule entails_tassn_disjI1)
              by auto
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')+
              apply(rule combine_assn_pure_pre_left')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_wait)
              subgoal by auto
              unfolding combine2.simps
              apply(rule entails_tassn_conj)
              subgoal
                apply auto
                using pre(6) unfolding inv_s'_def by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule entails_tassn_trans)
               prefer 2
              apply(rule pre(1))
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) unfolding propc'_def by auto
              subgoal using pre(4) unfolding proper'_def by auto
              subgoal using pre(5) unfolding inv_s_def by auto
              subgoal using pre(6) unfolding inv_s'_def by auto
              apply(rule combine_assn_left_tran)
              unfolding combine1.simps
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI1)
              subgoal for v
              apply(rule entails_tassn_exI[where x= v])
              by auto
            done
          apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')+
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_wait)
              subgoal by auto
              unfolding combine2.simps
              apply(rule entails_tassn_conj)
              subgoal
                apply auto
                using pre(6) unfolding inv_s'_def by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule entails_tassn_trans)
               prefer 2
              apply(rule pre(1))
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) unfolding propc'_def by auto
              subgoal using pre(4) unfolding proper'_def by auto
              subgoal using pre(5) unfolding inv_s_def by auto
              subgoal using pre(6) unfolding inv_s'_def by auto
              apply(rule combine_assn_left_tran)
              unfolding combine1.simps
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI1)
              subgoal for v
              apply(rule entails_tassn_exI[where x= v])
              by auto
            done
          subgoal
              apply(rule combine_assn_ex_pre_left')+
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_wait)
              subgoal by auto
              unfolding combine2.simps
              apply(rule entails_tassn_conj)
              subgoal
                apply auto
                using pre(6) unfolding inv_s'_def by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule entails_tassn_trans)
               prefer 2
              apply(rule pre(1))
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) unfolding propc'_def by auto
              subgoal using pre(4) unfolding proper'_def by auto
              subgoal using pre(5) unfolding inv_s_def by auto
              subgoal using pre(6) unfolding inv_s'_def by auto
              apply(rule combine_assn_left_tran)
              unfolding combine1.simps
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              subgoal for v
              apply(rule entails_tassn_exI[where x= v])
              by auto
            done
          done
         apply(simp only:T2_tr.simps)
        subgoal premises pre
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_or_right)
            subgoal
              apply(rule combine_assn_ex_pre_right')+
              apply(rule combine_assn_pure_pre_right')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_out)
              subgoal by auto
              apply(cases "rp\<ge>1")
              subgoal for v tt 
                apply auto
                apply(cases k')
                subgoal apply simp
                  by(simp add: combine_assn_emp_waitin)
                subgoal for ns''
                  apply(simp only: combine1.simps)
                  apply(rule combine_or_left)
                  subgoal
                    apply simp
                    by(simp add: combine_assn_in0_waitin)
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    by(simp add: combine_assn_in0_waitin)
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    by(simp add: combine_assn_in0_waitin)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    by(simp add: combine_assn_in0_waitin)
                  done
                done
              subgoal for v tt 
                apply simp
                apply(rule combine_assn_pure_pre_left')
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_out0_waitin)
                subgoal by auto
                apply auto
                apply(subgoal_tac"rn =-1")
                 prefer 2
                subgoal
                  using pre(4) unfolding proper'_def properp_def by auto
                apply auto
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre(1))
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) unfolding propc'_def by auto 
                subgoal using pre(4) unfolding proper'_def properp_def by auto
                subgoal using pre(5) unfolding inv_s_def by auto
                subgoal using pre(6) unfolding inv_s'_def by auto
                by auto
              done
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_out)
              subgoal by auto
              apply(cases "1\<le>rp")
              subgoal 
                apply auto
                apply(cases k')
                subgoal
                  apply auto
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_emp_wait')
                  apply(rule combine_or_right)
                  subgoal
                    by(auto simp add:combine_assn_emp_outrdy)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')
                    by(auto simp add:combine_assn_emp_inrdy)
                  done
                subgoal for k''
                  apply simp
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    subgoal by auto
                    apply auto
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_outrdy)
                      subgoal by auto
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')
                      apply(rule combine_assn_in0_inrdy)
                      by auto
                    done
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    subgoal by auto
                    apply auto
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_outrdy)
                      subgoal by auto
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')
                      apply(rule combine_assn_in0_inrdy)
                      by auto
                    done
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    subgoal by auto
                    apply auto
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_outrdy)
                      subgoal by auto
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')
                      apply(rule combine_assn_in0_inrdy)
                      by auto
                    done
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    subgoal by auto
                    apply auto
                    apply(rule combine_or_right)
                    subgoal for v
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_outrdy)
                      subgoal by auto
                      apply auto
                      apply(rule entails_tassn_disjI2)
                      apply(subgoal_tac"9 \<ge> ts2 T * 200 \<and> p = []")
                       prefer 2
                      subgoal
                        using pre(6,4) unfolding inv_s'_def proper'_def
                        by auto
                      apply auto
                      apply(rule entails_tassn_trans)
                       prefer 2
                       apply(rule pre(1))
                      subgoal by auto
                      subgoal using pre(2) unfolding propc_def by auto
                      subgoal using pre(3) unfolding propc'_def by auto 
                      subgoal using pre(4) unfolding proper'_def properp_def by auto
                      subgoal using pre(5) unfolding inv_s_def by auto
                      subgoal using pre(6) unfolding inv_s'_def by auto
                      by auto
                    subgoal
                      apply(rule combine_assn_ex_pre_right')
                      apply(rule combine_assn_in0_inrdy)
                      by auto
                    done
                  done
                done
              apply auto
              subgoal
                apply(rule combine_assn_pure_pre_left')
                    apply(rule entails_tassn_trans)
                apply(rule combine_assn_out0_wait'')
                subgoal by auto
                apply auto
                apply(rule combine_or_right)
                subgoal
                  apply(rule combine_assn_out0_outrdy)
                  by auto
                subgoal
                  apply(rule combine_assn_ex_pre_right')
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_out0_inrdy)
                  subgoal by auto
                  apply auto
                  apply(rule entails_tassn_disjI1)
                  apply(subgoal_tac"rn =-1 \<and> 9 \<ge> ts2 T * 200")
                   prefer 2
                  subgoal
                    using pre(4,6) unfolding proper'_def properp_def inv_s'_def by auto
                  apply auto
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5) unfolding inv_s_def by auto
                  subgoal using pre(6) unfolding inv_s'_def by auto
                  apply(subgoal_tac"ts2(F := 0) = ts2(T := 9 / 200, F := 0)")
                  by(auto simp add:T_def F_def)
                done
              done
            done
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            apply(rule combine_or_right)
            subgoal for v
              apply(rule combine_assn_ex_pre_right')+
              apply(rule combine_assn_pure_pre_right')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_out)
              by auto
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_out)
              by auto
            done
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_or_right)
            subgoal for v
              apply(rule combine_assn_ex_pre_right')+
              apply(rule combine_assn_pure_pre_right')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_out)
              by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_out)
              by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)                    
            done
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_or_right)
            subgoal for v
              apply(rule combine_assn_ex_pre_right')+
              apply(rule combine_assn_pure_pre_right')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_out)
              by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_out)
              by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)                    
            done
          done
        apply(simp only:T2_tr.simps)
        subgoal premises pre
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_or_right)
            subgoal
              apply(rule combine_assn_ex_pre_right')+
              apply(rule combine_assn_pure_pre_right')
              apply(rule combine_assn_in0_waitin)
              by auto
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_wait)
              subgoal by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule combine_or_right)
              subgoal
               apply(rule entails_tassn_trans)
                 apply(rule combine_assn_in0_outrdy)
                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              subgoal
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_in0_inrdy)
                by auto
              done
            done
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            apply(rule combine_or_right)
            subgoal
              apply(rule combine_assn_ex_pre_right')+
              apply(rule combine_assn_pure_pre_right')
              apply(rule combine_assn_in0_waitin)
              by auto
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_wait)
              subgoal by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule combine_or_right)
              subgoal
               apply(rule entails_tassn_trans)
                 apply(rule combine_assn_in0_outrdy)
                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              subgoal
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_in0_inrdy)
                by auto
              done
            done
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_or_right)
            subgoal
              apply(rule combine_assn_ex_pre_right')+
              apply(rule combine_assn_pure_pre_right')
              apply(rule combine_assn_in0_waitin)
              by auto
            subgoal for v
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_wait)
              subgoal by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule combine_or_right)
              subgoal
               apply(rule entails_tassn_trans)
                 apply(rule combine_assn_in0_outrdy)
                subgoal by auto
                apply(subgoal_tac"p=[]")
                 prefer 2
                subgoal using pre(4) unfolding proper'_def by auto
                apply auto
                apply(subgoal_tac"min (9 / 200 - ts2 T) (1 / 50 - C_upd ent2 (ts2 C)) = 0")
                 prefer 2
                subgoal using pre(6) unfolding inv_s'_def C_upd_def
                  apply(cases ent2) by auto
                apply auto
                apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5) unfolding inv_s_def by auto
                  subgoal using pre(6) unfolding inv_s'_def by auto
                  by auto
              subgoal
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_in0_inrdy)
                by auto
              done
            done
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_or_right)
            subgoal
              apply(rule combine_assn_ex_pre_right')+
              apply(rule combine_assn_pure_pre_right')
              apply(rule combine_assn_in0_waitin)
              by auto
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_in0_wait)
              subgoal by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule combine_or_right)
              subgoal
               apply(rule entails_tassn_trans)
                 apply(rule combine_assn_in0_outrdy)
                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              subgoal
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_in0_inrdy)
                by auto
              done
            done
          done
        done
      done
    subgoal for k1'
      apply(cases k2)
      subgoal
        apply(simp only:T2_tr.simps)
        apply(cases st1)
          apply(simp only:combine1.simps)
        subgoal premises pre
          apply(rule combine_or_left)
          subgoal
            apply(rule entails_tassn_trans)
             apply(rule combine_assn_wait_emp'')
            apply auto
            apply(subgoal_tac"9 \<ge> ts1 T * 200")
             prefer 2
            subgoal using pre(5) unfolding inv_s_def by auto
            apply auto
            apply(rule entails_tassn_trans)
             prefer 2
             apply(rule pre(1))
            subgoal by auto
            subgoal using pre(2) unfolding propc_def by auto
            subgoal using pre(3) unfolding propc'_def by auto 
            subgoal using pre(4) unfolding proper'_def properp_def by auto
            subgoal using pre(5) unfolding inv_s_def by auto
            subgoal using pre(6) unfolding inv_s'_def by auto
            by auto
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            apply(auto simp add: combine_assn_waitin_emp)
            done
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            apply(auto simp add: combine_assn_waitin_emp)
            done
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            apply(auto simp add: combine_assn_waitin_emp)
            done
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            apply(auto simp add: combine_assn_waitin_emp)
            done
          done
         apply(simp only:combine1.simps)
        subgoal premises pre
          apply(rule combine_or_left)
          subgoal
            apply(cases "rn = 2")
            subgoal
              apply auto
              apply(rule combine_or_left)
              subgoal
                by(auto simp add: combine_assn_out0_emp)
              apply(rule combine_or_left)
              subgoal
                by(auto simp add: combine_assn_waitp_emp)
              subgoal
                by(auto simp add: combine_assn_waitp_emp)
              done
            apply auto
            apply(subgoal_tac "rn=-1")
             prefer 2
            subgoal using pre(2,4) unfolding proper'_def propc_def properp_def by auto
            apply auto
            apply(rule entails_tassn_trans)
             prefer 2
             apply(rule pre(1))
            subgoal by auto
            subgoal using pre(2) unfolding propc_def by auto
            subgoal using pre(3) unfolding propc'_def by auto 
            subgoal using pre(4) unfolding proper'_def properp_def by auto
            subgoal using pre(5) unfolding inv_s_def by auto
            subgoal using pre(6) unfolding inv_s'_def by auto
            by auto
          apply(rule combine_or_left)
          subgoal
            by(auto simp add: combine_assn_in0_emp)
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            by(auto simp add: combine_assn_in0_emp)
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            by(auto simp add: combine_assn_in0_emp)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            by(auto simp add: combine_assn_in0_emp)
          done
        apply(simp only:combine1.simps)
        subgoal premises pre
          apply(rule combine_or_left)
          subgoal
            apply(subgoal_tac"p = [] \<and> min (45 / 10 ^ 3 - ts1 T) (1 / 10\<^sup>2 - C_upd ent1 (ts1 C)) \<ge>0")
             prefer 2
            subgoal using pre(4,5) unfolding proper'_def inv_s_def C_upd_def 
              apply(cases ent1) by auto
            apply auto
            apply(rule entails_tassn_trans)
             apply(rule combine_assn_wait_emp'')
            apply auto
            apply(subgoal_tac "min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)) = 0")
            prefer 2
            subgoal using pre(4,5) unfolding proper'_def inv_s_def C_upd_def 
              apply(cases ent1) by auto
            apply auto
            apply(rule entails_tassn_trans)
             prefer 2
             apply(rule pre(1))
            subgoal by auto
            subgoal using pre(2) unfolding propc_def by auto
            subgoal using pre(3) unfolding propc'_def by auto 
            subgoal using pre(4) unfolding proper'_def properp_def by auto
            subgoal using pre(5) unfolding inv_s_def by auto
            subgoal using pre(6) unfolding inv_s'_def by auto
            by auto
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            by(auto simp add: combine_assn_waitin_emp)
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            by(auto simp add: combine_assn_waitin_emp)
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            by(auto simp add: combine_assn_waitin_emp)
          subgoal
            apply(rule combine_assn_ex_pre_left')+
            apply(rule combine_assn_pure_pre_left')
            by(auto simp add: combine_assn_waitin_emp)
          done
        done



      subgoal for k2'
        apply(cases st1)
        subgoal
          apply(cases st2)
            apply(simp only:combine1.simps T2_tr.simps)
          subgoal premises pre
            apply(rule combine_or_left)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_wait_wait5)
              subgoal using pre(5,6) unfolding inv_s_def inv_s'_def
                by auto
              apply auto
              apply(rule entails_tassn_disjE)
              subgoal
                apply auto
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_cancel_left)
                apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre(1))
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) unfolding propc'_def by auto 
                subgoal using pre(4) unfolding proper'_def properp_def by auto
                subgoal using pre(5) unfolding inv_s_def by auto
                subgoal using pre(6) unfolding inv_s'_def by auto
                by auto
              apply(rule entails_tassn_disjE)
              subgoal
                apply auto
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_cancel_left)
                apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre(1))
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) unfolding propc'_def by auto 
                subgoal using pre(4) unfolding proper'_def properp_def by auto
                subgoal using pre(5) unfolding inv_s_def by auto
                subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                apply(rule combine_assn_right_tran)
                unfolding T2_tr.simps
                apply auto
                apply(subgoal_tac"(\<lambda>t. EState (Task WAIT ent2 1, ts2(T := ts2 T + (9 / 200 - ts1 T) + t))) = (\<lambda>t. EState (Task WAIT ent2 1, ts2(T := ts2 T + (t + (9 / 200 - ts1 T)))))")
                 apply auto
                apply(rule ext)
                by auto
              subgoal
                apply auto
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_cancel_left)
                apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre(1))
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) unfolding propc'_def by auto 
                subgoal using pre(4) unfolding proper'_def properp_def by auto
                subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                apply(rule combine_assn_left_tran)
                unfolding T2_tr.simps
                apply auto
                apply(rule entails_tassn_disjI1)
                apply(subgoal_tac"(\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState (Task WAIT ent1 2, ts1(T := ts1 T + (9 / 200 - ts2 T) + t)))) =
                                   (\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState (Task WAIT ent1 2, ts1(T := ts1 T + (t + (9 / 200 - ts2 T))))))")
                 apply auto
                apply(rule ext)
                by auto
              done
            apply(rule combine_or_left)
            subgoal
              apply(subgoal_tac"0 \<le> 9 / 200 - ts1 T \<and> 0 \<le> 9 / 200 - ts2 T")
               prefer 2
              subgoal using pre(5,6) unfolding inv_s_def inv_s'_def by auto
              apply(rule combine_assn_ex_pre_left')+
              apply(rule combine_assn_pure_pre_left')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_waitin_wait)
              subgoal by auto
              unfolding combine2.simps
              apply(rule entails_tassn_disjI2)+
              apply(rule entails_tassn_conj)
              subgoal by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule entails_tassn_cancel_both)
              subgoal for tt by auto
              apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre(1))
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) unfolding propc'_def by auto 
                subgoal using pre(4) unfolding proper'_def properp_def by auto
                subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                apply(rule combine_assn_left_tran)
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                subgoal for tt
                  apply(rule entails_tassn_exI[where x="(tt - (9 / 200 - ts2 T))"])
                  apply(rule entails_tassn_conj)
                  subgoal by auto
                  apply(rule entails_tassn_cancel_both)
                  subgoal 
                    apply(subgoal_tac "(\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState
             (Task WAIT ent1 2, ts1
              (T := ts1 T + (45 / 10 ^ 3 - ts2 T),
               T := (ts1(T := ts1 T + (45 / 10 ^ 3 - ts2 T))) T + t)))) = 
            (\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState (Task WAIT ent1 2, ts1(T := ts1 T + (t + (9 / 200 - ts2 T))))))")
                     apply auto
                    apply(rule ext)
                    apply auto
                    done
                  by auto
                done
              apply(rule combine_or_left)
              subgoal
              apply(subgoal_tac"0 \<le> 9 / 200 - ts1 T \<and> 0 \<le> 9 / 200 - ts2 T")
               prefer 2
              subgoal using pre(5,6) unfolding inv_s_def inv_s'_def by auto
              apply(rule combine_assn_ex_pre_left')+
              apply(rule combine_assn_pure_pre_left')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_waitin_wait)
              subgoal by auto
              unfolding combine2.simps
              apply(rule entails_tassn_disjI2)+
              apply(rule entails_tassn_conj)
              subgoal by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule entails_tassn_cancel_both)
              subgoal for tt by auto
              apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre(1))
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) unfolding propc'_def by auto 
                subgoal using pre(4) unfolding proper'_def properp_def by auto
                subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                apply(rule combine_assn_left_tran)
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                subgoal for tt v
                  apply(rule entails_tassn_exI[where x="(tt - (9 / 200 - ts2 T))"])
                  apply(rule entails_tassn_exI[where x=v])
                  apply(rule entails_tassn_conj)
                  subgoal by auto
                  apply(rule entails_tassn_cancel_both)
                  subgoal 
                    apply(subgoal_tac "(\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState
             (Task WAIT ent1 2, ts1
              (T := ts1 T + (45 / 10 ^ 3 - ts2 T),
               T := (ts1(T := ts1 T + (45 / 10 ^ 3 - ts2 T))) T + t)))) = 
            (\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState (Task WAIT ent1 2, ts1(T := ts1 T + (t + (9 / 200 - ts2 T))))))")
                     apply auto
                    apply(rule ext)
                    apply auto
                    done
                  by auto
                done
              apply(rule combine_or_left)
              subgoal
              apply(subgoal_tac"0 \<le> 9 / 200 - ts1 T \<and> 0 \<le> 9 / 200 - ts2 T")
               prefer 2
              subgoal using pre(5,6) unfolding inv_s_def inv_s'_def by auto
              apply(rule combine_assn_ex_pre_left')+
              apply(rule combine_assn_pure_pre_left')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_waitin_wait)
              subgoal by auto
              unfolding combine2.simps
              apply(rule entails_tassn_disjI2)+
              apply(rule entails_tassn_conj)
              subgoal by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule entails_tassn_cancel_both)
              subgoal for tt by auto
              apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre(1))
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) unfolding propc'_def by auto 
                subgoal using pre(4) unfolding proper'_def properp_def by auto
                subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                apply(rule combine_assn_left_tran)
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                subgoal for tt v
                  apply(rule entails_tassn_exI[where x="(tt - (9 / 200 - ts2 T))"])
                  apply(rule entails_tassn_exI[where x=v])
                  apply(rule entails_tassn_conj)
                  subgoal by auto
                  apply(rule entails_tassn_cancel_both)
                  subgoal 
                    apply(subgoal_tac "(\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState
             (Task WAIT ent1 2, ts1
              (T := ts1 T + (45 / 10 ^ 3 - ts2 T),
               T := (ts1(T := ts1 T + (45 / 10 ^ 3 - ts2 T))) T + t)))) = 
            (\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState (Task WAIT ent1 2, ts1(T := ts1 T + (t + (9 / 200 - ts2 T))))))")
                     apply auto
                    apply(rule ext)
                    apply auto
                    done
                  by auto
                done
              subgoal
              apply(subgoal_tac"0 \<le> 9 / 200 - ts1 T \<and> 0 \<le> 9 / 200 - ts2 T")
               prefer 2
              subgoal using pre(5,6) unfolding inv_s_def inv_s'_def by auto
              apply(rule combine_assn_ex_pre_left')+
              apply(rule combine_assn_pure_pre_left')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_waitin_wait)
              subgoal by auto
              unfolding combine2.simps
              apply(rule entails_tassn_disjI2)+
              apply(rule entails_tassn_conj)
              subgoal by auto
              apply(simp only:pure_assn_entails)
              apply(rule impI)
              apply(rule entails_tassn_cancel_both)
              subgoal for tt by auto
              apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre(1))
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) unfolding propc'_def by auto 
                subgoal using pre(4) unfolding proper'_def properp_def by auto
                subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                apply(rule combine_assn_left_tran)
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                subgoal for tt v
                  apply(rule entails_tassn_exI[where x="(tt - (9 / 200 - ts2 T))"])
                  apply(rule entails_tassn_exI[where x=v])
                  apply(rule entails_tassn_conj)
                  subgoal by auto
                  apply(rule entails_tassn_cancel_both)
                  subgoal 
                    apply(subgoal_tac "(\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState
             (Task WAIT ent1 2, ts1
              (T := ts1 T + (45 / 10 ^ 3 - ts2 T),
               T := (ts1(T := ts1 T + (45 / 10 ^ 3 - ts2 T))) T + t)))) = 
            (\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState (Task WAIT ent1 2, ts1(T := ts1 T + (t + (9 / 200 - ts2 T))))))")
                     apply auto
                    apply(rule ext)
                    apply auto
                    done
                  by auto
                done
              done





             apply(simp only:combine1.simps T2_tr.simps)
            subgoal premises pre
              apply(cases "(9 / 200 - ts1 T) = 0")
              subgoal
                apply simp
                apply(rule entails_tassn_disjI1)
                apply(rule combine_or_left)
                subgoal
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_right_tran)
                  by auto
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')
                  by auto
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')
                  by auto
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')
                  by auto
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')
                  by auto
                done
              apply(subgoal_tac"9 / 200 - ts1 T >0")
               prefer 2
                subgoal using pre(5) unfolding inv_s_def by auto
                apply auto
                apply(rule entails_tassn_disjI2)
              apply(rule combine_or_left)
              subgoal
                apply(rule combine_or_right)
                subgoal
                  apply(rule combine_assn_ex_pre_right')+
                  apply(rule combine_assn_pure_pre_right')
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_wait_out)
                  by auto
                subgoal
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_wait_out)
                  by auto
                done
              apply(rule combine_or_left)
              subgoal
                apply(subgoal_tac"rp = -1")
                 prefer 2
                subgoal
                  using pre(2,3,4) unfolding propc_def propc'_def proper'_def properp_def by auto
                apply(rule combine_assn_ex_pre_left')+
                apply(rule combine_assn_pure_pre_left')
                apply(rule combine_or_right)
                subgoal for tt
                  apply(rule combine_assn_ex_pre_right')+
                  apply(rule combine_assn_pure_pre_right')
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_out)
                  subgoal by auto
                  apply auto
                  apply(rule combine_or_left)
                  subgoal for v tta
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_out0_waitin1)
                    subgoal by auto
                    apply auto
                    apply(rule entails_tassn_trans)
                     prefer 2
                     apply(rule pre(1))
                    subgoal by auto
                    subgoal using pre(2) unfolding propc_def by auto
                    subgoal using pre(3) unfolding propc'_def by auto 
                    subgoal using pre(4) unfolding proper'_def properp_def by auto
                    subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                    subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                    by auto
                  subgoal for v tta
                    apply(rule combine_assn_waitp_waitin')
                    by auto
                  done
                subgoal for tt
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_out)
                  subgoal by auto
                  apply auto
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_out0_wait'')
                    subgoal by auto
                    apply auto
                    apply(subgoal_tac"9 = ts2 T * 200")
                     prefer 2
                    subgoal using pre(6) unfolding inv_s'_def by auto
                    apply auto
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_out0_outrdy)
                      by auto
                    subgoal
                      apply(rule combine_assn_ex_pre_right')
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_out0_inrdy)
                       apply auto
                      apply(rule entails_tassn_trans)
                       prefer 2
                       apply(rule pre(1))
                      subgoal by auto
                      subgoal using pre(2) unfolding propc_def by auto
                      subgoal using pre(3) unfolding propc'_def by auto 
                      subgoal using pre(4) unfolding proper'_def properp_def by auto
                      subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                      subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                      apply(subgoal_tac"ts2(F := 0) = ts2(T := 9 / 200, F := 0)")
                      by auto
                    done
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_waitp_wait'')
                     apply auto
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_waitp_outrdy')
                      by auto
                    subgoal
                      apply(rule combine_assn_ex_pre_right')
                      apply(rule combine_assn_waitp_inrdy')
                      by auto
                    done
                  done
                done
              apply(rule combine_or_left)
              subgoal
                apply(rule combine_assn_ex_pre_left')+
                apply(rule combine_assn_pure_pre_left')
                apply(rule combine_or_right)
                subgoal for tt v
                  apply(rule combine_assn_ex_pre_right')+
                  apply(rule combine_assn_pure_pre_right')
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_out)
                  by auto
                subgoal
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_out)
                  by auto
                done
              apply(rule combine_or_left)
              subgoal
                apply(rule combine_assn_ex_pre_left')+
                apply(rule combine_assn_pure_pre_left')
                apply(rule combine_or_right)
                subgoal for tt v
                  apply(rule combine_assn_ex_pre_right')+
                  apply(rule combine_assn_pure_pre_right')
                  apply(rule combine_assn_waitin_out'')
                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                subgoal
                  apply(rule combine_assn_waitin_out'')
                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                done
             subgoal
                apply(rule combine_assn_ex_pre_left')+
                apply(rule combine_assn_pure_pre_left')
                apply(rule combine_or_right)
                subgoal for tt v
                  apply(rule combine_assn_ex_pre_right')+
                  apply(rule combine_assn_pure_pre_right')
                  apply(rule combine_assn_waitin_out'')
                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                subgoal
                  apply(rule combine_assn_waitin_out'')
                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                done
              done



              apply(simp only:combine1.simps T2_tr.simps)
            subgoal premises pre
              apply(subgoal_tac"(9 / 200 - ts1 T)\<ge>0 \<and> min (45 / 10 ^ 3 - ts2 T) (2 / 10\<^sup>2 - C_upd ent2 (ts2 C)) \<ge>0")
               prefer 2
              subgoal using pre(5,6) unfolding inv_s_def inv_s'_def C_upd_def C_def T_def
                apply(cases ent2) by auto
              apply(cases "min (45 / 10 ^ 3 - ts2 T) (2 / 10\<^sup>2 - C_upd ent2 (ts2 C)) \<ge> (9 / 200 - ts1 T)")
              subgoal
                unfolding combine2.simps
                apply(rule entails_tassn_disjI1)
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_wait_waitin)
                    subgoal by auto
                    apply auto
                    apply(rule entails_tassn_cancel_left)
                    apply(rule entails_tassn_trans)
                       prefer 2
                       apply(rule pre(1))
                      subgoal by auto
                      subgoal using pre(2) unfolding propc_def by auto
                      subgoal using pre(3) unfolding propc'_def by auto 
                      subgoal using pre(4) unfolding proper'_def properp_def by auto
                      subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                      subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                      apply(rule combine_assn_right_tran)
                      unfolding T2_tr.simps
                      apply(rule entails_tassn_disjI1)
                      subgoal for v tt
                        apply(rule entails_tassn_exI[where x=v])
                        apply(rule entails_tassn_exI[where x="tt - (9 / 200 - ts1 T)"])
                        apply (auto simp add:T_def C_def)
                        apply(rule entails_tassn_cancel_right)
                        apply(subgoal_tac"(\<lambda>t. EState
           (Task RUNNING eone 1, ts2
            (CHR ''t'' := ts2 CHR ''t'' + (9 / 200 - ts1 CHR ''t'') + t,
             CHR ''c'' := C_upd ent2 (ts2 CHR ''c'') + (9 / 200 - ts1 CHR ''t'') + t))) =
                                          (\<lambda>t. EState
           (Task RUNNING eone 1, ts2
            (CHR ''t'' := ts2 CHR ''t'' + (t + (9 / 200 - ts1 CHR ''t'')),
             CHR ''c'' := C_upd ent2 (ts2 CHR ''c'') + (t + (9 / 200 - ts1 CHR ''t'')))))")
                         apply auto
                        apply(rule ext)
                        by auto
                      done
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_wait_wait3')
                       apply auto
                      apply(rule entails_tassn_cancel_left)
                      apply(rule entails_tassn_trans)
                       prefer 2
                       apply(rule pre(1))
                      subgoal by auto
                      subgoal using pre(2) unfolding propc_def by auto
                      subgoal using pre(3) unfolding propc'_def by auto 
                      subgoal using pre(4) unfolding proper'_def properp_def by auto
                      subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                      subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                      apply(rule combine_assn_right_tran)
                      unfolding T2_tr.simps
                      apply(rule entails_tassn_disjI2)
                      apply(auto simp add:C_def T_def)
                      apply(rule entails_tassn_cancel_both)
                      subgoal premises pre'
                      proof-
                        have 1:"(min (ts1 CHR ''t'' - ts2 CHR ''t'')
                                    (ts1 CHR ''t'' - C_upd ent2 (ts2 CHR ''c'') - 1 / 40)) =
                (min (9 / 200 - ts2 CHR ''t'') (1 / 50 - C_upd ent2 (ts2 CHR ''c'')) -
                          (9 / 200 - ts1 CHR ''t''))"
                          by auto
                        have 2:"(\<lambda>\<tau>. EState
           (Task RUNNING eone 1, ts2
            (CHR ''t'' := ts2 CHR ''t'' + (9 / 200 - ts1 CHR ''t'') + \<tau>,
             CHR ''c'' := C_upd ent2 (ts2 CHR ''c'') + (9 / 200 - ts1 CHR ''t'') + \<tau>))) =
                                  (\<lambda>t. EState
           (Task RUNNING eone 1, ts2
            (CHR ''t'' := ts2 CHR ''t'' + (t + (9 / 200 - ts1 CHR ''t'')),
             CHR ''c'' := C_upd ent2 (ts2 CHR ''c'') + (t + (9 / 200 - ts1 CHR ''t'')))))"
                          apply(rule ext)
                          by auto
                        show ?thesis
                          by(simp add:1 2)
                      qed
                      apply(subgoal_tac "ts2
      (CHR ''t'' :=
         ts2 CHR ''t'' + (9 / 200 - ts1 CHR ''t'') +
         min (ts1 CHR ''t'' - ts2 CHR ''t'')
          (ts1 CHR ''t'' - C_upd ent2 (ts2 CHR ''c'') - 1 / 40),
       CHR ''c'' :=
         C_upd ent2 (ts2 CHR ''c'') + (9 / 200 - ts1 CHR ''t'') +
         min (ts1 CHR ''t'' - ts2 CHR ''t'')
          (ts1 CHR ''t'' - C_upd ent2 (ts2 CHR ''c'') - 1 / 40)) = 
ts2
       (CHR ''t'' :=
          ts2 CHR ''t'' +
          min (9 / 200 - ts2 CHR ''t'') (1 / 50 - C_upd ent2 (ts2 CHR ''c'')),
        CHR ''c'' :=
          C_upd ent2 (ts2 CHR ''c'') +
          min (9 / 200 - ts2 CHR ''t'') (1 / 50 - C_upd ent2 (ts2 CHR ''c'')))")
                       apply auto
                      apply(rule ext)
                      by auto
                    done
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_or_right)
                    subgoal for tt
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_waitin_waitin)
                      by auto
                    subgoal for tt
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitin_wait)
                      by auto
                    done
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_or_right)
                    subgoal for tt
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_waitin_waitin)
                      by auto
                    subgoal for tt
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitin_wait)
                      by auto
                    done
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_or_right)
                    subgoal for tt
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_waitin_waitin)
                      by auto
                    subgoal for tt
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitin_wait)
                      by auto
                    done
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_or_right)
                    subgoal for tt
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_waitin_waitin)
                      by auto
                    subgoal for tt
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitin_wait)
                      by auto
                    done
                  done
                subgoal
                  apply(subgoal_tac"min (45 / 10 ^ 3 - ts2 T) (2 / 10\<^sup>2 - C_upd ent2 (ts2 C)) < 9 / 200 - ts1 T")
                   prefer 2
                  subgoal by auto
                  unfolding combine2.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_wait_waitin)
                      by auto
                    subgoal 
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_wait_wait4)
                      subgoal by auto
                      apply(rule entails_tassn_conj)
                      subgoal by auto
                      apply(rule entails_tassn_cancel_both)
                      subgoal by auto
                      apply(rule combine_or_right)
                      subgoal
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_wait_outrdy)
                        by auto
                      subgoal
                        apply(rule combine_assn_ex_pre_right')+
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_wait_inrdy)
                        by auto
                      done
                    done
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_waitin_waitin)
                      by auto
                    subgoal for tt
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitin_wait)
                      subgoal by auto
                      apply(rule entails_tassn_conj)
                      subgoal by auto
                      apply(simp only:pure_assn_entails)
                      apply(rule impI)
                      apply(rule entails_tassn_cancel_both)
                      subgoal by auto
                      apply(rule combine_or_right)
                      subgoal
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitin_outrdy)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      subgoal
                        apply(rule combine_assn_ex_pre_right')+
                        apply(rule combine_assn_waitin_inrdy)
                        by auto
                      done
                    done   
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_waitin_waitin)
                      by auto
                    subgoal for tt
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitin_wait)
                      subgoal by auto
                      apply(rule entails_tassn_conj)
                      subgoal by auto
                      apply(simp only:pure_assn_entails)
                      apply(rule impI)
                      apply(rule entails_tassn_cancel_both)
                      subgoal by auto
                      apply(rule combine_or_right)
                      subgoal
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitin_outrdy)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      subgoal
                        apply(rule combine_assn_ex_pre_right')+
                        apply(rule combine_assn_waitin_inrdy)
                        by auto
                      done
                    done
                  apply(rule combine_or_left)
                  subgoal 
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_waitin_waitin)
                      by auto
                    subgoal for tt v
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitin_wait)
                      subgoal by auto
                      apply(rule entails_tassn_conj)
                      subgoal by auto
                      apply(simp only:pure_assn_entails)
                      apply(rule impI)
                      apply(rule entails_tassn_cancel_both)
                      subgoal by auto
                      apply(rule combine_or_right)
                      subgoal
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitin_outrdy)
                        subgoal by auto
                        apply(subgoal_tac"p=[]")
                         prefer 2
                        subgoal using pre(4) unfolding proper'_def by auto
                        apply simp
                        apply(rule impI)
                        apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                        subgoal by auto
                        subgoal using pre(2) unfolding propc_def by auto
                        subgoal using pre(3) unfolding propc'_def by auto 
                        subgoal using pre(4) unfolding proper'_def properp_def by auto
                        subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                        subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                        apply(subgoal_tac"min (9 / 200 - ts2 T) (1 / 50 - C_upd ent2 (ts2 C)) = tt")
                        by auto
                      subgoal
                        apply(rule combine_assn_ex_pre_right')+
                        apply(rule combine_assn_waitin_inrdy)
                        by auto
                      done
                    done
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_waitin_waitin)
                      by auto
                    subgoal for tt
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitin_wait)
                      subgoal by auto
                      apply(rule entails_tassn_conj)
                      subgoal by auto
                      apply(simp only:pure_assn_entails)
                      apply(rule impI)
                      apply(rule entails_tassn_cancel_both)
                      subgoal by auto
                      apply(rule combine_or_right)
                      subgoal
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitin_outrdy)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      subgoal
                        apply(rule combine_assn_ex_pre_right')+
                        apply(rule combine_assn_waitin_inrdy)
                        by auto
                      done
                    done
                  done
                done
              done



            subgoal
          apply(cases st2)           
            apply(simp only:combine1.simps T2_tr.simps)
              subgoal premises pre
                apply(cases "(9 / 200 - ts2 T) = 0")
                subgoal
                  unfolding combine2.simps
                  apply(rule entails_tassn_disjI1)
                  apply(rule entails_tassn_conj)
                  subgoal by auto
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_both_tran)
                   apply auto
                  done
                subgoal
                  unfolding combine2.simps
                  apply(rule entails_tassn_disjI2)
                  apply(subgoal_tac "0 < 9 / 200 - ts2 T \<and> rn = -1 \<and> rp = -1 \<and> p =[]")
                   prefer 2
                  subgoal using pre(2,3,4,6) unfolding propc_def propc'_def proper'_def properp_def inv_s'_def 
                    by auto
                  apply auto
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule entails_tassn_trans)
                     prefer 2
                     apply(rule pre(1))
                    subgoal by auto
                    subgoal using pre(2) unfolding propc_def by auto
                    subgoal using pre(3) unfolding propc'_def by auto 
                    subgoal using pre(4) unfolding proper'_def properp_def by auto
                    subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                    subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                    by auto
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    by auto
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    by auto
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    by auto
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    by auto
                  done
                done





               apply(simp only:combine1.simps T2_tr.simps)
              subgoal premises pre
                apply(subgoal_tac "rn = -1 \<and> rp = -1 \<and> p =[]")
                   prefer 2
                  subgoal using pre(2,3,4,6) unfolding propc_def propc'_def proper'_def properp_def inv_s'_def 
                    by auto
                  apply auto
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule entails_tassn_disjI1)
                    apply(rule entails_tassn_trans)
                     prefer 2
                     apply(rule pre(1))
                    subgoal by auto
                    subgoal using pre(2) unfolding propc_def by auto
                    subgoal using pre(3) unfolding propc'_def by auto 
                    subgoal using pre(4) unfolding proper'_def properp_def by auto
                    subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                    subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                    by auto
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule entails_tassn_disjI2)
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_out)
                      subgoal by auto
                      apply auto
                      apply(rule combine_or_left)
                      subgoal for v tt
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_out0_waitin)
                        subgoal by auto
                        apply auto
                        apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                        subgoal by auto
                        subgoal using pre(2) unfolding propc_def by auto
                        subgoal using pre(3) unfolding propc'_def by auto 
                        subgoal using pre(4) unfolding proper'_def properp_def by auto
                        subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                        subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                        by auto
                      subgoal for v tt
                        apply(rule combine_assn_waitp_waitin')
                        by auto
                      done
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_out)
                      subgoal by auto
                      apply auto
                      apply(rule combine_or_left)
                       apply(rule entails_tassn_trans)
                        apply(rule combine_assn_out0_wait'')
                        apply auto
                       apply(rule combine_or_right)
                      subgoal
                        apply(rule combine_assn_out0_outrdy)
                        by auto
                      subgoal
                        apply(rule combine_assn_ex_pre_right')+
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_out0_inrdy)
                         apply auto
                        apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                        subgoal by auto
                        subgoal using pre(2) unfolding propc_def by auto
                        subgoal using pre(3) unfolding propc'_def by auto 
                        subgoal using pre(4) unfolding proper'_def properp_def by auto
                        subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                        subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                        apply(subgoal_tac"ts2(F := 0) = ts2(T := 9 / 200, F := 0)")
                         apply auto
                        using pre(6) unfolding inv_s'_def T_def F_def
                        by auto
                      subgoal
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitp_wait'')
                         apply auto
                        apply(rule combine_or_right)
                        subgoal
                          apply(rule combine_assn_waitp_outrdy')
                          by auto
                        subgoal
                          apply(rule combine_assn_ex_pre_right')+
                          apply(rule combine_assn_waitp_inrdy')
                          by auto
                        done
                      done
                    done
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_or_right)
                    subgoal for v
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_out)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_out)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    done
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_or_right)
                    subgoal for v
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_out)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_out)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    done
                  subgoal
                    apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_or_right)
                    subgoal for v
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_out)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_out)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    done
                  done




                apply(simp only:combine1.simps T2_tr.simps)
                subgoal premises pre
                  apply(rule combine_or_left)
                  subgoal
                   apply(subgoal_tac "rn = 2")
                    prefer 2 
                  subgoal using pre(3) unfolding propc'_def by auto
                  apply(rule combine_or_right)
                  subgoal
                    apply simp
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply(rule combine_or_left)
                    subgoal for v tt
                      apply(rule entails_tassn_disjI1)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_out0_waitin)
                      apply auto
                      apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                      subgoal by auto
                      subgoal using pre(2) unfolding propc_def by auto
                      subgoal using pre(3) unfolding propc'_def by auto 
                      subgoal using pre(4) unfolding proper'_def properp_def by auto
                      subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                      subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                      by auto
                    apply(rule combine_or_left)
                    subgoal for v tt
                      apply(rule combine_assn_waitp_waitin')
                      by auto
                    subgoal for v tt
                      apply(rule combine_assn_waitp_waitin')
                      by auto
                    done
                  apply simp
                  subgoal
                    apply(rule combine_or_left)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_out0_wait'')
                       apply auto
                      apply(rule combine_or_right)
                      subgoal
                        apply(rule combine_assn_out0_outrdy)
                        by auto
                      subgoal
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_disjI1)
                        apply(rule combine_assn_ex_pre_right')+
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_out0_inrdy)
                         apply auto
                        apply(subgoal_tac"min (9 / 200 - ts2 T) (1 / 50 - C_upd ent2 (ts2 C)) = 0")
                         prefer 2
                        subgoal using pre(6) unfolding inv_s'_def  C_upd_def C_def T_def
                          apply(cases ent2) by auto
                        apply auto
                        apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                        subgoal by auto
                        subgoal using pre(2) unfolding propc_def by auto
                        subgoal using pre(3) unfolding propc'_def by auto 
                        subgoal using pre(4) unfolding proper'_def properp_def by auto
                        subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                        subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                        by auto
                      done
                    apply(rule combine_or_left)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitp_wait'')
                       apply auto
                      apply(rule combine_or_right)
                      subgoal
                        apply(rule combine_assn_waitp_outrdy')
                        by auto
                      subgoal
                        apply(rule combine_assn_ex_pre_right')+
                        apply(rule combine_assn_waitp_inrdy')
                        by auto
                      done
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitp_wait'')
                       apply auto
                      apply(rule combine_or_right)
                      subgoal
                        apply(rule combine_assn_waitp_outrdy')
                        by auto
                      subgoal
                        apply(rule combine_assn_ex_pre_right')+
                        apply(rule combine_assn_waitp_inrdy')
                        by auto
                      done
                    done
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply(rule combine_assn_in0_waitin)
                    by auto
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    subgoal by auto
                    apply(simp only:pure_assn_entails)
                    apply(rule impI)
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_outrdy)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_in0_inrdy)
                      by auto
                    done
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_assn_pure_pre_left')
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply(rule combine_assn_in0_waitin)
                    by auto
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    subgoal by auto
                    apply(simp only:pure_assn_entails)
                    apply(rule impI)
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_outrdy)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_in0_inrdy)
                      by auto
                    done
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply(rule combine_assn_in0_waitin)
                    by auto
                  subgoal for v
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    subgoal by auto
                    apply(simp only:pure_assn_entails)
                    apply(rule impI)
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_outrdy)
                      subgoal by auto
                      apply(subgoal_tac"p = [] \<and> min (45 / 10 ^ 3 - ts2 T) (2 / 10\<^sup>2 - C_upd ent2 (ts2 C)) = 0")
                       prefer 2
                      subgoal using pre(4,6) unfolding proper'_def inv_s'_def C_upd_def C_def T_def
                        apply(cases ent2) by auto
                      apply auto
                      apply(rule entails_tassn_disjI2)
                      apply(rule entails_tassn_disjI2)
                      apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                        subgoal by auto
                        subgoal using pre(2) unfolding propc_def by auto
                        subgoal using pre(3) unfolding propc'_def by auto 
                        subgoal using pre(4) unfolding proper'_def properp_def by auto
                        subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                        subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                        by auto
                      subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_in0_inrdy)
                      by auto
                    done
                  done
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                    apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply(rule combine_assn_in0_waitin)
                    by auto
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_in0_wait)
                    subgoal by auto
                    apply(simp only:pure_assn_entails)
                    apply(rule impI)
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_in0_outrdy)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_in0_inrdy)
                      by auto
                    done
                  done
                done
              done

            
            
            
            
            
            
            apply(cases st2)
              apply(simp only:combine1.simps T2_tr.simps)
            subgoal premises pre
              apply(subgoal_tac "(min (45 / 10 ^ 3 - ts1 T) (1 / 10\<^sup>2 - C_upd ent1 (ts1 C))) \<ge>0 \<and> (9 / 200 - ts2 T) \<ge> 0 \<and> p=[]")
               prefer 2
              subgoal using pre(4,5,6) unfolding inv_s_def inv_s'_def C_upd_def T_def C_def proper'_def
                apply(cases ent1) by auto
              apply(cases "(min (45 / 10 ^ 3 - ts1 T) (1 / 10\<^sup>2 - C_upd ent1 (ts1 C))) \<ge> (9 / 200 - ts2 T)")
              subgoal
                unfolding combine2.simps
                apply(rule entails_tassn_disjI1)
                apply(rule combine_or_left)
                subgoal
                  apply simp
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_wait_wait4')
                  subgoal by auto
                  apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_left_tran)
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI1)
                  apply(auto simp add:T_def C_def)
                  apply(rule entails_tassn_cancel_both)
                  subgoal premises pre'
                  proof-
                    have 1:"(min (ts2 CHR ''t'' - ts1 CHR ''t'')
                    (ts2 CHR ''t'' - C_upd ent1 (ts1 CHR ''c'') - 7 / 200)) = 
                    (min (9 / 200 - ts1 CHR ''t'') (1 / 100 - C_upd ent1 (ts1 CHR ''c'')) -
                  (9 / 200 - ts2 CHR ''t''))"
                      by auto
                    have 2:" (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (9 / 200 - ts2 CHR ''t'') + t,
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (9 / 200 - ts2 CHR ''t'') + t)))) =
              (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (t + (9 / 200 - ts2 CHR ''t'')),
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (t + (9 / 200 - ts2 CHR ''t''))))))"
                      apply(rule ext)
                      by auto
                    show ?thesis
                      by(simp add: 1 2)
                  qed
                  subgoal premises pre'
                  proof-
                    have "ts1
      (CHR ''t'' :=
         ts1 CHR ''t'' + (9 / 200 - ts2 CHR ''t'') +
         min (ts2 CHR ''t'' - ts1 CHR ''t'')
          (ts2 CHR ''t'' - C_upd ent1 (ts1 CHR ''c'') - 7 / 200),
       CHR ''c'' :=
         C_upd ent1 (ts1 CHR ''c'') + (9 / 200 - ts2 CHR ''t'') +
         min (ts2 CHR ''t'' - ts1 CHR ''t'')
          (ts2 CHR ''t'' - C_upd ent1 (ts1 CHR ''c'') - 7 / 200)) = ts1
      (CHR ''t'' :=
         ts1 CHR ''t'' +
         min (9 / 200 - ts1 CHR ''t'') (1 / 100 - C_upd ent1 (ts1 CHR ''c'')),
       CHR ''c'' :=
         C_upd ent1 (ts1 CHR ''c'') +
         min (9 / 200 - ts1 CHR ''t'') (1 / 100 - C_upd ent1 (ts1 CHR ''c'')))"
                      apply (rule ext)
                      by auto
                    then show ?thesis
                      by auto
                  qed
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_wait)
                   apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_left_tran)
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI1)
                  subgoal for t
                    apply(rule entails_tassn_exI[where x="(t - (9 / 200 - ts2 T))"])
                    apply(auto simp add:T_def C_def)
                    apply(rule entails_tassn_cancel_right)
                    apply(subgoal_tac"
              (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (9 / 200 - ts2 CHR ''t'') + t,
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (9 / 200 - ts2 CHR ''t'') + t)))) =
              (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (t + (9 / 200 - ts2 CHR ''t'')),
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (t + (9 / 200 - ts2 CHR ''t''))))))")
                     apply auto
                    apply(rule ext)
                    by auto
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')+
                  apply auto
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_wait)
                   apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_left_tran)
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI1)
                  subgoal for t v
                    apply(rule entails_tassn_exI[where x= "(t - (9 / 200 - ts2 T))"])
                    apply(rule entails_tassn_exI[where x=v])
                    apply (auto simp add:T_def C_def)
                    apply(rule entails_tassn_cancel_right)
                    apply(subgoal_tac"
              (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (9 / 200 - ts2 CHR ''t'') + t,
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (9 / 200 - ts2 CHR ''t'') + t)))) =
              (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (t + (9 / 200 - ts2 CHR ''t'')),
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (t + (9 / 200 - ts2 CHR ''t''))))))")
                     apply auto
                    apply(rule ext)
                    by auto
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')+
                  apply auto
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_wait)
                   apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_left_tran)
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI1)
                  subgoal for t v
                    apply(rule entails_tassn_exI[where x= "(t - (9 / 200 - ts2 T))"])
                    apply(rule entails_tassn_exI[where x=v])
                    apply (auto simp add:T_def C_def)
                    apply(rule entails_tassn_cancel_right)
                    apply(subgoal_tac"
              (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (9 / 200 - ts2 CHR ''t'') + t,
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (9 / 200 - ts2 CHR ''t'') + t)))) =
              (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (t + (9 / 200 - ts2 CHR ''t'')),
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (t + (9 / 200 - ts2 CHR ''t''))))))")
                     apply auto
                    apply(rule ext)
                    by auto
                  done
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')+
                  apply auto
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_wait)
                   apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5) unfolding inv_s_def by (auto simp add:T_def C_def)
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_left_tran)
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  subgoal for t v
                    apply(rule entails_tassn_exI[where x= "(t - (9 / 200 - ts2 T))"])
                    apply(rule entails_tassn_exI[where x=v])
                    apply (auto simp add:T_def C_def)
                    apply(rule entails_tassn_cancel_right)
                    apply(subgoal_tac"
              (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (9 / 200 - ts2 CHR ''t'') + t,
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (9 / 200 - ts2 CHR ''t'') + t)))) =
              (\<lambda>t. ParState (EState (Sch [] rn rp, ss))
           (EState
             (Task RUNNING eone 2, ts1
              (CHR ''t'' := ts1 CHR ''t'' + (t + (9 / 200 - ts2 CHR ''t'')),
               CHR ''c'' :=
                 C_upd ent1 (ts1 CHR ''c'') + (t + (9 / 200 - ts2 CHR ''t''))))))")
                     apply auto
                    apply(rule ext)
                    by auto
                  done
                done
              subgoal
                unfolding combine2.simps
                apply(rule entails_tassn_disjI2)
                apply(subgoal_tac"9 / 200 - ts2 T > min (45 / 10 ^ 3 - ts1 T) (1 / 10\<^sup>2 - C_upd ent1 (ts1 C))")
                 prefer 2 subgoal by auto
                apply simp
                apply(rule combine_or_left)
                subgoal
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_wait_wait3)
                  subgoal by auto
                  apply(rule entails_tassn_cancel_both)
                  subgoal by auto
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5,6) unfolding inv_s_def inv_s'_def apply(cases "(9 / 200 - ts1 T) \<le>(1 / 100 - C_upd ent1 (ts1 C))") by auto
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_right_tran)
                  unfolding T2_tr.simps
                  apply(rule entails_tassn_cancel_both)
                  subgoal premises pre'
                  proof-
                    have 1:"(9 / 200 - (ts2 T + min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)))) = (9 / 200 - ts2 T - min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)))"
                      by auto
                    have 2:"(\<lambda>t. EState
           (Task WAIT ent2 1, ts2
            (T := ts2 T + min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C)) + t)))
                          = (\<lambda>t. EState
           (Task WAIT ent2 1, ts2
            (T := ts2 T + (t + min (9 / 200 - ts1 T) (1 / 100 - C_upd ent1 (ts1 C))))))"
                      apply (rule ext)
                      by auto
                    show ?thesis 
                      by (auto simp add:1 2)
                  qed
                  by auto
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')+
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_wait)
                  subgoal by auto
                  by auto
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')+
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_wait)
                  subgoal by auto
                  by auto
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')+
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_wait)
                  subgoal by auto
                  by auto
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')+
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_wait)
                  subgoal by auto
                  by auto
                done
              done








             apply(simp only:combine1.simps T2_tr.simps)
            subgoal premises pre
              apply(subgoal_tac"p=[] \<and> min (45 / 10 ^ 3 - ts1 T) (1 / 10\<^sup>2 - C_upd ent1 (ts1 C)) \<ge> 0 \<and> (9 / 200 - ts2 T) \<ge>0")
               prefer 2 
              subgoal using pre(4,5,6) unfolding proper'_def inv_s_def inv_s'_def C_upd_def by auto
              apply simp
              apply(rule combine_or_left)
              subgoal
                apply(rule combine_or_right)
                subgoal
                  apply(rule combine_assn_ex_pre_right')+
                  apply(rule combine_assn_pure_pre_right')
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_wait_out)
                  subgoal by auto
                  apply auto
                  apply(rule entails_tassn_disjI1)
                  apply(subgoal_tac"min (45 / 10 ^ 3 - ts1 T) (1 / 10\<^sup>2 - C_upd ent1 (ts1 C)) = 0")
                    prefer 2 subgoal by auto
                  apply auto
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5,6) unfolding inv_s_def inv_s'_def apply(cases "(9 / 200 - ts1 T) \<le>(1 / 100 - C_upd ent1 (ts1 C))") by auto
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_right_tran)
                  unfolding T2_tr.simps
                  apply(rule entails_tassn_disjI1)
                  subgoal for v tt
                    apply(rule entails_tassn_exI[where x=v])            
                    apply(rule entails_tassn_exI[where x=tt])
                    by auto
                  done
                subgoal
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_wait_out)
                  subgoal by auto
                  apply auto
                  apply(subgoal_tac"min (45 / 10 ^ 3 - ts1 T) (1 / 10\<^sup>2 - C_upd ent1 (ts1 C)) = 0")
                    prefer 2 subgoal by auto
                  apply auto
                  apply(rule entails_tassn_disjI1)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) unfolding propc'_def by auto 
                  subgoal using pre(4) unfolding proper'_def properp_def by auto
                  subgoal using pre(5,6) unfolding inv_s_def inv_s'_def apply(cases "(9 / 200 - ts1 T) \<le>(1 / 100 - C_upd ent1 (ts1 C))") by auto
                  subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                  apply(rule combine_assn_right_tran)
                  unfolding T2_tr.simps
                  apply(rule entails_tassn_disjI2)
                  by auto
                done
              apply(rule combine_or_left)
              subgoal
                apply(rule combine_assn_ex_pre_left')+
                apply(rule combine_assn_pure_pre_left')
                apply auto
                apply(rule combine_or_right)
                subgoal for t
                  apply(rule combine_assn_ex_pre_right')+
                  apply(rule combine_assn_pure_pre_right')
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_waitin_out)
                  subgoal by auto
                  apply auto
                  apply(cases k')
                  subgoal apply simp unfolding false_assn_def combine_assn_def entails_tassn_def
                    by auto
                  subgoal for v tt k''
                    apply (simp add: T_def C_def)
                    apply(rule combine_or_left)
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_wait_waitin)
                      subgoal by auto
                      apply auto
                      apply(rule entails_tassn_disjI2)
                      apply(rule entails_tassn_disjI1)
                      apply(rule entails_tassn_cancel_left)
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_out0_waitin)
                        subgoal by auto
                        apply auto
                        apply(subgoal_tac"min (9 / 200 - ts1 CHR ''t'') (1 / 100 - C_upd ent1 (ts1 CHR ''c'')) = tt")
                         prefer 2 subgoal by auto
                        apply auto
                        apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                        subgoal by auto
                        subgoal using pre(2) unfolding propc_def by auto
                        subgoal using pre(3) unfolding propc'_def by auto 
                        subgoal using pre(4) unfolding proper'_def properp_def by auto
                        subgoal using pre(5,6) unfolding inv_s_def inv_s'_def 
                          apply(cases "(9 / 200 - ts1 T) \<le>(1 / 100 - C_upd ent1 (ts1 C))") 
                          unfolding T_def C_def by auto
                        subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                        by auto
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_assn_waitp_waitin')
                        by auto
                      subgoal
                        apply(rule combine_assn_waitp_waitin')
                        by auto
                      done
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_assn_ex_pre_left')+
                        apply(rule combine_assn_pure_pre_left')
                        apply auto
                        apply(rule combine_assn_waitin_waitin)
                        by auto
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_assn_ex_pre_left')+
                        apply(rule combine_assn_pure_pre_left')
                        apply auto
                        apply(rule combine_assn_waitin_waitin)
                        by auto
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_assn_ex_pre_left')+
                        apply(rule combine_assn_pure_pre_left')
                        apply auto
                        apply(rule combine_assn_waitin_waitin)
                        by auto
                      subgoal
                        apply(rule combine_assn_ex_pre_left')+
                        apply(rule combine_assn_pure_pre_left')
                        apply auto
                        apply(rule combine_assn_waitin_waitin)
                        by auto
                      done
                    done
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_waitin_out)
                    subgoal by auto
                    apply auto
                    apply(cases k')
                    subgoal apply simp unfolding false_assn_def combine_assn_def entails_tassn_def
                      by auto
                    subgoal for k''
                      apply(auto simp add: T_def C_def)
                      apply(rule combine_or_left)
                      subgoal
                        apply(cases "(min (9 / 200 - ts1 CHR ''t'') (1 / 100 - C_upd ent1 (ts1 CHR ''c''))) < (9 / 200 - ts2 CHR ''t'')")
                        subgoal
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_wait_wait3)
                          subgoal by auto
                          apply auto
                          apply(rule entails_tassn_disjI2)
                          apply(rule entails_tassn_disjI1)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule combine_or_left)
                          subgoal 
                            apply(rule combine_assn_out0_wait)
                            by auto
                          apply(rule combine_or_left)
                          subgoal
                            apply(rule combine_assn_waitp_wait')
                            by auto
                          subgoal
                            apply(rule combine_assn_waitp_wait')
                            by auto
                          done
                        apply(cases " (9 / 200 - ts2 CHR ''t'') = (min (9 / 200 - ts1 CHR ''t'') (1 / 100 - C_upd ent1 (ts1 CHR ''c'')))")
                        subgoal
                          apply simp
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_wait_wait2)
                          subgoal by auto
                          apply auto
                          apply(rule entails_tassn_disjI2)
                          apply(rule entails_tassn_disjI1)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule combine_or_left)
                          subgoal 
                            apply(rule combine_or_right)
                            subgoal
                              apply(rule combine_assn_out0_outrdy)
                              by auto
                            subgoal
                              apply(rule combine_assn_ex_pre_right')+
                              apply(rule entails_tassn_trans)
                               apply(rule combine_assn_out0_inrdy)
                              subgoal by auto
                              apply auto
                              apply(rule entails_tassn_trans)
                               prefer 2
                               apply(rule pre(1))
                              subgoal by auto
                              subgoal using pre(2) unfolding propc_def by auto
                              subgoal using pre(3) unfolding propc'_def by auto 
                              subgoal using pre(4) unfolding proper'_def properp_def by auto
                              subgoal using pre(5,6) unfolding inv_s_def inv_s'_def 
                                apply(cases "(9 / 200 - ts1 T) \<le>(1 / 100 - C_upd ent1 (ts1 C))") 
                                unfolding T_def C_def by auto
                              subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                              apply(subgoal_tac "ts2(CHR ''t'' := ts2 CHR ''t'' + min (9 / 200 - ts1 CHR ''t'') (1 / 100 - C_upd ent1 (ts1 CHR ''c'')), F := 0) = ts2(CHR ''t'' := 9 / 200, F := 0)")
                              by auto
                            done
                          apply(rule combine_or_left)
                          subgoal
                            apply(rule combine_or_right)
                            subgoal
                              apply(rule combine_assn_waitp_outrdy')
                              by auto
                            subgoal
                              apply(rule combine_assn_ex_pre_right')+
                              apply(rule combine_assn_waitp_inrdy')
                              by auto
                            done
                            subgoal
                            apply(rule combine_or_right)
                            subgoal
                              apply(rule combine_assn_waitp_outrdy')
                              by auto
                            subgoal
                              apply(rule combine_assn_ex_pre_right')+
                              apply(rule combine_assn_waitp_inrdy')
                              by auto
                            done
                          done
                        apply(cases "(min (9 / 200 - ts1 CHR ''t'') (1 / 100 - C_upd ent1 (ts1 CHR ''c''))) > (9 / 200 - ts2 CHR ''t'')")
                        subgoal
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_wait_wait4)
                          subgoal by auto
                          apply auto
                          apply(rule entails_tassn_disjI2)
                          apply(rule entails_tassn_disjI2)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule combine_or_right)
                          subgoal
                            apply(rule entails_tassn_trans)
                            apply(rule combine_assn_wait_outrdy)
                            by auto
                          subgoal
                            apply(rule combine_assn_ex_pre_right')+
                            apply(rule entails_tassn_trans)
                            apply(rule combine_assn_wait_inrdy)
                            by auto
                          done
                        by auto
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_assn_ex_pre_left')+
                        apply(rule combine_assn_pure_pre_left')
                        apply auto
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitin_wait)
                        subgoal by auto
                        apply auto
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_cancel_left)
                        apply(rule combine_or_right)
                        subgoal
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_waitin_outrdy)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        subgoal
                          apply(rule combine_assn_ex_pre_right')+
                          apply(rule combine_assn_waitin_inrdy)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        done
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_assn_ex_pre_left')+
                        apply(rule combine_assn_pure_pre_left')
                        apply auto
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitin_wait)
                        subgoal by auto
                        apply auto
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_cancel_left)
                        apply(rule combine_or_right)
                        subgoal
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_waitin_outrdy)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        subgoal
                          apply(rule combine_assn_ex_pre_right')+
                          apply(rule combine_assn_waitin_inrdy)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        done
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_assn_ex_pre_left')+
                        apply(rule combine_assn_pure_pre_left')
                        apply auto
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitin_wait)
                        subgoal by auto
                        apply auto
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_cancel_left)
                        apply(rule combine_or_right)
                        subgoal
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_waitin_outrdy)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        subgoal
                          apply(rule combine_assn_ex_pre_right')+
                          apply(rule combine_assn_waitin_inrdy)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        done
                      subgoal
                        apply(rule combine_assn_ex_pre_left')+
                        apply(rule combine_assn_pure_pre_left')
                        apply auto
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitin_wait)
                        subgoal by auto
                        apply auto
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_cancel_left)
                        apply(rule combine_or_right)
                        subgoal for tt v
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_waitin_outrdy)
                          subgoal by auto
                          apply auto
                          apply(rule entails_tassn_trans)
                           prefer 2
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) unfolding propc'_def by auto 
                          subgoal using pre(4) unfolding proper'_def properp_def by auto
                          subgoal using pre(5,6) unfolding inv_s_def inv_s'_def 
                            apply(cases "(9 / 200 - ts1 T) \<le>(1 / 100 - C_upd ent1 (ts1 C))") 
                            unfolding T_def C_def by auto
                          subgoal using pre(5,6) unfolding inv_s'_def inv_s_def by(auto simp add:T_def C_def)
                          by auto
                        subgoal
                          apply(rule combine_assn_ex_pre_right')+
                          apply(rule combine_assn_waitin_inrdy)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        done
                      done
                    done
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')
                  apply auto
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply auto
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_waitin_out)
                    by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_waitin_out)
                    by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')
                  apply auto
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply auto
                    apply(rule combine_assn_waitin_out'')
                    by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  subgoal
                    apply(rule combine_assn_waitin_out'')
                    by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  done
                subgoal
                  apply(rule combine_assn_ex_pre_left')+
                  apply(rule combine_assn_pure_pre_left')
                  apply auto
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply auto
                    apply(rule combine_assn_waitin_out'')
                    by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  subgoal
                    apply(rule combine_assn_waitin_out'')
                    by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  done
                done

              apply(simp only:combine1.simps T2_tr.simps)
              subgoal 
                unfolding propc_def propc'_def by auto
              done
            done
          done
        done
    qed











end