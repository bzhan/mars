theory task2
  imports task1
begin


definition inv_s' :: "state \<Rightarrow> bool" where
 "inv_s' s = (s T \<le> 0.045 \<and> s C \<le> 0.02)"

definition T2 :: "estate proc" where
"T2 = IF (\<lambda>(a,s) . status a = WAIT) 
        THEN (Cont (ODE ((\<lambda> _ _ . 0)(T := (\<lambda> _ .1)))) (\<lambda> s. s T < 0.045);T ::= (\<lambda>_. 0); Basic (ent_assign ezero);Basic (ready_assign)) 
      ELSE 
      (IF(\<lambda>(a,s) . status a = READY) 
        THEN (Cm ((req_ch 2)[!](\<lambda>(a,s). task_prior a)); 
             (Interrupt (ODE ((\<lambda> _ _ . 0)(T := (\<lambda> _ .1)))) (\<lambda> s. s T < 0.045) [(run_ch 2[?]F,Basic run_assign)]); 
             (IF (\<lambda>(a,s) . status a = READY \<and> s T = 0.045) THEN (EChoice [(exit_ch 2[!](\<lambda>_.0),Basic wait_assign),(run_ch 2[?]F,Basic run_assign)]) ELSE Skip FI))  
      ELSE 
      (IF(\<lambda>(a,s) . entered a = ezero) THEN 
             (C ::= (\<lambda>_ . 0); Basic (ent_assign eone)) ELSE Skip FI; 
        (Interrupt (ODE ((\<lambda> _ _ . 0)(T := (\<lambda> _ .1),C := (\<lambda>_ .1)))) (\<lambda> s. s T < 0.045 \<and> s C < 0.02) [(preempt_ch 2[?]F,Basic ready_assign)]); 
        IF (\<lambda>(a,s) . status a = RUNNING) THEN EChoice [(free_ch 2[!](\<lambda>_.0),Basic wait_assign),(preempt_ch 2[?]F,Basic wait_assign)] ELSE Skip FI) 
      FI) FI"


fun T2_tr:: "nat \<Rightarrow> estate ext_state \<Rightarrow> estate tassn" where
  "T2_tr 0 (Task st ent tp,ss)  = emp\<^sub>t"
| "T2_tr (Suc k) (Task WAIT ent tp,ss) = 
   (Wait\<^sub>t (9 / 200 - ss T) (\<lambda>t. EState (Task WAIT ent tp, ss(T:= ss T + t))) ({}, {}) @\<^sub>t T2_tr k (Task READY ezero tp,ss(T:=0)))"
| "T2_tr (Suc k) (Task READY ent tp,ss) = (
             (\<exists>\<^sub>t v tt. \<up>(tt\<ge>0 \<and> tt \<le> 0.045 - ss T) \<and>\<^sub>t Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp @\<^sub>t
                   Waitin\<^sub>t tt (\<lambda>t. EState (Task READY ent tp, ss(T := ss T + t)))
                    (run_ch 2) v ({}, {run_ch 2}) @\<^sub>t 
                   T2_tr k (Task RUNNING ent tp,ss(T := ss T + tt, F:=v)))
           \<or>\<^sub>t (Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp @\<^sub>t
                   Wait\<^sub>t (9 / 200 - ss T) (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>)))
                    ({}, {run_ch 2}) @\<^sub>t
                    (outrdy_assn (Task READY ent tp, ss(T:=0.045)) (exit_ch 2) 0 ({exit_ch 2},{run_ch 2}) @\<^sub>t T2_tr k (Task WAIT ent tp,ss(T:=0.045))
                  \<or>\<^sub>t (\<exists>\<^sub>t v. inrdy_assn (Task READY ent tp, ss(T:=0.045)) (run_ch 2) v ({exit_ch 2},{run_ch 2}) @\<^sub>t T2_tr k (Task RUNNING ent tp,ss(T:=0.045,F:=v))))))"
| "T2_tr (Suc k) (Task RUNNING ent tp,ss) = (
             (\<exists>\<^sub>t v tt. \<up>(tt\<ge>0 \<and> tt \<le> (min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) \<and>\<^sub>t Waitin\<^sub>t tt
                           (\<lambda>t. EState
                                 (Task RUNNING eone tp, ss
                                  (T := ss T + t,
                                   C := C_upd ent (ss C) + t)))
                           (preempt_ch 2) v ({}, {preempt_ch 2}) @\<^sub>t
                         T2_tr k (Task READY eone tp,ss
                         (T := ss T + tt,
                          C := C_upd ent (ss C) + tt, F := v)))
            \<or>\<^sub>t (Wait\<^sub>t (min (0.045 - ss T) (0.02 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState
                (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>)))
          ({}, {preempt_ch 2}) @\<^sub>t 
             ((Outrdy\<^sub>t ((Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C))))) (free_ch 2) 0 ({free_ch 2},{preempt_ch 2})@\<^sub>t
                T2_tr k (Task WAIT eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))))
     \<or>\<^sub>t (\<exists>\<^sub>t v.(Inrdy\<^sub>t ((Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C))))) (preempt_ch 2) v ({free_ch 2},{preempt_ch 2})@\<^sub>t
                T2_tr k (Task WAIT eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)),F:=v)))))
)
)"
                                                                                                                              

lemma T2_Valid_WAIT:
"\<Turnstile> {\<lambda>s t. s = (Task WAIT ent tp,ss) \<and> inv_s' (snd s) \<and> P s t}
   T2
    {\<lambda> s t. s = (Task READY ezero tp,ss(T:=0)) \<and> inv_s' (snd s) \<and> (P (Task WAIT ent tp,ss) @\<^sub>t Wait\<^sub>t (9 / 200 - ss T) (\<lambda>t. EState (Task WAIT ent tp, ss(T:= ss T + t))) ({}, {})) t}"
  unfolding T2_def
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_cond_sp)
    apply(rule Valid_seq)
     apply(rule Valid_pre_cases'[where P="\<lambda>(a,s) . s T< 0.045"])
      apply(rule Valid_weaken_pre)
       prefer 2
       apply(rule Valid_strengthen_post[where Q'="\<lambda> s t. s = (Task WAIT ent tp,ss(T:=0.045)) \<and> inv_s' (snd s) \<and> (P (Task WAIT ent tp,ss) @\<^sub>t
         Wait\<^sub>t (45 / 10 ^ 3 - ss T) (\<lambda>t. EState (Task WAIT ent tp, ss(T := ss T + t))) ({}, {})) t"])
        prefer 2
        apply(rule Valid_ode_sol_sp[where ss= ss and aa = "Task WAIT ent tp" and d="0.045- ss T" and p="\<lambda> t. ss(T:= ss T+t)" and P = "\<lambda>(a,s) t. inv_s' (snd (a, s)) \<and> P (a, s) t"])
     subgoal by auto
     subgoal 
       apply auto unfolding state2vec_def has_vderiv_on_def
       apply clarify
       apply (rule has_vector_derivative_projI)
       apply auto
       apply (rule has_vector_derivative_eq_rhs)
        apply (fast intro!: derivative_intros)
       by auto
     subgoal by auto
     subgoal by auto
     subgoal
       apply auto unfolding state2vec_def vec2state_def
       apply (rule c1_implies_local_lipschitz[where f'="(\<lambda>(t,v). Blinfun(\<lambda>(v::vec) . \<chi> x. 0))"])
       apply auto
       unfolding has_derivative_def
       apply auto
        prefer 2
        apply (rule vec_tendstoI)
       subgoal
       proof-
         have b1:"bounded_linear (\<lambda> (v::vec). \<chi> a . 0)"
           apply (rule bounded_linearI')
           using vec_lambda_unique by fastforce+
         then have b2:"blinfun_apply (Blinfun (\<lambda> (v::vec). \<chi> x. 0)) = (\<lambda>v. \<chi> x. 0)"
           apply(rule bounded_linear_Blinfun_apply)
           done
         then have b3:"bounded_linear (blinfun_apply (Blinfun (\<lambda> (v::vec). \<chi> x. 0)))"
           using b1 
           by (simp add: blinfun.bounded_linear_right)
         show ?thesis
           by(auto simp add:b2)
       qed
       by (simp add: blinfun.bounded_linear_right)
     subgoal
       unfolding entails_def inv_s'_def by (auto simp add:C_def T_def pure_assn_def conj_assn_def)
     subgoal unfolding entails_def by auto
        apply(rule Valid_weaken_pre)
         prefer 2
         apply(rule Valid_strengthen_post)
          prefer 2
          apply(rule Valid_ode_not_sp[where ss= ss and aa = "Task WAIT ent tp" and d="0.045- ss T" and p="\<lambda> t. ss(T:= ss T+t)" and P = "\<lambda>(a,s) t. inv_s' (snd (a, s)) \<and> P (a, s) t"])
     subgoal by auto
     subgoal by auto
     subgoal unfolding entails_def inv_s'_def by (auto simp add:C_def T_def pure_assn_def conj_assn_def)
     subgoal unfolding entails_def inv_s'_def by (auto simp add:C_def T_def)
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
  apply(auto simp add: pure_assn_def conj_assn_def inv_s'_def C_def T_def)
  subgoal for ss' tr x
    apply (rule ext) subgoal for v
      apply (cases "v = CHR ''t''")
      subgoal by auto
      subgoal premises pre proof -
        have "(ss'(CHR ''t'' := x)) v = (ss(CHR ''t'' := 9 / 200)) v"
          using pre(2) by auto
        then have "ss' v = ss v"
          using pre(6) by auto
        then show ?thesis
          using pre(6) by auto
      qed
      done
    done
  done

  
  
    
  


lemma T2_Valid_READY:
"\<Turnstile> {\<lambda>s t. s = (Task READY ent tp,ss) \<and> inv_s' (snd s) \<and> P s t}
   T2
    {\<lambda> s tr. (inv_s' (snd s) \<and> (\<exists> tt v. tt\<ge>0 \<and> tt \<le> 0.045 - ss T \<and> s = (Task RUNNING ent tp,ss(T:= ss T + tt,F := v)) \<and>
                    ((P (Task READY ent tp, ss) @\<^sub>t
                    Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                   Waitin\<^sub>t tt (\<lambda>t. EState (Task READY ent tp, ss(T := ss T + t)))
                    (run_ch 2) v ({}, {run_ch 2})) tr)) 
              \<or> (inv_s' (snd s) \<and> s = (Task WAIT ent tp,ss(T:=0.045)) \<and> 
                   ((P (Task READY ent tp, ss) @\<^sub>t
                    Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                   Wait\<^sub>t (9 / 200 - ss T) (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>)))
                    ({}, {run_ch 2}) @\<^sub>t
                    Outrdy\<^sub>t (Task READY ent tp, ss(T:=0.045)) (exit_ch 2) 0 ({exit_ch 2},{run_ch 2}))
                   tr)
              \<or> (\<exists> v. (inv_s' (snd s) \<and> s = (Task RUNNING ent tp,ss(T:=0.045,F:=v)) \<and> 
                   ((P (Task READY ent tp, ss) @\<^sub>t
                    Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                   Wait\<^sub>t (9 / 200 - ss T) (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>)))
                    ({}, {run_ch 2}) @\<^sub>t
                    Inrdy\<^sub>t (Task READY ent tp, ss(T:=0.045)) (run_ch 2) v ({exit_ch 2},{run_ch 2}))
                   tr))}"
unfolding T2_def
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
  apply(rule Valid_seq[where 
    Q="\<lambda> (a,s) tr. (\<exists> tt v. tt\<ge>0 \<and> tt \<le> 0.045 - ss T \<and> (a,s) = (Task RUNNING ent tp,ss(T:= ss T + tt,F := v)) \<and> inv_s' s \<and> (
                   (P (Task READY ent tp, ss) @\<^sub>t
                    Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                   Waitin\<^sub>t tt (\<lambda>t. EState (Task READY ent tp, ss(T := ss T + t)))
                    (run_ch 2) v ({}, {run_ch 2})) tr)
              \<or>  ((a,s) = (Task READY ent tp,ss(T:=0.045)) \<and> inv_s' s \<and> 
                   ((P (Task READY ent tp, ss) @\<^sub>t
                    Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                   Wait\<^sub>t (9 / 200 - ss T) (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>)))
                    ({}, {run_ch 2}))
                   tr)"])
  apply(rule Valid_pre_cases'[where P="(\<lambda>(a,s). s T < 45 / 10 ^ 3)"])
   apply(rule Valid_weaken_pre)
  prefer 2
  apply(rule Valid_strengthen_post)
     prefer 2
     apply(rule Valid_interrupt_in_sol[where ss= ss and d="0.045- ss T" and p="\<lambda> t. ss(T:= ss T + t)" and aa= "Task READY ent tp" and P="\<lambda>(a,s) t. inv_s' s \<and> (P (a, s) @\<^sub>t Out\<^sub>t (EState (a, s)) (req_ch 2) tp) t"])
  subgoal by auto
  subgoal 
    apply auto unfolding state2vec_def has_vderiv_on_def
    apply clarify
    apply (rule has_vector_derivative_projI)
    apply auto
    apply (rule has_vector_derivative_eq_rhs)
     apply (fast intro!: derivative_intros)
    by auto
  subgoal by auto
  subgoal by auto
  subgoal
    apply auto unfolding state2vec_def vec2state_def
    apply (rule c1_implies_local_lipschitz[where f'="(\<lambda>(t,v). Blinfun(\<lambda>(v::vec) . \<chi> x. 0))"])
       apply auto
    unfolding has_derivative_def
    apply auto
    prefer 2
     apply (rule vec_tendstoI)
    subgoal
    proof-
    have b1:"bounded_linear (\<lambda> (v::vec). \<chi> a . 0)"
      apply (rule bounded_linearI')
      using vec_lambda_unique by fastforce+
    then have b2:"blinfun_apply (Blinfun (\<lambda> (v::vec). \<chi> x. 0)) = (\<lambda>v. \<chi> x. 0)"
      apply(rule bounded_linear_Blinfun_apply)
      done
    then have b3:"bounded_linear (blinfun_apply (Blinfun (\<lambda> (v::vec). \<chi> x. 0)))"
      using b1 
      by (simp add: blinfun.bounded_linear_right)
    show ?thesis
      by(auto simp add:b2)
  qed
  by (simp add: blinfun.bounded_linear_right)
     apply auto[1]
     apply(rule Valid_basic_sp1)
    prefer 2
  subgoal unfolding entails_def join_assn_def by auto
     prefer 2
  apply(rule Valid_weaken_pre)
  prefer 2
  apply(rule Valid_strengthen_post)
       prefer 2
       apply(rule Valid_interrupt_in_not[where p = "\<lambda> t. ss(T:= ss T + t)" and ss= ss and aa= "Task READY ent tp" and P="\<lambda>(a,s) t. inv_s' s \<and> (P (a, s) @\<^sub>t Out\<^sub>t (EState (a, s)) (req_ch 2) tp) t"])
  subgoal by auto
  apply auto[1]
       apply(rule Valid_basic_sp1)
      prefer 2
  subgoal unfolding entails_def join_assn_def by auto
  subgoal unfolding entails_def inv_s'_def pure_assn_def join_assn_def conj_assn_def
    apply (auto simp add: T_def C_def F_def)
    subgoal for v tr1 tr3 tr2
      apply(rule exI[where x = 0])
      apply auto
      apply(rule exI[where x = v])
      apply auto
      apply(rule exI[where x = "tr1@tr2"])
      by auto
    done
  subgoal 
    apply(rule entails_disjE)
     apply (auto simp del: fun_upd_apply)
    subgoal
    apply(rule entails_trans[where Q ="(\<lambda>a. case a of
         (a, s) \<Rightarrow>
           \<lambda>tr. (\<exists>tt\<ge>0.
                    tt \<le> 9 / 200 - ss T \<and>
                    a = Task RUNNING ent tp \<and>
                    (\<exists>v. s = ss(T := ss T + tt, F := v) \<and>
                         inv_s' s \<and>
                         ((P (Task READY ent tp, ss) @\<^sub>t
                           Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                          Waitin\<^sub>t tt (\<lambda>t. EState (Task READY ent tp, ss(T := ss T + t)))
                           (run_ch 2) v ({}, {run_ch 2}))
                          tr)))"])
      subgoal 
        unfolding entails_def C_def T_def F_def inv_s'_def pure_assn_def conj_assn_def join_assn_def
        apply (auto simp del: fun_upd_apply)
        subgoal for tt vv tr1 tr2 tr3
          apply(rule exI[where x="tt"])
          apply auto
          apply(rule exI[where x="vv"])
          apply auto
          apply(rule exI[where x="tr1@tr3"])
          by auto
        done
      unfolding entails_def by auto
    subgoal
      apply(rule entails_trans[where Q="\<lambda>a. case a of
         (a, s) \<Rightarrow>
           \<lambda>tr. a = Task READY ent tp \<and>
                s = ss(T := 9 / 200) \<and>
                inv_s' s \<and>
                ((P (Task READY ent tp, ss) @\<^sub>t
                  Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                 Wait\<^sub>t (9 / 200 - ss T)
                  (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>))) ({}, {run_ch 2}))
                 tr"])
      unfolding entails_def C_def T_def F_def inv_s'_def pure_assn_def conj_assn_def join_assn_def
      by auto
    done
   apply(rule Valid_cond_sp)
  apply simp
  apply(rule Valid_echoice[where R ="\<lambda> s tr.(inv_s' (snd s) \<and> s = (Task WAIT ent tp,ss(T:=0.045)) \<and> 
                   ((P (Task READY ent tp, ss) @\<^sub>t
                    Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                   Wait\<^sub>t (9 / 200 - ss T) (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>)))
                    ({}, {run_ch 2}) @\<^sub>t
                    Outrdy\<^sub>t (Task READY ent tp, ss(T:=0.045)) (exit_ch 2) 0 ({exit_ch 2},{run_ch 2}))
                   tr)
              \<or> (\<exists> v. (inv_s' (snd s) \<and> s = (Task RUNNING ent tp,ss(T:=0.045,F:=v)) \<and> 
                   ((P (Task READY ent tp, ss) @\<^sub>t
                    Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                   Wait\<^sub>t (9 / 200 - ss T) (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>)))
                    ({}, {run_ch 2}) @\<^sub>t
                    Inrdy\<^sub>t (Task READY ent tp, ss(T:=0.045)) (run_ch 2) v ({exit_ch 2},{run_ch 2}))
                   tr))"])
  subgoal for i
    apply(cases i)
    subgoal
      apply auto
      apply(rule exI[where x="\<lambda>s tr.
               inv_s' (snd s) \<and>
               s = (Task READY ent tp, ss(T := 9 / 200)) \<and>
               ((P (Task READY ent tp, ss) @\<^sub>t
                 Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                Wait\<^sub>t (9 / 200 - ss T)
                 (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>))) ({}, {run_ch 2}) @\<^sub>t
                Outrdy\<^sub>t (Task READY ent tp, ss(T := 9 / 200)) (exit_ch 2) 0
                 ({exit_ch 2}, {run_ch 2}))
                tr"])
      apply auto
      subgoal
        apply(rule Valid_strengthen_post)
         prefer 2
         apply(rule Valid_basic_sp1)
        unfolding entails_def
        by auto
      subgoal unfolding entails_def
        apply (auto simp add:join_assn_def join_assoc)
        subgoal for tr1a tr2 tr2a
          apply(rule exI[where x="tr1a@tr2a"])
          apply auto
          apply(rule exI[where x="tr2"])
          apply auto
          apply(rule )
          done
        done
      subgoal unfolding entails_def
        apply (auto simp add:join_assn_def join_assoc)
        subgoal for d tr1a tr2 tr2a
          apply(rule exI[where x="tr1a@tr2a"])
          apply auto
          apply(rule exI[where x="tr2"])
          apply auto
          apply rule 
          by auto
        done
      done
    subgoal for i'
      apply auto
      apply(rule exI[where x="\<lambda> s tr. (\<exists> v. (inv_s' (snd s) \<and> s = (Task READY ent tp,ss(T:=0.045,F:=v)) \<and> 
                   ((P (Task READY ent tp, ss) @\<^sub>t
                    Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                   Wait\<^sub>t (9 / 200 - ss T) (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>)))
                    ({}, {run_ch 2}) @\<^sub>t
                    Inrdy\<^sub>t (Task READY ent tp, ss(T:=0.045)) (run_ch 2) v ({exit_ch 2},{run_ch 2}))
                   tr))"])
      apply auto
      subgoal
        apply(rule Valid_strengthen_post)
         prefer 2
         apply(rule Valid_basic_sp1)
        unfolding entails_def
        by auto
      subgoal unfolding entails_def
        apply (auto simp add:inv_s'_def F_def T_def C_def join_assn_def join_assoc)
        subgoal for tr1a tr2 tr2a v
          apply(rule exI[where x=v])
          apply auto
          apply(rule exI[where x="tr1a@tr2a"])
          apply auto
          apply(rule exI[where x=tr2])
          apply auto
          apply rule
          done
        done
      subgoal unfolding entails_def
        apply (auto simp add:inv_s'_def F_def T_def C_def join_assn_def join_assoc)
        subgoal for d tr1a tr2 tr2a v
          apply(rule exI[where x=v])
          apply auto
          apply(rule exI[where x="tr1a@tr2a"])
          apply auto
          apply(rule exI[where x=tr2])
          apply auto
          apply rule
          by auto
        done
      done
    done
   apply(rule Valid_skip)
  by auto


    

lemma T2_Valid_RUNNING:
"\<Turnstile> {\<lambda>s t. s = (Task RUNNING ent tp,ss) \<and> inv_s' (snd s) \<and> P s t}
   T2
    {\<lambda> s tr. ((inv_s' (snd s) \<and> (\<exists> tt v. tt\<ge>0 \<and> tt \<le> (min (0.045 - ss T) (0.02 - C_upd ent (ss C))) \<and> 
                          s = (Task READY eone tp,ss
                         (CHR ''t'' := ss CHR ''t'' + tt,
                          CHR ''c'' := C_upd ent (ss CHR ''c'') + tt, F := v)) \<and> (
                    P (Task RUNNING ent tp, ss) @\<^sub>t
                          Waitin\<^sub>t tt
                           (\<lambda>t. EState
                                 (Task RUNNING eone tp, ss
                                  (CHR ''t'' := ss CHR ''t'' + t,
                                   CHR ''c'' := C_upd ent (ss CHR ''c'') + t)))
                           (preempt_ch 2) v ({}, {preempt_ch 2}))
                          tr)) 
              \<or>  (inv_s' (snd s) \<and> s =
          (Task WAIT eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) \<and> 
                   ((P (Task RUNNING ent tp, ss)) @\<^sub>t
         Wait\<^sub>t (min (0.045 - ss T) (0.02 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState
                (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>)))
          ({}, {preempt_ch 2}) @\<^sub>t
             Outrdy\<^sub>t (Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) (free_ch 2) 0 ({free_ch 2},{preempt_ch 2}))
         tr)
             \<or> (\<exists> v. (inv_s' (snd s) \<and> s =
          (Task WAIT eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)), F := v)) \<and> 
                   ((P (Task RUNNING ent tp, ss)) @\<^sub>t
         Wait\<^sub>t (min (0.045 - ss T) (0.02 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState
                (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>)))
          ({}, {preempt_ch 2}) @\<^sub>t
             Inrdy\<^sub>t (Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) (preempt_ch 2) v ({free_ch 2},{preempt_ch 2}))
         tr)))}"
  unfolding T2_def
apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_cond_sp)
  apply(rule Valid_weaken_pre[where P'="\<lambda> s t. False"])
unfolding entails_def
    apply auto[1]
  apply(rule Valid_False)
apply(rule Valid_cond_sp)
  apply(rule Valid_weaken_pre[where P'="\<lambda> s t. False"])
unfolding entails_def
    apply auto[1]
  apply(rule Valid_False)
  apply(rule Valid_seq[where Q="\<lambda> s t. s = (Task RUNNING eone tp, ss(C := C_upd ent (ss C))) \<and> inv_s' (snd s) \<and> P (Task RUNNING ent tp, ss) t"])
  apply(rule Valid_strengthen_post)
  prefer 2
   apply(rule Valid_cond_sp)
   apply(rule Valid_seq)
    apply(rule Valid_assign_sp1)
    apply(rule Valid_basic_sp1)
   apply(rule Valid_skip)
  subgoal unfolding entails_def inv_s'_def C_upd_def
    apply auto
    using entered.exhaust by blast
   apply(rule Valid_seq[where 
    Q="\<lambda> (a,s) tr. (\<exists> tt v. tt\<ge>0 \<and> tt \<le> (min (0.045 - ss T) (0.02 - C_upd ent (ss C))) \<and> 
                          (a,s) = (Task READY eone tp,ss
                         (CHR ''t'' := ss CHR ''t'' + tt,
                          CHR ''c'' := C_upd ent (ss CHR ''c'') + tt, F := v)) \<and> inv_s' s \<and> (
                    P (Task RUNNING ent tp, ss) @\<^sub>t
                          Waitin\<^sub>t tt
                           (\<lambda>t. EState
                                 (Task RUNNING eone tp, ss
                                  (CHR ''t'' := ss CHR ''t'' + t,
                                   CHR ''c'' := C_upd ent (ss CHR ''c'') + t)))
                           (preempt_ch 2) v ({}, {preempt_ch 2}))
                          tr) 
              \<or>  ((a, s) =
          (Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) \<and> inv_s' s \<and> 
                   ((P (Task RUNNING ent tp, ss)) @\<^sub>t
         Wait\<^sub>t (min (0.045 - ss T) (0.02 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState
                (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>)))
          ({}, {preempt_ch 2}))
         tr)"])
 apply(rule Valid_pre_cases'[where P="(\<lambda>(a,s). s T < 45 / 10 ^ 3 \<and> s C < 2 / 10\<^sup>2)"])
   apply(rule Valid_weaken_pre)
  prefer 2
  apply(rule Valid_strengthen_post)
     prefer 2
     apply(rule Valid_interrupt_in_sol[where ss= "ss(C := C_upd ent (ss C))" and d="min (0.045 - ss T) (0.02 - C_upd ent (ss C))" and p="\<lambda> t. ss(T:= ss T + t, C:= C_upd ent (ss C) + t)" and aa= "Task RUNNING eone tp" and P="\<lambda>(a,s) t. inv_s' s \<and> P (Task RUNNING ent tp, ss)  t"])
  subgoal apply auto unfolding T_def C_def by auto
  subgoal 
    apply auto unfolding state2vec_def has_vderiv_on_def
    apply clarify
    apply (rule has_vector_derivative_projI)
    apply auto
    unfolding T_def C_def
    apply auto
    apply (rule has_vector_derivative_eq_rhs)
      apply (fast intro!: derivative_intros)
     apply auto
      apply (rule has_vector_derivative_eq_rhs)
      apply (fast intro!: derivative_intros)
    by auto
  subgoal by auto
  subgoal unfolding T_def C_def
     apply auto
    apply(cases "(9 / 200 - ss CHR ''t'') \<le> (2 / 100 - C_upd ent (ss CHR ''c''))")
    by auto
  subgoal
    apply auto unfolding state2vec_def vec2state_def
    apply (rule c1_implies_local_lipschitz[where f'="(\<lambda>(t,v). Blinfun(\<lambda>(v::vec) . \<chi> x. 0))"])
       apply auto
    unfolding has_derivative_def
    apply auto
    prefer 2
     apply (rule vec_tendstoI)
    subgoal
    proof-
    have b1:"bounded_linear (\<lambda> (v::vec). \<chi> a . 0)"
      apply (rule bounded_linearI')
      using vec_lambda_unique by fastforce+
    then have b2:"blinfun_apply (Blinfun (\<lambda> (v::vec). \<chi> x. 0)) = (\<lambda>v. \<chi> x. 0)"
      apply(rule bounded_linear_Blinfun_apply)
      done
    then have b3:"bounded_linear (blinfun_apply (Blinfun (\<lambda> (v::vec). \<chi> x. 0)))"
      using b1 
      by (simp add: blinfun.bounded_linear_right)
    show ?thesis
      by(auto simp add:b2)
    qed
    by (simp add: blinfun.bounded_linear_right)
  apply clarify[1]
       apply (simp add: T_def C_def)[1]
       apply(rule Valid_basic_sp1)
      prefer 2
  subgoal unfolding entails_def
    by auto
     prefer 2
     apply(rule Valid_weaken_pre)
  prefer 2
     apply(rule Valid_strengthen_post)
       prefer 2
       apply(rule Valid_interrupt_in_not[where ss= "ss(C := C_upd ent (ss C))" and p="\<lambda> t. ss(T:= ss T + t, C:= C_upd ent (ss C) + t)" and aa= "Task RUNNING eone tp" and P="\<lambda>(a,s) t. inv_s' s \<and> P (Task RUNNING ent tp, ss)  t"])
  subgoal by auto
  unfolding T_def C_def 
  apply auto[1]
       apply(rule Valid_basic_sp1)
      prefer 2
  subgoal unfolding entails_def by auto
  subgoal 
    unfolding entails_def
    apply (rule allI)+
    apply(rule impI)
    subgoal for s tr
      apply(cases s)
      subgoal for a sss
        apply simp
        apply(erule disjE)
        subgoal apply(rule disjI1)
          apply(rule exI[where x=0])
          apply clarify
          apply(rule conjI) subgoal by auto
          apply(rule conjI) subgoal unfolding pure_assn_def join_assn_def conj_assn_def inv_s'_def T_def C_def by auto
          apply(rule conjI) subgoal unfolding pure_assn_def join_assn_def conj_assn_def inv_s'_def T_def C_def by auto
          subgoal for v
            apply simp
            apply(rule exI[where x=v])
            unfolding pure_assn_def join_assn_def conj_assn_def inv_s'_def T_def C_def F_def by auto
          done
        subgoal apply(rule disjI2)
          apply simp
          apply(rule conjI) subgoal unfolding pure_assn_def join_assn_def conj_assn_def inv_s'_def T_def C_def F_def by auto
          apply(rule conjI) subgoal unfolding pure_assn_def join_assn_def conj_assn_def inv_s'_def T_def C_def F_def by auto
          unfolding pure_assn_def join_assn_def conj_assn_def inv_s'_def T_def C_def F_def 
          apply(subgoal_tac"(min (9 / 200 - ss CHR ''t'') (2 / 100 - C_upd ent (ss CHR ''c''))) = 0")
          subgoal by (auto simp add: emp_assn_def)
          by auto 
        done
      done
    done
  subgoal 
    unfolding entails_def
    apply (rule allI)+
    apply(rule impI)
    subgoal for s tr
      apply(cases s)
      subgoal for a sss
        apply simp
        apply(erule disjE)
        subgoal apply(rule disjI1)
          apply auto
          subgoal for tt vv
            apply(rule exI[where x=tt])
            apply auto
            apply(rule exI[where x=vv])
            apply auto
            unfolding pure_assn_def join_assn_def conj_assn_def inv_s'_def T_def C_def F_def
            by auto
          done
        subgoal apply(rule disjI2)
          unfolding pure_assn_def join_assn_def conj_assn_def inv_s'_def T_def C_def F_def
          apply auto
          subgoal
           apply(cases "(9 / 200 - ss CHR ''t'') \<le>(2 / 100 - C_upd ent (ss CHR ''c''))")
            by auto
          subgoal
           apply(cases "(9 / 200 - ss CHR ''t'') \<le>(2 / 100 - C_upd ent (ss CHR ''c''))")
            by auto
          done
        done
      done
    done
   apply(rule Valid_cond_sp)
    apply simp
    apply(rule Valid_echoice[where R="\<lambda> s tr.(inv_s' (snd s) \<and> s =
          (Task WAIT eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) \<and> 
                   ((P (Task RUNNING ent tp, ss)) @\<^sub>t
         Wait\<^sub>t (min (0.045 - ss T) (0.02 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState
                (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>)))
          ({}, {preempt_ch 2}) @\<^sub>t
             Outrdy\<^sub>t (Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) (free_ch 2) 0 ({free_ch 2},{preempt_ch 2}))
         tr)
             \<or> (\<exists> v. (inv_s' (snd s) \<and> s =
          (Task WAIT eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)), F := v)) \<and> 
                   ((P (Task RUNNING ent tp, ss)) @\<^sub>t
         Wait\<^sub>t (min (0.045 - ss T) (0.02 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState
                (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>)))
          ({}, {preempt_ch 2}) @\<^sub>t
             Inrdy\<^sub>t (Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) (preempt_ch 2) v ({free_ch 2},{preempt_ch 2}))
         tr))"])
  subgoal for i
    apply(cases i)
    subgoal
      apply simp
      apply(rule exI[where x = "\<lambda> s tr.(inv_s' (snd s) \<and> s =
          (Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) \<and> 
                   ((P (Task RUNNING ent tp, ss)) @\<^sub>t
         Wait\<^sub>t (min (0.045 - ss T) (0.02 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState
                (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>)))
          ({}, {preempt_ch 2}) @\<^sub>t
             Outrdy\<^sub>t (Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) (free_ch 2) 0 ({free_ch 2},{preempt_ch 2}))
         tr)"])
      apply(rule conjI)
      subgoal
        apply(rule Valid_strengthen_post)
         prefer 2
         apply(rule Valid_basic_sp1)
        unfolding entails_def
        by auto
      subgoal unfolding entails_def
        apply (auto simp add:T_def C_def join_assn_def)
        subgoal for tr1 tr2
          apply(rule exI[where x= tr1])
          apply auto
          apply(rule exI[where x= tr2])
          apply auto
          apply rule
          done
        subgoal for d tr1 tr2
          apply(rule exI[where x= tr1])
          apply auto
          apply(rule exI[where x= tr2])
          apply auto
          apply rule
          by auto
        done
      done
    subgoal for i'
      apply simp
      apply(rule exI[where x="\<lambda> s tr.(\<exists> v. (inv_s' (snd s) \<and> s =
          (Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)), F := v)) \<and> 
                   ((P (Task RUNNING ent tp, ss)) @\<^sub>t
         Wait\<^sub>t (min (0.045 - ss T) (0.02 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState
                (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>)))
          ({}, {preempt_ch 2}) @\<^sub>t
             Inrdy\<^sub>t (Task RUNNING eone tp, ss
         (T := ss T + min (0.045 - ss T) (0.02 - C_upd ent (ss C)),
          C := C_upd ent (ss C) +
               min (0.045 - ss T) (0.02 - C_upd ent (ss C)))) (preempt_ch 2) v ({free_ch 2},{preempt_ch 2}))
         tr))"])
      apply(rule conjI)
      subgoal
        apply(rule Valid_ex_pre)
        subgoal for v
          apply(rule Valid_strengthen_post)
         prefer 2
         apply(rule Valid_basic_sp1)
        unfolding entails_def
        by auto
      done
    subgoal unfolding entails_def
      apply (auto simp add:T_def C_def F_def join_assn_def inv_s'_def)
      subgoal for tr1 tr2 v
        apply(rule exI[where x= v])
        apply auto
        apply(rule exI[where x= tr1])
        apply auto
        apply(rule exI[where x= tr2])
        apply auto
        apply rule
        done
      subgoal for d tr1 tr2 v
        apply(rule exI[where x= v])
        apply auto
        apply(rule exI[where x= tr1])
        apply auto
        apply(rule exI[where x= tr2])
        apply auto
        apply rule
        by auto
      done
    done
  done
  apply(rule Valid_skip)
  apply(rule allI)+
  apply(rule impI)
  apply(erule disjE)
  subgoal by auto
  apply(erule disjE)
  subgoal by auto
  apply(erule disjE)
  subgoal for s tr
    by (auto simp add:T_def C_def )
  subgoal for s tr
    by auto
  done
  
  


         
lemma Valid_T2_rep:
  "\<Turnstile> {\<lambda>s t. s = (Task st ent tp,ss) \<and> inv_s' (snd s) \<and> emp\<^sub>t t}
                      Rep T2
      {\<lambda>s t. inv_s' (snd s) \<and> (\<exists>n. (emp\<^sub>t @\<^sub>t T2_tr n (Task st ent tp,ss)) t)}"
  apply(rule Valid_rep')
  subgoal for n p
    apply(induction n arbitrary:p st ent tp ss)
    subgoal for p
      apply auto
      apply(rule Valid_strengthen_post)
       prefer 2
       apply(rule Valid_skip)
      unfolding entails_def by auto
    subgoal premises pre for n p st ent tp ss
      apply auto
      apply(cases st)
      subgoal
        apply simp
        apply(rule Valid_seq)
         apply(rule T2_Valid_WAIT)
        apply(rule Valid_strengthen_post)
         prefer 2
         apply(rule pre)
        unfolding entails_def by (auto simp add:join_assoc)
      subgoal
        apply simp
        apply(rule Valid_seq)
         apply(rule T2_Valid_READY)
        apply(rule Valid_pre_or)
        subgoal
          thm pre
          apply auto
          apply(rule Valid_weaken_pre[where P' = "\<lambda>s tr. \<exists>tt v . s = (Task RUNNING ent tp, ss(T := ss T + tt, F := v)) \<and> inv_s' (snd s) \<and>
               (((\<up>(0 \<le> tt \<and> tt \<le> 9 / 200 - ss T) \<and>\<^sub>t p @\<^sub>t Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                         Waitin\<^sub>t tt (\<lambda>t. EState (Task READY ent tp, ss(T := ss T + t)))
                          (run_ch 2) v ({}, {run_ch 2}))
                         tr)"])
          subgoal unfolding entails_def
            by(auto simp add: pure_assn_def conj_assn_def)
          apply(rule Valid_ex_pre)+
          apply(rule Valid_strengthen_post)
           prefer 2
           apply(rule pre)
          unfolding entails_def
          apply (auto simp add: join_disj_assn)
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(auto simp add: ex_assn_def pure_assn_def conj_assn_def join_assn_def)
          subgoal for tt v b tr2 tr1b tr2a tr2b
            apply(rule exI[where x="tr1b"])
            apply auto
            apply(rule exI[where x=v])
            apply(rule exI[where x=tt])
            by auto
          done
        apply(rule Valid_pre_or)
        subgoal
        apply(rule Valid_weaken_pre[where P'="\<lambda>s tr. 
                s = (Task WAIT ent tp, ss(T := 45 / 10 ^ 3)) \<and> inv_s' (snd s) \<and>
               ((p @\<^sub>t Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                Wait\<^sub>t (9 / 200 - ss T)
                 (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>))) ({}, {run_ch 2}) @\<^sub>t
                Outrdy\<^sub>t ((Task READY ent tp, ss(T := 45 / 10 ^ 3))) (exit_ch 2) 0 ({exit_ch 2},{run_ch 2}))
                tr"])
        subgoal unfolding entails_def by auto
        apply(rule Valid_strengthen_post)
           prefer 2
           apply(rule pre)
          unfolding entails_def
          apply (auto simp add: join_disj_assn)
          unfolding disj_assn_def
          apply(rule disjI2)
          by(auto simp add: join_assoc) 
        subgoal
          apply(rule Valid_ex_pre)
          subgoal for v
          apply(rule Valid_weaken_pre[where P'="\<lambda>s tr. 
                s = (Task RUNNING ent tp, ss(T := 45 / 10 ^ 3,F:=v)) \<and> inv_s' (snd s) \<and>
               ((p @\<^sub>t Out\<^sub>t (EState (Task READY ent tp, ss)) (req_ch 2) tp) @\<^sub>t
                Wait\<^sub>t (9 / 200 - ss T)
                 (\<lambda>\<tau>. EState (Task READY ent tp, ss(T := ss T + \<tau>))) ({}, {run_ch 2}) @\<^sub>t
                Inrdy\<^sub>t ((Task READY ent tp, ss(T := 45 / 10 ^ 3))) (run_ch 2) v ({exit_ch 2},{run_ch 2}))
                tr"])
        subgoal unfolding entails_def by auto
        apply(rule Valid_strengthen_post)
           prefer 2
         apply(rule pre)
          unfolding entails_def
          apply (auto simp add: join_disj_assn ex_assn_def)
          unfolding disj_assn_def
          apply(rule disjI2)+
          apply (auto simp add: join_assoc join_assn_def)
          subgoal for b tr2 tr1b tr2b tr1c tr2c
            apply(rule exI[where x= tr1b])
            apply auto
            apply(rule exI[where x= tr2b])
            apply auto
            apply(rule exI[where x= tr1c])
            apply auto
            done
          done
        done
      done
        subgoal
          apply simp
          apply(rule Valid_seq)
           apply(rule T2_Valid_RUNNING)
          apply(rule Valid_pre_or)
        subgoal
          thm pre
          apply auto
          apply(rule Valid_weaken_pre[where P' = "\<lambda>s tr. \<exists>tt v . s = (Task READY eone tp, ss
                         (CHR ''t'' := ss CHR ''t'' + tt,CHR ''c'' := C_upd ent (ss CHR ''c'') + tt, F := v)) \<and> inv_s' (snd s) \<and>
               ((\<up>(0 \<le> tt \<and> tt \<le> 9 / 200 - ss T \<and> tt \<le> 2 / 100 - C_upd ent (ss C)) 
                       \<and>\<^sub>t p @\<^sub>t Waitin\<^sub>t tt
                          (\<lambda>t. EState
                                (Task RUNNING eone tp, ss
                                 (CHR ''t'' := ss CHR ''t'' + t,
                                  CHR ''c'' := C_upd ent (ss CHR ''c'') + t)))
                          (preempt_ch 2) v ({}, {preempt_ch 2}))
                         tr)"])
          subgoal unfolding entails_def
            by(auto simp add: pure_assn_def conj_assn_def)
          apply(rule Valid_ex_pre)+
          apply(rule Valid_strengthen_post)
           prefer 2
           apply(rule pre)
          unfolding entails_def
          apply (auto simp add: join_disj_assn)
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(auto simp add: ex_assn_def pure_assn_def conj_assn_def join_assn_def T_def C_def)
          subgoal for tt v b tr1a tr2 tr2a
            apply(rule exI[where x="tr1a"])
            by auto
          done
        apply(rule Valid_pre_or)
        subgoal
        apply(rule Valid_weaken_pre[where P'="\<lambda>s tr. 
                s = (Task WAIT eone tp, ss
                (T := ss T + min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)),
                 C := C_upd ent (ss C) +
                      min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)))) \<and> inv_s' (snd s) \<and>
               ((p @\<^sub>t Wait\<^sub>t (min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>))) ({}, {preempt_ch 2}) @\<^sub>t
         Outrdy\<^sub>t ((Task RUNNING eone tp, ss(T := ss T + min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)),
              C := C_upd ent (ss C) + min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)))))(free_ch 2) 0 ({free_ch 2}, {preempt_ch 2}))
                tr)"])
        subgoal unfolding entails_def by auto
        apply(rule Valid_strengthen_post)
           prefer 2
           apply(rule pre)
          unfolding entails_def
          apply (auto simp add: join_disj_assn)
          unfolding disj_assn_def
          apply(rule disjI2)
          by(auto simp add: join_assoc) 
        subgoal
          apply(rule Valid_ex_pre)
          subgoal for v
            apply(rule Valid_weaken_pre[where P'="\<lambda>s tr. 
                s = (Task WAIT eone tp, ss
                (T := ss T + min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)),
                 C := C_upd ent (ss C) +
                      min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)),F:=v)) \<and> inv_s' (snd s) \<and>
               ((p @\<^sub>t Wait\<^sub>t (min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)))
          (\<lambda>\<tau>. EState (Task RUNNING eone tp, ss(T := ss T + \<tau>, C := C_upd ent (ss C) + \<tau>))) ({}, {preempt_ch 2}) @\<^sub>t
         Inrdy\<^sub>t ((Task RUNNING eone tp, ss(T := ss T + min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)),
              C := C_upd ent (ss C) + min (45 / 10 ^ 3 - ss T) (2 / 10\<^sup>2 - C_upd ent (ss C)))))(preempt_ch 2) v ({free_ch 2}, {preempt_ch 2}))
                tr)"])
        subgoal unfolding entails_def by auto
        apply(rule Valid_strengthen_post)
           prefer 2
           apply(rule pre)
          unfolding entails_def
          apply (auto simp add: join_disj_assn)
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule disjI2)
          apply(auto simp add: join_assoc ex_assn_def join_assn_def) 
          subgoal for b tr1a tr2 tr1b tr2b
            apply(rule exI[where x = tr1a])
            apply auto
            apply(rule exI[where x = tr1b])
            by auto
        done
      done
    done
  done
  done
  done



end