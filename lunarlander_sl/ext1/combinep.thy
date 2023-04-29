theory combinep
  imports combine2
begin


lemma Valid_T1_rep':
  "\<Turnstile> {\<lambda>(a,s) t. (a,s) = (Task WAIT ent 2, \<lambda>_. 0) \<and> emp\<^sub>t t}
                      Rep T1
      {\<lambda>(a,s) t. (\<exists>n. T1_tr n (Task WAIT ent 2, \<lambda>_. 0) t)}"
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
   apply(rule Valid_T1_rep)
  unfolding entails_def inv_s_def by auto


lemma Valid_T2_rep':
  "\<Turnstile> {\<lambda>(a,s) t. (a,s) = (Task WAIT ent 1, \<lambda>_. 0) \<and> emp\<^sub>t t}
                      Rep T2
      {\<lambda>(a,s) t. (\<exists>n. T2_tr n (Task WAIT ent 1, \<lambda>_. 0) t)}"
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
   apply(rule Valid_T2_rep)
  unfolding entails_def inv_s'_def by auto


lemma Valid_SCH_rep':
  "\<Turnstile> {\<lambda>(a,s) t. (a,s) = (Sch p rn rp,ss) \<and> emp\<^sub>t t}
                      Rep SCH
      {\<lambda>(a,s) t. (\<exists>n. SCH_tr n (Sch p rn rp,ss) t)}"
   apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
   apply(rule Valid_SCH_rep)
  unfolding entails_def by auto 



lemma g1:
"\<Turnstile>\<^sub>p {pair_assn  (\<lambda> (a,s). (a,s) = (Sch [] (-1) (-1),(\<lambda>_ . 0))) (\<lambda> (a,s). (a,s) = (Task WAIT ezero 2,(\<lambda>_ . 0)))}
      Parallel (Single (Rep SCH)) {req_ch 1, preempt_ch 1, run_ch 1, free_ch 1, exit_ch 1} (Single (Rep T1))
    {\<lambda> s tr. \<exists> n n1. combine1 n n1 (Sch [] (-1) (-1),(\<lambda>_ . 0)) (Task WAIT ezero 2,(\<lambda>_ . 0)) tr}"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel'[of "\<lambda> (a,s). (a,s) = (Sch [] (-1) (-1),(\<lambda>_ . 0))" _ _ "\<lambda>(a,s). (a, s) = (Task WAIT ezero 2, \<lambda>_. 0)"])
  apply clarify
     apply(rule Valid_SCH_rep')
    apply clarify
    apply(rule Valid_T1_rep')
  unfolding inv_s_def apply auto
  unfolding entails_gassn_def
  apply auto
  subgoal for s tr
    apply(cases s)
     apply auto
    subgoal for x21 x22 tr1 tr2
      apply(cases x21)
       apply(cases x22)
        apply auto
      subgoal for a1 b1 a2 b2 n n1
        apply(rule exI[where x=n])
        apply(rule exI[where x=n1])
        using combine_SCH_T1[of n1 "[]" "(- 1)" "(- 1)" WAIT ezero "\<lambda>_ . 0" n "\<lambda>_ . 0"]
        unfolding combine_assn_def entails_tassn_def propc_def proper_def properp_def inv_s_def
        by auto
      done
    done
  done

lemma ParValid_Single':
  assumes "\<Turnstile> {\<lambda>(a,s) tr. P (a,s) \<and> emp\<^sub>t tr} c {Q}"
  shows "\<Turnstile>\<^sub>p {sing_assn P} Single c {sing_gassn Q}"
  using assms unfolding ParValid_def Valid_def emp_assn_def
  by (smt (z3) SingleE append_self_conv2 case_prodI2' sing_assn.simps(1) sing_gassn.simps(1))

      
lemma g2:
 "\<Turnstile>\<^sub>p {par_assn (par_assn (sing_assn (\<lambda>(a, s). a = Sch [] (- 1) (- 1) \<and> s = (\<lambda>_. 0)))
                          (sing_assn (\<lambda>(a, s). a = Task WAIT ezero 2 \<and> s = (\<lambda>_. 0)))) 
                (sing_assn (\<lambda>(a, s). a = Task WAIT ezero 1 \<and> s = (\<lambda>_. 0)))} 
       Parallel (Parallel (Single (Rep SCH)) {req_ch 1, preempt_ch 1, run_ch 1, free_ch 1, exit_ch 1} 
                          (Single (Rep T1)))
                {req_ch 2, preempt_ch 2, run_ch 2, free_ch 2, exit_ch 2} 
                (Single (Rep T2)) 
      {\<lambda> s tr. \<exists> n n1 n2. combine2 n n1 n2 (Sch [] (- 1) (- 1),(\<lambda>_.0)) (Task WAIT ezero 2,(\<lambda>_.0)) (Task WAIT ezero 1,(\<lambda>_. 0)) tr}"
  apply (rule ParValid_conseq')
  apply(rule ParValid_Parallel)
     apply(rule g1)
    apply(rule ParValid_Single')
    apply(rule Valid_T2_rep'[of ezero])
  subgoal premises pre for s
  proof-
    have 1:"(\<lambda>a. a = (Task WAIT ezero 1, \<lambda>_. 0)) = (\<lambda>(a, s). a = Task WAIT ezero 1 \<and> s = (\<lambda>_. 0))"
      apply(rule ext)
      by auto
    show ?thesis
      apply(subst 1) using pre unfolding pair_assn_def by auto
  qed
  unfolding entails_gassn_def
  apply auto
  subgoal for s tr
    apply (cases s)
     apply auto
    subgoal for x21 x22 tr1 n tr2 n1
      apply(cases x22)
       apply auto
      subgoal for a b n2
      apply(rule exI[where x= n])
      apply(rule exI[where x= n1])
        apply(rule exI[where x= n2])
        using combine_SCH_T1_T2[of n1 "[]" "(- 1)" "(- 1)" WAIT ezero n2 WAIT ezero "\<lambda>_.0" "\<lambda>_.0" n "\<lambda>_.0"]
        unfolding propc_def propc'_def proper'_def properp_def inv_s_def inv_s'_def
        apply auto
        unfolding entails_tassn_def combine_assn_def by auto
      done
    done
  done


      
   
    





end