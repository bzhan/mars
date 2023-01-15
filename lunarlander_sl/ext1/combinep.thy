theory combinep
  imports combine2
begin


lemma Valid_T1_rep':
  "\<Turnstile> {\<lambda>s t. s = (Task st ent tp,ss) \<and> inv_s (snd s) \<and> emp\<^sub>t t}
                      Rep T1
      {\<lambda>s t. (\<exists>n. T1_tr n (Task st ent tp,ss) t)}"
  apply(rule Valid_strengthen_post)
  prefer 2
   apply(rule  Valid_T1_rep)
  unfolding entails_def by auto


lemma Valid_T2_rep':
  "\<Turnstile> {\<lambda>s t. s = (Task st ent tp,ss) \<and> inv_s' (snd s) \<and> emp\<^sub>t t}
                      Rep T2
      {\<lambda>s t. (\<exists>n. T2_tr n (Task st ent tp,ss) t)}"
  apply(rule Valid_strengthen_post)
  prefer 2
   apply(rule  Valid_T2_rep)
  unfolding entails_def by auto


lemma Valid_SCH_rep':
  "\<Turnstile> {\<lambda>s t. s = (Sch p rn rp,ss) \<and> emp\<^sub>t t}
                      Rep SCH
      {\<lambda>s t. (\<exists>n. SCH_tr n (Sch p rn rp,ss) t)}"
  using Valid_SCH_rep by auto


lemma g1:
"\<Turnstile>\<^sub>p {pair_assn  (\<lambda> (a,s). (a,s) = (Sch [] (-1) (-1),(\<lambda>_ . 0))) (\<lambda> (a,s). (a,s) = (Task st ent 2,(\<lambda>_ . 0)))}
      Parallel (Single (Rep SCH)) {req_ch 1, preempt_ch 1, run_ch 1, free_ch 1, exit_ch 1} (Single (Rep T1))
    {sync_gassn {req_ch 1, preempt_ch 1, run_ch 1, free_ch 1, exit_ch 1} 
      (sing_gassn (\<lambda> s tr. \<exists>n. (SCH_tr n (Sch [] (-1) (-1),(\<lambda>_ . 0)) tr))) (sing_gassn (\<lambda> s tr. \<exists>n. (T1_tr n (Task st ent 2,(\<lambda>_ . 0)) tr)))}"
  apply(rule ParValid_Parallel')
  subgoal 
    apply(rule Valid_weaken_pre) 
     prefer 2 
     apply(rule Valid_SCH_rep') unfolding entails_def
    by auto
  subgoal 
    apply(rule Valid_weaken_pre) 
     prefer 2 
     apply(rule Valid_T1_rep') unfolding entails_def
    unfolding inv_s_def
    by auto
  done





end