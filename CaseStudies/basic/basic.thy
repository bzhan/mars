theory basic
  imports
    HHLProver.ContinuousInv
    HHLProver.BigStepParallel
    basicprime
begin


lemma b1:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0}
     X ::= (\<lambda>s . s X + 1)
   {\<lambda>s tr. s X \<ge> 1}"
  apply (rule Valid_strengthen_post)
  prefer 2
   apply (rule Valid_assign_sp)
  unfolding entails_def by auto


lemma b2:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0}
     X ::= (\<lambda>s . s X + 1);
     IChoice (X ::= (\<lambda>s . s X + 1)) (Y ::= (\<lambda>s . s X + 1))
   {\<lambda>s tr. s X \<ge> 1}"
  apply (rule Valid_seq)
   apply (rule Valid_assign_sp)
  apply(rule Valid_ichoice_sp_st)
  subgoal
apply (rule Valid_strengthen_post)
  prefer 2
    apply (rule Valid_assign_sp)
    unfolding entails_def by auto
apply (rule Valid_strengthen_post)
  prefer 2
    apply (rule Valid_assign_sp)
  unfolding entails_def by auto


lemma b3:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0}
     X ::= (\<lambda>s . s X + 1);
     Rep (X ::= (\<lambda>s . s X + 1)) 
   {\<lambda>s tr. s X \<ge> 1}"
  apply (rule Valid_seq)
   prefer 2
  apply(rule Valid_rep)
 subgoal
apply (rule Valid_strengthen_post)
  prefer 2
    apply (rule Valid_assign_sp)
    unfolding entails_def by auto
apply (rule Valid_strengthen_post)
  prefer 2
    apply (rule Valid_assign_sp)
  unfolding entails_def by auto


lemma b4:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0}
     X ::= (\<lambda>s . s X + 1);
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. 2, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
   {\<lambda>s tr. s X \<ge> 1}"
  apply (rule Valid_seq)
   apply (rule Valid_strengthen_post)
  prefer 2
    apply(rule Valid_assign_sp)
   prefer 2
   apply(rule Valid_inv_s_ge)
    apply clarify
 unfolding vec2state_def
     apply (fast intro!: derivative_intros)
    apply (auto simp add: vec2state_def state2vec_def)
  apply (auto simp add:entails_def)
  done


lemma b5:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0}
     X ::= (\<lambda>s . s X + 1);
     X ::= (\<lambda>s . SOME k. k \<ge> 1)
   {\<lambda>s tr. s X \<ge> 1}"
  apply(rule Valid_seq)
   apply(rule Valid_assign_sp)
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_assign_sp)
  apply(auto simp add: entails_def)
  using someI 
  by (metis one_le_exp_iff)


lemma b7:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0 \<and> s Y \<ge> 1 \<and> s T = 0}
     X ::= (\<lambda>s . s X + 1);
     IChoice (Rep(X ::= (\<lambda>s . s X + 1))) (Y ::= (\<lambda>s . s X + 1));
     Cont (ODE ((\<lambda>_ _. 0)(Y := \<lambda>s. 2, T := \<lambda>s. 1))) (\<lambda>s. s T < P);
     X ::= (\<lambda>s . s Y)
   {\<lambda>s tr. s X \<ge> 1}"
 apply (rule Valid_seq)
   apply(rule Valid_assign_sp)
  apply (rule Valid_seq)
   apply(rule Valid_ichoice_sp)
    apply(rule Valid_weaken_pre)
  prefer 2
     apply(rule Valid_rep[of "\<lambda>s tr. s X \<ge>1 \<and> s Y \<ge> 1"])
     apply (rule Valid_strengthen_post)
  prefer 2
      apply(rule Valid_assign_sp)
     apply(auto simp add: entails_def)
   apply(rule Valid_assign_sp)
  apply(rule Valid_seq)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_s_ge[where inv = "\<lambda>s. s Y" and r = 1])
     apply clarify
  unfolding vec2state_def
     apply (fast intro!: derivative_intros)
    apply (auto simp add:state2vec_def entails_def)
  apply (rule Valid_strengthen_post)
  prefer 2
apply(rule Valid_assign_sp)
  apply(auto simp add: entails_def)
  done


lemma b8:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0 \<and> s Y \<ge> 0 \<and> s T = 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. 5, T := \<lambda>s. 1))) (\<lambda>s. s T < P);
     IChoice (Rep(X ::= (\<lambda>s . s X + 3))) (Y ::= (\<lambda>s . s X))
 {\<lambda>s tr. s X \<ge> 0 \<and> s Y \<ge> 0}"
  apply(rule Valid_seq)
   apply(rule Valid_post_and)
    apply(rule Valid_weaken_pre)
  prefer 2
     apply(rule Valid_inv_s_ge[where inv = "\<lambda>s. s X" and r = 0])
apply clarify
  unfolding vec2state_def
      apply (fast intro!: derivative_intros)
     apply (auto simp add:state2vec_def entails_def)
apply(rule Valid_weaken_pre)
  prefer 2
     apply(rule Valid_inv_s_ge[where inv = "\<lambda>s. s Y" and r = 0])
apply clarify
  unfolding vec2state_def
      apply (fast intro!: derivative_intros)
    apply (auto simp add:state2vec_def entails_def)
  apply(rule Valid_ichoice_sp_st)
   apply(rule Valid_rep)
    apply (rule Valid_strengthen_post)
  prefer 2
apply(rule Valid_assign_sp)
   apply(auto simp add: entails_def)
 apply (rule Valid_strengthen_post)
  prefer 2
apply(rule Valid_assign_sp)
  apply(auto simp add: entails_def)
  done


lemma b9:
  "\<Turnstile> {\<lambda>s tr. s X > 0 \<and> s Y > 0 \<and> s T = 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P);
     IChoice (Rep(X ::= (\<lambda>s . s X + 3))) (Y ::= (\<lambda>s . s X))
 {\<lambda>s tr. s X > 0 \<and> s Y > 0}"
  apply(rule Valid_seq)
apply(rule Valid_post_and)
    apply(rule Valid_weaken_pre)
     prefer 2
     apply(rule exp_1)
     apply(auto simp add: entails_def)
apply(rule Valid_weaken_pre)
  prefer 2
    apply(rule Valid_inv_s_g[where inv = "\<lambda>s. s Y" and r = 0])
apply clarify
  unfolding vec2state_def
     apply (fast intro!: derivative_intros)
 apply (auto simp add:state2vec_def entails_def)
  apply(rule Valid_weaken_pre)
   prefer 2
 apply(rule Valid_ichoice_sp_st)
   apply(rule Valid_rep)
    apply (rule Valid_strengthen_post)
  prefer 2
     apply(rule Valid_assign_sp)
    prefer 2
apply (rule Valid_strengthen_post)
  prefer 2
     apply(rule Valid_assign_sp)
    apply(auto simp add: entails_def)
  done


lemma b10:
  "\<Turnstile> {\<lambda>s tr. s X > 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. 5, T := \<lambda>s. 1))) (\<lambda>s. s T < P1);
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. 2, T := \<lambda>s. 1))) (\<lambda>s. s T < P2);
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P3)
 {\<lambda>s tr. s X > 0 }"
  apply(rule Valid_seq)
    apply(rule Valid_inv_s_g[where inv = "\<lambda>s. s X" and r = 0])
     apply clarify
     apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
    apply(auto simp add: state2vec_def entails_def)
  apply(rule Valid_seq)
    apply(rule Valid_inv_s_g[where inv = "\<lambda>s. s X" and r = 0])
     apply clarify
     apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
    apply(auto simp add: state2vec_def entails_def)
  apply(rule exp_2)
  done


lemma b11:
  "\<Turnstile> {\<lambda>s tr. s X = 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. 1, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X \<ge> 0}"
  apply(rule Valid_weaken_pre)
  prefer 2
apply(rule Valid_inv_s_ge[where inv = "\<lambda>s. s X" and r = 0])
     apply clarify
     apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
   apply(auto simp add: state2vec_def entails_def)
  done


lemma b12:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0 \<and> s Y \<ge> 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s Y, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X \<ge> 0}"
  apply(rule Valid_pre_cases[where Q = "(\<lambda>s. s T < P)"])
   prefer 2
   apply(rule Valid_ode_not)
    apply auto
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
    apply(rule DC'[where P = "\<lambda>tr. True" and init = "\<lambda>s . 0 \<le> s X \<and> 0 \<le> s Y" and c = "\<lambda>s. s Y \<ge>0" and d = "\<lambda>s . s X \<ge>0"])
     apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
      apply(auto simp add:state2vec_def)
    prefer 2
apply(rule Valid_weaken_pre)
      prefer 2
     apply(rule Valid_inv_s_tr_ge)
apply clarify
       apply(simp add:vec2state_def)
      apply (fast intro!: derivative_intros)
     apply(auto simp add:state2vec_def entails_def)
  done


lemma b13:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0 \<and> s Y \<ge> 0 \<and> s Z \<ge> 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s Y, Y := \<lambda>s. s Z, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X \<ge> 0}"
apply(rule Valid_pre_cases[where Q = "(\<lambda>s. s T < P)"])
   prefer 2
   apply(rule Valid_ode_not)
    apply auto
apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
    apply(rule DC'[where P = "\<lambda>tr. True" and init = "\<lambda>s . 0 \<le> s X \<and> 0 \<le> s Y \<and> s Z \<ge> 0" and c = "\<lambda>s. s Y \<ge>0" and d = "\<lambda>s . s X \<ge>0"])
     apply(auto simp add: entails_def)
apply(rule Valid_strengthen_post)
   prefer 2
apply(rule Valid_weaken_pre)
  prefer 2
 apply(rule DC'[where P = "\<lambda>tr. True" and init = "\<lambda>s . 0 \<le> s X \<and> 0 \<le> s Y \<and> s Z \<ge> 0" and c = "\<lambda>s. s Z \<ge>0" and d = "\<lambda>s . s Y \<ge>0"])
      apply(auto simp add: entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
     apply(auto simp add:state2vec_def entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
    apply(auto simp add:state2vec_def entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  done


lemma b14:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0 \<and> s Y \<ge> 0 \<and> s Z \<ge> 0 \<and> s J \<ge> 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s Y, Y := \<lambda>s. s Z, Z := \<lambda>s. s J, J := \<lambda> s. (s J)^2, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X \<ge> 0}"
apply(rule Valid_pre_cases[where Q = "(\<lambda>s. s T < P)"])
   prefer 2
   apply(rule Valid_ode_not)
    apply auto     
apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
    apply(rule DC'[where P = "\<lambda>tr. True" and init = "\<lambda>s . 0 \<le> s X \<and> 0 \<le> s Y \<and> s Z \<ge> 0 \<and> s J \<ge> 0" and c = "\<lambda>s. s Y \<ge>0" and d = "\<lambda>s . s X \<ge>0"])
     apply(auto simp add: entails_def)
apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
    apply(rule DC'[where P = "\<lambda>tr. True" and init = "\<lambda>s . 0 \<le> s X \<and> 0 \<le> s Y \<and> s Z \<ge> 0 \<and> s J \<ge> 0" and c = "\<lambda>s. s Z \<ge>0" and d = "\<lambda>s . s Y \<ge>0"])
      apply(auto simp add: entails_def)
apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
    apply(rule DC'[where P = "\<lambda>tr. True" and init = "\<lambda>s . 0 \<le> s X \<and> 0 \<le> s Y \<and> s Z \<ge> 0 \<and> s J \<ge> 0" and c = "\<lambda>s. s J \<ge>0" and d = "\<lambda>s . s Z \<ge>0"])
       apply(auto simp add: entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
      apply(auto simp add:state2vec_def entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
     apply(auto simp add:state2vec_def entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
    apply(auto simp add:state2vec_def entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  done


lemma b15:
 "\<Turnstile> {\<lambda>s tr. s X > 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  using exp_1 by auto


lemma b16:
 "\<Turnstile> {\<lambda>s tr. s X > 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s X + 1, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  using exp_3 by auto


lemma b17:
 "\<Turnstile> {\<lambda>s tr. s X > 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s Y * s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  using exp_4 by auto


lemma b18:
 "\<Turnstile> {\<lambda>s tr. s X \<ge> 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X , T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X \<ge> 0}"
  using exp_5 by auto


lemma b19:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0 \<and> s Y \<ge> 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s Y, Y := \<lambda>s. s Y ^ 2, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X \<ge> 0}"
  apply(rule Valid_pre_cases[where Q = "(\<lambda>s. s T < P)"])
   prefer 2
   apply(rule Valid_ode_not) apply auto
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
    apply(rule DC'[where P = "\<lambda>tr. True" and init = "\<lambda>s . 0 \<le> s X \<and> 0 \<le> s Y " and c = "\<lambda>s. s Y \<ge>0" and d = "\<lambda>s . s X \<ge>0"])
     apply(auto simp add: entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
      apply(auto simp add:state2vec_def entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
       apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  done


lemma b21:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 1}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X ^ 2 + 2 * (s X ^ 4), T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X ^ 3 - s X ^ 2 \<ge> 0}"
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_inv_s_ge)
apply clarify
       apply(simp add:vec2state_def)
       apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  by (simp add: power_increasing)


lemma b22:
  "\<Turnstile> {\<lambda>s tr. s X ^ 2 + s Y ^ 2 = 1}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s Y, Y := \<lambda> s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X ^ 2 + s Y ^ 2 = 1}"
  apply(rule Valid_inv_s_eq)
apply clarify
       apply(simp add:vec2state_def)
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done


lemma b23:
  "\<Turnstile> {\<lambda>s tr. s X ^ 2 + s Y ^ 2 = 1 \<and> s Z - s X = 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s Y, Y := \<lambda> s. s X, Z := \<lambda> s. - s Y, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X ^ 2 + s Y ^ 2 = 1 \<and> s Z - s X = 0}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
apply(rule Valid_inv_s_eq)
apply clarify
       apply(simp add:vec2state_def)
   apply (fast intro!: derivative_intros)
    apply(simp add:state2vec_def entails_def)
   prefer 2
apply(rule Valid_weaken_pre)
    prefer 2
apply(rule Valid_inv_s_eq)
apply clarify
       apply(simp add:vec2state_def)
   apply (fast intro!: derivative_intros)
    apply(auto simp add:state2vec_def entails_def)
  done


lemma b24:
  "\<Turnstile> {\<lambda>s tr. s Z ^ 2 + s J ^ 2 - s L ^ 2 * s M ^ 2 = 0 \<and> s Z + s L * s Y = 0 \<and> s J - s L * s X = 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s Z, Y := \<lambda> s. s J, Z := \<lambda> s. - s L * s J, J := \<lambda> s. s L * s Z , T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s Z ^ 2 + s J ^ 2 - s L ^ 2 * s M ^ 2 = 0 \<and> s Z + s L * s Y = 0 \<and> s J - s L * s X = 0}"
  apply(rule Valid_post_and)
  apply(rule Valid_weaken_pre)
    prefer 2
apply(rule Valid_inv_s_eq)
apply clarify
       apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
    apply(simp add:state2vec_def entails_def)
  prefer 2
 apply(rule Valid_post_and)
  apply(rule Valid_weaken_pre)
    prefer 2
apply(rule Valid_inv_s_eq)
apply clarify
       apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
     apply(simp add:state2vec_def entails_def)
    prefer 2
 apply(rule Valid_weaken_pre)
    prefer 2
apply(rule Valid_inv_s_eq)
apply clarify
       apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
     apply(auto simp add:state2vec_def entails_def)
  done


lemma b25:
  "\<Turnstile> {\<lambda>s tr. s Z \<ge> 0 \<and>  s X = 0  \<and>  s Y = 3}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s Y, Y := \<lambda> s. - s X * s Z ^ 2 - 2 * s Z * s Y, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s Z ^ 2 * s X ^ 2 + s Y ^ 2 \<le> 9 }"
apply(rule Valid_pre_cases[where Q = "(\<lambda>s. s T < P)"])
   prefer 2
   apply(rule Valid_ode_not) apply auto
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_weaken_pre)
  prefer 2
    apply(rule DC'[where P = "\<lambda>tr. True" and init = "\<lambda>s . s Z \<ge> 0 \<and>  s X = 0  \<and>  s Y = 3 " and c = "\<lambda>s. s Z \<ge>0" and d = "\<lambda> s. s Z ^ 2 * s X ^ 2 + s Y ^ 2 \<le> 9"])
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_ge)
apply clarify
       apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
      apply(auto simp add:state2vec_def entails_def)
apply(rule Valid_weaken_pre)
      prefer 2
      apply(rule Valid_inv_s_tr_le)
apply clarify
       apply(simp add:vec2state_def)
    apply (fast intro!: derivative_intros)
 apply(auto simp add:state2vec_def entails_def algebra_simps power_add power2_eq_square power4_eq_xxxx)
  by (simp add: vector_space_over_itself.scale_scale)


lemma b26:
  "\<Turnstile> {\<lambda>s tr. s X ^ 3 > 5  \<and>  s Y > 2}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X ^ 3 + s X ^ 4, Y := \<lambda> s. 5 * s Y + s Y ^ 2, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X ^ 3 > 5  \<and>  s Y > 2 }"    
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
  apply(rule Valid_inv_new_s_g)
apply clarify
       apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
    apply(auto simp add:state2vec_def entails_def)
   apply (simp add: power3_eq_cube)
apply(rule Valid_weaken_pre)
    prefer 2
  apply(rule Valid_inv_new_s_g)
apply clarify
       apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  done


lemma b27:
 "\<Turnstile> {\<lambda>s tr. s X \<ge> 1  \<and> s Y = 10 \<and> s Z = -2}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s Y, Y := \<lambda> s. s Z + s Y ^ 2 - s Y))) (\<lambda>s. s Y > 0)
 {\<lambda>s tr. s X \<ge> 1  \<and>  s Y \<ge> 0 }"
  apply(rule Valid_post_and)
  subgoal
   apply(rule Valid_weaken_pre)
     prefer 2
     apply(rule Valid_inv_s_ge)
apply clarify
       apply(simp add:vec2state_def)
      apply (fast intro!: derivative_intros)
     apply(auto simp add:state2vec_def entails_def)
    done
  apply(rule Valid_weaken_pre)
   prefer 2
   apply(rule Valid_strengthen_post)
    prefer 2
    apply(rule Valid_inv_b_s_ge)
apply clarify
       apply(simp add:vec2state_def)
    apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  done


lemma b28:
 "\<Turnstile> {\<lambda>s tr. s X ^ 4 * s Y ^ 2 + s X ^ 2 * s Y ^ 4 - 3 * s X ^ 2 * s Y ^ 2 + 1 \<le> c}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. 2 * s X ^ 4 * s Y + 4 * s X ^ 2 * s Y ^ 3 - 6 * s X ^ 2 * s Y, 
       Y := \<lambda> s. - 4 * s X ^ 3 * s Y ^ 2 - 2 * s X * s Y ^ 4  + 6 * s X * s Y ^ 2, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X ^ 4 * s Y ^ 2 + s X ^ 2 * s Y ^ 4 - 3 * s X ^ 2 * s Y ^ 2 + 1 \<le> c}"
  apply(rule Valid_inv_s_le)
apply clarify
       apply(simp add:vec2state_def)
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def algebra_simps power2_eq_square power4_eq_xxxx)
  done


lemma b29:
  "\<Turnstile> {\<lambda>s tr. s X + s Z = 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. A * s X ^ 2 + B * s X, Z := \<lambda> s. A * s Z * s X + B * s Z, T := \<lambda> s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X + s Z = 0 }"
  apply(rule Valid_dbx_s_eq[where g = "\<lambda> s. A * s X + B"])
apply clarify
apply(simp add:vec2state_def)
    apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def power2_eq_square algebra_simps)
  apply(auto simp add:  continuous_on_eq_continuous_within , intro continuous_intros)
  apply(auto simp add:  vec2state_def )
  done


lemma b31:
  "\<Turnstile> {\<lambda>s tr. s X + s Z \<ge> 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X ^ 2, Z := \<lambda> s. s Z * s X + s Y))) (\<lambda>s. s Y > s X ^ 2)
 {\<lambda>s tr. s X + s Z \<ge> 0 }"
  apply(rule Valid_dbxg_s_ge[where g = "\<lambda> s. s X"])
    apply clarify
    apply(simp add:vec2state_def)
    apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def power2_eq_square algebra_simps)
  apply (smt zero_le_square)
  apply(auto simp add: continuous_on_eq_continuous_within  vec2state_def)
  done


lemma b32:
  assumes "r\<le>0"
  shows "\<exists> f . \<Turnstile> {\<lambda>s tr. s X  = f}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . r + s X ^ 2, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X  = f }"
  apply(rule exI[where x = "sqrt(-r)"])
   apply(rule Valid_weaken_pre[where P' = "\<lambda>s tr. s X - sqrt (- r) = 0"])
   prefer 2
   apply(rule Valid_strengthen_post)
    prefer 2
  apply(rule Valid_dbx_s_eq[where g="\<lambda> s. s X + sqrt(- r)"])
apply clarify
apply(simp add:vec2state_def)
    apply (fast intro!: derivative_intros)
apply(auto simp add:state2vec_def algebra_simps assms power2_eq_square)
apply(auto simp add:  continuous_on_eq_continuous_within , intro continuous_intros)
  apply(auto simp add:  vec2state_def )
  done


lemma b33:
  assumes "a^2 \<le> 4"
      and "b^2 \<ge> 1/3"
    shows "\<Turnstile> {\<lambda>s tr. s L \<ge> 0 \<and> s M \<ge> 0 \<and> s L ^ 2 * s X ^ 2 + s Y ^ 2 - s N \<le> 0}
Rep(
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>s. - (s L ^ 2) * s X - 2 * s M * s L * s Y))) Con;
IF (\<lambda> s . s X = s Y * a) THEN (L ::= (\<lambda> s. 2 * s L) ; M ::= (\<lambda> s. 1/2 * s M); N ::= (\<lambda> s. s N * (4 * s L ^ 2 + 1)/(s L ^ 2 + 1))) ELSE 
IF (\<lambda> s . s X = s Y * b) THEN (L ::= (\<lambda> s. 1/2 * s L) ; M ::= (\<lambda> s. 2 * s M); N ::= (\<lambda> s. s N * (s L ^ 2 + 1)/(2 * s L ^ 2 + 1))) ELSE 
Skip FI
FI
)
 {\<lambda>s tr. s L ^ 2 * s X ^ 2 + s Y ^ 2 - s N \<le> 0}"
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_rep)
   apply(rule Valid_seq[where Q = "\<lambda>s tr. 0 \<le> s L \<and> 0 \<le> s M \<and> (s L)\<^sup>2 * (s X)\<^sup>2 + (s Y)\<^sup>2 - s N \<le> 0"])
  subgoal
    apply(rule Valid_pre_cases[where Q = Con])
    subgoal
    apply(rule Valid_weaken_pre)
     prefer 2
     apply(rule DC'''[where init ="\<lambda> s. 0 \<le> s L \<and> 0 \<le> s M \<and> (s L)\<^sup>2 * (s X)\<^sup>2 + (s Y)\<^sup>2 - s N \<le> 0" and P = "\<lambda> tr . True"])
  subgoal 
    apply(rule Valid_weaken_pre)
     prefer 2
     apply(rule Valid_inv_tr_ge)
apply clarify
apply(simp add:vec2state_def)
      apply (fast intro!: derivative_intros)
     apply(auto simp add:state2vec_def entails_def)
    done
 apply(rule Valid_weaken_pre)
     prefer 2
apply(rule DC'''[where init ="\<lambda> s. 0 \<le> s L \<and> 0 \<le> s M \<and> (s L)\<^sup>2 * (s X)\<^sup>2 + (s Y)\<^sup>2 - s N \<le> 0" and P = "\<lambda> tr . True"])
  subgoal 
    apply(rule Valid_weaken_pre)
     prefer 2
     apply(rule Valid_inv_tr_ge)
apply clarify
apply(simp add:vec2state_def)
      apply (fast intro!: derivative_intros)
     apply(auto simp add:state2vec_def entails_def)
    done
apply(rule Valid_weaken_pre)
       prefer 2
       apply(rule Valid_inv_s_le)
apply clarify
apply(simp add:vec2state_def)
      apply (fast intro!: derivative_intros)
       apply(auto simp add:state2vec_def algebra_simps)
  apply(auto simp add: entails_def)
  done
  apply(rule Valid_ode_not)
  apply auto
  done
  subgoal
    apply(rule Valid_cond_split)
    subgoal
      apply(rule Valid_seq)
       apply(rule Valid_assign_sp)
 apply(rule Valid_seq)
       apply(rule Valid_assign_sp)
      apply(rule Valid_strengthen_post)
       prefer 2
       apply(rule Valid_assign_sp)
      apply(auto simp add: entails_def)
      apply(subgoal_tac "(4 * xa\<^sup>2 * (s Y * a)\<^sup>2 + (s Y)\<^sup>2) * ((4 * xa\<^sup>2 + 1)) \<le> x * (16 * xa\<^sup>2 + 1)")
       apply (smt pos_divide_less_eq zero_less_power zero_power2)
      apply(subgoal_tac "(4 * xa\<^sup>2 * (s Y * a)\<^sup>2 + (s Y)\<^sup>2) * ((4 * xa\<^sup>2 + 1)) \<le> (xa\<^sup>2 * (s Y * a)\<^sup>2 + (s Y)\<^sup>2) * (16 * xa\<^sup>2 + 1)")
       apply (smt power2_less_0 real_mult_less_iff1)
      apply(auto simp add: algebra_simps )
      apply(subgoal_tac "xa\<^sup>2 * (a\<^sup>2 * (s Y)\<^sup>2) = a\<^sup>2 * (xa\<^sup>2 * (s Y)\<^sup>2) ")
      prefer 2 
      using mult.left_commute apply blast
      apply(subgoal_tac "a\<^sup>2 * (xa\<^sup>2 * (s Y)\<^sup>2) \<le> 4 * (xa\<^sup>2 * (s Y)\<^sup>2) ")
       apply linarith
      apply(subgoal_tac "0 \<le> (xa\<^sup>2 * (s Y)\<^sup>2) ")
      using mult_right_mono 
      using assms(1) apply blast
      by simp
subgoal
    apply(rule Valid_cond_split)
    subgoal
      apply(rule Valid_seq)
       apply(rule Valid_assign_sp)
 apply(rule Valid_seq)
       apply(rule Valid_assign_sp)
      apply(rule Valid_strengthen_post)
       prefer 2
       apply(rule Valid_assign_sp)
      apply(auto simp add: entails_def)
      apply(subgoal_tac "((s L)\<^sup>2 * (s Y * b)\<^sup>2 + (s Y)\<^sup>2) * (2 * (s L)\<^sup>2 + 1) \<le> x * ((s L)\<^sup>2 + 1)")
       apply (smt pos_divide_less_eq zero_less_power zero_power2)
      apply(subgoal_tac "((s L)\<^sup>2 * (s Y * b)\<^sup>2 + (s Y)\<^sup>2) * (2 * (s L)\<^sup>2 + 1) \<le> ((s L)\<^sup>2 * 4 * (s Y * b)\<^sup>2 + (s Y)\<^sup>2)* ((s L)\<^sup>2 + 1) ")
       apply (smt power2_less_0 real_mult_less_iff1)
      apply(auto simp add: algebra_simps )
      apply(subgoal_tac "3 * (b\<^sup>2 * ((s L)\<^sup>2 * (s Y)\<^sup>2)) \<ge> (s L)\<^sup>2 * (s Y)\<^sup>2 ")
       apply(subgoal_tac "2 * (b\<^sup>2 * ((s Y)\<^sup>2 * s L ^ 4)) \<ge> 0")
        apply linarith
       apply simp
      apply(subgoal_tac "3 * (b\<^sup>2 * ((s L)\<^sup>2 * (s Y)\<^sup>2)) = (3 * b\<^sup>2) * ((s L)\<^sup>2 * (s Y)\<^sup>2)")      
      apply(subgoal_tac "(s L)\<^sup>2 * (s Y)\<^sup>2 \<ge> 0 ")
      using assms
      using mult_right_mono 
      apply (metis divide_eq_eq_numeral1(1) divide_le_eq_numeral1(1) mult_cancel_right1 nonzero_mult_div_cancel_left zero_neq_numeral)
       apply simp
      by linarith
apply(rule Valid_strengthen_post)
       prefer 2
     apply(rule Valid_skip)
    apply(auto simp add:entails_def)
    done
  done
  apply(auto simp add:entails_def)
  done


lemma b34:
  assumes "a\<ge>0"
  shows" \<Turnstile> {\<lambda>s tr. s X ^ 3 \<ge> -1}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . (s X - 3) ^ 4 + a, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X ^ 3 \<ge> -1 }"
  apply(rule Valid_inv_s_ge)
apply clarify
       apply(simp add:vec2state_def)
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  using assms by auto

lemma b35:
"\<Turnstile> {\<lambda>s tr. s X + 1/2 * s Y ^ 2 =  a}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s X * s Y, Y := \<lambda> s. - s X , T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X + 1/2 * s Y ^ 2 =  a }"
  apply(rule Valid_inv_s_eq)
   apply clarify
  unfolding vec2state_def
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done


lemma b36:
"\<Turnstile> {\<lambda>s tr. 1/2 * s X ^ 2 - 1/2 * s Y ^ 2 >=  a}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y + s X * s Y ^ 2, Y := \<lambda> s. - s X + s X ^ 2 * s Y))) (\<lambda>s. s X > 0 \<and> s Y > 0)
 {\<lambda>s tr. 1/2 * s X ^ 2 - 1/2 * s Y ^ 2 >=  a }"
  apply(rule Valid_pre_cases [where Q =  "(\<lambda>s. s X > 0 \<and> s Y > 0)"])
   prefer 2 
  subgoal
   apply(rule Valid_ode_not)
     apply auto
    done
  subgoal
  apply(rule Valid_weaken_pre)
   prefer 2
     apply(rule DC'' [where P = "\<lambda> tr . True" and c = "(\<lambda>s. s X \<ge> 0 \<and> s Y \<ge> 0)" and init = "\<lambda> s. 1/2 * s X ^ 2 - 1/2 * s Y ^ 2 >=  a "])
    subgoal
    apply(rule Valid_weaken_pre)
    prefer 2
     apply(rule Valid_strengthen_post)
      prefer 2
      apply(rule Valid_inv_b_tr_ge_and_ge[where P= "\<lambda> tr . True"])
apply clarify
  unfolding vec2state_def
     apply (fast intro!: derivative_intros)
apply clarify
  unfolding vec2state_def
   apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  done
  subgoal
apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_s_ge)
apply clarify
  unfolding vec2state_def
    apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  apply(auto simp add:state2vec_def entails_def algebra_simps power2_eq_square )
  done
  apply(auto simp add:state2vec_def entails_def)
  done
  done


lemma b37:
"\<Turnstile> {\<lambda>s tr. - s X * s Y \<ge> a}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s X - s Y + s X * s Y , Y := \<lambda> s. - s Y - s Y ^ 2, T := \<lambda> s. 1 ))) (\<lambda>s. s T < P)
 {\<lambda>s tr. - s X * s Y \<ge> a }"
  apply(rule Valid_inv_s_ge)
apply clarify
  unfolding vec2state_def
    apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  apply(auto simp add:state2vec_def entails_def algebra_simps power_add power2_eq_square )
  done


lemma b38:
"\<Turnstile> {\<lambda>s tr. 2 * s X ^ 3 \<ge> 1/4}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s X ^ 2  + s X ^ 4 , T := \<lambda> s. 1 ))) (\<lambda>s. s T < P)
 {\<lambda>s tr. 2 * s X ^ 3 \<ge> 1/4}"
  apply(rule Valid_inv_s_ge)
apply clarify 
  unfolding vec2state_def
    apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done


lemma b39:
"\<Turnstile> {\<lambda>s tr. s X ^ 3 \<ge> -1 \<and> s Y ^ 5 \<ge> 0 }
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . (s X - 3) ^ 4  + s Y ^ 5 , Y := \<lambda>  s. s Y ^ 2, T := \<lambda> s. 1 ))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X ^ 3 \<ge> -1 \<and> s Y ^ 5 \<ge> 0}"
  apply(rule Valid_pre_cases[where Q = "(\<lambda>s. s T < P)"])
   prefer 2
   apply(rule Valid_ode_not)
  apply auto
  apply(rule Valid_post_and)
  subgoal
  apply(rule Valid_weaken_pre)    
  prefer 2
  apply(rule DC''[where P = "\<lambda> tr . True" and init = "\<lambda> s. s X ^ 3 \<ge> -1 \<and> s Y ^ 5 \<ge> 0" and c = "\<lambda> s. s Y ^ 5 \<ge> 0"])
  subgoal
    apply(rule Valid_weaken_pre)
    prefer 2
     apply(rule Valid_inv_tr_ge)
      apply clarify
 unfolding vec2state_def
    apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done
  apply(rule Valid_weaken_pre)
  prefer 2
  apply(rule Valid_inv_s_ge)
apply clarify
 unfolding vec2state_def
    apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  done
  apply(rule Valid_weaken_pre)
  prefer 2
  apply(rule Valid_inv_s_ge)
apply clarify
 unfolding vec2state_def
    apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done


lemma b40:
  assumes "A > 0"
  shows "\<Turnstile> {\<lambda>s tr. s Y \<ge> 0 }
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. A , T := \<lambda> s. 1 ))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s Y \<ge> 0}"
  apply(rule Valid_inv_s_ge)
apply clarify
 unfolding vec2state_def
    apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  using assms by auto


lemma b41:
  assumes "A > 0" and "B > 0"
  shows "\<Turnstile> {\<lambda>s tr. s Y \<ge> 0 }
    Rep ( IChoice (IChoice (Z ::= (\<lambda> s . A)) (Z ::= (\<lambda> s . 0))) (Z ::= (\<lambda> s . - B) );
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s Y > 0))
 {\<lambda>s tr. s Y \<ge> 0}"
  apply(rule Valid_rep)
  apply(rule Valid_seq[where Q = "\<lambda>s tr. 0 \<le> s Y"])
   apply(rule Valid_ichoice_sp_st)
    apply(rule Valid_ichoice_sp_st)
     apply(rule Valid_strengthen_post)
  prefer 2
      apply(rule Valid_assign_sp)
apply(auto simp add:entails_def)
apply(rule Valid_strengthen_post)
  prefer 2
      apply(rule Valid_assign_sp)
    apply(auto simp add:entails_def)
apply(rule Valid_strengthen_post)
  prefer 2
      apply(rule Valid_assign_sp)
   apply(auto simp add:entails_def)
  apply(rule Valid_pre_cases[where Q ="(\<lambda>s. 0 < s Y)"])
   prefer 2
   apply(rule Valid_ode_not) 
    apply auto
  apply(rule Valid_weaken_pre)
   prefer 2
apply(rule Valid_strengthen_post)
  prefer 2
    apply(rule Valid_inv_b_s_ge)
  apply clarify
 unfolding vec2state_def
    apply (fast intro!: derivative_intros)
  apply(auto simp add:entails_def)
  done


lemma b42:
  assumes "A > 0" and "B > 0"
  shows "\<Turnstile> {\<lambda>s tr. s Y \<ge> 0 \<and> s X + 1/(2*B) * s Y ^ 2 < S}
    Rep (Cond (\<lambda>s. s X + 1/(2*B) * s Y ^ 2 < S)(Z ::= (\<lambda> s . A)) (Cond (\<lambda> s . s Y = 0) (Z ::= (\<lambda> s . 0)) (Z ::= (\<lambda> s . - B)));
     IChoice (Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s X + 1/(2*B) * s Y ^ 2 < S))
      (Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s X + 1/(2*B) * s Y ^ 2 > S)))
 {\<lambda>s tr. s X \<le> S}"
 apply(rule Valid_weaken_pre)
   prefer 2
apply(rule Valid_strengthen_post)
    prefer 2
    apply(rule Valid_rep[where P = "\<lambda>s tr. s X + 1/(2*B) * s Y ^ 2 \<le> S"])
    apply(rule Valid_seq[where Q = "\<lambda>s tr. s X + 1/(2*B) * s Y ^ 2 \<le> S"])
  subgoal
     apply(rule Valid_strengthen_post)
    prefer 2
     apply(rule Valid_cond_sp)
      apply(rule Valid_assign_sp)
     apply(rule Valid_cond_sp)
      apply(rule Valid_assign_sp)
     apply(rule Valid_assign_sp)
    apply(auto simp add:entails_def)
    done
  subgoal 
    apply(rule  Valid_ichoice_sp_st)
    subgoal
      apply(rule Valid_pre_cases[where Q = "\<lambda>s . s X + 1/(2*B) * s Y ^ 2 < S"])
      apply(rule Valid_weaken_pre)
   prefer 2
apply(rule Valid_strengthen_post)
         prefer 2
         apply(rule Valid_inv_b_s_le)
apply clarify
 unfolding vec2state_def
    apply (fast intro!: derivative_intros)
   apply(auto simp add:entails_def)
  apply(rule Valid_ode_not)
  apply auto
  done
apply(rule Valid_ode_not)
  apply auto
  done
  apply(auto simp add:entails_def)
  using assms
  by (smt divide_nonneg_pos power2_less_0)


lemma b43:
  assumes "A > 0" 
  shows "\<Turnstile> {\<lambda>s tr. s Y \<le> V}
    Rep (Cond (\<lambda>s. s Y = V)(Z ::= (\<lambda> s . 0)) (Z ::= (\<lambda> s . A));
      (Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s Y < V)))
 {\<lambda>s tr. s Y \<le> V}"
  apply(rule Valid_rep)
  apply(rule Valid_seq)
   apply(rule Valid_cond_sp)
    apply(rule Valid_assign_sp)
   apply(rule Valid_assign_sp)
  apply(rule Valid_pre_cases[where Q = "\<lambda>s. s Y < V"])
   apply(rule Valid_weaken_pre) prefer 2
    apply(rule Valid_strengthen_post) prefer 2
     apply(rule Valid_inv_b_s_le)
apply clarify
 unfolding vec2state_def
    apply (fast intro!: derivative_intros)
   apply(auto simp add:entails_def)
  apply(rule Valid_ode_not) 
  by auto


lemma b44:
  assumes "A > 0" 
  shows "\<Turnstile> {\<lambda>s tr. s Y \<le> V}
    Rep ((Z ::= (\<lambda> s . A);
      (Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s Y < V))))
 {\<lambda>s tr. s Y \<le> V}"
  apply(rule Valid_rep)
  apply(rule Valid_seq)
   apply(rule Valid_assign_sp)
  apply(rule Valid_pre_cases[where Q = "\<lambda>s. s Y < V"])
  apply(rule Valid_weaken_pre) prefer 2
    apply(rule Valid_strengthen_post) prefer 2
     apply(rule Valid_inv_b_s_le)
apply clarify
 unfolding vec2state_def
    apply (fast intro!: derivative_intros)
   apply(auto simp add:entails_def)
  apply(rule Valid_ode_not) 
  by auto


lemma b45:
  assumes "A > 0" 
  shows "\<Turnstile> {\<lambda>s tr. s Y \<le> V}
    Rep (Cond (\<lambda>s. s Y = V)(Z ::= (\<lambda> s . 0)) (Z ::= (\<lambda> s . A));
      IChoice (Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s Y < V))
       (Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s Y > V)))
 {\<lambda>s tr. s Y \<le> V}"
apply(rule Valid_rep)
  apply(rule Valid_seq)
 apply(rule Valid_cond_sp)
    apply(rule Valid_assign_sp)
   apply(rule Valid_assign_sp)
  apply(rule Valid_ichoice_sp_st)
  apply(rule Valid_pre_cases[where Q = "\<lambda>s. s Y < V"])
   apply(rule Valid_weaken_pre) prefer 2
    apply(rule Valid_strengthen_post) prefer 2
     apply(rule Valid_inv_b_s_le)
apply clarify
 unfolding vec2state_def
    apply (fast intro!: derivative_intros)
   apply(auto simp add:entails_def)
  apply(rule Valid_ode_not) 
   apply auto
apply(rule Valid_ode_not) 
  apply auto
  done


lemma b46:
  assumes "A > 0" and "B > 0" and "ep > 0"
  shows "\<Turnstile> {\<lambda>s tr. s Y \<ge> 0 \<and> s X + s Y ^ 2/(2 * B) \<le> S}
    Rep (Cond (\<lambda>s. s X + s Y ^ 2/(2 * B) + (A/B + 1)*(A/2 * ep^2 + ep * s Y)\<le> S)(Z ::= (\<lambda> s . A)) (Z ::= (\<lambda> s . - B));
        T ::= (\<lambda> s. 0);
       (Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z , T := \<lambda> s . 1))) (\<lambda>s. s Y > 0 \<and> s T < ep)))
 {\<lambda>s tr. s X \<le> S}"
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_rep)
   apply(rule Valid_cond_split')
  subgoal
    apply(rule Valid_seq)
     apply(rule Valid_assign_sp)
    apply(rule Valid_seq)
     apply(rule Valid_assign_sp)
    apply (rule Valid_pre_cases[where Q ="\<lambda> s. s Y > 0"])
     prefer 2
     apply(rule Valid_ode_not)
    apply auto
    apply(rule Valid_strengthen_post)
     prefer 2
     apply(rule Valid_ode_unique_solution_s_sp[where d = "\<lambda> s.  ep " and p ="\<lambda> s t . s(X := s X + s Y * t + 1/2 * s Z * t^2 , Y := s Y + s Z * t,  T := s T + t) "])
       apply (auto simp add:assms)
    unfolding ODEsol_def has_vderiv_on_def
    apply auto
    using assms 
    apply linarith
 apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
    prefer 2
apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     apply (auto simp add: has_vector_derivative_def)
       apply (rule has_derivative_eq_rhs)
        apply (simp add: power2_eq_square)
        apply (fast intro!: derivative_intros)[1]
    apply (rule ext)
       apply (auto simp add: algebra_simps)[1]
    using assms
      apply (smt mult_nonneg_nonneg)
    subgoal
    proof-
      have b1:"bounded_linear (\<lambda>(v :: vec). (\<chi> a. if a = T then 0 else if a = X then  v $ Y else if a = Y then  v $ Z else 0)) "
        apply(rule bounded_linearI')
        using vec_lambda_unique by fastforce+
      show ?thesis 
        unfolding state2vec_def vec2state_def fun_upd_def
     apply(rule c1_implies_local_lipschitz[where f'="(\<lambda>_. Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then  v $ Y else if a = Y then  v $ Z else 0)))"])
 apply (auto simp add: bounded_linear_Blinfun_apply[OF b1])
        subgoal premises pre for t x
          unfolding has_derivative_def apply(auto simp add: b1)
          apply(rule vec_tendstoI)
          by(auto simp add: state2vec_def)
        done
    qed
    apply(auto simp add:entails_def)
    using assms
     apply auto[1]
    using assms
    by (auto simp add: algebra_simps power_add power2_eq_square  add_divide_distrib )
   subgoal
    apply(rule Valid_seq)
     apply(rule Valid_assign_sp)
    apply(rule Valid_seq)
     apply(rule Valid_assign_sp)
    apply (rule Valid_pre_cases[where Q ="\<lambda> s. s Y > 0"])
     prefer 2
     apply(rule Valid_ode_not)
    apply auto
    apply(rule Valid_strengthen_post)
     prefer 2
      apply(rule Valid_ode_unique_solution_s_sp[where d = "\<lambda> s.  if s Y \<le> ep * B then s Y/B else ep " and p ="\<lambda> s t . s(X := s X + s Y * t + 1/2 * s Z * t^2 , Y := s Y + s Z * t,  T := s T + t) "])
     using assms apply auto
     subgoal
unfolding ODEsol_def has_vderiv_on_def
    apply auto
apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
       apply (rule has_vector_derivative_eq_rhs)
  unfolding power2_eq_square
      apply (fast intro!: derivative_intros)[1]
             apply (auto simp add: has_vector_derivative_def)
    using assms apply auto
       apply (rule has_derivative_eq_rhs)
           apply (fast intro!: derivative_intros)[1]
          apply (rule ext)
    apply auto
    done
         apply (metis (no_types, hide_lams) div_by_1 divide_divide_eq_right pos_less_divide_eq real_divide_square_eq)
  using mult_imp_div_pos_less 
  apply (smt divide_eq_imp)
  subgoal
unfolding ODEsol_def has_vderiv_on_def
    apply auto
apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
       apply (rule has_vector_derivative_eq_rhs)
  unfolding power2_eq_square
      apply (fast intro!: derivative_intros)[1]
             apply (auto simp add: has_vector_derivative_def)
    using assms apply auto
       apply (rule has_derivative_eq_rhs)
           apply (fast intro!: derivative_intros)[1]
          apply (rule ext)
    apply auto
    done
    apply(auto simp add: algebra_simps)
    apply (smt mult.commute real_mult_less_iff1)
  subgoal
 proof-
      have b1:"bounded_linear (\<lambda>(v :: vec). (\<chi> a. if a = T then 0 else if a = X then  v $ Y else if a = Y then  v $ Z else 0)) "
        apply(rule bounded_linearI')
        using vec_lambda_unique by fastforce+
      show ?thesis 
        unfolding state2vec_def vec2state_def fun_upd_def
     apply(rule c1_implies_local_lipschitz[where f'="(\<lambda>_. Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then  v $ Y else if a = Y then  v $ Z else 0)))"])
 apply (auto simp add: bounded_linear_Blinfun_apply[OF b1])
        subgoal premises pre for t x
          unfolding has_derivative_def apply(auto simp add: b1)
          apply(rule vec_tendstoI)
          by(auto simp add: state2vec_def)
        done
    qed
    unfolding entails_def fun_upd_def apply auto 
    apply (simp add: mult.commute)
      by (auto simp add: algebra_simps power_add power2_eq_square  add_divide_distrib  diff_divide_distrib)
    apply(auto simp add: entails_def)
    using assms 
    by (smt divide_nonneg_pos power2_less_0)


lemma b49:
  assumes "c>0" and "p=2" and "d=3"
  shows"\<Turnstile> {\<lambda> s t. s Y \<ge> 0 \<and> (5/4 * (s X - r)^ 2 + (s X - r) * s Y / 2 + (s Y ^ 2)/4 < c)}
Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. - p * (s X - r) - d * s Y , T := \<lambda> s . 1))) (\<lambda>s. s T < P)
{\<lambda> s t.  5/4 * (s X - r)^ 2 + (s X - r) * s Y / 2 + (s Y ^ 2)/4 < c}"
  apply(rule Valid_weaken_pre)
   prefer 2
   apply(rule Valid_inv_s_l)
apply clarify
 unfolding vec2state_def
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  using assms apply auto
  apply (auto simp add: algebra_simps power_add power2_eq_square  power2_diff add_divide_distrib  diff_divide_distrib )
  using  power2_diff zero_le_power2 power2_eq_square
  by (smt mult.commute)


lemma b50:
  assumes "p=2" and "d=3"
  shows"\<Turnstile> {\<lambda> s t. s Y \<ge> 0 \<and>  s X - s M \<ge> 0 \<and> s X \<le> S \<and> (s M + S)- 2 * s L = 0 \<and> (5/4 * (s X - s L)^ 2 + (s X - s L) * s Y / 2 + (s Y ^ 2)/4 - ((S - s M)/2)^2 < 0)}
Rep(

Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. - p * (s X - s L) - d * s Y ))) (\<lambda>s. s Y > 0)
)
{\<lambda> s t.  s X \<le> S}"
  apply(rule Valid_weaken_pre[where P' = "\<lambda> s t . s Y \<ge> 0 \<and> s X - s M \<ge> 0 \<and> (s M + S)- 2 * s L = 0 \<and> (5/4 * (s X - s L)^ 2 + (s X - s L) * s Y / 2 + (s Y ^ 2)/4 - ((S - s M)/2)^2 < 0)"])
   apply(simp add:entails_def)
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_rep)
 subgoal
   apply(rule Valid_pre_cases[where Q = "\<lambda> s. s Y > 0 "])
   subgoal
    apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule DC'''[where P= "\<lambda> tr . True" and init = "\<lambda> s.  0 \<le> s Y \<and> s X - s M \<ge> 0 \<and> (s M + S)- 2 * s L = 0 \<and> (5/4 * (s X - s L)^ 2 + (s X - s L) * s Y / 2 + (s Y ^ 2)/4 - ((S - s M)/2)^2 < 0)"])
    subgoal 
      apply (rule Valid_weaken_pre)
      prefer 2
       apply (rule Valid_inv_b_tr_ge)
apply clarify
 unfolding vec2state_def
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done
  subgoal
 apply(rule Valid_weaken_pre)
    prefer 2
   apply(rule DC'''[where P= "\<lambda> tr . True" and init = "\<lambda> s.  0 \<le> s Y \<and> s X - s M \<ge> 0 \<and> s X \<le> S \<and> (s M + S)- 2 * s L = 0 \<and> (5/4 * (s X - s L)^ 2 + (s X - s L) * s Y / 2 + (s Y ^ 2)/4 - ((S - s M)/2)^2 < 0)"])
    subgoal
      apply (rule Valid_weaken_pre)
       prefer 2
       apply(rule Valid_inv_tr_ge[where inv="\<lambda> s. s X - s M"])
apply clarify
 unfolding vec2state_def
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done
subgoal
 apply(rule Valid_weaken_pre)
    prefer 2
   apply(rule DC'''[where P= "\<lambda> tr . True" and init = "\<lambda> s.  0 \<le> s Y \<and> s X - s M \<ge> 0 \<and> s X \<le> S \<and> (s M + S)- 2 * s L = 0 \<and> (5/4 * (s X - s L)^ 2 + (s X - s L) * s Y / 2 + (s Y ^ 2)/4 - ((S - s M)/2)^2 < 0)"])
    subgoal
      apply (rule Valid_weaken_pre)
       prefer 2
       apply(rule Valid_inv_tr_eq)
apply clarify
 unfolding vec2state_def
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done
  subgoal
 apply(rule Valid_weaken_pre)
     prefer 2
     apply(rule Valid_inv_s_l)
apply clarify
 unfolding vec2state_def
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def assms)
  apply(auto simp add: algebra_simps add_mult_distrib add_divide_distrib  diff_divide_distrib )
  subgoal for Sa
  apply(subgoal_tac" Sa L * (Sa X * 2) \<le> Sa L * Sa L + Sa X * Sa X")
  apply (smt zero_le_square)
  apply(subgoal_tac" 0 \<le> Sa L * Sa L + Sa X * Sa X - Sa L * (Sa X * 2)")
  apply auto
  using power2_diff[of "Sa L" "Sa X"] zero_le_square[of "Sa L - Sa X"] 
  by (simp add: power2_eq_square)
  done
  apply(auto simp add:entails_def)
  done
  apply(auto simp add:entails_def)
  subgoal premises pre for s
  proof-
    have 1:"5 * (s X - s L)\<^sup>2 / 4 + (s X - s L) * s Y / 2 + (s Y)\<^sup>2 / 4 < ((S - s M) / 2)\<^sup>2"
      using pre by auto
    have 2:"(s X - s L)\<^sup>2 / 4 + (s X - s L) * s Y / 2 + (s Y)\<^sup>2 / 4 \<ge> 0 "
      apply(rule mult_left_le_imp_le[of 4])
       apply auto
      using power2_sum[of "s Y" "(s X - s L)"] apply( auto simp add: power2_eq_square)
      by (smt combine_common_factor not_square_less_zero)
    have 3:"5 * (s X - s L)\<^sup>2 / 4 = (s X - s L)\<^sup>2 / 4 + (s X - s L)\<^sup>2"
      by auto
    have 4:"(s X - s L)\<^sup>2 < ((S - s M) / 2)\<^sup>2"
      using 1 2 3 
      by linarith
    have 5:"((S - s M) / 2 - (s X - s L)) * ((S - s M) / 2 + (s X - s L)) = ((S - s M) / 2)\<^sup>2 - (s X - s L)\<^sup>2" 
      by(auto simp add: algebra_simps add_mult_distrib add_divide_distrib  diff_divide_distrib power2_eq_square)
    have 6:"((S - s M) / 2 - (s X - s L)) * ((S - s M) / 2 + (s X - s L)) > 0"
      using 4 5 by auto
    have 7:"((S - s M) / 2 - s X + s L) * ((S - s M) / 2 + s X - s L) > 0"
      using 6 
      by smt
    have 8:"s L = (S + s M) / 2"
      using pre by auto
    have 9:"(S - s M) / 2 - s X + s L = S - s X" 
      using 8 
      by (smt field_sum_of_halves)
    have 10:"(S - s M) / 2 + s X - s L = s X - s M"
      using 8
      by (smt field_sum_of_halves pre(2))
    have 11:"(S - s X) * (s X - s M) > 0"
      using 7 9 10 by auto
    show ?thesis using 11 pre(1)
      by (simp add: zero_less_mult_iff)
  qed
done
  apply(auto simp add:entails_def)
  done
  apply(auto simp add:entails_def)
  apply(rule Valid_ode_not)
  apply auto
  done
  apply(auto simp add:entails_def)
  subgoal premises pre for s
  proof-
    have 1:"5 * (s X - s L)\<^sup>2 / 4 + (s X - s L) * s Y / 2 + (s Y)\<^sup>2 / 4 < ((S - s M) / 2)\<^sup>2"
      using pre by auto
    have 2:"(s X - s L)\<^sup>2 / 4 + (s X - s L) * s Y / 2 + (s Y)\<^sup>2 / 4 \<ge> 0 "
      apply(rule mult_left_le_imp_le[of 4])
       apply auto
      using power2_sum[of "s Y" "(s X - s L)"] apply( auto simp add: power2_eq_square)
      by (smt combine_common_factor not_square_less_zero)
    have 3:"5 * (s X - s L)\<^sup>2 / 4 = (s X - s L)\<^sup>2 / 4 + (s X - s L)\<^sup>2"
      by auto
    have 4:"(s X - s L)\<^sup>2 < ((S - s M) / 2)\<^sup>2"
      using 1 2 3 
      by linarith
    have 5:"((S - s M) / 2 - (s X - s L)) * ((S - s M) / 2 + (s X - s L)) = ((S - s M) / 2)\<^sup>2 - (s X - s L)\<^sup>2" 
      by(auto simp add: algebra_simps add_mult_distrib add_divide_distrib  diff_divide_distrib power2_eq_square)
    have 6:"((S - s M) / 2 - (s X - s L)) * ((S - s M) / 2 + (s X - s L)) > 0"
      using 4 5 by auto
    have 7:"((S - s M) / 2 - s X + s L) * ((S - s M) / 2 + s X - s L) > 0"
      using 6 
      by smt
    have 8:"s L = (S + s M) / 2"
      using pre by auto
    have 9:"(S - s M) / 2 - s X + s L = S - s X" 
      using 8 
      by (smt field_sum_of_halves)
    have 10:"(S - s M) / 2 + s X - s L = s X - s M"
      using 8
      by (smt field_sum_of_halves pre(2))
    have 11:"(S - s X) * (s X - s M) > 0"
      using 7 9 10 by auto
    show ?thesis using 11 pre(2)
      by (simp add: zero_less_mult_iff)
  qed
done


lemma b52:
 "\<Turnstile> {\<lambda> s t. s Y \<ge> 0 \<and> s Z \<ge> 0 }
Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s Y > 0)
{\<lambda> s t.  s Y \<ge>0}"
  apply(rule Valid_pre_cases[where Q = "\<lambda> s. s Y > 0"])
  apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_strengthen_post)
  prefer 2
     apply(rule Valid_inv_b_s_ge)
apply clarify
 unfolding vec2state_def
   apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  apply(rule Valid_ode_not)
  apply auto
  done


lemma b53:
  assumes"A\<ge>0" and "B>0"
  shows
 "\<Turnstile> {\<lambda> s t. s Y \<ge> 0 }
IChoice (Z ::= (\<lambda> s . A)) (Z ::= (\<lambda> s . - B));
Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s Y > 0)
{\<lambda> s t.  s Y \<ge>0}"
  apply(rule Valid_seq)
   apply(rule Valid_ichoice_sp)
    apply(rule Valid_assign_sp)
   apply(rule Valid_assign_sp)
  apply auto
apply(rule Valid_pre_cases[where Q = "\<lambda> s. s Y > 0"])
  apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_strengthen_post)
  prefer 2
     apply(rule Valid_inv_b_s_ge)
apply clarify
 unfolding vec2state_def
   apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  apply(rule Valid_ode_not)
  apply auto
  done


lemma b54:
  assumes"A\<ge>0" and "B>0"
  shows
 "\<Turnstile> {\<lambda> s t. s Y \<ge> 0 }
IF (\<lambda> s. m - s X \<ge> 2) THEN (Z ::= (\<lambda> s . A)) ELSE (Z ::= (\<lambda> s . - B)) FI;
Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z ))) (\<lambda>s. s Y > 0)
{\<lambda> s t.  s Y \<ge>0}"
  apply(rule Valid_seq)
   apply(rule Valid_cond_sp)
apply(rule Valid_assign_sp)
   apply(rule Valid_assign_sp)
  apply auto
apply(rule Valid_pre_cases[where Q = "\<lambda> s. s Y > 0"])
  apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_strengthen_post)
  prefer 2
     apply(rule Valid_inv_b_s_ge)
apply clarify
 unfolding vec2state_def
   apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def)
  apply(rule Valid_ode_not)
  apply auto
  done


lemma b55:
  assumes "A \<ge> 0" and "B > 0" and "ep > 0"
  shows "\<Turnstile> {\<lambda>s tr. s Y \<ge> 0 \<and> s Y ^ 2 \<le> (S - s X)*(2 * B)}
    Rep (Cond (\<lambda>s. (A + B)*(A * ep^2 + 2 * ep * s Y) + s Y ^ 2  \<le> (S - s X) * 2 * B)(Z ::= (\<lambda> s . A)) (Z ::= (\<lambda> s . - B));
        T ::= (\<lambda> s. 0);
       (Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s Y , Y := \<lambda>  s. s Z , T := \<lambda> s . 1))) (\<lambda>s. s Y > 0 \<and> s T < ep)))
 {\<lambda>s tr. s X \<le> S}"
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_rep)
   apply(rule Valid_cond_split')
  subgoal
    apply(rule Valid_seq)
     apply(rule Valid_assign_sp)
    apply(rule Valid_seq)
     apply(rule Valid_assign_sp)
    apply (rule Valid_pre_cases[where Q ="\<lambda> s. s Y > 0"])
     prefer 2
     apply(rule Valid_ode_not)
    apply auto
    apply(rule Valid_strengthen_post)
     prefer 2
     apply(rule Valid_ode_unique_solution_s_sp[where d = "\<lambda> s.  ep " and p ="\<lambda> s t . s(X := s X + s Y * t + 1/2 * s Z * t^2 , Y := s Y + s Z * t,  T := s T + t) "])
       apply (auto simp add:assms)
    unfolding ODEsol_def has_vderiv_on_def
    apply auto
    using assms 
    apply linarith
 apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
    prefer 2
apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     apply (auto simp add: has_vector_derivative_def)
       apply (rule has_derivative_eq_rhs)
        apply (simp add: power2_eq_square)
        apply (fast intro!: derivative_intros)[1]
    apply (rule ext)
       apply (auto simp add: algebra_simps)[1]
    using assms
      apply (smt mult_nonneg_nonneg)
    subgoal
    proof-
      have b1:"bounded_linear (\<lambda>(v :: vec). (\<chi> a. if a = T then 0 else if a = X then  v $ Y else if a = Y then  v $ Z else 0)) "
        apply(rule bounded_linearI')
        using vec_lambda_unique by fastforce+
      show ?thesis 
        unfolding state2vec_def vec2state_def fun_upd_def
     apply(rule c1_implies_local_lipschitz[where f'="(\<lambda>_. Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then  v $ Y else if a = Y then  v $ Z else 0)))"])
 apply (auto simp add: bounded_linear_Blinfun_apply[OF b1])
        subgoal premises pre for t x
          unfolding has_derivative_def apply(auto simp add: b1)
          apply(rule vec_tendstoI)
          by(auto simp add: state2vec_def)
        done
    qed
    apply(auto simp add:entails_def)
    using assms
     apply auto[1]
    using assms
    by (auto simp add: algebra_simps power_add power2_eq_square  add_divide_distrib )
   subgoal
    apply(rule Valid_seq)
     apply(rule Valid_assign_sp)
    apply(rule Valid_seq)
     apply(rule Valid_assign_sp)
    apply (rule Valid_pre_cases[where Q ="\<lambda> s. s Y > 0"])
     prefer 2
     apply(rule Valid_ode_not)
    apply auto
    apply(rule Valid_strengthen_post)
     prefer 2
      apply(rule Valid_ode_unique_solution_s_sp[where d = "\<lambda> s.  if s Y \<le> ep * B then s Y/B else ep " and p ="\<lambda> s t . s(X := s X + s Y * t + 1/2 * s Z * t^2 , Y := s Y + s Z * t,  T := s T + t) "])
     using assms apply auto
     subgoal
unfolding ODEsol_def has_vderiv_on_def
    apply auto
apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
       apply (rule has_vector_derivative_eq_rhs)
  unfolding power2_eq_square
      apply (fast intro!: derivative_intros)[1]
             apply (auto simp add: has_vector_derivative_def)
    using assms apply auto
       apply (rule has_derivative_eq_rhs)
           apply (fast intro!: derivative_intros)[1]
          apply (rule ext)
    apply auto
    done
         apply (metis (no_types, hide_lams) div_by_1 divide_divide_eq_right pos_less_divide_eq real_divide_square_eq)
  using mult_imp_div_pos_less 
  apply (smt divide_eq_imp)
  subgoal
unfolding ODEsol_def has_vderiv_on_def
    apply auto
apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
       apply (rule has_vector_derivative_eq_rhs)
  unfolding power2_eq_square
      apply (fast intro!: derivative_intros)[1]
             apply (auto simp add: has_vector_derivative_def)
    using assms apply auto
       apply (rule has_derivative_eq_rhs)
           apply (fast intro!: derivative_intros)[1]
          apply (rule ext)
    apply auto
    done
    apply(auto simp add: algebra_simps)
    apply (smt mult.commute real_mult_less_iff1)
  subgoal
 proof-
      have b1:"bounded_linear (\<lambda>(v :: vec). (\<chi> a. if a = T then 0 else if a = X then  v $ Y else if a = Y then  v $ Z else 0)) "
        apply(rule bounded_linearI')
        using vec_lambda_unique by fastforce+
      show ?thesis 
        unfolding state2vec_def vec2state_def fun_upd_def
     apply(rule c1_implies_local_lipschitz[where f'="(\<lambda>_. Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then  v $ Y else if a = Y then  v $ Z else 0)))"])
 apply (auto simp add: bounded_linear_Blinfun_apply[OF b1])
        subgoal premises pre for t x
          unfolding has_derivative_def apply(auto simp add: b1)
          apply(rule vec_tendstoI)
          by(auto simp add: state2vec_def)
        done
    qed
    unfolding entails_def fun_upd_def apply auto 
    apply (simp add: mult.commute)
      apply (auto simp add: algebra_simps power_add power2_eq_square  diff_divide_distrib divide_right_mono)
    subgoal for s'
      apply(subgoal_tac "B* (s' X * 2 + s' Y * s' Y / B) \<le> B *( S * 2)")
      subgoal by auto
      by (auto simp add: algebra_simps)
        subgoal for s'
      apply(subgoal_tac "B* (s' X * 2 + s' Y * s' Y / B) \<le> B *( S * 2)")
      subgoal by auto
      by (auto simp add: algebra_simps)
    done
 apply(auto simp add: entails_def)
    using assms 
    by (smt mult_neg_pos zero_le_power2)
    

end