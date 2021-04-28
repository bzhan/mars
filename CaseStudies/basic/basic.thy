theory basic
    imports HHLProver.ContinuousInv  HHLProver.BigStepParallel  basicprime
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
 apply(auto simp add:state2vec_def entails_def algebra_simps power_add power2_eq_square power4_eq_xxxx
    power_mult_distrib power_mult del: one_add_one )
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

lemma 28:
 "\<Turnstile> {\<lambda>s tr. s X ^ 4 * s Y ^ 2 + s X ^ 2 * s Y ^ 4 - 3 * s X ^ 2 * s Y ^ 2 + 1 \<le> c}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. 2 * s X ^ 4 * s Y + 4 * s X ^ 2 * s Y ^ 3 - 6 * s X ^ 2 * s Y, 
       Y := \<lambda> s. - 4 * s X ^ 3 * s Y ^ 2 - 2 * s X * s Y ^ 4  + 6 * s X * s Y ^ 2, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X ^ 4 * s Y ^ 2 + s X ^ 2 * s Y ^ 4 - 3 * s X ^ 2 * s Y ^ 2 + 1 \<le> c}"
  apply(rule Valid_inv_s_le)
apply clarify
       apply(simp add:vec2state_def)
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def algebra_simps power_add power2_eq_square power4_eq_xxxx
    power_mult_distrib power_mult del: one_add_one )
  done


lemma 32:
  assumes "r\<le>0"
  shows "\<exists> f . \<Turnstile> {\<lambda>s tr. s X  = f}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . r + s X ^ 2, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X  = f }"
  sorry


lemma 34:
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

lemma 35:
"\<Turnstile> {\<lambda>s tr. s X + 1/2 * s Y ^ 2 =  a}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s X * s Y, Y := \<lambda> s. - s X , T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X + 1/2 * s Y ^ 2 =  a }"
  apply(rule Valid_inv_s_eq)
   apply clarify
  unfolding vec2state_def
   apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done


lemma 36:
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
  apply(auto simp add:state2vec_def entails_def algebra_simps power_add power2_eq_square power4_eq_xxxx
    power_mult_distrib power_mult del: one_add_one )
  done
  apply(auto simp add:state2vec_def entails_def)
  done
  done

lemma 37:
"\<Turnstile> {\<lambda>s tr. - s X * s Y \<ge> a}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s X - s Y + s X * s Y , Y := \<lambda> s. - s Y - s Y ^ 2, T := \<lambda> s. 1 ))) (\<lambda>s. s T < P)
 {\<lambda>s tr. - s X * s Y \<ge> a }"
  apply(rule Valid_inv_s_ge)
apply clarify
  unfolding vec2state_def
    apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  apply(auto simp add:state2vec_def entails_def algebra_simps power_add power2_eq_square power4_eq_xxxx
    power_mult_distrib power_mult del: one_add_one )
  done

lemma 38:
"\<Turnstile> {\<lambda>s tr. 2 * s X ^ 3 \<ge> 1/4}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda> s . s X ^ 2  + s X ^ 4 , T := \<lambda> s. 1 ))) (\<lambda>s. s T < P)
 {\<lambda>s tr. 2 * s X ^ 3 \<ge> 1/4}"
  apply(rule Valid_inv_s_ge)
apply clarify 
  unfolding vec2state_def
    apply (fast intro!: derivative_intros)
  apply(auto simp add:state2vec_def entails_def)
  done
  
lemma 39:
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

lemma 40:
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


lemma 41:
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

lemma 42:
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


lemma 43:
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


lemma 44:
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


lemma 45:
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










end