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
     

end