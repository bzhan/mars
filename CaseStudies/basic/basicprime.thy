theory basicprime
  imports
    HHLProver.ContinuousInv
    HHLProver.BigStepParallel
    HHLProver.Complementlemma
begin

text \<open>Variables\<close>

definition T :: char where "T = CHR ''t''"
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"
definition J :: char where "J = CHR ''j''"
definition L :: char where "L = CHR ''l''"
definition M :: char where "M = CHR ''m''"
definition N :: char where "N = CHR ''n''"

lemma vars_distinct [simp]: "T \<noteq> X" "T \<noteq> Y" "T \<noteq> Z" "T \<noteq> J" "T \<noteq> L" "T \<noteq> M" "T \<noteq> N"
                            "X \<noteq> T" "X \<noteq> Y" "X \<noteq> Z" "X \<noteq> J" "X \<noteq> L" "X \<noteq> M" "X \<noteq> N"
                            "Y \<noteq> T" "Y \<noteq> X" "Y \<noteq> Z" "Y \<noteq> J" "Y \<noteq> L" "Y \<noteq> M" "Y \<noteq> N"
                            "Z \<noteq> T" "Z \<noteq> X" "Z \<noteq> Y" "Z \<noteq> J" "Z \<noteq> L" "Z \<noteq> M" "Z \<noteq> N"
                            "J \<noteq> T" "J \<noteq> X" "J \<noteq> Y" "J \<noteq> Z" "J \<noteq> L" "J \<noteq> M" "J \<noteq> N"
                            "L \<noteq> T" "L \<noteq> X" "L \<noteq> Y" "L \<noteq> Z" "L \<noteq> J" "L \<noteq> M" "L \<noteq> N"
                            "M \<noteq> T" "M \<noteq> X" "M \<noteq> Y" "M \<noteq> Z" "M \<noteq> J" "M \<noteq> L" "M \<noteq> N"
                            "N \<noteq> T" "N \<noteq> X" "N \<noteq> Y" "N \<noteq> Z" "N \<noteq> J" "N \<noteq> L" "N \<noteq> M"
  unfolding T_def X_def Y_def Z_def J_def  L_def M_def N_def by auto


text \<open>
  Analysis of <x' = -x, t' = 1> by explicit solution.
\<close>
lemma exp_1_subst:
  "(state2vec
     (\<lambda>a. (if a = T then \<lambda>s. 1 else ((\<lambda>_ _. 0)(X := \<lambda>s. - s X)) a)
          (vec2state v))) = (\<chi> a. if a = T then 1 else if a = X then -v $ X else 0)" for v
  apply(auto simp add: state2vec_def)
  using vec2state_def by auto
  
lemma exp_1_deriv_bounded:
  "bounded_linear (\<lambda>v. \<chi> a. if a = T then 0 else if a = X then - v $ X else 0)"
  apply (rule Real_Vector_Spaces.bounded_linear_intro[where K=1])
    apply (auto simp add: plus_vec_def scaleR_vec_def)
  by (simp add: norm_le_componentwise_cart)

lemma exp_1_deriv:
  "((\<lambda>v. \<chi> a. if a = T then 1 else if a = X then - v $ X else 0) has_derivative
      (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then - v $ X else 0)))
     (at x)"
proof -
  have a: "((\<chi> a. if a = T then 1 else if a = X then - y $ X else 0) -
            (\<chi> a. if a = T then 1 else if a = X then - x $ X else 0) -
            (\<chi> a. if a = T then 0 else if a = X then - (y - x) $ X else 0)) = (\<chi> a. 0)" for y
    by (auto simp add: minus_vec_def)
  show ?thesis
    apply (rule has_derivativeI)
     prefer 2
    apply (rule tendstoI)
     apply auto
    subgoal for e
      apply (subst a)
      by (metis (mono_tags, lifting) eventuallyI mult.commute norm_zero
          vector_space_over_itself.scale_zero_left zero_vec_def)
    by (rule exp_1_deriv_bounded)
qed

lemma exp_1_1:
  "\<Turnstile> {\<lambda>s tr. s X > 0 \<and> s T < P}
       Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
      {\<lambda>s tr. s X > 0}"
  apply (rule Valid_strengthen_post)
  prefer 2
   apply (rule Valid_ode_unique_solution_s_sp[where
              d="\<lambda>s. P - s T" and
              p = "\<lambda>s. (\<lambda>t. s(X := s X * exp (-1 * t), T := s T + t))" ] )
     apply auto
  subgoal for s
    unfolding ODEsol_def has_vderiv_on_def
    apply auto
    apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
     prefer 2
     apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     apply (auto simp add: has_vector_derivative_def)
    apply (rule has_derivative_eq_rhs)
     apply (fast intro!: derivative_intros)[1]
    by auto
   apply(rule c1_implies_local_lipschitz[where
            f'="(\<lambda>_. Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then -v $ X else 0)))"])
       apply (subst exp_1_subst) 
      apply (rule has_derivative_eq_rhs)
        apply (rule exp_1_deriv)
       apply (auto simp add: bounded_linear_Blinfun_apply exp_1_deriv_bounded)
  apply(auto simp add: entails_def)
  done

lemma exp_1:
 "\<Turnstile> {\<lambda>s tr. s X > 0}
      Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
     {\<lambda>s tr. s X > 0}"
  apply(rule Valid_pre_cases)
   apply(rule exp_1_1)
  apply (rule Valid_ode_not) by auto


text \<open>
  Analysis of <x' = x, t' = 1> by explicit solution
\<close>
lemma exp_2_subst:
  "(state2vec
     (\<lambda>a. (if a = T then \<lambda>s. 1 else ((\<lambda>_ _. 0)(X := \<lambda>s. s X)) a)
          (vec2state v))) = ( \<chi> a. if a = T then 1 else if a = X then v $ X else 0)" for v
  apply(auto simp add: state2vec_def)
  using vec2state_def by auto

lemma exp_2_deriv_bounded:
  "bounded_linear (\<lambda>v. \<chi> a. if a = T then 0 else if a = X then v $ X else 0)"
  apply (rule Real_Vector_Spaces.bounded_linear_intro[where K=1])
    apply (auto simp add: plus_vec_def scaleR_vec_def)
  by (simp add: norm_le_componentwise_cart)

lemma exp_2_deriv:
  "((\<lambda>v. \<chi> a. if a = T then 1 else if a = X then v $ X else 0) has_derivative
      (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then v $ X else 0)))
     (at x)"
proof -
  have a: "((\<chi> a. if a = T then 1 else if a = X then y $ X else 0) -
            (\<chi> a. if a = T then 1 else if a = X then x $ X else 0) -
            (\<chi> a. if a = T then 0 else if a = X then (y - x) $ X else 0)) = (\<chi> a. 0)" for y
    by (auto simp add: minus_vec_def)
  show ?thesis
    apply (rule has_derivativeI)
     prefer 2
    apply (rule tendstoI)
     apply auto
    subgoal for e
      apply (subst a)
      by (metis (mono_tags, lifting) eventuallyI mult.commute norm_zero
          vector_space_over_itself.scale_zero_left zero_vec_def)
    by (rule exp_2_deriv_bounded)
qed

lemma exp_2_1:
  "\<Turnstile> {\<lambda>s tr. s X > 0 \<and> s T < P}
       Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
      {\<lambda>s tr. s X > 0}"
  apply (rule Valid_strengthen_post)
  prefer 2
  apply (rule Valid_ode_unique_solution_s_sp[where
            d="\<lambda>s. P - s T" and
            p = "\<lambda>s. (\<lambda>t. s(X := s X * exp t, T := s T + t))" ] )
     apply auto
  subgoal for s
    unfolding ODEsol_def has_vderiv_on_def
    apply auto
    apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
    prefer 2
    apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     apply (auto simp add: has_vector_derivative_def)
    apply (rule has_derivative_eq_rhs)
     apply (fast intro!: derivative_intros)[1]
    by auto
  apply(rule c1_implies_local_lipschitz[where
            f'="(\<lambda>_. Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then v $ X else 0)))"])
       apply (subst exp_2_subst) 
      apply (rule has_derivative_eq_rhs)
        apply (rule exp_2_deriv)
       apply (auto simp add: bounded_linear_Blinfun_apply exp_2_deriv_bounded)
  apply (auto simp add: entails_def)
  done

lemma exp_2:
  "\<Turnstile> {\<lambda>s tr. s X > 0}
       Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
     {\<lambda>s tr. s X > 0}"
  apply(rule Valid_pre_cases)
   apply(rule exp_2_1)
  apply(rule Valid_ode_not) by auto


text \<open>
  Analysis of <x' = -x + 1, t' = 1> by explicit solution.
\<close>
lemma exp_3_subst:
  "(state2vec
      (\<lambda>a. (if a = T then \<lambda>s. 1 else ((\<lambda>_ _. 0)(X := \<lambda>s. 1 - s X)) a)
      (vec2state v))) = (\<chi> a. if a = T then 1 else if a = X then 1 - v $ X else 0)" for v
  apply(auto simp add: state2vec_def)
  using vec2state_def by auto

lemma exp_3_deriv_bounded:
  "bounded_linear (\<lambda>v. \<chi> a. if a = T then 0 else if a = X then -v $ X else 0)"
  apply (rule Real_Vector_Spaces.bounded_linear_intro[where K=1])
    apply (auto simp add: plus_vec_def scaleR_vec_def)
  by (simp add: norm_le_componentwise_cart)

lemma exp_3_deriv:
  "((\<lambda>v. \<chi> a. if a = T then 1 else if a = X then 1 - v $ X else 0) has_derivative
      (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then -v $ X else 0)))
     (at x)"
proof -
  have a: "((\<chi> a. if a = T then 1 else if a = X then 1 - y $ X else 0) -
            (\<chi> a. if a = T then 1 else if a = X then 1 - x $ X else 0) -
            (\<chi> a. if a = T then 0 else if a = X then -(y - x) $ X else 0)) = (\<chi> a. 0)" for y
    by (auto simp add: minus_vec_def)
  show ?thesis
    apply (rule has_derivativeI)
     prefer 2
    apply (rule tendstoI)
     apply auto
    subgoal for e
      apply (subst a)
      by (metis (mono_tags, lifting) eventuallyI mult.commute norm_zero
          vector_space_over_itself.scale_zero_left zero_vec_def)
    by (rule exp_3_deriv_bounded)
qed

lemma exp_3_1:
  "\<Turnstile> {\<lambda>s tr. s X > 0 \<and> s T < P}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s X + 1, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply (rule Valid_strengthen_post)
  prefer 2
   apply (rule Valid_ode_unique_solution_s_sp[where
             d="\<lambda>s. P - s T" and
             p = "\<lambda>s. (\<lambda>t. s(X := (s X - 1) * exp (-t) + 1, T := s T + t))" ] )
     apply auto
  subgoal for s
    unfolding ODEsol_def has_vderiv_on_def
    apply auto
    apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
    prefer 2
apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     apply (auto simp add: has_vector_derivative_def)
    apply (rule has_derivative_eq_rhs)
     apply (fast intro!: derivative_intros)[1]
    by auto
    apply(rule c1_implies_local_lipschitz[where f'="(\<lambda>_. Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then -v $ X else 0)))"])
       apply (subst exp_3_subst) 
      apply (rule has_derivative_eq_rhs)
       apply (rule exp_3_deriv)
       apply (auto simp add: bounded_linear_Blinfun_apply exp_3_deriv_bounded)
  apply(auto simp add: entails_def)
  subgoal premises pre for s
  proof(cases "s X \<ge> 1")
    case True
    then show ?thesis
      using exp_ge_zero
      by (smt mult_nonneg_nonneg)
  next
    case False
    then have 1:"s X - 1 < 0" by auto
    have 2:"exp (s T - P) > 0" by auto
    have 3:"exp (s T - P) < 1" using pre by auto
    have 4:"(s X - 1) * exp (s T - P) > (s X - 1)"
      using 1 2 3 by auto
    then show ?thesis using pre by auto
  qed
 done

lemma exp_3:
  "\<Turnstile> {\<lambda>s tr. s X > 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. -s X + 1, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply(rule Valid_pre_cases)
   apply(rule exp_3_1)
  apply(rule Valid_ode_not) by auto


text \<open>
  Analysis of <x' = -y * x, t = 1> by Darboux invariants (with g = -y).
\<close>
lemma exp_4:
  "\<Turnstile> {\<lambda>s tr. s X > 0}
       Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s Y * s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
     {\<lambda>s tr. s X > 0}"
  apply (rule Valid_dbx_s_g[where g="\<lambda> s . - s Y"])
    apply clarify
  unfolding vec2state_def
    apply (fast intro!: derivative_intros)[1]
   apply(auto simp add: state2vec_def)
  apply(auto simp add: continuous_on_eq_continuous_within)
  done


text \<open>
  Analysis of <x' = x, t' = 1>, to show x remains non-negative.
\<close>
lemma exp_5_1:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0 \<and> s T < P}
       Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
      {\<lambda>s tr. s X \<ge> 0}"
  apply (rule Valid_strengthen_post)
  prefer 2
   apply (rule Valid_ode_unique_solution_s_sp[where
             d="\<lambda>s. P - s T" and
             p = "\<lambda>s. (\<lambda>t. s(X := s X * exp t, T := s T + t))" ] )
     apply auto
  subgoal for s
    unfolding ODEsol_def has_vderiv_on_def
    apply auto
    apply (rule exI[where x="1"])
    apply auto
     apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
    prefer 2
apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     apply (auto simp add: has_vector_derivative_def)
    apply (rule has_derivative_eq_rhs)
     apply (fast intro!: derivative_intros)[1]
    by auto
    apply(rule c1_implies_local_lipschitz[where f'="(\<lambda>_. Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then  v $ X else 0)))"])
       apply (subst exp_2_subst) 
      apply (rule has_derivative_eq_rhs)
        apply (rule exp_2_deriv)
       apply (auto simp add: bounded_linear_Blinfun_apply exp_2_deriv_bounded)
  apply(auto simp add: entails_def)
  done

lemma exp_5:
 "\<Turnstile> {\<lambda>s tr. s X \<ge> 0}
      Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
     {\<lambda>s tr. s X \<ge> 0}"
  apply(rule Valid_pre_cases)
   apply (rule exp_5_1)
   apply (rule Valid_ode_not) by auto

end
