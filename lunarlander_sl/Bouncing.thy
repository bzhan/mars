theory Bouncing
  imports ContinuousInv
begin

lemma has_vector_derivative_divide[derivative_intros]:
  fixes a :: "'a::real_normed_field"
  shows "(f has_vector_derivative x) F \<Longrightarrow> ((\<lambda>x. f x / a) has_vector_derivative (x / a)) F"
  unfolding divide_inverse by (fact has_vector_derivative_mult_left)

locale bouncing_ball =
  fixes g :: real and
    c :: real and
    H :: real
  assumes pos_g: "g > 0" and
    pos_c: "c > 0" and
    le1_c: "c \<le> 1"
begin

definition V :: char where "V = CHR ''v''"

lemma vars_distinct: "X \<noteq> V" "V \<noteq> X"
  unfolding X_def V_def by auto

definition Inv :: "state \<Rightarrow> real" where
  "Inv = (\<lambda>s. (s V) ^ 2 + 2 * g * s X)"

lemma bouncingBallInv:
  assumes "v0 > 0"
  shows "Valid
    (\<lambda>s tr. Inv s = r \<and> P tr \<and> s = ((\<lambda>_. 0)(V := v0)))
    (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (\<lambda>s. s X > 0 \<or> s V > 0))
    (\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. Inv s = r)) tr)"
  apply(rule Valid_weaken_pre)
   prefer 2
   apply(rule Valid_inv')
  unfolding Inv_def
    apply (auto simp add: vec2state_def)[1]
    apply (auto intro!: derivative_intros)[1]
   apply (auto simp add: vec2state_def state2vec_def)
   apply(auto simp add: entails_def)
    apply(auto simp add: vars_distinct assms)
  done

end
end