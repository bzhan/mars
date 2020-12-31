theory continuousInv
  imports Complete
begin

lemma chainrule:
  assumes "\<forall>x. ((\<lambda>v. g (vec2state v)) has_derivative g' (vec2state x)) (at x within UNIV)"
    and "ODEsol ode p d"
    and "t \<in> {0 .. d}"
  shows "((\<lambda>t. g (p t)) has_derivative (\<lambda>s. g' (p t) (s *\<^sub>R ODE2Vec ode (p t)))) (at t within {0 .. d})"
proof -
  have 1: "(\<And>x. x \<in> UNIV \<Longrightarrow> ((\<lambda>v. g (vec2state v)) has_derivative g' (vec2state x)) (at x))"
    using assms(1) by auto
  have 2: "0 \<le> t \<and> t \<le> d"
    using assms(3) by auto
  have 3: "((\<lambda>t. state2vec(p t)) has_derivative (\<lambda>s. s *\<^sub>R ODE2Vec ode (p t))) (at t within {0..d})"
    using 2 assms(2) unfolding ODEsol_def has_vderiv_on_def has_vector_derivative_def by auto
  show ?thesis
  using 1 2 3 has_derivative_in_compose2[of UNIV "(\<lambda>v. g (vec2state v))" "(\<lambda>v. g' (vec2state v))" "(\<lambda>t. state2vec (p t))" "{0 .. d}" t "(\<lambda>s. s *\<^sub>R ODE2Vec ode (p t))"]
  by auto
qed

theorem Valid_inv:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) = 0"
    shows "\<Turnstile> {\<lambda>s tr. inv s = r \<and> tr = tra \<and> b s}
       Cont ode b
      {\<lambda>s tr. (\<exists> p d. tr = tra @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})] \<and> (\<forall>t \<in>{0..d}. inv (p t) = r))}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal for d p
    apply (rule exI[where x="p"])
    apply auto
    subgoal premises pre for \<tau>
    proof-
      have 1: "\<forall>t\<in>{0 .. d}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))) (at t within {0 .. d})"
        using pre assms
        using chainrule[of inv "\<lambda>x. g'(state2vec x)" ode p d] 
        by auto
      have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec ode (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec ode (p t))" if "t\<in>{0 .. d}" for t
        using 1 unfolding has_derivative_def bounded_linear_def 
        using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))"]
        by blast
      have 3: "\<forall>s. (s *\<^sub>R 1) = s" by simp
      have 4: "\<forall>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)) = s *\<^sub>R g' (state2vec(p t)) (ODE2Vec ode (p t))" if "t\<in>{0 .. d}" for t
        using 2 3 that by auto
      have 5: "\<forall>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t))= 0" if "t\<in>{0 ..<d}" for t
        using 4 assms(2) that pre by auto
      show ?thesis
        using mvt_real_eq[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" \<tau>]
        using 1 5 pre by auto
    qed
    done
  done




end