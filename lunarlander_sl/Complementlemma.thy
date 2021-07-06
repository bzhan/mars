theory Complementlemma
  imports
    ContinuousInv
    BigStepParallel 
begin

subsection \<open>More theorems about derivatives\<close>

text \<open>
  p' = q implies p[i]' = q[i] for each component i.
\<close>
lemma has_derivative_proj:
  fixes x :: vec
    and p :: "vec \<Rightarrow> vec"
  assumes "(p has_derivative q x) (at x within D)"
  shows "((\<lambda>v. p v $ i) has_derivative (\<lambda>v. q x v $ i)) (at x within D)"
  using assms unfolding has_derivative_def  
  apply auto
  subgoal
    unfolding bounded_linear_def bounded_linear_axioms_def
    apply auto
    subgoal for K
      unfolding linear_iff by auto
    subgoal for K
      apply (rule exI[where x=K])
      apply auto subgoal for x'
        using norm_bound_component_le_cart by blast
      done
    done
  subgoal
    using tendsto_vec_nth by fastforce
  done

text \<open>
  p[i]' = q[i] for each component i implies p' = q.
\<close>
lemma has_derivative_projI:
  fixes p :: "vec \<Rightarrow> vec"
  assumes "\<forall>i. ((\<lambda>v. p v $ i) has_derivative (\<lambda> v. q t v $ i)) (at t within D)"
  shows "(p has_derivative q t) (at t within D)"
  using assms unfolding  has_derivative_def
  apply auto
  subgoal
    unfolding bounded_linear_def bounded_linear_axioms_def
    apply auto
  subgoal  
    unfolding linear_iff apply auto 
     apply (simp add: vec_eq_iff)
    apply (simp add: vec_eq_iff)
    done
  subgoal premises pre 
  proof-
    have a1: "\<forall>i. (\<exists>K. \<forall>x. norm (q t x $ i) \<le> norm x * K)"
      using pre by auto
    have a2: "(\<exists>K. \<forall>x. norm (q t x $ i) \<le> norm x * K)" for i
      using a1 by auto
    let ?K="\<chi> i. SOME k. \<forall>x. norm (q t x $ i) \<le> norm x * k"
    have a3: "\<forall>x. norm (q t x $ i) \<le> norm x * (?K$i)" for i
    proof -
      obtain k where k: "\<forall>x. norm (q t x $ i) \<le> norm x * k"
        using a2 by auto
      show ?thesis
        unfolding vec_lambda_beta
        apply (rule someI[where P="\<lambda>k. \<forall>x. norm (q t x $ i) \<le> norm x * k" and x=k])
        using k by auto
    qed
    obtain K where K: "\<forall>x. norm (q t x $ i) \<le> norm x * (K$i)" for i
      using a3 by blast
    show ?thesis
      apply (rule exI[where x= "sum(\<lambda>i. K$i) UNIV"])
      apply auto
      subgoal for x
      proof-
        have "\<And>i. norm (q t x $ i) \<le> norm x * (K$i)"
          using K apply auto
          done
        then have "\<And>i. \<bar>q t x $ i\<bar> \<le> norm x * (K$i)"
          apply(clarsimp simp: norm_vec_def L2_set_def)
          done
        then have b1: "(\<Sum>i\<in>UNIV. \<bar>q t x $ i\<bar>) \<le> (\<Sum>i\<in>UNIV. norm x * K $ i)"
          by (rule sum_mono)
        have b2: "(\<Sum>i\<in>UNIV. norm x * K $ i) = norm x * (\<Sum>i\<in>UNIV. K $ i)"
          by (simp add: sum_distrib_left)
        show ?thesis
        using norm_le_l1_cart[where x= " q t x"] b1 b2 by auto
        qed
        done
    qed
  done
  subgoal
    by (auto intro: vec_tendstoI)
  done

lemma derivative_exp [simp, derivative_intros]:
  "(exp has_derivative (*) (exp (x :: real))) (at x)"
  using DERIV_exp unfolding has_field_derivative_def
  by auto

lemma derivative_exp_const [derivative_intros]:
  fixes c :: real
  shows "((\<lambda>x. exp (c * x)) has_derivative (\<lambda>xa. xa * c * exp (c * x))) (at x)"
proof-
  have 1: "((*) c has_derivative (\<lambda>x. x * c)) (at x)"
    apply (rule has_derivative_eq_rhs)
     apply (auto intro!: derivative_intros)[1]
    by auto
  show ?thesis using has_derivative_exp[OF 1] 
    by auto
  qed

lemma SOME_const_vderiv [derivative_intros, simp]:
  fixes p :: " real \<Rightarrow> bool"
  assumes "(f has_vderiv_on f') S"
  shows "((\<lambda>t. (SOME k. p k) * f t) has_vderiv_on (\<lambda>t. (SOME k . p k) * f' t)) S"
  apply (rule has_vderiv_on_eq_rhs)
   apply (rule has_vderiv_on_mult)
    apply (auto intro: derivative_intros)[1]
  using assms apply auto
  done


subsection \<open>More theorems about logical operators\<close>

theorem Valid_post_and:
  assumes "\<Turnstile> {P} c {Q1}"
    and "\<Turnstile> {P} c {Q2}"
  shows "\<Turnstile> {P} c {\<lambda>s tr. Q1 s tr \<and> Q2 s tr}"
  using assms unfolding Valid_def entails_def by blast

theorem Valid_pre_cases:
  assumes "\<Turnstile> {\<lambda>s tr. P s \<and> Q s} c {R}"
    and "\<Turnstile> {\<lambda>s tr. P s \<and> \<not> Q s} c {R}"
  shows "\<Turnstile> {\<lambda>s tr. P s} c {R}"
  using assms unfolding Valid_def entails_def by blast

theorem Valid_ichoice_sp_st:
  assumes "\<Turnstile> {P} c1 {Q}"
    and "\<Turnstile> {P} c2 {Q}"
  shows "\<Turnstile> {P} IChoice c1 c2 {Q}"
  using assms unfolding Valid_def by (auto elim: ichoiceE)

theorem Valid_cond_split:
  assumes "\<Turnstile> {\<lambda>s t. b s \<and> P s t} c1 {Q}"
    and "\<Turnstile> {\<lambda>s t. \<not>b s \<and> P s t} c2 {Q}"
  shows "\<Turnstile> {\<lambda>s t. P s t}
             IF b THEN c1 ELSE c2 FI
            {\<lambda>s t. Q s t}"
  using assms unfolding Valid_def
  by (auto elim!: condE seqE)

theorem Valid_cond_split':
  assumes "\<Turnstile> {\<lambda>s t. b s \<and> P s t} c1; d {Q}"
    and "\<Turnstile> {\<lambda>s t. \<not>b s \<and> P s t} c2; d {Q}"
  shows "\<Turnstile> {\<lambda>s t. P s t}
             IF b THEN c1 ELSE c2 FI; d
            {\<lambda>s t. Q s t}"
  using assms unfolding Valid_def
  apply (auto elim!: condE seqE)
  by (auto simp add: seqB)

theorem Valid_ode_not:
  assumes "\<And>s. P s \<Longrightarrow> \<not> b s"
    and "\<And>s. P s \<Longrightarrow> Q s"
  shows "\<Turnstile> {\<lambda>s tr. P s}
     Cont ode b
    {\<lambda>s tr. Q s}"
  unfolding Valid_def
  using assms by (auto elim: contE)

subsection \<open>Differential invariant rules\<close>

text \<open>
  If the Lie derivative of inv with respect to ODE is zero, then inv
  is an invariant of the state.
\<close>
theorem Valid_inv_s_eq:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) = 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s = r}
     Cont ode b
    {\<lambda>s tr. inv s = r}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof -
    have 1: "\<forall>t\<in>{0 .. d}. ((\<lambda>t. inv (p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))) (at t within {0 .. d})"
      using pre assms
      using chainrule[of inv "\<lambda>x. g'(state2vec x)" ode p d] 
      by auto
    have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec ode (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec ode (p t))" if "t\<in>{0 .. d}" for t
      using 1 unfolding has_derivative_def bounded_linear_def 
      using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))"]
      by blast
    have 3: "\<forall>s. (s *\<^sub>R 1) = s" by simp
    have 4: "\<forall>s. g' (state2vec (p t)) (s *\<^sub>R ODE2Vec ode (p t)) = s *\<^sub>R g' (state2vec(p t)) (ODE2Vec ode (p t))" if "t\<in>{0 .. d}" for t
      using 2 3 that by auto
    have 5: "\<forall>s. g' (state2vec (p t)) (s *\<^sub>R ODE2Vec ode (p t)) = 0" if "t\<in>{0 ..<d}" for t
      using 4 assms(2) that pre by auto
    show ?thesis
      using mvt_real_eq[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" d]
      using 1 5 pre by auto
  qed
  done

text \<open>
  Version of invariant rule with trace (already proved).
\<close>
lemmas Valid_inv_tr_eq = Valid_inv'

text \<open>
  Version of invariant rule with both state and trace.
\<close>
theorem Valid_inv_s_tr_eq:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) = 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s = r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. inv s = r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s = r)) tr}"
  apply (rule Valid_post_and)
   apply (rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_s_eq)
     prefer 3
  subgoal
    by(auto simp add: entails_def)
    prefer 3
    apply (rule Valid_inv_tr_eq)
    using assms by auto

text \<open>
  If the Lie derivative of inv with respect to ODE is nonnegative, then
  inv is a non-decreasing function of the state.
\<close>
theorem Valid_inv_s_ge:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s \<ge> r}
     Cont ode b
    {\<lambda>s tr. inv s \<ge> r}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof -
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
    have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)) \<ge> 0" if "t\<in>{0 ..<d}" for t
      using 4 assms(2) that pre by auto
    show ?thesis
      using mvt_real_ge[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" d]
      using 1 5 pre by auto
  qed
  done

text \<open>
  Version of nonnegative invariant rule for trace.
\<close>
theorem Valid_inv_tr_ge:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s \<ge> r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s \<ge> r)) tr}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal for tr1 d p
    apply(simp add: join_assn_def)
    apply(rule exI [where x="tr1"])
    apply auto
    apply (auto intro!: ode_inv_assn.intros)
  subgoal premises pre for \<tau>
  proof -
    have 1: "\<forall>t\<in>{0 .. d}. ((\<lambda>t. inv(p t)) has_derivative (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))) (at t within {0 .. d})"
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
    have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t))\<ge> 0" if "t\<in>{0 ..<d}" for t
      using 4 assms(2) that pre by auto
    show ?thesis
      using mvt_real_ge[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" \<tau>]
      using 1 5 pre by auto
  qed
  done
  done

text \<open>
  Version of nonnegative invariant rule for both state and trace.
\<close>
theorem Valid_inv_s_tr_ge:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s \<ge> r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. inv s \<ge> r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s \<ge> r)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_s_ge)
     prefer 3
  subgoal
    by(auto simp add: entails_def)
    prefer 3
    apply(rule Valid_inv_tr_ge)
    using assms by auto

text \<open>
  Versions of invariant rule with inv s > r.
\<close>
theorem Valid_inv_s_g:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s > r}
     Cont ode b
    {\<lambda>s tr. inv s > r}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof -
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
    have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)) \<ge> 0" if "t\<in>{0 ..<d}" for t
      using 4 assms(2) that pre by auto
    show ?thesis
      using mvt_real_ge[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" d]
      using 1 5 pre by auto
  qed
  done


theorem Valid_inv_tr_g:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s > r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s > r)) tr}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal for tr1 d p
    apply(simp add: join_assn_def)
    apply(rule exI [where x="tr1"])
    apply auto
    apply (auto intro!: ode_inv_assn.intros)
  subgoal premises pre for \<tau>
  proof -
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
    have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t))\<ge> 0" if "t\<in>{0 ..<d}" for t
      using 4 assms(2) that pre by auto
    show ?thesis
      using mvt_real_ge[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" \<tau>]
      using 1 5 pre by auto
  qed
  done
  done

theorem Valid_inv_s_tr_g:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s > r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. inv s > r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s > r)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_s_g)
     prefer 3
  subgoal
    by(auto simp add: entails_def)
    prefer 3
    apply(rule Valid_inv_tr_g)
    using assms by auto

text \<open>
  If the Lie derivative of inv with respect to ODE is nonpositive, then
  inv is a non-increasing function of the state.
\<close>
theorem Valid_inv_s_le:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<le> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s \<le> r}
     Cont ode b
    {\<lambda>s tr. inv s \<le> r}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof -
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
    have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)) \<le> 0" if "t\<in>{0 ..<d}" for t
      using 4 assms(2) that pre 
      using scaleR_nonneg_nonpos by fastforce
    show ?thesis
      using mvt_real_le[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" d]
      using 1 5 pre by auto
  qed
  done

theorem Valid_inv_tr_le:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<le> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s \<le> r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s \<le> r)) tr}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal for tr1 d p
    apply(simp add: join_assn_def)
    apply(rule exI [where x="tr1"])
    apply auto
    apply (auto intro!: ode_inv_assn.intros)
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
    have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t))\<le> 0" if "t\<in>{0 ..<d}" for t
      using 4 assms(2) that pre
      using scaleR_nonneg_nonpos by fastforce
    show ?thesis
      using mvt_real_le[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" \<tau>]
      using 1 5 pre by auto
  qed
  done
  done

theorem Valid_inv_s_tr_le:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<le> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s \<le> r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. inv s \<le> r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s \<le> r)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_s_le)
     prefer 3
  subgoal
    by(auto simp add: entails_def)
    prefer 3
    apply(rule Valid_inv_tr_le)
  using assms by auto

text \<open>
  Version of invariant rule with inv < r.
\<close>
theorem Valid_inv_s_l:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<le> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s < r}
     Cont ode b
    {\<lambda>s tr. inv s < r}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
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
    have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)) \<le> 0" if "t\<in>{0 ..<d}" for t
      using 4 assms(2) that pre 
      using scaleR_nonneg_nonpos by fastforce
    show ?thesis
      using mvt_real_le[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" d]
      using 1 5 pre by auto
  qed
  done

theorem Valid_inv_tr_l:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<le> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s < r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s < r)) tr}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal for tr1 d p
    apply(simp add: join_assn_def)
    apply(rule exI [where x="tr1"])
    apply auto
    apply (auto intro!: ode_inv_assn.intros)
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
      have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t))\<le> 0" if "t\<in>{0 ..<d}" for t
        using 4 assms(2) that pre
        using scaleR_nonneg_nonpos by fastforce
      show ?thesis
        using mvt_real_le[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" \<tau>]
        using 1 5 pre by auto
    qed
    done
  done

theorem Valid_inv_s_tr_l:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<le> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s < r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. inv s < r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s < r)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_s_l)
     prefer 3
  subgoal
    by(auto simp add: entails_def)
    prefer 3
    apply(rule Valid_inv_tr_l)
  using assms by auto


subsection \<open>Unique solution rules\<close>

text \<open>
  Strongest-postcondition rule for unique solutions, state only.
\<close>
theorem Valid_ode_unique_solution_s_sp:
  assumes "\<And>s. P s \<Longrightarrow> d s > 0 \<and> ODEsol ode (p s) (d s) \<and>
                (\<forall>t. t \<ge> 0 \<and> t < d s \<longrightarrow> b (p s t)) \<and>
                \<not>b (p s (d s)) \<and> p s 0 = s"
    and "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    and "\<And>s. P s \<Longrightarrow> b s"
  shows "\<Turnstile>
    {\<lambda>s t. P s}
      Cont ode b
    {\<lambda>s t. \<exists>s'. s = p s' (d s') \<and> P s'}"
proof -
  have a: "s' = p s (d s) \<and> Wait\<^sub>t (d s) (\<lambda>\<tau>. State (p s \<tau>)) ({}, {}) tr2"
    if "ODE\<^sub>t s ode b s' tr2" "P s" for s s' tr2
  proof -
    have a1: "d s > 0" "ODEsol ode (p s) (d s)" "\<forall>t. 0 \<le> t \<and> t < d s \<longrightarrow> b (p s t)"
             "\<not>b (p s (d s))" "p s 0 = s"
      using assms(1) that(2) by auto
    show ?thesis
      using Valid_ode_unique_solution_aux[OF a1(1-2) _ a1(4-5) assms(2) that(1)] a1(3)
      by auto
  qed
  have b: "ODE\<^sub>t s ode b s' tr2 \<Longrightarrow> \<not>b s \<Longrightarrow> s = s' \<and> tr2 = []" for s s' tr2
    apply (induct rule: ode_assn.induct) by auto
  show ?thesis
    apply (rule Valid_weaken_pre)
     prefer 2 apply (rule Valid_ode')
    apply (auto simp add: entails_def magic_wand_assn_def)
    subgoal for s  s' tr
      apply (rule exI[where x=s])
      apply (auto simp add: join_assn_def conj_assn_def pure_assn_def)
      apply (auto simp add: a)
      done
    done
qed

subsection \<open>More refined invariant rules\<close>

text \<open>
  Strengthen the nonnegative invariant rule by requiring that the
  Lie derivative of inv is nonnegative only in the region inv \<ge> r.
\<close>
theorem Valid_inv_new_s_g:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> inv S \<ge> r \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s > r}
     Cont ode b
    {\<lambda>s tr. inv s > r}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof -
    obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
     using pre unfolding ODEsol_def by auto
    have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
      using pre assms e
      using chainrule'[of inv "\<lambda>x. g'(state2vec x)" p "( ode)" e d] 
      by auto
    have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec (ode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec (ode) (p t))" if "t\<in>{-e .. d+e}" for t
        using 1 unfolding has_derivative_def bounded_linear_def 
        using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ode) (p t)))"]
        by blast
     have 3: "\<forall>s. (s *\<^sub>R 1) = s" by simp
     have 4: "\<forall>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (ODE2Vec (ode) (p t))" if "t\<in>{-e .. d+e}" for t
        using 2 3 that by auto
      show ?thesis
        using real_inv_g[OF 1,of r d]
        using 4 pre assms e(1) 
        by auto
    qed
    done

subsection \<open>Boundary rules\<close>

text \<open>
  Boundary rule: if the boundary condition is b s > r, then on reaching
  the boundary we must have b s = r.
\<close>
theorem Valid_inv_b_s_ge:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' x) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. b s > r}
     Cont ode (\<lambda> s. b s > r)
    {\<lambda>s tr. b s = r}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof(rule ccontr)
    assume "b (p d) \<noteq> r"
    then have g: "b (p d) < r" using pre by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
      using pre unfolding ODEsol_def by auto
    have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b (p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
      using pre assms e
      using chainrule'[of b "\<lambda>x. g'(state2vec x)" p ode e d] 
      by auto
    have 2:"continuous (at t within {-e<..<d+e}) (\<lambda>t. b (p t))" if "t\<in>{0 .. d}" for t
      apply(rule has_derivative_continuous)
      apply(rule has_derivative_subset)
      using 1 that e(1) pre(2) by auto
    have 3:"\<forall>t\<in>{0 .. d}. isCont (\<lambda>t. b (p t)) t"
      apply auto subgoal for t
      using continuous_within_open[of t "{-e<..<d+e}" "\<lambda>t. b (p t)"]
      using 2  e(1) by simp
    done
    then obtain dd where dd:"b (p dd) = r" "dd \<in> {0..d}"
      using IVT2[of "(\<lambda>t. b (p t))" d r 0]
      using pre g by force
    then have 4:"dd<d" 
      using g  le_less by auto
    then show False using dd pre
      using atLeastAtMost_iff by blast
    qed
    done

text \<open>
  Trace version of the boundary rule.
\<close>
theorem Valid_inv_b_tr_ge:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' x) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. P tr \<and> b s > r}
     Cont ode (\<lambda> s. b s > r)
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. b s \<ge> r)) tr}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal for tr1 d p
    apply(simp add: join_assn_def)
    apply(rule exI [where x="tr1"])
    apply auto
    apply (auto intro!: ode_inv_assn.intros)
  subgoal premises pre for \<tau>
  proof(rule ccontr)
    assume "\<not> r \<le> b (p \<tau>)"
    then have g:"b (p \<tau>) < r" by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b (p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of b "\<lambda>x. g'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2:"continuous (at t within {-e<..<\<tau>+e}) (\<lambda>t. b (p t))" if "t\<in>{0 .. d}" for t
        apply(rule has_derivative_continuous)
        apply(rule has_derivative_subset)
        using 1 that e(1) pre by auto
      have 3:"\<forall>t\<in>{0 .. \<tau>}. isCont (\<lambda>t. b (p t)) t"
        apply auto subgoal for t
        using continuous_within_open[of t "{-e<..<\<tau>+e}" "(\<lambda>t. b (p t))"]
        using 2  e(1) pre by auto
      done
      then obtain dd where dd:"b (p dd) = r" "dd \<in> {0..\<tau>}"
        using IVT2[of "(\<lambda>t. b (p t))" \<tau> r 0]
        using pre g by force
      then have 4:"dd<\<tau>" 
        using g  le_less by auto
      then show False using dd pre
        by auto
    qed
    done
  done

text \<open>
  Version of boundary rule with both state and trace.
\<close>
theorem Valid_inv_b_s_tr_ge:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' x) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. P tr \<and> b s > r}
     Cont ode (\<lambda>s. b s > r)
    {\<lambda>s tr. b s = r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. b s \<ge> r)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_b_s_ge)
     prefer 3
    apply(rule Valid_inv_b_tr_ge)
  apply(auto simp add: entails_def)
    using assms by auto

text \<open>
  Two-boundary rules: if the boundary is b1 s > r1 and b2 s > r2, then
  on reaching the boundary at least one of the inequality becomes equal.
\<close>
theorem Valid_inv_b_s_ge_and_ge:
  fixes b1 :: "state \<Rightarrow> real"
  fixes b2 :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b1 (vec2state v)) has_derivative g1' x) (at x within UNIV)"
      and "\<forall>x. ((\<lambda>v. b2 (vec2state v)) has_derivative g2' x) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. b1 s > r1 \<and> b2 s > r2}
     Cont ode (\<lambda> s. b1 s > r1 \<and> b2 s > r2)
    {\<lambda>s tr. b1 s = r1 \<or> b2 s = r2}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof(rule ccontr)
    assume "\<not> r1 < b1 (p d)"
    then have g: "b1 (p d) < r1" using pre by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b1 (p t)) has_derivative  (\<lambda>s. g1' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of b1 "\<lambda>x. g1'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2:"continuous (at t within {-e<..<d+e}) (\<lambda>t. b1 (p t))" if "t\<in>{0 .. d}" for t
        apply(rule has_derivative_continuous)
        apply(rule has_derivative_subset)
        using 1 that e(1) pre(2) by auto
      have 3:"\<forall>t\<in>{0 .. d}. isCont (\<lambda>t. b1 (p t)) t"
        apply auto subgoal for t
        using continuous_within_open[of t "{-e<..<d+e}" "(\<lambda>t. b1 (p t))"]
        using 2  e(1) by simp
      done
    then obtain dd where dd:"b1 (p dd) = r1" "dd \<in> {0..d}"
      using IVT2[of "(\<lambda>t. b1 (p t))" d r1 0]
      using pre g by force
    then have 4:"dd<d" 
      using g  le_less by auto
    then show False using dd pre
      using atLeastAtMost_iff by blast
  qed
subgoal premises pre for d p
  proof(rule ccontr)
    assume "\<not> r2 < b2 (p d)"
    then have g: "b2 (p d) < r2" using pre by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b2 (p t)) has_derivative  (\<lambda>s. g2' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of b2 "\<lambda>x. g2'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2:"continuous (at t within {-e<..<d+e}) (\<lambda>t. b2 (p t))" if "t\<in>{0 .. d}" for t
        apply(rule has_derivative_continuous)
        apply(rule has_derivative_subset)
        using 1 that e(1) pre(2) by auto
      have 3:"\<forall>t\<in>{0 .. d}. isCont (\<lambda>t. b2 (p t)) t"
        apply auto subgoal for t
        using continuous_within_open[of t "{-e<..<d+e}" "(\<lambda>t. b2 (p t))"]
        using 2  e(1) by simp
      done
    then obtain dd where dd:"b2 (p dd) = r2" "dd \<in> {0..d}"
      using IVT2[of "(\<lambda>t. b2 (p t))" d r2 0]
      using pre g by force
    then have 4:"dd<d" 
      using g  le_less by auto
    then show False using dd pre
      using atLeastAtMost_iff by blast
    qed
    done

text \<open>
  Trace version of the two boundary rule.
\<close>
theorem Valid_inv_b_tr_ge_and_ge:
  fixes b1 :: "state \<Rightarrow> real"
  fixes b2 :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b1 (vec2state v)) has_derivative g1' x) (at x within UNIV)"
      and "\<forall>x. ((\<lambda>v. b2 (vec2state v)) has_derivative g2' x) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. P tr \<and> b1 s > r1 \<and> b2 s > r2}
     Cont ode (\<lambda> s. b1 s > r1 \<and> b2 s > r2)
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. b1 s \<ge> r1 \<and> b2 s \<ge> r2)) tr}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises ppre for tr1 d p
  proof-
    have "P tr1 \<Longrightarrow>
    0 < d \<Longrightarrow>
    ODEsol ode p d \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> r1 < b1 (p t) \<and> r2 < b2 (p t) \<Longrightarrow>
    \<not>   r1 < b1 (p d) \<Longrightarrow> (P @\<^sub>t ode_inv_assn (\<lambda>s. r1 \<le> b1 s \<and> r2 \<le> b2 s))
        (tr1 @ [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
    apply(simp add: join_assn_def)
    apply(rule exI [where x="tr1"])
    apply auto
    apply (auto intro!: ode_inv_assn.intros)
  subgoal premises pre for \<tau>
  proof(rule ccontr)
    assume "\<not> r1 \<le> b1 (p \<tau>)"
    then have g:"b1 (p \<tau>) < r1" by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b1 (p t)) has_derivative  (\<lambda>s. g1' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of b1 "\<lambda>x. g1'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2:"continuous (at t within {-e<..<\<tau>+e}) (\<lambda>t. b1 (p t))" if "t\<in>{0 .. d}" for t
        apply(rule has_derivative_continuous)
        apply(rule has_derivative_subset)
        using 1 that e(1) pre by auto
      have 3:"\<forall>t\<in>{0 .. \<tau>}. isCont (\<lambda>t. b1 (p t)) t"
        apply auto subgoal for t
        using continuous_within_open[of t "{-e<..<\<tau>+e}" "(\<lambda>t. b1 (p t))"]
        using 2  e(1) pre by auto
      done
      then obtain dd where dd:"b1 (p dd) = r1" "dd \<in> {0..\<tau>}"
        using IVT2[of "(\<lambda>t. b1 (p t))" \<tau> r1 0]
        using pre g by force
      then have 4:"dd<\<tau>" 
        using g  le_less by auto
      then show False using dd pre
        by auto
    qed
    subgoal premises pre for \<tau>
  proof(rule ccontr)
    assume "\<not> r2 \<le> b2 (p \<tau>)"
    then have g:"b2 (p \<tau>) < r2" by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b2 (p t)) has_derivative  (\<lambda>s. g2' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of b2 "\<lambda>x. g2'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2:"continuous (at t within {-e<..<\<tau>+e}) (\<lambda>t. b2 (p t))" if "t\<in>{0 .. d}" for t
        apply(rule has_derivative_continuous)
        apply(rule has_derivative_subset)
        using 1 that e(1) pre by auto
      have 3:"\<forall>t\<in>{0 .. \<tau>}. isCont (\<lambda>t. b2 (p t)) t"
        apply auto subgoal for t
        using continuous_within_open[of t "{-e<..<\<tau>+e}" "(\<lambda>t. b2 (p t))"]
        using 2  e(1) pre by auto
      done
      then obtain dd where dd:"b2 (p dd) = r2" "dd \<in> {0..\<tau>}"
        using IVT2[of "(\<lambda>t. b2 (p t))" \<tau> r2 0]
        using pre g by force
      then have 4:"dd<\<tau>" 
        using g  le_less by auto
      then show False using dd pre
        by auto
    qed
    done
  then show ?thesis using ppre by auto
qed
 subgoal premises ppre for tr1 d p
  proof-
    have "P tr1 \<Longrightarrow>
    0 < d \<Longrightarrow>
    ODEsol ode p d \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> r1 < b1 (p t) \<and> r2 < b2 (p t) \<Longrightarrow>
    \<not>   r2 < b2 (p d) \<Longrightarrow> (P @\<^sub>t ode_inv_assn (\<lambda>s. r1 \<le> b1 s \<and> r2 \<le> b2 s))
        (tr1 @ [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
    apply(simp add: join_assn_def)
    apply(rule exI [where x="tr1"])
    apply auto
    apply (auto intro!: ode_inv_assn.intros)
  subgoal premises pre for \<tau>
  proof(rule ccontr)
    assume "\<not> r1 \<le> b1 (p \<tau>)"
    then have g:"b1 (p \<tau>) < r1" by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b1 (p t)) has_derivative  (\<lambda>s. g1' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of b1 "\<lambda>x. g1'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2:"continuous (at t within {-e<..<\<tau>+e}) (\<lambda>t. b1 (p t))" if "t\<in>{0 .. d}" for t
        apply(rule has_derivative_continuous)
        apply(rule has_derivative_subset)
        using 1 that e(1) pre by auto
      have 3:"\<forall>t\<in>{0 .. \<tau>}. isCont (\<lambda>t. b1 (p t)) t"
        apply auto subgoal for t
        using continuous_within_open[of t "{-e<..<\<tau>+e}" "(\<lambda>t. b1 (p t))"]
        using 2  e(1) pre by auto
      done
      then obtain dd where dd:"b1 (p dd) = r1" "dd \<in> {0..\<tau>}"
        using IVT2[of "(\<lambda>t. b1 (p t))" \<tau> r1 0]
        using pre g by force
      then have 4:"dd<\<tau>" 
        using g  le_less by auto
      then show False using dd pre
        by auto
    qed
    subgoal premises pre for \<tau>
  proof(rule ccontr)
    assume "\<not> r2 \<le> b2 (p \<tau>)"
    then have g:"b2 (p \<tau>) < r2" by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b2 (p t)) has_derivative  (\<lambda>s. g2' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of b2 "\<lambda>x. g2'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2:"continuous (at t within {-e<..<\<tau>+e}) (\<lambda>t. b2 (p t))" if "t\<in>{0 .. d}" for t
        apply(rule has_derivative_continuous)
        apply(rule has_derivative_subset)
        using 1 that e(1) pre by auto
      have 3:"\<forall>t\<in>{0 .. \<tau>}. isCont (\<lambda>t. b2 (p t)) t"
        apply auto subgoal for t
        using continuous_within_open[of t "{-e<..<\<tau>+e}" "(\<lambda>t. b2 (p t))"]
        using 2  e(1) pre by auto
      done
      then obtain dd where dd:"b2 (p dd) = r2" "dd \<in> {0..\<tau>}"
        using IVT2[of "(\<lambda>t. b2 (p t))" \<tau> r2 0]
        using pre g by force
      then have 4:"dd<\<tau>" 
        using g  le_less by auto
      then show False using dd pre
        by auto
    qed
    done
  then show ?thesis using ppre by auto
qed
  done

text \<open>
  Version of two-boundary rule with both state and trace.
\<close>
theorem Valid_inv_b_s_tr_ge_and_ge:
  fixes b1 :: "state \<Rightarrow> real"
  fixes b2 :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b1 (vec2state v)) has_derivative g1' x) (at x within UNIV)"
      and "\<forall>x. ((\<lambda>v. b2 (vec2state v)) has_derivative g2' x) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. P tr \<and> b1 s > r1 \<and> b2 s > r2}
     Cont ode (\<lambda> s. b1 s > r1 \<and> b2 s > r2)
    {\<lambda>s tr. (b1 s = r1 \<or> b2 s = r2) \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. b1 s \<ge> r1 \<and> b2 s \<ge> r2)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_b_s_ge_and_ge)
     prefer 4
    apply(rule Valid_inv_b_tr_ge_and_ge)
  apply(auto simp add: entails_def)
  using assms by auto

text \<open>
  Boundary rule: less-than version.
\<close>
theorem Valid_inv_b_s_le:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' x) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. b s < r}
     Cont ode (\<lambda> s. b s < r)
    {\<lambda>s tr. b s = r}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof(rule ccontr)
    assume "b (p d) \<noteq> r"
    then have g: "b (p d) > r" using pre by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b (p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of b "\<lambda>x. g'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2:"continuous (at t within {-e<..<d+e}) (\<lambda>t. b (p t))" if "t\<in>{0 .. d}" for t
        apply(rule has_derivative_continuous)
        apply(rule has_derivative_subset)
        using 1 that e(1) pre(2) by auto
      have 3:"\<forall>t\<in>{0 .. d}. isCont (\<lambda>t. b (p t)) t"
        apply auto subgoal for t
        using continuous_within_open[of t "{-e<..<d+e}" "(\<lambda>t. b (p t))"]
        using 2  e(1) by simp
      done
    then obtain dd where dd:"b (p dd) = r" "dd \<in> {0..d}"
      using IVT[of "(\<lambda>t. b (p t))" 0 r d]
      using pre g by force
    then have 4:"dd<d" 
      using g  le_less by auto
    then show False using dd pre
      using atLeastAtMost_iff by blast
    qed
    done

theorem Valid_inv_b_tr_le:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' x) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. P tr \<and> b s < r}
     Cont ode (\<lambda> s. b s < r)
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. b s \<le> r)) tr}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal for tr1 d p
    apply(simp add: join_assn_def)
    apply(rule exI [where x="tr1"])
    apply auto
    apply (auto intro!: ode_inv_assn.intros)
  subgoal premises pre for \<tau>
  proof(rule ccontr)
    assume "\<not> b (p \<tau>) \<le> r"
    then have g:"b (p \<tau>) > r" by auto
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. b (p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of b "\<lambda>x. g'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2:"continuous (at t within {-e<..<\<tau>+e}) (\<lambda>t. b (p t))" if "t\<in>{0 .. d}" for t
        apply(rule has_derivative_continuous)
        apply(rule has_derivative_subset)
        using 1 that e(1) pre by auto
      have 3:"\<forall>t\<in>{0 .. \<tau>}. isCont (\<lambda>t. b (p t)) t"
        apply auto subgoal for t
        using continuous_within_open[of t "{-e<..<\<tau>+e}" "(\<lambda>t. b (p t))"]
        using 2  e(1) pre by auto
      done
      then obtain dd where dd:"b (p dd) = r" "dd \<in> {0..\<tau>}"
        using IVT[of "(\<lambda>t. b (p t))" 0 r \<tau>]
        using pre g by force
      then have 4:"dd<\<tau>" 
        using g  le_less by auto
      then show False using dd pre
        by auto
    qed
    done
  done

theorem Valid_inv_b_s_tr_le:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' x) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. P tr \<and> b s < r}
     Cont ode (\<lambda>s. b s < r)
    {\<lambda>s tr. b s = r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. b s \<le> r)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_b_s_le)
     prefer 3
    apply(rule Valid_inv_b_tr_le)
  apply(auto simp add: entails_def)
    using assms by auto

subsection \<open>Differential cut rules\<close>

text \<open>
  If c is an invariant, then it can be added to the boundary.
\<close>
theorem DC':
  assumes
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {\<lambda>s tr. c s \<and> (P @\<^sub>t ode_inv_assn c) tr}"
  and
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> (\<lambda>s. b s \<and> c s) s}
         Cont ode (\<lambda>s. b s \<and> c s)
        {\<lambda>s tr. d s \<and> (P @\<^sub>t ode_inv_assn d) tr}"
  shows
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {\<lambda>s tr. d s \<and> (P @\<^sub>t ode_inv_assn d) tr}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for tr T p
  proof -
    have 1:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre by auto
    have 2:"(P @\<^sub>t ode_inv_assn c) (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using assms(1) 1
      unfolding Valid_def using pre by auto
    obtain tra1 tra2 where tra1:"P tra1" and tra2:"ode_inv_assn c tra2" and tra3:"tra1 @ tra2 = (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using 2 unfolding join_assn_def by auto
    obtain T' p' where Tp:"tra2 = [WaitBlk (ereal T') (\<lambda>\<tau>. State (p' \<tau>)) ({}, {})]"
      using tra2 apply (induct rule: ode_inv_assn.induct)
      by auto
    have 3:"ode_inv_assn c [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
      using Tp tra3 tra2 by auto
    have 4: "\<forall>t\<in>{0..T}. c (p t)"
      using 3 apply (elim ode_inv_assn_elim)
      apply auto
      subgoal for d p' t
        apply (frule WaitBlk_cong)
        apply (frule WaitBlk_cong2)
        by auto
      done
    have 5:"big_step (Cont ode (\<lambda>s. b s \<and> c s)) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre 4 by auto
    show ?thesis
      using assms(2) 
      unfolding Valid_def 
      using pre 4 5
      by (smt atLeastAtMost_iff)
  qed
subgoal premises pre for tr T p
  proof-
    have 1:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre by auto
    have 2:"(P @\<^sub>t ode_inv_assn c) (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using assms(1) 1
      unfolding Valid_def using pre by auto
    obtain tra1 tra2 where tra1:"P tra1" and tra2:"ode_inv_assn c tra2" and tra3:"tra1 @ tra2 = (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using 2 unfolding join_assn_def by auto
    obtain T' p' where Tp:"tra2 = [WaitBlk (ereal T') (\<lambda>\<tau>. State (p' \<tau>)) ({}, {})]"
      using tra2 apply (induct rule: ode_inv_assn.induct)
      by auto
    have 3:"ode_inv_assn c [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
      using Tp tra3 tra2 by auto
    have 4: "\<forall>t\<in>{0..T}. c (p t)"
      using 3 apply (elim ode_inv_assn_elim)
      apply auto
      subgoal for d p' t
        apply (frule WaitBlk_cong)
        apply (frule WaitBlk_cong2)
        by auto
      done
    have 5:"big_step (Cont ode (\<lambda>s. b s \<and> c s)) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre 4 by auto
    show ?thesis
      using assms(2) 
      unfolding Valid_def 
      using pre 4 5
      by (smt atLeastAtMost_iff)
  qed
  done

text \<open>
  Version of differential-cut rule with state only.
\<close>
theorem DC'':
  assumes
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {\<lambda>s tr. (P @\<^sub>t ode_inv_assn c) tr}"
  and
    "\<Turnstile> {\<lambda>s tr. init s \<and> (\<lambda>s. b s \<and> c s) s}
         Cont ode (\<lambda>s. b s \<and> c s)
        {\<lambda>s tr. d s}"
  shows
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {\<lambda>s tr. d s }"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for tr T p
  proof-
    have 1:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre by auto
    have 2:"(P @\<^sub>t ode_inv_assn c) (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using assms(1) 1
      unfolding Valid_def using pre by auto
    obtain tra1 tra2 where tra1:"P tra1" and tra2:"ode_inv_assn c tra2" and tra3:"tra1 @ tra2 = (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using 2 unfolding join_assn_def by auto
    obtain T' p' where Tp:"tra2 = [WaitBlk (ereal T') (\<lambda>\<tau>. State (p' \<tau>)) ({}, {})]"
      using tra2 apply (induct rule: ode_inv_assn.induct)
      by auto
    have 3:"ode_inv_assn c [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
      using Tp tra3 tra2 by auto
    have 4: "\<forall>t\<in>{0..T}. c (p t)"
      using 3 apply (elim ode_inv_assn_elim)
      apply auto
      subgoal for d p' t
        apply (frule WaitBlk_cong)
        apply (frule WaitBlk_cong2)
        by auto
      done
    have 5:"big_step (Cont ode (\<lambda>s. b s \<and> c s)) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre 4 by auto
    show ?thesis
      using assms(2) 
      unfolding Valid_def 
      using pre 4 5
      by (smt atLeastAtMost_iff)
  qed
  done

theorem DC''g:
  assumes
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {\<lambda>s tr. (P @\<^sub>t ode_inv_assn c) tr}"
  and
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> (\<lambda>s. b s \<and> c s) s}
         Cont ode b
        {\<lambda> s tr. (c s \<and> (P @\<^sub>t ode_inv_assn c) tr) \<longrightarrow> d s tr}"
  shows
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {d}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for tr T p
  proof-
    have 1:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre by auto
    have 2:"(P @\<^sub>t ode_inv_assn c) (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using assms(1) 1
      unfolding Valid_def using pre by auto
    obtain tra1 tra2 where tra1:"P tra1" and tra2:"ode_inv_assn c tra2" and tra3:"tra1 @ tra2 = (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using 2 unfolding join_assn_def by auto
    obtain T' p' where Tp:"tra2 = [WaitBlk (ereal T') (\<lambda>\<tau>. State (p' \<tau>)) ({}, {})]"
      using tra2 apply (induct rule: ode_inv_assn.induct)
      by auto
    have 3:"ode_inv_assn c [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
      using Tp tra3 tra2 by auto
    have 4: "\<forall>t\<in>{0..T}. c (p t)"
      using 3 apply (elim ode_inv_assn_elim)
      apply auto
      subgoal for d p' t
        apply (frule WaitBlk_cong)
        apply (frule WaitBlk_cong2)
        by auto
      done
    have 5:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre 4 by auto
    show ?thesis
      using assms(2) 
      unfolding Valid_def 
      using pre 2 3 4 5
      by (smt atLeastAtMost_iff)
  qed
  done

text \<open>
  Version of differential-cut rule, adding c to the conclusion.
\<close>
theorem DC''':
  assumes
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {\<lambda>s tr. (P @\<^sub>t ode_inv_assn c) tr}"
  and
    "\<Turnstile> {\<lambda>s tr. init s \<and> (\<lambda>s. b s \<and> c s) s}
         Cont ode (\<lambda>s. b s \<and> c s)
        {\<lambda>s tr. d s}"
  shows
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {\<lambda>s tr. c s \<and> d s }"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for tr T p
  proof-
    have 1:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre by auto
    have 2:"(P @\<^sub>t ode_inv_assn c) (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using assms(1) 1
      unfolding Valid_def using pre by auto
    obtain tra1 tra2 where tra1:"P tra1" and tra2:"ode_inv_assn c tra2" and tra3:"tra1 @ tra2 = (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using 2 unfolding join_assn_def by auto
    obtain T' p' where Tp:"tra2 = [WaitBlk (ereal T') (\<lambda>\<tau>. State (p' \<tau>)) ({}, {})]"
      using tra2 apply (induct rule: ode_inv_assn.induct)
      by auto
    have 3:"ode_inv_assn c [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
      using Tp tra3 tra2 by auto
    have 4: "\<forall>t\<in>{0..T}. c (p t)"
      using 3 apply (elim ode_inv_assn_elim)
      apply auto
      subgoal for d p' t
        apply (frule WaitBlk_cong)
        apply (frule WaitBlk_cong2)
        by auto
      done
    have 5:"big_step (Cont ode (\<lambda>s. b s \<and> c s)) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre 4 by auto
    show ?thesis
      using assms(2) 
      unfolding Valid_def 
      using pre 4 5
      by (smt atLeastAtMost_iff)
  qed
subgoal premises pre for tr T p
  proof-
    have 1:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre by auto
    have 2:"(P @\<^sub>t ode_inv_assn c) (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using assms(1) 1
      unfolding Valid_def using pre by auto
    obtain tra1 tra2 where tra1:"P tra1" and tra2:"ode_inv_assn c tra2" and tra3:"tra1 @ tra2 = (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using 2 unfolding join_assn_def by auto
    obtain T' p' where Tp:"tra2 = [WaitBlk (ereal T') (\<lambda>\<tau>. State (p' \<tau>)) ({}, {})]"
      using tra2 apply (induct rule: ode_inv_assn.induct)
      by auto
    have 3:"ode_inv_assn c [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
      using Tp tra3 tra2 by auto
    have 4: "\<forall>t\<in>{0..T}. c (p t)"
      using 3 apply (elim ode_inv_assn_elim)
      apply auto
      subgoal for d p' t
        apply (frule WaitBlk_cong)
        apply (frule WaitBlk_cong2)
        by auto
      done
    have 5:"big_step (Cont ode (\<lambda>s. b s \<and> c s)) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre 4 by auto
    show ?thesis
      using assms(2) 
      unfolding Valid_def 
      using pre 4 5
      by (smt atLeastAtMost_iff)
  qed
  done

theorem DC'''g:
  assumes
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {\<lambda>s tr. (P @\<^sub>t ode_inv_assn c) tr}"
  and
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> (\<lambda>s. b s \<and> c s) s}
         Cont ode (\<lambda>s. b s)
        {\<lambda>s tr. (c s \<and> (P @\<^sub>t ode_inv_assn c) tr) \<longrightarrow> d s tr}"
  shows
    "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
         Cont ode b
        {\<lambda>s tr. c s \<and> d s tr}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for tr T p
  proof-
    have 1:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre by auto
    have 2:"(P @\<^sub>t ode_inv_assn c) (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using assms(1) 1
      unfolding Valid_def using pre by auto
    obtain tra1 tra2 where tra1:"P tra1" and tra2:"ode_inv_assn c tra2" and tra3:"tra1 @ tra2 = (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using 2 unfolding join_assn_def by auto
    obtain T' p' where Tp:"tra2 = [WaitBlk (ereal T') (\<lambda>\<tau>. State (p' \<tau>)) ({}, {})]"
      using tra2 apply (induct rule: ode_inv_assn.induct)
      by auto
    have 3:"ode_inv_assn c [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
      using Tp tra3 tra2 by auto
    have 4: "\<forall>t\<in>{0..T}. c (p t)"
      using 3 apply (elim ode_inv_assn_elim)
      apply auto
      subgoal for d p' t
        apply (frule WaitBlk_cong)
        apply (frule WaitBlk_cong2)
        by auto
      done
    have 5:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre 4 by auto
    show ?thesis
      using assms(2) 
      unfolding Valid_def 
      using pre 4 5
      by (smt atLeastAtMost_iff)
  qed
subgoal premises pre for tr T p
  proof-
    have 1:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre by auto
    have 2:"(P @\<^sub>t ode_inv_assn c) (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using assms(1) 1
      unfolding Valid_def using pre by auto
    obtain tra1 tra2 where tra1:"P tra1" and tra2:"ode_inv_assn c tra2" and tra3:"tra1 @ tra2 = (tr @ [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      using 2 unfolding join_assn_def by auto
    obtain T' p' where Tp:"tra2 = [WaitBlk (ereal T') (\<lambda>\<tau>. State (p' \<tau>)) ({}, {})]"
      using tra2 apply (induct rule: ode_inv_assn.induct)
      by auto
    have 3:"ode_inv_assn c [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
      using Tp tra3 tra2 by auto
    have 4: "\<forall>t\<in>{0..T}. c (p t)"
      using 3 apply (elim ode_inv_assn_elim)
      apply auto
      subgoal for d p' t
        apply (frule WaitBlk_cong)
        apply (frule WaitBlk_cong2)
        by auto
      done
    have 5:"big_step (Cont ode b) (p 0) [WaitBlk (ereal T) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p T)"
      apply (rule big_step.intros)
      using pre 4 by auto
    show ?thesis
      using assms(2) 
      unfolding Valid_def 
      using pre 2 3 4 5
      by (smt atLeastAtMost_iff)
  qed
  done


subsection \<open>Local Lipschitz-Condition\<close>

lemma local_lipschitz_t_v:
  "local_lipschitz UNIV UNIV (\<lambda> (t :: real) (v :: real). t * v)"
  apply(simp add: local_lipschitz_def lipschitz_on_def)
apply auto
  subgoal for x t
    apply(rule exI[where x = 1])
    apply auto
    apply(rule exI[where x = "norm t + 1"])
    apply auto
    apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
    apply(subgoal_tac "\<bar>ta * xa - ta * y\<bar> \<le> (\<bar>ta\<bar>) * \<bar>xa - y\<bar>")
     prefer 2
    subgoal 
      by (metis abs_mult dual_order.refl vector_space_over_itself.scale_right_diff_distrib)
    apply(subgoal_tac "\<bar>ta\<bar> \<le> (\<bar>t\<bar> + 1)")
     apply (smt mult_right_mono)
    by linarith
  done

lemma local_lipschitz_gt_v:
  fixes g :: "real \<Rightarrow> real"
  assumes "continuous_on {-e<..<P+e} (\<lambda>t. g t)"
  shows "local_lipschitz {-e<..<P+e} UNIV (\<lambda> t v . g t * v)"
  apply(rule  local_lipschitz_compose1[OF _ assms(1)])
  apply(rule local_lipschitz_subset[OF local_lipschitz_t_v])
  by auto


subsection \<open>Darboux Invariant rules\<close>

text \<open>
  If f' = g * f, where g is continuous on a finite interval, and f equals
  zero initially, then f always remain at zero.
\<close>
lemma dbxeq:
  fixes f :: "real \<Rightarrow> real"
   assumes "(f has_vderiv_on (\<lambda> t . g t * f t)) {-e..P+e}" 
    and "e > 0 \<and> P > 0"
    and "continuous_on {-e<..<P+e} (\<lambda>t. g t)"
    and "f 0 = 0"
    and "D \<in> {0 .. P}"
  shows "f D = 0"
proof-
  have local:"local_lipschitz {-e<..<P+e} UNIV (\<lambda> t v . g t * v)"
    using local_lipschitz_gt_v[OF assms(3)]
    by auto
interpret loc:ll_on_open_it "{-e<..<P+e}"
      "\<lambda> t v . g t * v" UNIV 0
      apply standard
  using local apply auto
  using assms(3)
  by (simp add: continuous_on_mult_right)
  have s1:" (f solves_ode (\<lambda> t v . g t * v)) {0..P} UNIV" 
    unfolding solves_ode_def
    using assms    
    using has_vderiv_on_subset[OF assms(1)] by auto
 have s2: "(loc.flow 0 0) t = (\<lambda>t. f t) t" if "t \<in> {0..P}" for t
   apply (rule loc.maximal_existence_flow(2)[OF s1])
   using that assms by auto
  have s3:" ((\<lambda> t . 0) solves_ode (\<lambda> t v . g t * v)) {0..P} UNIV"
 unfolding solves_ode_def
  apply auto
  by (simp add: has_vderiv_on_const)
 have s4: "(loc.flow 0 0) t = (\<lambda>t. 0) t" if "t \<in> {0..P}" for t
   apply (rule loc.maximal_existence_flow(2)[OF s3])
  using that assms by auto
  show ?thesis using s2 s4 assms by auto
qed


lemma dbxeq_weak:
  fixes f :: "real \<Rightarrow> real"
   assumes "(f has_vderiv_on (\<lambda> t . g t * f t)) {0..P}" 
    and "e > 0 \<and> P > 0"
    and "continuous_on {-e<..<P+e} (\<lambda>t. g t)"
    and "f 0 = 0"
    and "D \<in> {0 .. P}"
  shows "f D = 0"
proof-
  have local:"local_lipschitz {-e<..<P+e} UNIV (\<lambda> t v . g t * v)"
    using local_lipschitz_gt_v[OF assms(3)]
    by auto
interpret loc:ll_on_open_it "{-e<..<P+e}"
      "\<lambda> t v . g t * v" UNIV 0
      apply standard
  using local apply auto
  using assms(3)
  by (simp add: continuous_on_mult_right)
  have s1:" (f solves_ode (\<lambda> t v . g t * v)) {0..P} UNIV" 
    unfolding solves_ode_def
    apply auto
    using assms    
    using has_vderiv_on_subset[OF assms(1),of "{0..P}"] 
    by fastforce
 have s2: "(loc.flow 0 0) t = (\<lambda>t. f t) t" if "t \<in> {0..P}" for t
   apply (rule loc.maximal_existence_flow(2)[OF s1])
   using that assms by auto
  have s3:" ((\<lambda> t . 0) solves_ode (\<lambda> t v . g t * v)) {0..P} UNIV"
 unfolding solves_ode_def
  apply auto
  by (simp add: has_vderiv_on_const)
 have s4: "(loc.flow 0 0) t = (\<lambda>t. 0) t" if "t \<in> {0..P}" for t
   apply (rule loc.maximal_existence_flow(2)[OF s3])
  using that assms by auto
  show ?thesis using s2 s4 assms by auto
qed

text \<open>
  Version of the previous theorem, where we assume f d = 0 at some d within
  the interval, rather than at zero.
\<close>
lemma dbxeq':
  fixes f :: "real \<Rightarrow> real"
   assumes " (f has_vderiv_on (\<lambda> t . g t * f t)) {-e..P+e}" 
    and "e > 0 \<and> P > 0"    
    and "continuous_on {-e<..<P+e} (\<lambda>t. g t)"
    and "d \<in> {0 .. P}"
    and "f d = 0" 
    and "D \<in> {0 .. P}"
  shows "f D = 0"
proof(cases "D \<ge> d")
  case g:True
  then show ?thesis

  proof-
have local:"local_lipschitz {-e<..<P+e} UNIV (\<lambda> t v . g t * v)"
    using local_lipschitz_gt_v[OF assms(3)]
    by auto
interpret loc:ll_on_open_it "{-e-d<..<P+e-d}"
      "\<lambda> t v . g (t + d) * v" UNIV 0
      apply standard
  apply auto
  subgoal
    apply(rule  local_lipschitz_compose1 [where g = "\<lambda> t . t + d"])
    subgoal 
      apply (subgoal_tac "((\<lambda>t. t + d) ` {- e - d<..<P + e - d}) = {- e <..<P + e }")
      subgoal using local by auto
      unfolding image_def
       apply auto 
      by (metis cancel_comm_monoid_add_class.diff_cancel diff_diff_eq2 diff_strict_right_mono diff_zero greaterThanLessThan_iff)
    apply(auto intro:continuous_intros)
    done
  subgoal for x
  proof-
    have 1:"continuous_on UNIV (\<lambda>t. t + d)"
      apply(auto intro:continuous_intros)
      done
    have 2:"((\<lambda>t. t + d) ` {- e - d<..<P + e - d}) = {- e<..<P + e}"
      unfolding image_def
       apply auto 
      by (metis cancel_comm_monoid_add_class.diff_cancel diff_diff_eq2 diff_strict_right_mono diff_zero greaterThanLessThan_iff)
    have 3:"continuous_on {- e - d<..<P + e - d} (g \<circ> (\<lambda>t. t + d))"
      using continuous_on_compose[where f="\<lambda> t . t + d" and g= "g" and s= "{- e - d<..<P + e - d}"]
      using 2 continuous_on_subset[OF 1] assms(3) by auto
    then show ?thesis
    using continuous_on_mult_right[where f="\<lambda> t .g( t + d)" and c= "x" and s= "{- e - d<..<P + e - d}"]
    by auto 
qed
  done
  have m:"((\<lambda>t. t + d) has_vderiv_on (\<lambda>_ . 1)) UNIV"
    apply (auto intro!: derivative_intros)
    done
  have s1:" ((\<lambda>t. f(t+d)) solves_ode (\<lambda> t v . g (t+d) * v)) {0..P-d} UNIV" 
    unfolding solves_ode_def
    apply auto
    using has_vderiv_on_compose[where g="\<lambda> t. t+d" and f = "f" and f' = "(\<lambda>t. g t * f t)" and g'="\<lambda>_. 1" and T="{0..P-d}"]
    apply auto
    using has_vderiv_on_subset[OF m]
    using has_vderiv_on_subset[OF assms(1)]
    using assms
    by auto
 have s2: "(loc.flow 0 0) t = (\<lambda>t. f(t+d)) t" if "t \<in> {0..P-d}" for t
   apply(rule loc.maximal_existence_flow(2)[OF s1])
   using that assms by auto
  have s3:" ((\<lambda> t . 0) solves_ode (\<lambda> t v . g (t+d) * v)) {0..P-d} UNIV"
 unfolding solves_ode_def
  apply auto
  by (simp add: has_vderiv_on_const)
 have s4: "(loc.flow 0 0) t = (\<lambda>t. 0) t" if "t \<in> {0..P-d}" for t
   apply (rule loc.maximal_existence_flow(2)[OF s3])
  using that assms by auto
  show ?thesis using s2[of "D-d"] s4[of "D-d"] g assms by auto
qed
next
  case l:False
  then show ?thesis 
  proof-
have local:"local_lipschitz {-e<..<P+e} UNIV (\<lambda> t v . g t * v)"
    using local_lipschitz_gt_v[OF assms(3)]
    by auto
interpret loc:ll_on_open_it "{d-P-e<..<d+e}"
      "\<lambda> t v . - g (d - t) * v" UNIV 0
      apply standard
  apply auto
  subgoal
    apply(rule  local_lipschitz_compose1 [where g = "\<lambda> t . d - t"])
    subgoal 
      apply (subgoal_tac "((-) d ` {d - P - e<..<d + e}) = {-e<..<P+e}")
      subgoal 
        using local 
        by (simp add: local_lipschitz_minus)
      unfolding image_def
      apply auto 
      by (smt greaterThanLessThan_iff)
    apply(auto intro:continuous_intros)
    done
  subgoal for x
  proof-
    have 1:"continuous_on UNIV (\<lambda>t. d - t)"
      apply(auto intro:continuous_intros)
      done
    have 2:"((-) d ` {d - P - e<..<d + e}) = {-e<..<P+e}"
      unfolding image_def
       apply auto 
      by (smt greaterThanLessThan_iff)
    have 3:"continuous_on {d - P - e<..<d + e} (g \<circ> (\<lambda>t. d - t))"
      using continuous_on_compose[where f="\<lambda> t . d - t" and g= "g" and s= "{d - P - e<..<d + e}"]
      using 2 continuous_on_subset[OF 1] assms(3) by auto
    then show ?thesis
    using continuous_on_mult_right[where f="\<lambda> t .g( d - t)" and c= "x" and s= "{d - P - e<..<d + e}"]
    using continuous_on_minus by auto
qed
  done
  have m:"((\<lambda>t. d - t) has_vderiv_on (\<lambda>_ . -1)) UNIV"
    apply (auto intro!: derivative_intros)
    done
  have s1:" ((\<lambda>t. f(d - t)) solves_ode (\<lambda> t v . - g (d - t) * v)) {0..d} UNIV" 
    unfolding solves_ode_def
    apply auto
    using has_vderiv_on_compose[where g="\<lambda> t. d-t" and f = "f" and f' = "(\<lambda>t. g t * f t)" and g'="\<lambda>_. -1" and T="{0..d}"]
    apply auto
    using has_vderiv_on_subset [OF m]
    using has_vderiv_on_subset [OF assms(1)]
    using assms  by auto
 have s2: "(loc.flow 0 0) t = (\<lambda>t. f(d-t)) t" if "t \<in> {0..d}" for t
   apply(rule loc.maximal_existence_flow(2)[OF s1])
   using that assms by auto
  have s3:" ((\<lambda> t . 0) solves_ode (\<lambda> t v . - g (d - t) * v)) {0..d} UNIV"
 unfolding solves_ode_def
  apply auto
  by (simp add: has_vderiv_on_const)
 have s4: "(loc.flow 0 0) t = (\<lambda>t. 0) t" if "t \<in> {0..d}" for t
   apply (rule loc.maximal_existence_flow(2)[OF s3])
  using that assms by auto
  show ?thesis using s2[of "d-D"] s4[of "d-D"] l assms by auto
qed
qed

text \<open>
  Version of theorem with f initially positive.
\<close>
lemma dbxg:
  fixes f :: "real \<Rightarrow> real"
   assumes " (f has_vderiv_on (\<lambda>t. g t * f t)) {-e..P+e}" 
    and "e > 0 \<and> P > 0"
    and "continuous_on {-e<..<P+e} (\<lambda>t. g t)"
    and "f 0 > 0" 
    and "D \<in> {0 .. P}"
  shows "f D > 0"
proof(rule ccontr)
  assume "\<not> 0 < f D"
  then have 1:"f D \<le> 0" 
    by auto
  have 2:"\<forall>t\<in>{0..P}. continuous (at t within {-e<..<P+e}) f"
    using assms unfolding has_vderiv_on_def has_vector_derivative_def
    using has_derivative_continuous has_derivative_subset
     by (smt atLeastAtMost_iff continuous_within_subset greaterThanLessThan_subseteq_atLeastAtMost_iff greaterThan_iff)
  have 3:"\<forall>t\<in>{0..P}. isCont f t"
    apply auto subgoal for t
      using continuous_within_open[of t "{-e<..<P+e}" f]
      using 2 assms
      by auto
    done
  have 4:"{d. f d = 0 \<and> d \<in> {0 .. D}} \<noteq> {}"
    using IVT2[of f D 0 0] using 1 3 assms by auto
  obtain d where "d \<in> {0 .. D}" and "f d = 0"
    using 4 by auto
  then have "f 0 = 0"
    using dbxeq'[OF assms(1) assms(2) assms(3)] using assms 
    by (smt atLeastAtMost_iff)
  then show False using assms by auto
qed

text \<open>
  Version of theorem with f initially negative.
\<close>
lemma dbxl:
  fixes f :: "real \<Rightarrow> real"
  assumes " (f has_vderiv_on (\<lambda>t. g t * f t)) {-e..P+e}" 
    and "e > 0 \<and> P > 0"
    and "continuous_on {-e<..<P+e} (\<lambda>t. g t)"
    and "f 0 < 0" 
    and "D \<in> {0 .. P}"
  shows "f D < 0"
proof(rule ccontr)
  assume "\<not> f D < 0"
  then have 1:"f D \<ge> 0" 
    by auto
  have 2:"\<forall>t\<in>{0..P}. continuous (at t within {-e<..<P+e}) f"
    using assms unfolding has_vderiv_on_def has_vector_derivative_def
    using has_derivative_continuous has_derivative_subset
     by (smt atLeastAtMost_iff continuous_within_subset greaterThanLessThan_subseteq_atLeastAtMost_iff greaterThan_iff)
  have 3:"\<forall>t\<in>{0..P}. isCont f t"
    apply auto subgoal for t
      using continuous_within_open[of t "{-e<..<P+e}" f]
      using 2 assms
      by auto
    done
  have 4:"{d. f d = 0 \<and> d \<in> {0 .. D}} \<noteq> {}"
    using IVT[of f 0 0 D] using 1 3 assms by auto
  obtain d where "d \<in> {0 .. D}" and "f d = 0"
    using 4 by auto
  then have "f 0 = 0"
    using dbxeq'[OF assms(1) assms(2) assms(3)]  using assms 
    by (smt atLeastAtMost_iff)
  then show False using assms by auto
qed

text \<open>
  Darboux invariant theorem: if the Lie derivative of inv equals g * inv,
  then inv is an invariant of the state.
\<close>
theorem Valid_dbx_s_eq:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "(\<lambda>S. g' (state2vec S) (ODE2Vec ode S)) = (\<lambda> S. g S * inv S)"
      and "continuous_on UNIV (\<lambda> v. g (vec2state v))"
  shows "\<Turnstile> {\<lambda>s tr. inv s = 0}
     Cont ode b
    {\<lambda>s tr. inv s = 0}"
unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof-
    obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of inv "\<lambda>x. g'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec (ode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec (ode) (p t))" if "t\<in>{-e .. d+e}" for t
        using 1 unfolding has_derivative_def bounded_linear_def 
        using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ode) (p t)))"]
        by blast
      have 3:"\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. s *\<^sub>R  g' (state2vec(p t)) (ODE2Vec ode (p t)))) (at t within {-e .. d+e})"
      using 1 2 by auto
      have 4:"(\<lambda>s. s *\<^sub>R  g' (state2vec(p t)) (ODE2Vec ode (p t))) = (\<lambda>s. s *\<^sub>R  g (p t) * inv (p t))" for t
        using assms(2) 
        by (metis mult.commute mult_scaleR_right)
      have 5:"\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. s *\<^sub>R  g (p t) * inv (p t))) (at t within {-e .. d+e})"
        using 3 4 by auto
      have 6:"((\<lambda>t. inv(p t)) has_vderiv_on  (\<lambda>t.  g (p t) * inv (p t))) ({-e .. d+e})"
        unfolding has_vderiv_on_def has_vector_derivative_def using 5 
        by (metis "3" assms(2))
      have 7:"\<forall>x\<in>{- e<..<d + e}. ((\<lambda>t. state2vec (p t)) has_derivative (\<lambda>xa. xa *\<^sub>R ODE2Vec ode (p x))) (at x within {- e<..<d + e})"
        using  e(2) unfolding has_vderiv_on_def has_vector_derivative_def 
        using has_derivative_subset
        by (metis atLeastAtMost_iff greaterThanLessThan_iff greaterThanLessThan_subseteq_atLeastAtMost_iff less_eq_real_def)
      have 8:"continuous_on {-e<..<d+e} (\<lambda>t. state2vec (p t))"
        apply(auto simp add: continuous_on_eq_continuous_within)
        using 7 has_derivative_continuous 
        using greaterThanLessThan_iff by blast
      have 9:"continuous_on {-e<..<d+e} (\<lambda>t. g (p t))"
        using assms(3) continuous_on_compose2 8  
        by (smt continuous_on_cong subset_UNIV vec_state_map1)
      show ?thesis using dbxeq[OF 6 _ 9]
        using pre e(1) by auto
    qed
    done

text \<open>
  Version of theorem with inv initially positive, then it remains
  positive.
\<close>
theorem Valid_dbx_s_g:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "(\<lambda>S. g' (state2vec S) (ODE2Vec ode S)) = (\<lambda> S. g S * inv S)"
      and "continuous_on UNIV (\<lambda> v. g (vec2state v))"
  shows "\<Turnstile> {\<lambda>s tr. inv s > 0}
     Cont ode b
    {\<lambda>s tr. inv s > 0}"
unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof-
    obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of inv "\<lambda>x. g'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec (ode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec (ode) (p t))" if "t\<in>{-e .. d+e}" for t
        using 1 unfolding has_derivative_def bounded_linear_def 
        using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ode) (p t)))"]
        by blast
      have 3:"\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. s *\<^sub>R  g' (state2vec(p t)) (ODE2Vec ode (p t)))) (at t within {-e .. d+e})"
      using 1 2 by auto
      have 4:"(\<lambda>s. s *\<^sub>R  g' (state2vec(p t)) (ODE2Vec ode (p t))) = (\<lambda>s. s *\<^sub>R  g (p t) * inv (p t))" for t
        using assms(2) 
        by (metis mult.commute mult_scaleR_right)
      have 5:"\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. s *\<^sub>R  g (p t) * inv (p t))) (at t within {-e .. d+e})"
        using 3 4 by auto
      have 6:"((\<lambda>t. inv(p t)) has_vderiv_on  (\<lambda>t.  g (p t) * inv (p t))) ({-e .. d+e})"
        unfolding has_vderiv_on_def has_vector_derivative_def using 5 
        by (metis "3" assms(2))
      have 7:"\<forall>x\<in>{- e<..<d + e}. ((\<lambda>t. state2vec (p t)) has_derivative (\<lambda>xa. xa *\<^sub>R ODE2Vec ode (p x))) (at x within {- e<..<d + e})"
        using  e(2) unfolding has_vderiv_on_def has_vector_derivative_def 
        using has_derivative_subset
        by (metis atLeastAtMost_iff greaterThanLessThan_iff greaterThanLessThan_subseteq_atLeastAtMost_iff less_eq_real_def)
      have 8:"continuous_on {-e<..<d+e} (\<lambda>t. state2vec (p t))"
        apply(auto simp add: continuous_on_eq_continuous_within)
        using 7 has_derivative_continuous 
        using greaterThanLessThan_iff by blast
      have 9:"continuous_on {-e<..<d+e} (\<lambda>t. g (p t))"
        using assms(3) continuous_on_compose2 8  
        by (smt continuous_on_cong subset_UNIV vec_state_map1)
      show ?thesis using dbxg[OF 6 _ 9]
        using pre e(1) by auto
    qed
    done

text \<open>
  Version of theorem with inv initially negative, then it remains
  negative.
\<close>
theorem Valid_dbx_s_l:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "(\<lambda> S .  g' (state2vec S) (ODE2Vec ode S)) = (\<lambda> S. g S * inv S)"
      and "continuous_on UNIV (\<lambda> v. g (vec2state v))"
  shows "\<Turnstile> {\<lambda>s tr. inv s < 0}
     Cont ode b
    {\<lambda>s tr. inv s < 0}"
unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof-
    obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
      have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
        using pre assms e
        using chainrule'[of inv "\<lambda>x. g'(state2vec x)" p "( ode)" e d] 
        by auto
      have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec (ode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec (ode) (p t))" if "t\<in>{-e .. d+e}" for t
        using 1 unfolding has_derivative_def bounded_linear_def 
        using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ode) (p t)))"]
        by blast
      have 3:"\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. s *\<^sub>R  g' (state2vec(p t)) (ODE2Vec ode (p t)))) (at t within {-e .. d+e})"
      using 1 2 by auto
      have 4:"(\<lambda>s. s *\<^sub>R  g' (state2vec(p t)) (ODE2Vec ode (p t))) = (\<lambda>s. s *\<^sub>R  g (p t) * inv (p t))" for t
        using assms(2) 
        by (metis mult.commute mult_scaleR_right)
      have 5:"\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. s *\<^sub>R  g (p t) * inv (p t))) (at t within {-e .. d+e})"
        using 3 4 by auto
      have 6:"((\<lambda>t. inv(p t)) has_vderiv_on  (\<lambda>t.  g (p t) * inv (p t))) ({-e .. d+e})"
        unfolding has_vderiv_on_def has_vector_derivative_def using 5 
        by (metis "3" assms(2))
      have 7:"\<forall>x\<in>{- e<..<d + e}. ((\<lambda>t. state2vec (p t)) has_derivative (\<lambda>xa. xa *\<^sub>R ODE2Vec ode (p x))) (at x within {- e<..<d + e})"
        using  e(2) unfolding has_vderiv_on_def has_vector_derivative_def 
        using has_derivative_subset
        by (metis atLeastAtMost_iff greaterThanLessThan_iff greaterThanLessThan_subseteq_atLeastAtMost_iff less_eq_real_def)
      have 8:"continuous_on {-e<..<d+e} (\<lambda>t. state2vec (p t))"
        apply(auto simp add: continuous_on_eq_continuous_within)
        using 7 has_derivative_continuous 
        using greaterThanLessThan_iff by blast
      have 9:"continuous_on {-e<..<d+e} (\<lambda>t. g (p t))"
        using assms(3) continuous_on_compose2 8  
        by (smt continuous_on_cong subset_UNIV vec_state_map1)
      show ?thesis using dbxl[OF 6 _ 9]
        using pre e(1) by auto
    qed
    done

text \<open>
  Darboux's theorem, inequality version.

  If f' \<ge> g * f, where g is continuous on a finite interval, and f is
  positive initially, then f is always positive.
\<close>
lemma dbxgg:
  fixes f :: "real \<Rightarrow> real"
  assumes "(f has_vderiv_on f') {-e..P+e}" 
    and "\<forall>t \<in> {0<..<P} . f' t \<ge> g t * f t"
    and "e > 0 \<and> P > 0"
    and "continuous_on {-e<..<P+e} (\<lambda>t. g t)"
    and "f 0 > 0"
    and "D \<in> {0 .. P}"
  shows "f D > 0"
proof (cases "D = 0")
  case True
  then show ?thesis using assms by auto
next
  case ca':False
  then show ?thesis
  proof -
    have ca:"D > 0"
      using ca' assms by auto
    have 0:"{- e / 2..P + e / 2} \<subseteq> {- e<..<P + e}"
      using assms(3) by auto
    have 1:"continuous_on {-e/2..P+e/2} (\<lambda>t. g t)"
      using continuous_on_subset [OF assms(4) 0]
      by auto
    have 2:"continuous_on {-e/2..P+e/2} (\<lambda>t. -g t)"
      using continuous_on_minus[OF 1]
      by auto
    have 3:"((\<lambda>u. ivl_integral 0 u (\<lambda>t.- g t)) has_vderiv_on (\<lambda>t.- g t)) {-e/2..P+e/2}"
      using ivl_integral_has_vderiv_on_subset_segment[of "-e/2" "P+e/2" "(\<lambda>t.- g t)" "0"]
      using 2 closed_segment_eq_real_ivl1 assms(3)
      by auto
    let ?h= "\<lambda>u. exp (ivl_integral 0 u (\<lambda>t.- g t))"
    have 4:"(exp has_vderiv_on exp) UNIV"
      unfolding has_vderiv_on_def 
      using DERIV_exp has_field_derivative_iff_has_vector_derivative has_vector_derivative_def by blast
    have 5:"(?h has_vderiv_on (\<lambda> t. - g t * ?h t)) {-e/2..P+e/2}"
      using has_vderiv_on_compose2[OF 4 3]by auto
    have 6:"(f has_vderiv_on f') {-e/2..P+e/2}"
      using has_vderiv_on_subset[OF assms(1)] using assms(3) by auto
    have 7:"((\<lambda> t. f t * ?h t) has_vderiv_on (\<lambda> t.  f t * (- g t * ?h t) + f' t * ?h t )) {-e/2..P+e/2}"
      using has_vderiv_on_mult[OF 6 5] by auto
    have 8:"((\<lambda> t. f t * ?h t) has_vderiv_on (\<lambda> t.  f t * (- g t * ?h t) + f' t * ?h t )) {0..D}"
      using has_vderiv_on_subset[OF 7] using assms by auto
    let ?e = "(\<lambda> t. f t * ?h t)"
    let ?e' = "(\<lambda> t.  f t * (- g t * ?h t) + f' t * ?h t )"
    obtain y where y1:"?e D - ?e 0 = D * ?e' y" and y2:"y\<in>{0<..<D}"
      using mvt_simple_closed_segmentE [of ?e ?e' 0 D]
      using 8 ca open_segment_eq_real_ivl[of 0 D] closed_segment_eq_real_ivl1[of 0 D]
      by smt
    have 9:"?h y > 0"
      by simp
    have 10:"?e' y = (f' y - g y * f y) * ?h y" 
      by(auto simp add: algebra_simps)
    have 11:"(f' y - g y * f y) \<ge> 0 "
      using y2 assms(2,3,6) by auto
    have 12:"?e' y \<ge> 0" 
      using 9 10 11 by auto
    have 13:"?e D \<ge> ?e 0"
      using y1 12 ca 
      by (smt split_mult_pos_le)
    have 14:"?e 0 > 0"
      using assms by auto
    have 15:"?e D > 0"
      using 13 14 by auto
    then show ?thesis 
      using exp_gt_zero zero_less_mult_pos2 by blast
  qed
qed

text \<open>
  Non-negative version of the previous theorem.
\<close>
lemma dbxgge:
  fixes f :: "real \<Rightarrow> real"
  assumes " (f has_vderiv_on f') {-e..P+e}" 
    and "\<forall> t \<in> {0<..<P} . f' t \<ge> g t * f t"
    and "e > 0 \<and> P > 0"
    and "continuous_on {-e<..<P+e} (\<lambda>t. g t)"
    and "f 0 \<ge> 0"
    and "D \<in> {0 .. P}"
  shows "f D \<ge> 0"
proof(cases "D = 0")
  case True
  then show ?thesis using assms by auto
next
  case ca':False
  then show ?thesis
  proof-
    have ca:"D > 0"
      using ca' assms by auto
  have 0:"{- e / 2..P + e / 2} \<subseteq> {- e<..<P + e}"
    using assms(3) by auto
  have 1:"continuous_on {-e/2..P+e/2} (\<lambda>t. g t)"
    using continuous_on_subset [OF assms(4) 0]
    by auto
  have 2:"continuous_on {-e/2..P+e/2} (\<lambda>t. -g t)"
    using continuous_on_minus[OF 1]
    by auto
  have 3:"((\<lambda>u. ivl_integral 0 u (\<lambda>t.- g t)) has_vderiv_on (\<lambda>t.- g t)) {-e/2..P+e/2}"
    using ivl_integral_has_vderiv_on_subset_segment[of "-e/2" "P+e/2" "(\<lambda>t.- g t)" "0"]
    using 2 closed_segment_eq_real_ivl1 assms(3)
    by auto
  let ?h= "\<lambda>u. exp (ivl_integral 0 u (\<lambda>t.- g t))"
  have 4:"(exp has_vderiv_on exp) UNIV"
    unfolding has_vderiv_on_def 
    using DERIV_exp has_field_derivative_iff_has_vector_derivative has_vector_derivative_def by blast
  have 5:"(?h has_vderiv_on (\<lambda> t. - g t * ?h t)) {-e/2..P+e/2}"
    using has_vderiv_on_compose2[OF 4 3]by auto
  have 6:"(f has_vderiv_on f') {-e/2..P+e/2}"
    using has_vderiv_on_subset[OF assms(1)] using assms(3) by auto
  have 7:"((\<lambda> t. f t * ?h t) has_vderiv_on (\<lambda> t.  f t * (- g t * ?h t) + f' t * ?h t )) {-e/2..P+e/2}"
    using has_vderiv_on_mult[OF 6 5] by auto
  have 8:"((\<lambda> t. f t * ?h t) has_vderiv_on (\<lambda> t.  f t * (- g t * ?h t) + f' t * ?h t )) {0..D}"
    using has_vderiv_on_subset[OF 7] using assms by auto
  let ?e = "(\<lambda> t. f t * ?h t)"
  let ?e' = "(\<lambda> t.  f t * (- g t * ?h t) + f' t * ?h t )"
  obtain y where y1:"?e D - ?e 0 = D * ?e' y" and y2:"y\<in>{0<..<D}"
    using mvt_simple_closed_segmentE [of ?e ?e' 0 D]
    using 8 ca open_segment_eq_real_ivl[of 0 D] closed_segment_eq_real_ivl1[of 0 D]
    by smt
  have 9:"?h y > 0"
    by simp
  have 10:"?e' y = (f' y - g y * f y) * ?h y" 
    by(auto simp add: algebra_simps)
  have 11:"(f' y - g y * f y) \<ge> 0 "
    using y2 assms(2,3,6) by auto
  have 12:"?e' y \<ge> 0" 
    using 9 10 11 by auto
  have 13:"?e D \<ge> ?e 0"
    using y1 12 ca 
    by (smt split_mult_pos_le)
  have 14:"?e 0 \<ge> 0"
    using assms by auto
  have 15:"?e D \<ge> 0"
    using 13 14 by auto
  then show ?thesis 
    by (simp add: zero_le_mult_iff)
  qed
qed

text \<open>
  Darboux invariant theorem, version where the Lie derivative of inv
  is greater than or equal to g * inv, and inv is positive initially.
\<close>
theorem Valid_dbxg_s_g:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and "\<And> S. b S \<Longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> (g S * inv S)"
      and "continuous_on UNIV (\<lambda> v. g (vec2state v))"
  shows "\<Turnstile> {\<lambda>s tr. inv s > 0}
     Cont ode b
    {\<lambda>s tr. inv s > 0}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof -
    obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
       using pre unfolding ODEsol_def by auto
    have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
      using pre assms e
      using chainrule'[of inv "\<lambda>x. g'(state2vec x)" p "( ode)" e d] 
      by auto
    have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec (ode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec (ode) (p t))" if "t\<in>{-e .. d+e}" for t
      using 1 unfolding has_derivative_def bounded_linear_def 
      using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ode) (p t)))"]
      by blast
    have 3:"\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. s *\<^sub>R  g' (state2vec(p t)) (ODE2Vec ode (p t)))) (at t within {-e .. d+e})"
      using 1 2 by auto
    have 4:"((\<lambda>t. inv(p t)) has_vderiv_on  (\<lambda>t.  g' (state2vec(p t)) (ODE2Vec ode (p t)))) ({-e .. d+e})"
      unfolding has_vderiv_on_def has_vector_derivative_def 
      by (metis "3")
    have 5:"\<forall>x\<in>{- e<..<d + e}. ((\<lambda>t. state2vec (p t)) has_derivative (\<lambda>xa. xa *\<^sub>R ODE2Vec ode (p x))) (at x within {- e<..<d + e})"
      using  e(2) unfolding has_vderiv_on_def has_vector_derivative_def 
      using has_derivative_subset
      by (metis atLeastAtMost_iff greaterThanLessThan_iff greaterThanLessThan_subseteq_atLeastAtMost_iff less_eq_real_def)
    have 6:"continuous_on {-e<..<d+e} (\<lambda>t. state2vec (p t))"
      apply(auto simp add: continuous_on_eq_continuous_within)
      using 5 has_derivative_continuous 
      using greaterThanLessThan_iff by blast
    have 7:"continuous_on {-e<..<d+e} (\<lambda>t. g (p t))"
      using assms(3) continuous_on_compose2 6
      by (smt continuous_on_cong subset_UNIV vec_state_map1)
    have 8:" \<forall>t\<in>{0<..<d}. g (p t) * inv (p t) \<le> g' (state2vec (p t)) (ODE2Vec ode (p t))"
      using pre(4) assms(2) by auto
    show ?thesis using dbxgg[OF 4 8 _ 7]
      using pre e by auto
  qed
  done
        
text \<open>
  Version of the previous theorem, where inv is initially non-negative.
\<close>
theorem Valid_dbxg_s_ge:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<And> S. b S \<Longrightarrow> (g' (state2vec S) (ODE2Vec ode S)) \<ge> ( g S * inv S)"
      and "continuous_on UNIV (\<lambda> v. g (vec2state v))"
  shows "\<Turnstile> {\<lambda>s tr. inv s \<ge> 0}
     Cont ode b
    {\<lambda>s tr. inv s \<ge> 0}"
  unfolding Valid_def
  apply (auto elim!: contE)
  subgoal premises pre for d p
  proof -
    obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ( ode) (p t))) {-e .. d+e}"
      using pre unfolding ODEsol_def by auto
    have 1: "\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ( ode) (p t)))) (at t within {-e .. d+e})"
      using pre assms e
      using chainrule'[of inv "\<lambda>x. g'(state2vec x)" p "( ode)" e d] 
      by auto
    have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec (ode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec (ode) (p t))" if "t\<in>{-e .. d+e}" for t
      using 1 unfolding has_derivative_def bounded_linear_def 
      using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ode) (p t)))"]
      by blast
    have 3:"\<forall>t\<in>{-e .. d+e}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. s *\<^sub>R  g' (state2vec(p t)) (ODE2Vec ode (p t)))) (at t within {-e .. d+e})"
      using 1 2 by auto
    have 4:"((\<lambda>t. inv(p t)) has_vderiv_on  (\<lambda>t.  g' (state2vec(p t)) (ODE2Vec ode (p t)))) ({-e .. d+e})"
      unfolding has_vderiv_on_def has_vector_derivative_def 
      by (metis "3")
    have 5:"\<forall>x\<in>{- e<..<d + e}. ((\<lambda>t. state2vec (p t)) has_derivative (\<lambda>xa. xa *\<^sub>R ODE2Vec ode (p x))) (at x within {- e<..<d + e})"
      using  e(2) unfolding has_vderiv_on_def has_vector_derivative_def 
      using has_derivative_subset
      by (metis atLeastAtMost_iff greaterThanLessThan_iff greaterThanLessThan_subseteq_atLeastAtMost_iff less_eq_real_def)
    have 6:"continuous_on {-e<..<d+e} (\<lambda>t. state2vec (p t))"
      apply(auto simp add: continuous_on_eq_continuous_within)
      using 5 has_derivative_continuous 
      using greaterThanLessThan_iff by blast
    have 7:"continuous_on {-e<..<d+e} (\<lambda>t. g (p t))"
      using assms(3) continuous_on_compose2 6
      by (smt continuous_on_cong subset_UNIV vec_state_map1)
    have 8:" \<forall>t\<in>{0<..<d}. g (p t) * inv (p t) \<le> g' (state2vec (p t)) (ODE2Vec ode (p t))"
      using pre(4) assms(2) by auto
    show ?thesis using dbxgge[OF 4 8 _ 7]
      using pre e by auto
  qed
  done

end
