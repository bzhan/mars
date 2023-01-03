theory ext_Complementlemma
  imports
    ext_ContinuousInv
    ext_BigStepParallel 
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

theorem Valid_post_and':
  assumes "\<Turnstile> {P} c {\<lambda>(a,s) tr. Q1 s tr}"
    and "\<Turnstile> {P} c {\<lambda>(a,s) tr. Q2 s tr}"
  shows "\<Turnstile> {P} c {\<lambda>(a,s) tr. Q1 s tr \<and> Q2 s tr}"
  using assms unfolding Valid_def entails_def by blast

theorem Valid_pre_cases:
  assumes "\<Turnstile> {\<lambda>s tr. P s \<and> Q s} c {R}"
    and "\<Turnstile> {\<lambda>s tr. P s \<and> \<not> Q s} c {R}"
  shows "\<Turnstile> {\<lambda>s tr. P s} c {R}"
  using assms unfolding Valid_def entails_def by blast

theorem Valid_pre_cases':
  assumes "\<Turnstile> {\<lambda>(a,s) tr. P (a,s) \<and> Q (a,s) tr} c {R}"
    and "\<Turnstile> {\<lambda>(a,s) tr. \<not> P (a,s) \<and> Q (a,s) tr} c {R}"
  shows "\<Turnstile> {Q} c {R}"
  using assms unfolding Valid_def entails_def 
  by (smt (verit, best) case_prodI2')

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

theorem Valid_cond_split'':
  assumes "\<Turnstile> {\<lambda>(a,s) t. b (a,s) \<and> P (a,s) t} c1 {Q}"
    and "\<Turnstile> {\<lambda>(a,s) t. \<not>b (a,s) \<and> P (a,s) t} c2 {Q}"
  shows "\<Turnstile> {\<lambda>(a,s) t. P (a,s) t}
             IF b THEN c1 ELSE c2 FI
            {\<lambda>(a,s) t. Q (a,s) t}"
  using assms unfolding Valid_def
  by (auto elim!: condE seqE)

theorem Valid_ode_not:
  assumes "\<And>s. P s \<Longrightarrow> \<not> b s"
    and "\<And>s. P s \<Longrightarrow> Q s"
  shows "\<Turnstile> {\<lambda>(a,s) tr. P s}
     Cont ode b
    {\<lambda>(a,s) tr. Q s}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s = r}
     Cont ode b
    {\<lambda>(a,s) tr. inv s = r}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s = r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>(a,s) tr. inv s = r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s = r)) tr}"
  apply (rule Valid_post_and')
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s \<ge> r}
     Cont ode b
    {\<lambda>(a,s) tr. inv s \<ge> r}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s \<ge> r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>(a,s) tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s \<ge> r)) tr}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s \<ge> r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>(a,s) tr. inv s \<ge> r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s \<ge> r)) tr}"
  apply(rule Valid_post_and')
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s > r}
     Cont ode b
    {\<lambda>(a,s) tr. inv s > r}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s > r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>(a,s) tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s > r)) tr}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s > r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>(a,s) tr. inv s > r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s > r)) tr}"
  apply(rule Valid_post_and')
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s \<le> r}
     Cont ode b
    {\<lambda>(a,s) tr. inv s \<le> r}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s \<le> r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>(a,s) tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s \<le> r)) tr}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s \<le> r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>(a,s) tr. inv s \<le> r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s \<le> r)) tr}"
  apply(rule Valid_post_and')
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s < r}
     Cont ode b
    {\<lambda>(a,s) tr. inv s < r}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s < r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>(a,s) tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s < r)) tr}"
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
  shows "\<Turnstile> {\<lambda>(a,s) tr. inv s < r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>(a,s) tr. inv s < r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s < r)) tr}"
  apply(rule Valid_post_and')
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
    {\<lambda>(a,s) t. P s}
      Cont ode b
    {\<lambda>(a,s) t. \<exists>s'. s = p s' (d s') \<and> P s'}"
proof -
  have a: "s' = p s (d s) \<and> Wait\<^sub>t (d s) (\<lambda>\<tau>. EState (a,p s \<tau>)) ({}, {}) tr2"
    if "ODE\<^sub>t (a,s) ode b (a,s') tr2" "P s" for a s s' tr2
  proof -
    have a1: "d s > 0" "ODEsol ode (p s) (d s)" "\<forall>t. 0 \<le> t \<and> t < d s \<longrightarrow> b (p s t)"
             "\<not>b (p s (d s))" "p s 0 = s"
      using assms(1) that(2) by auto
    show ?thesis
      using Valid_ode_unique_solution_aux[OF a1(1-2) _ a1(4-5) assms(2) that(1)] a1(3)
      by auto
  qed
  have b: "ODE\<^sub>t (a,s) ode b (a,s') tr2 \<Longrightarrow> \<not>b s \<Longrightarrow> s = s' \<and> tr2 = []" for a s s' tr2
    apply (induct rule: ode_assn_induct) by auto
  show ?thesis
    apply (rule Valid_weaken_pre)
     prefer 2 apply (rule Valid_ode')
    apply (auto simp add: entails_def magic_wand_assn_def)
    subgoal for a  s  s' tr
      apply (rule exI[where x=s])
      apply (auto simp add: join_assn_def conj_assn_def pure_assn_def)
      apply (auto simp add: a)
      done
    done
qed


inductive waitin_assn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow>  'a tassn" ("Waitin\<^sub>t") where
  "d > 0 \<Longrightarrow> Waitin\<^sub>t d p ch v rdy [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy, InBlock ch v]"
| "d \<le> 0 \<Longrightarrow> Waitin\<^sub>t d p ch v rdy [InBlock ch v]"


inductive waitout_assn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> 'a tassn" ("Waitout\<^sub>t") where
  "d > 0 \<Longrightarrow> Waitout\<^sub>t d p ch v rdy [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy, OutBlock ch v]"
| "d \<le> 0 \<Longrightarrow> Waitout\<^sub>t d p ch v rdy [OutBlock ch v]"


theorem Valid_interrupt_sol:
  assumes "b ss \<Longrightarrow> d > 0"
    and "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) UNIV"
    and "p 0 = ss"
    and "(\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d)"
    and "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    and "\<And>i. i < length cs \<Longrightarrow>
    case cs ! i of
      (ch[!]e, p2) \<Rightarrow> \<forall> tt. ((tt \<ge>0 \<and> tt\<le>d) \<longrightarrow>
        \<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,p tt) \<and> b ss \<and>
          (P (aa,ss) @\<^sub>t Waitout\<^sub>t tt (\<lambda> t. EState (aa,p t)) ch (e (aa,p tt)) (rdy_of_echoice cs)) tr} p2 {R})
    | (ch[?]var, p2) \<Rightarrow> \<forall> tt v. ((tt \<ge>0 \<and> tt\<le>d) \<longrightarrow>
        \<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,(p tt)(var := v)) \<and> b ss \<and>
          (P (aa,ss) @\<^sub>t Waitin\<^sub>t tt (\<lambda> t. EState (aa,p t)) ch v (rdy_of_echoice cs)) tr} p2 {R})"
    and "(\<lambda>(a,s) tr. (a,s) = (aa,ss) \<and> b ss \<and> P (a,s) tr) \<Longrightarrow>\<^sub>A (\<lambda>(a,s) tr. R (a,p d) (tr @ [WaitBlk d (\<lambda>\<tau>. EState (a,p \<tau>)) (rdy_of_echoice cs)]))" 
  shows "\<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,ss) \<and> b ss \<and> P (a,s) tr} Interrupt ode b cs {R}"
proof -
  have main: "d2 = d \<and> p2 d = p d \<and> (\<forall>\<tau>\<in>{0..d}. EState (aa,p2 \<tau>) = EState (aa,p \<tau>))"
    if cond: "0 < d2"
       "ODEsol ode p2 d2"
       "(\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t))"
       "\<not> b (p2 d2)"
       "p2 0 = ss" "d>0"for p2 d2
  proof -
    interpret loc:ll_on_open_it "{-1<..}"
      "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
      apply standard
      using assms by auto
    have s1: "((\<lambda>t. state2vec (p t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..} UNIV"
      using assms(2) has_vderiv_on_subset unfolding solves_ode_def 
      by (smt (verit, del_insts) Pi_UNIV UNIV_I has_vderiv_on_eq_rhs top_greatest vec_state_map1)
    have s2: "(loc.flow 0 (state2vec ss)) t = (\<lambda>t. state2vec (p t)) t" if "t \<in> {0..d}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s1])
      using that by (auto simp add: state2vec_def assms(3))
    have s3: "((\<lambda>t. state2vec(p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d2} UNIV"
      using cond(2) using ODEsol_old[OF cond(2)]unfolding ODEsol_def solves_ode_def by auto
    have s4: "loc.flow 0 (state2vec ss) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s3])
      using cond that by auto
    have s5: "d \<le> d2"
    proof (rule ccontr)
      assume 0: "\<not>(d \<le> d2)"
      from 0 have 1: "(\<lambda>t. state2vec (p t)) d2 = (\<lambda>t. state2vec (p2 t)) d2"
        using s2[of d2] s4[of d2] cond(1) by auto
      from 1 have "p d2 = p2 d2"
        by (auto simp add: state2vec_def)
      show False
        using "0" \<open>p d2 = p2 d2\<close> assms that(1) that(4)
        using less_eq_real_def by auto
    qed
    have s6: "d2 \<le> d"
    proof (rule ccontr)
      assume 0: "\<not>(d2 \<le> d)"
      from 0 have 1: "(\<lambda>t. state2vec (p t)) d = (\<lambda>t. state2vec (p2 t)) d"
        using s2[of d] s4[of d] assms cond by auto 
      from 1 have "p d = p2 d"
        by (auto simp add: state2vec_def)
      show False
        using "0" \<open>p d = p2 d\<close> assms that(3) cond by auto
    qed
    have s7: "d = d2" using s5 s6 by auto
    have s8: "t\<in>{0..d} \<Longrightarrow> p2 t = p t" for t
      using s2 s4 s7 
      by (metis vec_state_map1)
    have s10: "p d = p2 d"
      using s8 that(1) assms cond by auto
    show ?thesis using s7 s8 s10 assms 
      by auto
  qed
  have main': "d2 \<le> d \<and> p2 d2 = p d2 \<and> (\<forall>\<tau>\<in>{0..d2}. EState (aa,p2 \<tau>) = EState (aa,p \<tau>))"
    if cond: "0 < d2"
       "ODEsol ode p2 d2"
       "(\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t))"
       "p2 0 = ss" "d>0"for p2 d2
  proof -
    interpret loc:ll_on_open_it "{-1<..}"
      "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
      apply standard
      using assms by auto
    have s1: "((\<lambda>t. state2vec (p t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..} UNIV"
      using assms(2) has_vderiv_on_subset unfolding solves_ode_def 
      by (smt (verit, del_insts) Pi_UNIV UNIV_I has_vderiv_on_eq_rhs top_greatest vec_state_map1)
    have s2: "(loc.flow 0 (state2vec ss)) t = (\<lambda>t. state2vec (p t)) t" if "t \<in> {0..d}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s1])
      using that by (auto simp add: state2vec_def assms(3))
    have s3: "((\<lambda>t. state2vec(p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d2} UNIV"
      using cond(2) using ODEsol_old[OF cond(2)]unfolding ODEsol_def solves_ode_def by auto
    have s4: "loc.flow 0 (state2vec ss) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s3])
      using cond that by auto
    have s6: "d2 \<le> d"
    proof (rule ccontr)
      assume 0: "\<not>(d2 \<le> d)"
      from 0 have 1: "(\<lambda>t. state2vec (p t)) d = (\<lambda>t. state2vec (p2 t)) d"
        using s2[of d] s4[of d] assms cond by auto 
      from 1 have "p d = p2 d"
        by (auto simp add: state2vec_def)
      show False
        using "0" \<open>p d = p2 d\<close> assms that(3) cond by auto
    qed
    have s8: "t\<in>{0..d2} \<Longrightarrow> p2 t = p t" for t
      using s2 s4 s6 cond(1)
      by (smt (verit) atLeastAtMost_iff vec_state_map1)
    have s10: "p d2 = p2 d2"
      using s8 that(1) assms by auto
    show ?thesis using s6 s8 s10 assms 
      by auto
  qed
  show ?thesis
    unfolding Valid_def
    apply(auto elim!: interruptE)
    subgoal for tr1 a s i ch e p2 tr2
      using assms(6)[of i] 
      apply auto
      subgoal premises pre
      proof-
        have 1:"\<Turnstile> {\<lambda>(a, s) tr.
                a = aa \<and>
                s = p 0 \<and> b ss \<and>
                (P (aa, ss) @\<^sub>t
                 Waitout\<^sub>t 0 (\<lambda>t. EState (aa, p t)) ch (e (aa, p 0))
                  (rdy_of_echoice cs))
                 tr}
            p2 {R}"
          using pre assms(1) by auto
        have 2:"Waitout\<^sub>t 0 (\<lambda>t. EState (aa, p t)) ch (e (aa, p 0))
                      (rdy_of_echoice cs) [OutBlock ch (e (aa, p 0))]"
          apply(rule waitout_assn.intros(2))
          by auto
        show ?thesis using 1 2 unfolding Valid_def join_assn_def
          apply auto
          using pre 
          using assms(3) by fastforce
      qed
      done
    subgoal for tr1 a s dd pp i ch e p2 tr2
      using assms(6)[of i] 
      using main'[of dd pp]
      apply auto
      subgoal premises pre
      proof-
        have 1:"WaitBlk dd (\<lambda>\<tau>. EState (aa, pp \<tau>)) (rdy_of_echoice cs) = WaitBlk dd (\<lambda>\<tau>. EState (aa, p \<tau>)) (rdy_of_echoice cs)"
          apply(rule WaitBlk_ext_real)
          using pre assms(1) by auto
        have 2:"Waitout\<^sub>t dd (\<lambda>t. EState (aa, p t)) ch (e (aa, p dd))
                  (rdy_of_echoice cs) [WaitBlk dd (\<lambda>\<tau>. EState (aa, pp \<tau>)) (rdy_of_echoice cs) ,OutBlock ch (e (aa, p dd))]"
          apply(auto simp add: 1)
          apply(rule ) using pre by auto
        have 3:"\<Turnstile> {\<lambda>(a, s) tr.
                a = aa \<and>
                s = p dd \<and> 
                (P (aa, p 0) @\<^sub>t
                 Waitout\<^sub>t dd (\<lambda>t. EState (aa, p t)) ch (e (aa, p dd))
                  (rdy_of_echoice cs))
                 tr}
            p2 {R}"
          using pre assms(1) by auto
        have 4:"d>0" using assms pre by auto
        thm pre
        show ?thesis using 2 3 4 unfolding Valid_def join_assn_def 
          apply auto using assms(3) pre(1,2,7,10) apply auto by fastforce
      qed
      done
    subgoal for tr1 a s i ch var p2 v tr2
      using assms(6)[of i] 
      apply auto
      subgoal premises pre
      proof-
        have 1:"\<Turnstile> {\<lambda>(a, s) tr.
                a = aa \<and>
                s = (p 0)(var := v) \<and> b ss \<and>
                (P (aa, ss) @\<^sub>t
                 Waitin\<^sub>t 0 (\<lambda>t. EState (aa, p t)) ch v (rdy_of_echoice cs))
                 tr}
            p2 {R}"
          using pre assms(1) by auto
        have 2:"Waitin\<^sub>t 0 (\<lambda>t. EState (aa, p t)) ch v (rdy_of_echoice cs) [InBlock ch v]"
          apply(rule ) by auto
        show ?thesis using 1 2 unfolding Valid_def join_assn_def
          apply auto
          using pre 
          using assms(3) by fastforce
      qed
      done
    subgoal for tr1 a s dd pp i ch var p2 v tr2
      using assms(6)[of i] 
      using main'[of dd pp]
      apply auto
      subgoal premises pre
      proof-
        have 1:"WaitBlk dd (\<lambda>\<tau>. EState (aa, pp \<tau>)) (rdy_of_echoice cs) = WaitBlk dd (\<lambda>\<tau>. EState (aa, p \<tau>)) (rdy_of_echoice cs)"
          apply(rule WaitBlk_ext_real)
          using pre assms(1) by auto
        have 2:"Waitin\<^sub>t dd (\<lambda>t. EState (aa, p t)) ch v (rdy_of_echoice cs)
                  [WaitBlk dd (\<lambda>\<tau>. EState (aa, pp \<tau>)) (rdy_of_echoice cs) ,InBlock ch v]"
          apply(auto simp add: 1)
          apply(rule ) using pre by auto
        have 3:"\<Turnstile> {\<lambda>(a, s) tr.
                a = aa \<and>
                s = (p dd)(var := v) \<and>
                (P (aa, p 0) @\<^sub>t
                 Waitin\<^sub>t dd (\<lambda>t. EState (aa, p t)) ch v
                  (rdy_of_echoice cs))
                 tr}
            p2 {R}"
          using pre assms(1) by auto
        have 4:"d>0" using assms pre by auto
        show ?thesis using 2 3 4 pre unfolding Valid_def join_assn_def 
          apply auto using assms(1,3) by fastforce
      qed
      done
    subgoal for tr1 dd pp
      using assms(7) unfolding entails_def 
      using main[of dd pp]
      apply auto
      apply(subgoal_tac "d>0")
       prefer 2
      subgoal using assms(1) by blast
      apply(subgoal_tac"WaitBlk d (\<lambda>\<tau>. EState (aa, pp \<tau>)) (rdy_of_echoice cs) = WaitBlk d (\<lambda>\<tau>. EState (aa, p \<tau>)) (rdy_of_echoice cs)")
      prefer 2
       apply(rule WaitBlk_ext_real)
      by auto
    done
  qed

theorem Valid_interrupt_not:
  assumes "p 0 = ss"
    and "\<And>i. i < length cs \<Longrightarrow>
    case cs ! i of
      (ch[!]e, p2) \<Rightarrow> 
        \<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,ss) \<and> \<not> b ss \<and> 
          (P (aa,ss) @\<^sub>t Waitout\<^sub>t 0 (\<lambda> t. EState (aa,p t)) ch (e (aa,p 0)) (rdy_of_echoice cs)) tr} p2 {R}
    | (ch[?]var, p2) \<Rightarrow> \<forall> v.
        \<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,(p 0)(var := v)) \<and> \<not> b ss \<and> 
          (P (aa,ss) @\<^sub>t Waitin\<^sub>t 0 (\<lambda> t. EState (aa,p t)) ch v (rdy_of_echoice cs)) tr} p2 {R}"
    and "(\<lambda>(a,s) tr. (a,s) = (aa,ss) \<and> \<not> b ss \<and> P (a,s) tr) \<Longrightarrow>\<^sub>A (\<lambda>(a,s) tr. R (a,s) tr )" 
  shows "\<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,ss) \<and> \<not> b ss \<and> P (a,s) tr} Interrupt ode b cs {R}"
unfolding Valid_def
    apply(auto elim!: interruptE)
  subgoal for tr1 a s i ch e p2 tr2
    using assms(2)[of i]
    apply auto
    unfolding Valid_def join_assn_def
    apply(subgoal_tac "Waitout\<^sub>t 0 (\<lambda>t. EState (aa, p t)) ch (e (aa, p 0)) (rdy_of_echoice cs) [OutBlock ch (e (aa, p 0))]")
     prefer 2
     apply rule
     apply auto using assms
    by fastforce
  subgoal for tr1 a s i ch var p2 v tr2
    using assms(2)[of i]
    apply auto
    unfolding Valid_def join_assn_def
    apply(subgoal_tac"Waitin\<^sub>t 0 (\<lambda>t. EState (aa, p t)) ch v (rdy_of_echoice cs)[InBlock ch v]")
     prefer 2
     apply rule
     apply auto using assms
    by fastforce
  subgoal for tr1
    using assms(3) unfolding entails_def
    by auto
  done
    
theorem Valid_interrupt_in_sol:
  assumes "b ss \<Longrightarrow> d > 0"
    and "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) UNIV"
    and "p 0 = ss"
    and "(\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d)"
    and "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    and "\<forall> tt v. ((tt \<ge>0 \<and> tt\<le>d) \<longrightarrow>
        \<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,(p tt)(var := v)) \<and> b ss \<and> 
          (P (aa,ss) @\<^sub>t Waitin\<^sub>t tt (\<lambda> t. EState (aa,p t)) ch v ({},{ch})) tr} pp {R tt v})"
    shows "\<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,ss) \<and> b ss \<and> P (a,s) tr} Interrupt ode b [(ch[?]var, pp)] {\<lambda>(a,s) tr. (\<exists>tt vv. (tt \<ge>0 \<and> tt\<le>d) \<and> R tt vv (a,s) tr) \<or> ((a,s) = (aa,p d) \<and> b ss \<and> (P(aa,ss) @\<^sub>t Wait\<^sub>t d (\<lambda>\<tau>. EState (aa,p \<tau>)) ({},{ch})) tr )}"
  apply(rule Valid_interrupt_sol[where d= d and p = p])
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal
    using assms(6)
    apply auto
    subgoal for tt v
      apply(rule Valid_strengthen_post[where Q ="R tt v"])
       prefer 2 apply auto
      unfolding entails_def
      by auto
    done
  unfolding entails_def join_assn_def
  apply auto
  subgoal for tr
    apply(subgoal_tac "Wait\<^sub>t d (\<lambda>\<tau>. EState (aa, p \<tau>)) ({}, {ch}) [WaitBlk d (\<lambda>\<tau>. EState (aa, p \<tau>)) ({}, {ch})]")
     apply auto
    apply(rule )
    using assms by auto
  done


theorem Valid_interrupt_in_not:
  assumes "p 0 = ss"
    and "\<forall> v.
        \<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,(p 0)(var := v)) \<and> \<not> b ss \<and> 
          (P (aa,ss) @\<^sub>t Waitin\<^sub>t 0 (\<lambda> t. EState (aa,p t)) ch v ({},{ch})) tr} pp {R 0 v}"
    shows "\<Turnstile> {\<lambda>(a,s) tr. (a,s) = (aa,ss) \<and> \<not> b ss \<and> P (a,s) tr} Interrupt ode b [(ch[?]var, pp)] {\<lambda> (a,s) tr. \<exists> v. R 0 v (a,s) tr \<or> ((a,s) = (aa,p 0) \<and> \<not> b ss \<and> (P(aa,ss) @\<^sub>t Wait\<^sub>t 0 (\<lambda>\<tau>. EState (aa,p \<tau>)) ({},{ch})) tr)}"
  apply(rule Valid_interrupt_not[where p=p])
  subgoal using assms by auto
  subgoal using assms(2)
    apply auto
    subgoal for v
      apply(rule Valid_strengthen_post[where Q ="R 0 v"])
       prefer 2 apply auto
      unfolding entails_def
      by auto
    done
  unfolding entails_def
  apply auto
  subgoal for tr
    apply(subgoal_tac "Wait\<^sub>t 0 (\<lambda>\<tau>. EState (aa, p \<tau>)) ({}, {ch}) []")
     apply auto
    apply(rule )
    using assms by auto
  done

end
