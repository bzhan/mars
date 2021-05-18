theory basicprime
    imports HHLProver.ContinuousInv  HHLProver.BigStepParallel 
begin

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

lemma has_derivative_proj:
  fixes x :: vec
    and p :: "vec \<Rightarrow> vec"
  assumes "(p has_derivative q x) (at x within D)"
  shows "((\<lambda>v. p v $ i) has_derivative (\<lambda> v. q x v $ i)) (at x within D)"
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


lemma has_derivative_projI:
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
    have "\<forall>i. (\<exists>K. \<forall>x. norm (q t x $ i) \<le> norm x * K)"
      using pre by auto
    then have "(\<exists>K. \<forall>x. norm (q t x $ i) \<le> norm x * K)" for i
      by auto
    then obtain K where "\<forall>x. norm (q t x $ i) \<le> norm x * (K$i)" for i
      
      sorry
    show ?thesis
      sorry
  qed
  done
subgoal
    by (auto intro: vec_tendstoI)
  done

theorem Valid_post_and:
  "\<Turnstile> {P} c {\<lambda>s tr. Q1 s tr} \<Longrightarrow> \<Turnstile> {P} c {\<lambda>s tr . Q2 s tr} \<Longrightarrow> \<Turnstile> {P} c {\<lambda>s tr. Q1 s tr \<and> Q2 s tr}"
  unfolding Valid_def entails_def by blast

theorem Valid_pre_cases:
  "\<Turnstile> {\<lambda>s tr. P s \<and> Q s} c {R} \<Longrightarrow> \<Turnstile> {\<lambda>s tr. P s \<and> \<not> Q s} c {R} \<Longrightarrow> \<Turnstile> {\<lambda>s tr. P s} c {R}"
  unfolding Valid_def entails_def by blast

theorem Valid_ichoice_sp_st:
  assumes "\<Turnstile> {P} c1 {Q}"
    and "\<Turnstile> {P} c2 {Q}"
  shows "\<Turnstile> {P} IChoice c1 c2 {Q}"
  using assms unfolding Valid_def by (auto elim: ichoiceE)

theorem Valid_cond_split:
  assumes "\<Turnstile> {\<lambda>s t. b s \<and> P s t} c1;d {Q}"
    and "\<Turnstile> {\<lambda>s t. \<not>b s \<and> P s t} c2;d {Q}"
  shows "\<Turnstile> {\<lambda>s t. P s t}
             IF b THEN c1 ELSE c2 FI;d
            {\<lambda>s t. Q s t}"
 using assms unfolding Valid_def
  apply (auto elim!: condE seqE)
  apply (simp add: seqB)
  apply (simp add: seqB)
  done


theorem Valid_ode_not:
  assumes "\<And>s. P s \<Longrightarrow> \<not> b s"
    and "\<And>s. P s \<Longrightarrow> Q s"
  shows "\<Turnstile> {\<lambda>s tr. P s}
     Cont ode b
    {\<lambda>s tr. Q s}"
  unfolding Valid_def
  using assms
  by(auto elim: contE)

theorem Valid_inv_s_eq:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) = 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s = r}
     Cont ode b
    {\<lambda>s tr. inv s = r}"
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
      have 5: "\<forall>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t))= 0" if "t\<in>{0 ..<d}" for t
        using 4 assms(2) that pre by auto
      show ?thesis
        using mvt_real_eq[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" d]
        using 1 5 pre by auto
    qed
    done

theorem Valid_inv_tr_eq:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) = 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s = r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s = r)) tr}"
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
      have 5: "\<forall>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t))= 0" if "t\<in>{0 ..<d}" for t
        using 4 assms(2) that pre by auto
      show ?thesis
        using mvt_real_eq[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" \<tau>]
        using 1 5 pre by auto
    qed
    done
  done


theorem Valid_inv_s_tr_eq:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) = 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s = r \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. inv s = r \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s = r)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_s_eq)
     prefer 3
  subgoal
    by(auto simp add: entails_def)
    prefer 3
    apply(rule Valid_inv_tr_eq)
    using assms by auto

theorem Valid_inv_s_ge:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s \<ge> r}
     Cont ode b
    {\<lambda>s tr. inv s \<ge> r}"
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
      have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)) \<ge> 0" if "t\<in>{0 ..<d}" for t
        using 4 assms(2) that pre by auto
      show ?thesis
        using mvt_real_ge[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" d]
        using 1 5 pre by auto
    qed
    done

theorem Valid_inv_tr_ge:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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
      have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t))\<ge> 0" if "t\<in>{0 ..<d}" for t
        using 4 assms(2) that pre by auto
      show ?thesis
        using mvt_real_ge[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" \<tau>]
        using 1 5 pre by auto
    qed
    done
  done
theorem Valid_inv_s_tr_ge:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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

theorem Valid_inv_s_g:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s > r}
     Cont ode b
    {\<lambda>s tr. inv s > r}"
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
      have 5: "\<forall>s\<ge>0. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)) \<ge> 0" if "t\<in>{0 ..<d}" for t
        using 4 assms(2) that pre by auto
      show ?thesis
        using mvt_real_ge[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" d]
        using 1 5 pre by auto
    qed
    done


theorem Valid_inv_tr_g:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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


theorem Valid_inv_s_le:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<le> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s \<le> r}
     Cont ode b
    {\<lambda>s tr. inv s \<le> r}"
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


theorem Valid_inv_tr_le:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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


theorem Valid_inv_s_l:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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

theorem Valid_ode_unique_solution_s_sp:
  assumes "\<And>s. P s \<Longrightarrow> d s > 0 \<and> ODEsol ode (p s) (d s) \<and>
                (\<forall>t. t \<ge> 0 \<and> t < d s \<longrightarrow> b (p s t)) \<and>
                \<not>b (p s (d s)) \<and> p s 0 = s"
    and "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    and "\<And>s. P s \<Longrightarrow> b s"
  shows "\<Turnstile>
    {\<lambda>s t. P s}
      Cont ode b
    {\<lambda>s t. \<exists>s'.(s = p s' (d s')) \<and> P s'}"
proof-
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


theorem Valid_inv_new_s_g:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>S. b S \<longrightarrow> (inv S \<ge> r) \<longrightarrow> g' (state2vec S) (ODE2Vec ode S) \<ge> 0"
  shows "\<Turnstile> {\<lambda>s tr. inv s > r}
     Cont ode b
    {\<lambda>s tr. inv s > r}"
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
     have 3: "\<forall>s. (s *\<^sub>R 1) = s" by simp
     have 4: "\<forall>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (ODE2Vec (ode) (p t))" if "t\<in>{-e .. d+e}" for t
        using 2 3 that by auto
      show ?thesis
        using real_inv_g[OF 1,of r d]
        using 4 pre assms e(1) 
        by auto
    qed
    done

theorem Valid_inv_b_s_ge:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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
      using IVT2[of "(\<lambda>t. b (p t))" d r 0]
      using pre g by force
    then have 4:"dd<d" 
      using g  le_less by auto
    then show False using dd pre
      using atLeastAtMost_iff by blast
      
    qed
    done

theorem Valid_inv_b_tr_ge:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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

theorem Valid_inv_b_s_tr_ge:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. P tr \<and> b s > r}
     Cont ode (\<lambda>s. b s > r)
    {\<lambda>s tr. b s = r  \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. b s \<ge> r)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_b_s_ge)
     prefer 3
    apply(rule Valid_inv_b_tr_ge)
  apply(auto simp add: entails_def)
    using assms by auto


theorem Valid_inv_b_s_ge_and_ge:
  fixes b1 :: "state \<Rightarrow> real"
  fixes b2 :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b1 (vec2state v)) has_derivative g1' (x)) (at x within UNIV)"
      and "\<forall>x. ((\<lambda>v. b2 (vec2state v)) has_derivative g2' (x)) (at x within UNIV)"
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


theorem Valid_inv_b_tr_ge_and_ge:
  fixes b1 :: "state \<Rightarrow> real"
  fixes b2 :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b1 (vec2state v)) has_derivative g1' (x)) (at x within UNIV)"
      and "\<forall>x. ((\<lambda>v. b2 (vec2state v)) has_derivative g2' (x)) (at x within UNIV)"
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

theorem Valid_inv_b_s_tr_ge_and_ge:
  fixes b1 :: "state \<Rightarrow> real"
  fixes b2 :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b1 (vec2state v)) has_derivative g1' (x)) (at x within UNIV)"
      and "\<forall>x. ((\<lambda>v. b2 (vec2state v)) has_derivative g2' (x)) (at x within UNIV)"
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



theorem Valid_inv_b_s_le:
  fixes b :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
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
  assumes "\<forall>x. ((\<lambda>v. b (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
  shows "\<Turnstile> {\<lambda>s tr. P tr \<and> b s < r}
     Cont ode (\<lambda>s. b s < r)
    {\<lambda>s tr. b s = r  \<and> (P @\<^sub>t ode_inv_assn (\<lambda>s. b s \<le> r)) tr}"
  apply(rule Valid_post_and)
   apply(rule Valid_weaken_pre)
    prefer 2
    apply(rule Valid_inv_b_s_le)
     prefer 3
    apply(rule Valid_inv_b_tr_le)
  apply(auto simp add: entails_def)
    using assms by auto

theorem DC':
  assumes "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr.  c s \<and> (P @\<^sub>t ode_inv_assn c) tr}"
      and "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> (\<lambda>s. b s \<and> c s) s}
     Cont ode (\<lambda>s. b s \<and> c s)
    {\<lambda>s tr. d s \<and> (P @\<^sub>t ode_inv_assn d) tr}"
    shows "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. d s \<and> (P @\<^sub>t ode_inv_assn d) tr}"
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

theorem DC'':
  assumes "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn c) tr}"
      and "\<Turnstile> {\<lambda>s tr. init s \<and> (\<lambda>s. b s \<and> c s) s}
     Cont ode (\<lambda>s. b s \<and> c s)
    {\<lambda>s tr. d s}"
    shows "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
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

theorem DC''':
  assumes "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. (P @\<^sub>t ode_inv_assn c) tr}"
      and "\<Turnstile> {\<lambda>s tr. init s \<and> (\<lambda>s. b s \<and> c s) s}
     Cont ode (\<lambda>s. b s \<and> c s)
    {\<lambda>s tr. d s}"
    shows "\<Turnstile> {\<lambda>s tr. init s \<and> P tr \<and> b s}
     Cont ode b
    {\<lambda>s tr. c s \<and>d s }"
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











thm has_derivative_exp
lemma derivative_exp[simp,derivative_intros]:
" ((exp has_derivative (*) (exp (x :: real))) (at x))"
  using DERIV_exp unfolding has_field_derivative_def
  by auto

lemma derivative_exp_const[derivative_intros]:
"((\<lambda>x. exp ((c:: real) * x)) has_derivative (\<lambda>xa. xa * c * exp (c * x))) (at x)"
proof-
  have 1:"((*) c has_derivative (\<lambda>x. x * c)) (at x)"
    apply (rule has_derivative_eq_rhs)
     apply (auto intro!: derivative_intros)[1]
    by auto
  show ?thesis using has_derivative_exp[OF 1] 
    by auto
  qed



lemma exp_1_subst:
"(state2vec
           (\<lambda>a. (if a = T then \<lambda>s. 1 else ((\<lambda>_ _. 0)(X := \<lambda>s. - s X)) a)
                 (vec2state v))) = ( \<chi> a. if a = T then 1 else if a = X then - v$X else 0)" for v
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
   apply (rule Valid_ode_unique_solution_s_sp[where d="\<lambda>s. P - s T" and p = "\<lambda>s. (\<lambda>t. s( X := s X * exp (-1 * t), T := s T + t))" ] )
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
    apply(rule c1_implies_local_lipschitz[where f'="(\<lambda>_. Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then - v $ X else 0)))"])
       apply (subst exp_1_subst) 
      apply (rule has_derivative_eq_rhs)
        apply (rule exp_1_deriv)
       apply (auto simp add: bounded_linear_Blinfun_apply exp_1_deriv_bounded)
  apply(auto simp add: entails_def)
  done
  
lemma exp_1_2:
 "\<Turnstile> {\<lambda>s tr. s X > 0 \<and> \<not> s T < P}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply(rule Valid_ode_not)
  by auto

lemma exp_1:
 "\<Turnstile> {\<lambda>s tr. s X > 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply(rule Valid_pre_cases)
   apply(rule exp_1_1)
   apply(rule exp_1_2)
  done

lemma exp_2_subst:
"(state2vec
           (\<lambda>a. (if a = T then \<lambda>s. 1 else ((\<lambda>_ _. 0)(X := \<lambda>s. s X)) a)
                 (vec2state v))) = ( \<chi> a. if a = T then 1 else if a = X then  v$X else 0)" for v
  apply(auto simp add: state2vec_def)
  using vec2state_def by auto

lemma exp_2_deriv_bounded:
  "bounded_linear (\<lambda>v. \<chi> a. if a = T then 0 else if a = X then  v $ X else 0)"
  apply (rule Real_Vector_Spaces.bounded_linear_intro[where K=1])
    apply (auto simp add: plus_vec_def scaleR_vec_def)
  by (simp add: norm_le_componentwise_cart)

lemma exp_2_deriv:
  "((\<lambda>v. \<chi> a. if a = T then 1 else if a = X then  v $ X else 0) has_derivative
      (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then  v $ X else 0)))
     (at x)"
proof -
  have a: "((\<chi> a. if a = T then 1 else if a = X then  y $ X else 0) -
            (\<chi> a. if a = T then 1 else if a = X then  x $ X else 0) -
            (\<chi> a. if a = T then 0 else if a = X then  (y - x) $ X else 0)) = (\<chi> a. 0)" for y
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
   apply (rule Valid_ode_unique_solution_s_sp[where d="\<lambda>s. P - s T" and p = "\<lambda>s. (\<lambda>t. s( X := s X * exp (t), T := s T + t))" ] )
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
  
lemma exp_2_2:
  "\<Turnstile> {\<lambda>s tr. s X > 0 \<and> \<not> s T < P}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply(rule Valid_ode_not)
  by auto

lemma exp_2:
  "\<Turnstile> {\<lambda>s tr. s X > 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply(rule Valid_pre_cases)
   apply(rule exp_2_1)
apply(rule exp_2_2)
  done


lemma exp_3_subst:
"(state2vec (\<lambda>a. (if a = T then \<lambda>s. 1 else ((\<lambda>_ _. 0)(X := \<lambda>s. 1 - s X)) a)
                          (vec2state v))) = ( \<chi> a. if a = T then 1 else if a = X then 1- v$X else 0)" for v
  apply(auto simp add: state2vec_def)
  using vec2state_def by auto


lemma exp_3_deriv_bounded:
  "bounded_linear (\<lambda>v. \<chi> a. if a = T then 0 else if a = X then  -v $ X else 0)"
  apply (rule Real_Vector_Spaces.bounded_linear_intro[where K=1])
    apply (auto simp add: plus_vec_def scaleR_vec_def)
  by (simp add: norm_le_componentwise_cart)

lemma exp_3_deriv:
  "((\<lambda>v. \<chi> a. if a = T then 1 else if a = X then 1 - v $ X else 0) has_derivative
      (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then  -v $ X else 0)))
     (at x)"
proof -
  have a: "((\<chi> a. if a = T then 1 else if a = X then 1- y $ X else 0) -
            (\<chi> a. if a = T then 1 else if a = X then 1- x $ X else 0) -
            (\<chi> a. if a = T then 0 else if a = X then  -(y - x) $ X else 0)) = (\<chi> a. 0)" for y
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
   apply (rule Valid_ode_unique_solution_s_sp[where d="\<lambda>s. P - s T" and p = "\<lambda>s. (\<lambda>t. s( X := (s X - 1) * exp (-t) + 1, T := s T + t))" ] )
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

lemma exp_3_2:
  "\<Turnstile> {\<lambda>s tr. s X > 0 \<and> \<not> s T < P}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. -s X + 1, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply(rule Valid_ode_not)
  by auto

lemma exp_3:
  "\<Turnstile> {\<lambda>s tr. s X > 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. -s X + 1, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply(rule Valid_pre_cases)
   apply(rule exp_3_1)
apply(rule exp_3_2)
  done




lemma exp_4_subst:
"(state2vec(\<lambda>a. (if a = T then \<lambda>s. 1 else ((\<lambda>_ _. 0)(X := \<lambda>s. - (s Y * s X))) a)
                          (vec2state v))) = ( \<chi> a. if a = T then 1 else if a = X then -v$Y * v$X else 0)" for v
  apply(auto simp add: state2vec_def)
  using vec2state_def by auto


lemma exp_4_deriv_bounded:
  "bounded_linear (\<lambda>v. \<chi> a. if a = T then 0 else if a = X then  -v$Y*x$X - v$X*x$Y else 0)"
  apply (rule Real_Vector_Spaces.bounded_linear_intro[where K=1])
    apply (auto simp add: plus_vec_def scaleR_vec_def)
 
  sorry

lemma exp_4_deriv:
  "((\<lambda>(v ::vec). \<chi> a. if a = T then 1 else if a = X then -v$Y * v$X else 0) has_derivative
      (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then  -v$Y*x$X - v$X*x$Y else 0)))
     (at x)"
proof -
 
  have a: "((\<chi> a. if a = T then 1 else if a = X then - (y::vec)$Y * y$X else 0) -
            (\<chi> a. if a = T then 1 else if a = X then - (x::vec)$Y * x$X else 0) -
            (\<chi> a. if a = T then 0 else if a = X then  - (y - x) $ Y * x $ X - (y - x) $ X * x $ Y else 0)) = (\<chi> i. if i = X then - (y - x)$X * (y - x)$Y else 0)" for y and x
    apply (auto simp add: minus_vec_def)
    apply (rule ext)
    apply (auto simp add:left_diff_distrib' mult.commute right_diff_distrib')
    done
  show ?thesis
    
    apply (rule has_derivativeI)
     prefer 2
    apply (rule tendstoI)
     apply auto
    subgoal for e
      apply (subst a)
      using eventually_at[where P = "\<lambda>xa. inverse (norm (xa - x)) * norm (\<chi> i. if i = X then - (xa - x) $ X * (xa - x) $ Y else 0) < e" and a = "x" and S = "UNIV"]
      apply auto
      sorry
    sorry
qed



lemma exp_4_1:
  "\<Turnstile> {\<lambda>s tr. s X > 0 \<and> s T < P}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s Y * s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply (rule Valid_strengthen_post)
  prefer 2
   apply (rule Valid_ode_unique_solution_s_sp[where d="\<lambda>s. P - s T" and p = "\<lambda>s. (\<lambda>t. s( X := (s X) * exp (-s Y * t), T := s T + t))" ] )
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
    apply(rule c1_implies_local_lipschitz[where f'="(\<lambda> (t,x) . Blinfun (\<lambda>v. (\<chi> a. if a = T then 0 else if a = X then -v$Y*x$X - v$X*x$Y else 0)))"])
       apply (subst exp_4_subst) 
      
      
    apply (rule has_derivative_eq_rhs)
  
        apply (rule exp_4_deriv)
       apply (auto simp add: bounded_linear_Blinfun_apply exp_4_deriv_bounded)
   apply(auto simp add: entails_def)

  sorry


lemma exp_4_2:
  "\<Turnstile> {\<lambda>s tr. s X > 0 \<and> \<not> s T < P}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s Y * s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply(rule Valid_ode_not)
  by auto

lemma exp_4:
  "\<Turnstile> {\<lambda>s tr. s X > 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. - s Y * s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X > 0}"
  apply(rule Valid_pre_cases)
   apply(rule exp_4_1)
apply(rule exp_4_2)
  done

lemma exp_5_1:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0 \<and> s T < P}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X \<ge> 0}"
  apply (rule Valid_strengthen_post)
  prefer 2
   apply (rule Valid_ode_unique_solution_s_sp[where d="\<lambda>s. P - s T" and p = "\<lambda>s. (\<lambda>t. s( X := s X * exp (t), T := s T + t))" ] )
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
  
lemma exp_5_2:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0 \<and> \<not> s T < P}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X \<ge> 0}"
  apply(rule Valid_ode_not)
  by auto

lemma exp_5:
  "\<Turnstile> {\<lambda>s tr. s X \<ge> 0}
     Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s X, T := \<lambda>s. 1))) (\<lambda>s. s T < P)
 {\<lambda>s tr. s X \<ge> 0}"
  apply(rule Valid_pre_cases)
   apply(rule exp_5_1)
apply(rule exp_5_2)
  done


lemma local_lipschitz_t_v:
  "local_lipschitz UNIV UNIV (\<lambda> (t :: real) (v :: real). t * v)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def)
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
  assumes "continuous_on UNIV (\<lambda>t. g t)"
  shows "local_lipschitz UNIV UNIV (\<lambda> t v . g t * v)"
  apply(rule  local_lipschitz_compose1[OF _ assms(1)])
  apply(rule local_lipschitz_subset[OF local_lipschitz_t_v])
  by auto


lemma dbxeq:
  fixes f :: "real \<Rightarrow> real"
  assumes " (f has_vderiv_on (\<lambda> t . g t * f t)) UNIV" 
    and "continuous_on UNIV (\<lambda>t. g t)"
    and "f 0 = 0"
    and "D \<ge> 0 "
  shows "f D = 0"
proof-
  have local:"local_lipschitz UNIV UNIV (\<lambda> t v . g t * v)"
    using local_lipschitz_gt_v[OF assms(2)]
    by auto
interpret loc:ll_on_open_it "UNIV"
      "\<lambda> t v . g t * v" UNIV 0
      apply standard
  using local apply auto
  using assms(2)
  by (simp add: continuous_on_mult_right)
  have s1:" (f solves_ode (\<lambda> t v . g t * v)) {0..D} UNIV" 
    unfolding solves_ode_def
    using assms    
    using has_vderiv_on_subset by blast
 have s2: "(loc.flow 0 0) t = (\<lambda>t. f t) t" if "t \<in> {0..D}" for t
   apply (rule loc.maximal_existence_flow(2)[OF s1])
   using that assms by auto
  have s3:" ((\<lambda> t . 0) solves_ode (\<lambda> t v . g t * v)) {0..D} UNIV"
 unfolding solves_ode_def
  apply auto
  by (simp add: has_vderiv_on_const)
 have s4: "(loc.flow 0 0) t = (\<lambda>t. 0) t" if "t \<in> {0..D}" for t
   apply (rule loc.maximal_existence_flow(2)[OF s3])
  using that assms by auto
  show ?thesis using s2 s4 assms by auto
qed

lemma dbxeq':
  fixes f :: "real \<Rightarrow> real"
  assumes " (f has_vderiv_on (\<lambda> t . g t * f t)) UNIV" 
    and "continuous_on UNIV (\<lambda>t. g t)"
    and "f d = 0" 
    and "d\<ge>0"
    and "D \<ge> 0"
  shows "f D = 0"
proof(cases "D \<ge> d")
  case g:True
  then show ?thesis

  proof-
have local:"local_lipschitz UNIV UNIV (\<lambda> t v . g t * v)"
    using local_lipschitz_gt_v[OF assms(2)]
    by auto
interpret loc:ll_on_open_it "UNIV"
      "\<lambda> t v . g (t + d) * v" UNIV 0
      apply standard
  apply auto
  subgoal
    apply(rule  local_lipschitz_compose1 [where g = "\<lambda> t . t + d"])
    subgoal using assms local_lipschitz_subset local
      by blast
    apply(auto intro:continuous_intros)
    done
  subgoal for x
  proof-
    have "continuous_on UNIV (\<lambda>t. t + d)"
      apply(auto intro:continuous_intros)
      done
    then show ?thesis
    using assms(2)
    using continuous_on_mult_right[where f="\<lambda> t .g( t + d)" and c= "x" and s= "UNIV"]
    using continuous_on_compose[where f="\<lambda> t . t + d" and g= "g" and s= "UNIV"]
    using continuous_on_subset 
    by auto
qed
  done
  have m:"((\<lambda>t. t + d) has_vderiv_on (\<lambda>_ . 1)) UNIV"
    apply (auto intro!: derivative_intros)
    done
  have s1:" ((\<lambda>t. f(t+d)) solves_ode (\<lambda> t v . g (t+d) * v)) {0..D} UNIV" 
    unfolding solves_ode_def
    apply auto
    apply(rule has_vderiv_on_subset[where S = "UNIV"])
    apply auto
    using assms(1) m
    using has_vderiv_on_compose[where g="\<lambda> t. t+d" and f = "f" and f' = "(\<lambda>t. g t * f t)" and g'="\<lambda>_. 1" and T=UNIV]
    apply auto
    using has_vderiv_on_subset by blast
 have s2: "(loc.flow 0 0) t = (\<lambda>t. f(t+d)) t" if "t \<in> {0..D}" for t
   apply(rule loc.maximal_existence_flow(2)[OF s1])
   using that assms by auto
  have s3:" ((\<lambda> t . 0) solves_ode (\<lambda> t v . g (t+d) * v)) {0..D} UNIV"
 unfolding solves_ode_def
  apply auto
  by (simp add: has_vderiv_on_const)
 have s4: "(loc.flow 0 0) t = (\<lambda>t. 0) t" if "t \<in> {0..D}" for t
   apply (rule loc.maximal_existence_flow(2)[OF s3])
  using that assms by auto
  show ?thesis using s2[of "D-d"] s4[of "D-d"] g assms by auto
qed
next
  case l:False
  then show ?thesis 
  proof-
have local:"local_lipschitz UNIV UNIV (\<lambda> t v . g t * v)"
    using local_lipschitz_gt_v[OF assms(2)]
    by auto
interpret loc:ll_on_open_it "UNIV"
      "\<lambda> t v . - g (d - t) * v" UNIV 0
      apply standard
  apply auto
  subgoal
    apply(rule  local_lipschitz_compose1 [where g = "\<lambda> t . d - t"])
    subgoal using assms local_lipschitz_subset local_lipschitz_minus local
      by fastforce
    apply(auto intro:continuous_intros)
    done
  subgoal for x
  proof-
    have "continuous_on UNIV (\<lambda>t. d - t)"
      apply(auto intro:continuous_intros)
      done
    then show ?thesis
    using assms(2)
    using continuous_on_mult_right[where f="\<lambda> t .g( d - t)" and c= "x" and s= "UNIV"]
    using continuous_on_subset continuous_on_minus
    by (metis continuous_on_compose2 subset_UNIV)
qed
  done
  have m:"((\<lambda>t. d - t) has_vderiv_on (\<lambda>_ . -1)) UNIV"
    apply (auto intro!: derivative_intros)
    done
  have s1:" ((\<lambda>t. f(d - t)) solves_ode (\<lambda> t v . - g (d - t) * v)) {0..d} UNIV" 
    unfolding solves_ode_def
    apply auto
    apply(rule has_vderiv_on_subset[where S = "UNIV"])
    apply auto
    using assms(1) m
    using has_vderiv_on_compose[where g="\<lambda> t. d-t" and f = "f" and f' = "(\<lambda>t. g t * f t)" and g'="\<lambda>_. -1" and T=UNIV]
    apply auto
    using has_vderiv_on_subset by blast
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

lemma dbxg:
  fixes f :: "real \<Rightarrow> real"
  assumes " (f has_vderiv_on (\<lambda> t . g t * f t)) UNIV" 
    and "continuous_on UNIV (\<lambda>t. g t)"
    and "f 0 > 0"
    and "D \<ge> 0 "
  shows "f D > 0"
proof(rule ccontr)
  assume "\<not> 0 < f D"
  then have 1:"f D \<le> 0" and "D > 0"
     apply linarith    
    using assms 
    using \<open>\<not> 0 < f D\<close> less_eq_real_def by blast
  have 2:"\<forall>t. continuous (at t within UNIV) f"
    using assms(1) unfolding has_vderiv_on_def has_vector_derivative_def
    using has_derivative_continuous has_derivative_subset
    by blast
  have 3:"\<forall>t\<in>{0 .. D}. isCont f t"
    using 2 by auto
  have 4:"{d. f d = 0 \<and> d \<in> {0 .. D}} \<noteq> {}"
    using IVT2[of f D 0 0] using 1 3 assms by auto
  obtain d where "d \<in> {0 .. D}" and "f d = 0"
    using 4 by auto
  then have "f 0 = 0"
    using dbxeq'[OF assms(1) assms(2)] by auto
  then show False using assms by auto
qed

lemma dbxl:
  fixes f :: "real \<Rightarrow> real"
  assumes " (f has_vderiv_on (\<lambda> t . g t * f t)) UNIV" 
    and "continuous_on UNIV (\<lambda>t. g t)"
    and "f 0 < 0"
    and "D \<ge> 0 "
  shows "f D < 0"
proof(rule ccontr)
  assume "\<not> f D < 0"
  then have 1:"f D \<ge> 0" and "D > 0"
     apply linarith    
    using assms 
    using \<open>\<not> 0 > f D\<close> less_eq_real_def by blast
  have 2:"\<forall>t. continuous (at t within UNIV) f"
    using assms(1) unfolding has_vderiv_on_def has_vector_derivative_def
    using has_derivative_continuous has_derivative_subset
    by blast
  have 3:"\<forall>t\<in>{0 .. D}. isCont f t"
    using 2 by auto
  have 4:"{d. f d = 0 \<and> d \<in> {0 .. D}} \<noteq> {}"
    using IVT[of f 0 0 D] using 1 3 assms by auto
  obtain d where "d \<in> {0 .. D}" and "f d = 0"
    using 4 by auto
  then have "f 0 = 0"
    using dbxeq'[OF assms(1) assms(2)] by auto
  then show False using assms by auto
qed

    
  
  




end