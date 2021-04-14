theory basicprime
    imports HHLProver.ContinuousInv  HHLProver.BigStepParallel 
begin

definition T :: char where "T = CHR ''t''"
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"
definition J :: char where "J = CHR ''j''"

lemma vars_distinct [simp]: "T \<noteq> X" "T \<noteq> Y" "T \<noteq> Z" "T \<noteq> J"
                                  "X \<noteq> T" "X \<noteq> Y" "X \<noteq> Z" "X \<noteq> J"
                                  "Y \<noteq> T" "Y \<noteq> X" "Y \<noteq> Z" "Y \<noteq> J"
                                  "Z \<noteq> T" "Z \<noteq> X" "Z \<noteq> Y" "Z \<noteq> J"
                                  "J \<noteq> T" "J \<noteq> X" "J \<noteq> Y" "J \<noteq> Z"


  unfolding T_def X_def Y_def Z_def J_def by auto



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

theorem Valid_ode_unique_solution_s_sp:
  assumes "\<And>s. b s \<Longrightarrow> d s > 0 \<and> ODEsol ode (p s) (d s) \<and>
                (\<forall>t. t \<ge> 0 \<and> t < d s \<longrightarrow> b (p s t)) \<and>
                \<not>b (p s (d s)) \<and> p s 0 = s"
    and "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    and "\<And>s. P s \<Longrightarrow> b s"
  shows "\<Turnstile>
    {\<lambda>s t. P s}
      Cont ode b
    {\<lambda>s t. \<exists>s'.(s = p s' (d s')) \<and> P s'}"
proof-
  have 1:"\<Turnstile>
    {\<lambda>s t. (\<lambda> s t. P s) s t}
      Cont ode b
    {\<lambda>s t. \<exists>s'. if b s' then (\<up>(s = p s' (d s')) \<and>\<^sub>t (\<lambda> s t. P s) s' @\<^sub>t Wait\<^sub>t (d s') (\<lambda>\<tau>. State (p s' \<tau>)) ({}, {})) t
                else (\<up>(s = s') \<and>\<^sub>t (\<lambda> s t. P s) s') t}"
    apply(rule Valid_ode_unique_solution_sp)
    using assms by auto
  show ?thesis
    apply(rule Valid_strengthen_post [OF _ 1])
    apply(auto simp add: entails_def pure_assn_def conj_assn_def join_assn_def)
    using assms(3) by auto
qed




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

end