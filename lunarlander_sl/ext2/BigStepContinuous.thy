theory BigStepContinuous
  imports BigStepSimple
begin

subsection \<open>Continuous evolution\<close>

inductive ode_c :: "ODE \<Rightarrow> 'a eform \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "\<not>b s0 \<Longrightarrow> P 0 s0 s tr \<Longrightarrow> ode_c ode b P s0 s tr"
| "d > 0 \<Longrightarrow> P d s' s tr \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   p 0 = rpart s0 \<Longrightarrow>
   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (updr s0 (p t))) \<Longrightarrow>
   \<not>b (updr s0 (p d)) \<Longrightarrow>
   s' = updr s0 (p d) \<Longrightarrow>
   ode_c ode b P s0 s (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. updr s0 (p \<tau>)) ({}, {}) # tr)"

text \<open>Hoare rules for ODE\<close>

lemma spec_of_cont:
  "spec_of (Cont ode b) (ode_c ode b (\<lambda>d. init))"
  unfolding Valid_def spec_of_def init_def
  apply (auto elim!: contE)
  subgoal for s0
    apply (rule ode_c.intros(1)) by auto
  subgoal for s0 d p
    apply (rule ode_c.intros(2)) by auto
  done

lemma Valid_cont_sp:
  assumes "spec_of c Q"
  shows "spec_of (Cont ode b; c)
                 (ode_c ode b (\<lambda>d. Q))"
  using assms unfolding Valid_def spec_of_def init_def
  apply (auto elim!: seqE contE)
  subgoal for s0 s' tr'
    apply (rule ode_c.intros(1)) by auto
  subgoal for s0 s' tr' d p
    apply (rule ode_c.intros(2)) by auto
  done

text \<open>Unique solution rule\<close>

text \<open>Waiting while the state is characterized by a particular solution.
  The parameters are:
  - d: mapping from initial state to waiting time.
  - p: mapping from initial state and time to new state. The value of p
       is only used in the time interval between 0 and d for any initial
       state.
\<close>
inductive wait_sol_c :: "('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "d s0 > 0 \<Longrightarrow> P (d s0) (updr s0 (p s0 (d s0))) s tr \<Longrightarrow>
   wait_sol_c p d P s0 s (WaitBlock (d s0) (\<lambda>t\<in>{0..d s0}. updr s0 (p s0 t)) ({}, {}) # tr)"
| "\<not>d s0 > 0 \<Longrightarrow> P 0 s0 s tr \<Longrightarrow> wait_sol_c p d P s0 s tr"

definition paramODEsol :: "ODE \<Rightarrow> 'a eform \<Rightarrow> ('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> 'a eexp \<Rightarrow> bool" where
  "paramODEsol ode b p d \<longleftrightarrow>
    (\<forall>s. if b s then
            d s > 0 \<and> ODEsol ode (p s) (d s) \<and> (\<forall>t. t \<ge> 0 \<and> t < d s \<longrightarrow> b (updr s (p s t))) \<and>
            \<not> b (updr s (p s (d s))) \<and> p s 0 = rpart s
         else
            \<not> d s > 0)"

lemma paramODEsolD:
  assumes "paramODEsol ode b p d"
    and "b s"
  shows "d s > 0"
        "ODEsol ode (p s) (d s)"
        "t \<ge> 0 \<and> t < d s \<longrightarrow> b (updr s (p s t))"
        "\<not> b (updr s (p s (d s)))"
        "p s 0 = rpart s"
  using assms unfolding paramODEsol_def by auto

lemma ode_c_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "ode_c ode b P s0 \<Longrightarrow>\<^sub>A wait_sol_c p d P s0"
proof -
  \<comment> \<open>The key result is to show that, for any other solution satisfying
      the ODE, it must be equal to the solution given by d, p.\<close>
  have main:
    "d2 = d s \<and> p s (d s) = p2 d2 \<and> (\<forall>\<tau>\<in>{0..d s}. p s \<tau> = p2 \<tau>) \<and>
     WaitBlock (d s) (\<lambda>t\<in>{0..d s}. updr s (p s t)) = WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p2 t))"
    if cond: "b s" "0 < d2"
      "ODEsol ode p2 d2"
      "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (updr s (p2 t))"
      "\<not>b (updr s (p2 d2))"
      "p2 0 = rpart s"
    for s p2 d2
  proof -
    interpret loc:ll_on_open_it "{-1<..}"
      "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
      apply standard
      using assms(2) by auto
    have s0: "0 < d s"
      using assms(1) unfolding paramODEsol_def using cond(1) by auto
    have s1: "((\<lambda>t. state2vec (p s t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d s} UNIV"
      using paramODEsolD(2)[OF assms(1) cond(1)] ODEsol_old unfolding ODEsol_def solves_ode_def by auto
    have s2: "(loc.flow 0 (state2vec (rpart s))) t = (\<lambda>t. state2vec (p s t)) t" if "t \<in> {0..d s}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s1])
      using that by (auto simp add: state2vec_def paramODEsolD[OF assms(1) cond(1)])
    have s3: "((\<lambda>t. state2vec (p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d2} UNIV"
      using cond(3) ODEsol_old unfolding ODEsol_def solves_ode_def by auto
    have s4: "loc.flow 0 (state2vec (rpart s)) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s3])
      using cond(2,6) that by auto
    have s5: "d s \<le> d2"
    proof (rule ccontr)
      assume 0: "\<not>(d s \<le> d2)"
      from 0 have 1: "(\<lambda>t. state2vec (p s t)) d2 = (\<lambda>t. state2vec (p2 t)) d2"
        using s2[of d2] s4[of d2] cond(2) by auto
      from 1 have "p s d2 = p2 d2"
        by (auto simp add: state2vec_def)
      show False
        using "0" \<open>p s d2 = p2 d2\<close> paramODEsolD(3)[OF assms(1) cond(1)] cond(2,5)
        using less_eq_real_def by fastforce
    qed
    have s6: "d2 \<le> d s"
    proof (rule ccontr)
      assume 0: "\<not>(d2 \<le> d s)"
      from 0 have 1: "(\<lambda>t. state2vec (p s t)) (d s) = (\<lambda>t. state2vec (p2 t)) (d s)"
        using s2[of "d s"] s4[of "d s"] s0 by auto
      from 1 have "p s (d s) = p2 (d s)"
        by (auto simp add: state2vec_def)
      show False
        using "0" \<open>p s (d s) = p2 (d s)\<close> paramODEsolD[OF assms(1) cond(1)] cond(1,4)
        by auto
    qed
    have s7: "d s = d2" using s5 s6 by auto
    have s8: "t\<in>{0..d s} \<Longrightarrow> p2 t = p s t" for t
      using s2 s4 s7 by (metis vec_state_map1)
    have s9: "p s (d s) = p2 (d s)"
      using s8 by (simp add: s0 less_eq_real_def)
    have s10: "WaitBlock (d s) (\<lambda>t\<in>{0..d s}. updr s (p s t)) = WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p2 t))"
      using s7 s8 by fastforce
    show ?thesis using s7 s8 s9 s10 by auto
  qed
  show ?thesis
    unfolding entails_def apply auto
    subgoal for s tr
      apply (auto simp add: ode_c.simps)
      subgoal
        apply (rule wait_sol_c.intros)
        using assms(1) unfolding paramODEsol_def by auto
      subgoal premises pre for d' tr' p'
      proof -
        have "b (updr s0 (p' 0))"
          using pre(2,5,6) by auto
        then have "b s0"
          apply (cases s0)
          by (auto simp add: pre(5) rpart.simps updr.simps)
        have a: "d' = d s0"
              "p s0 (d s0) = p' d'"
              "(\<forall>\<tau>\<in>{0..d s0}. p s0 \<tau> = p' \<tau>)"
              "WaitBlock (d s0) (\<lambda>t\<in>{0..d s0}. updr s0 (p s0 t)) = WaitBlock d' (\<lambda>t\<in>{0..d'}. updr s0 (p' t))"
          using main[of s0 d' p', OF \<open>b s0\<close> pre(2,4,6,7,5)] by auto
        show ?thesis
          unfolding a(4)[symmetric]
          apply (rule wait_sol_c.intros(1))
          using pre(2,3) a(1,2) by auto
      qed
      done
    done
qed

lemma spec_of_cont_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "spec_of (Cont ode b)
             (wait_sol_c p d (\<lambda>_. init))"
  apply (rule spec_of_post)
   apply (rule spec_of_cont) apply auto
  apply (rule ode_c_unique)
  using assms by auto

lemma Valid_cont_unique_sp:
  assumes "spec_of c Q"
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows "spec_of (Cont ode b; c)
                 (wait_sol_c p d (\<lambda>d. Q))"
  apply (rule spec_of_post)
  apply (rule Valid_cont_sp[OF assms(1)]) apply auto
  apply (rule ode_c_unique)
  using assms by auto

lemma test1:
  "spec_of (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. val s X < 1))
           (wait_sol_c (\<lambda>s0 t. (rpart s0)(X := val s0 X + t)) (\<lambda>s0. 1 - val s0 X) (\<lambda>_. init))"
proof -
  have 1: "paramODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>s. val s X < 1)
                       (\<lambda>s0 t. (rpart s0)(X := val s0 X + t)) (\<lambda>s0. 1 - val s0 X)"
    unfolding paramODEsol_def apply clarify
    subgoal for s
      apply (cases "val s X < 1")
      subgoal apply auto
        subgoal
          unfolding ODEsol_def solves_ode_def has_vderiv_on_def
          apply auto
          apply (rule exI[where x="1"])
          apply auto
          apply (rule has_vector_derivative_projI)
          apply (auto simp add: state2vec_def)
          apply (rule has_vector_derivative_eq_rhs)
           apply (auto intro!: derivative_intros)[1]
          by simp
        subgoal for t
          apply (cases s) by (auto simp add: updr.simps val.simps)
        subgoal 
          apply (cases s) by (auto simp add: updr.simps val.simps)
        subgoal
          apply (cases s) by (auto simp add: rpart.simps val.simps)
        done
      subgoal by auto
      done
    done
  have 2: "local_lipschitz {- 1<..} UNIV (\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (vec2state v))"
  proof -
    have eq: "(\<chi> a. (if a = X then \<lambda>_. 1 else (\<lambda>_. 0)) (($) v)) = (\<chi> a. if a = X then 1 else 0)" for v::vec
      by auto
    show ?thesis
      unfolding fun_upd_def vec2state_def
      apply (auto simp add: state2vec_def eq)
      by (rule local_lipschitz_constI)
  qed
  show ?thesis
    apply (rule spec_of_post)
     apply (rule spec_of_cont_unique)
    apply (rule 1) apply (rule 2)
    apply clarify by (rule entails_triv)
qed


end
