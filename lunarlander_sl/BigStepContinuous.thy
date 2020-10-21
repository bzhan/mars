theory BigStepContinuous
  imports BigStepSimple Analysis_More
begin


subsection \<open>Hoare rules for ODE\<close>

inductive_cases contE: "big_step (Cont ode b) s1 tr s2"
thm contE

text \<open>Weakest precondition form\<close>
theorem Valid_ode:
  "Valid
    (\<lambda>s tr. (\<not>b s \<longrightarrow> Q s tr) \<and>
            (\<forall>d p. 0 < d \<longrightarrow> ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                   Q (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})])))
    (Cont ode b)
    Q"
  unfolding Valid_def
  by (auto elim!: contE)

text \<open>Strongest postcondition form\<close>
theorem Valid_ode':
  assumes "b st"
  shows "Valid
    (\<lambda>s tr. s = st \<and> tr = [])
    (Cont ode b)
    (\<lambda>s tr. (\<exists>d p. 0 < d \<and> ODEsol ode p d \<and> p 0 = st \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d) \<and>
                   s = p d \<and> tr = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})]))"
  apply (rule Valid_weaken_pre)
  prefer 2 apply (rule Valid_ode)
  by (auto simp add: entails_def assms)


theorem Valid_ode_unique_solution:
  assumes
    "d > 0" "ODEsol ode p d" "\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)"
    "\<not> b (p d)" "p 0 = st"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows "Valid
    (\<lambda>s t. s = st \<and> t = tr)
    (Cont ode b)
    (\<lambda>s t. s = p d \<and> t = tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})])"
proof -
  have "b (p 0)"
    using assms(1,3) by auto
  have main: "d2 = d \<and> p d = p2 d2 \<and> (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) = (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>))"
    if cond: "0 < d2"
       "ODEsol ode p2 d2"
       "(\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t))"
       "\<not> b (p2 d2)"
       "p2 0 = st"
     for p2 d2
  proof -
    interpret loc:ll_on_open_it "{-1<..}"
      "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
      apply standard
      using assms(6) by auto
    have s1: "((\<lambda>t. state2vec (p t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d} UNIV"
      using assms(2) unfolding ODEsol_def solves_ode_def by auto
    have s2: "(loc.flow 0 (state2vec st)) t = (\<lambda>t. state2vec (p t)) t" if "t \<in> {0..d}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s1])
      using that by (auto simp add: state2vec_def assms(1,5))
    have s3: "((\<lambda>t. state2vec(p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d2} UNIV"
      using cond(2) unfolding ODEsol_def solves_ode_def by auto
    have s4: "loc.flow 0 (state2vec st) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s3])
      using cond(1,5) that by auto
    have s5: "d \<le> d2"
    proof (rule ccontr)
      assume 0: "\<not>(d \<le> d2)"
      from 0 have 1: "(\<lambda>t. state2vec (p t)) d2 = (\<lambda>t. state2vec (p2 t)) d2"
        using s2[of d2] s4[of d2] cond(1) by auto
      from 1 have "p d2 = p2 d2"
        by (auto simp add: state2vec_def)
      show False
        using "0" \<open>p d2 = p2 d2\<close> assms(3) that(1) that(4)
        using less_eq_real_def by auto
    qed
    have s6: "d2 \<le> d"
    proof (rule ccontr)
      assume 0: "\<not>(d2 \<le> d)"
      from 0 have 1: "(\<lambda>t. state2vec (p t)) d = (\<lambda>t. state2vec (p2 t)) d"
        using s2[of d] s4[of d] assms(1) by auto
      from 1 have "p d = p2 d"
        by (auto simp add: state2vec_def)
      show False
        using "0" \<open>p d = p2 d\<close> assms(1) assms(4) that(3) by auto
    qed
    have s7: "d = d2" using s5 s6 by auto
    have s8: "t\<in>{0..d} \<Longrightarrow> p2 t = p t" for t
      using s2 s4 s7 by (metis vec_state_map1)
    have s9: "(\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) = (\<lambda>\<tau>\<in>{0..d}. State (p2 \<tau>))"
      using s7 s8 unfolding restrict_def by auto
    have s10: "p d = p2 d"
      using s8 by (simp add: assms(1) less_eq_real_def)
    show ?thesis using s7 s9 s10 by auto
  qed
  show ?thesis
    apply (rule Valid_weaken_pre)
     prefer 2 apply (rule Valid_ode)
    apply (auto simp add: entails_def)
    using assms(5) \<open>b (p 0)\<close> apply simp
    subgoal for d1 p1
      using main[of d1 p1] by auto
    subgoal for d1 p1
      using main[of d1 p1] by auto
    subgoal for d1 p1
      using main[of d1 p1] by auto
    done
qed


subsection \<open>Tests for ODE\<close>

lemma testHL12:
  "Valid
    (\<lambda>s t. s = (\<lambda>_. 0) \<and> t = tr)
    (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
    (\<lambda>s t. s = ((\<lambda>_. 0)(X := 1)) \<and> t = tr @ [WaitBlock 1 (\<lambda>t\<in>{0..1}. State ((\<lambda>_. 0)(X := t))) ({}, {})])"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (fun_upd (\<lambda>_. 0) X) 1"
     unfolding ODEsol_def solves_ode_def has_vderiv_on_def
     apply auto
     apply (rule has_vector_derivative_projI)
     by (auto simp add: state2vec_def)
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
    apply (rule Valid_strengthen_post)
    prefer 2 apply (rule Valid_ode_unique_solution[of 1 _ "\<lambda>t. (\<lambda>_. 0)(X := t)"])
    using 1 2 by (auto simp add: entails_def)
qed


end
