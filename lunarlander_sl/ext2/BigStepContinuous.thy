theory BigStepContinuous
  imports BigStepSimple
begin

subsection \<open>Continuous evolution\<close>

inductive ode_c :: "ODE \<Rightarrow> 'a eform \<Rightarrow> 'a assn2 \<Rightarrow> 'a assn2" where
  "\<not>b s0 \<Longrightarrow> P s0 s tr \<Longrightarrow> ode_c ode b P s0 s tr"
| "0 < d \<Longrightarrow> P (updr s0 (p d)) s tr \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   p 0 = rpart s0 \<Longrightarrow>
   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (updr s0 (p t))) \<Longrightarrow>
   \<not>b (updr s0 (p d)) \<Longrightarrow>
   ode_c ode b P s0 s (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. updr s0 (p \<tau>)) ({}, {}) # tr)"

text \<open>Hoare rules for ODE\<close>

lemma spec_of_cont:
  "spec_of (Cont ode b) (ode_c ode b init)"
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
                 (ode_c ode b Q)"
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
inductive wait_sol_c :: "('a estate \<Rightarrow> real \<Rightarrow> 'a estate) \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "d s0 > 0 \<Longrightarrow> P (d s0) s0 s tr \<Longrightarrow>
   wait_sol_c p d P s0 s (WaitBlock (d s0) (\<lambda>t\<in>{0..d s0}. p s0 t) ({}, {}) # tr)"
| "\<not>d s0 > 0 \<Longrightarrow> P 0 s0 s tr \<Longrightarrow> wait_sol_c p d P s0 s tr"

lemma wait_sol_mono:
  assumes "\<And>d' s0. P d' s0 \<Longrightarrow>\<^sub>A Q d' s0"
  shows "wait_sol_c p d P s0 \<Longrightarrow>\<^sub>A wait_sol_c p d Q s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (induct rule: wait_sol_c.cases) apply auto
    subgoal for tr'
      apply (rule wait_sol_c.intros(1))
      using assms unfolding entails_def by auto
    subgoal
      apply (rule wait_sol_c.intros(2))
      using assms unfolding entails_def by auto
    done
  done

definition paramODEsol :: "ODE \<Rightarrow> 'a eform \<Rightarrow> ('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> 'a eexp \<Rightarrow> bool" where
  "paramODEsol ode b p d \<longleftrightarrow>
    (\<forall>s. p s 0 = rpart s \<and>
        (if b s then
            d s > 0 \<and> ODEsol ode (p s) (d s) \<and> (\<forall>t. t \<ge> 0 \<and> t < d s \<longrightarrow> b (updr s (p s t))) \<and>
            \<not> b (updr s (p s (d s)))
         else
            \<not> d s > 0))"

lemma paramODEsolD:
  assumes "paramODEsol ode b p d"
    and "b s"
  shows "d s > 0"
        "ODEsol ode (p s) (d s)"
        "t \<ge> 0 \<and> t < d s \<longrightarrow> b (updr s (p s t))"
        "\<not> b (updr s (p s (d s)))"
  using assms unfolding paramODEsol_def by auto

lemma paramODEsolD2:
  assumes "paramODEsol ode b p d"
  shows "p s 0 = rpart s"
  using assms unfolding paramODEsol_def by auto

lemma ode_c_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "ode_c ode b P s0 \<Longrightarrow>\<^sub>A wait_sol_c (\<lambda>s t. updr s (p s t)) d (\<lambda>d' s. P (updr s (p s d'))) s0"
proof -
  \<comment> \<open>The key result is to show that, for any other solution satisfying
      the ODE, it must be equal to the solution given by d, p.\<close>
  have main:
    "d2 = d s \<and> p s (d s) = p2 d2 \<and>
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
      using that by (auto simp add: state2vec_def paramODEsolD[OF assms(1) cond(1)] paramODEsolD2[OF assms(1)])
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
    show ?thesis using s7 s9 s10 by auto
  qed
  show ?thesis
    unfolding entails_def apply auto
    subgoal for s tr
      apply (auto simp add: ode_c.simps)
      subgoal
        apply (rule wait_sol_c.intros)
        using assms(1) unfolding paramODEsol_def by auto
      subgoal premises pre for d' p' tr'
      proof -
        have "b (updr s0 (p' 0))"
          using pre(2,5,6) by auto
        then have "b s0" by (auto simp add: pre(5))
        have a: "d' = d s0"
              "p s0 (d s0) = p' d'"
              "WaitBlock (d s0) (\<lambda>t\<in>{0..d s0}. updr s0 (p s0 t)) = WaitBlock d' (\<lambda>t\<in>{0..d'}. updr s0 (p' t))"
          using main[of s0 d' p', OF \<open>b s0\<close> pre(2,4,6,7,5)] by auto
        show ?thesis
          unfolding a(3)[symmetric]
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
             (wait_sol_c (\<lambda>s t. updr s (p s t)) d (\<lambda>d' s. init (updr s (p s d'))))"
  apply (rule spec_of_post)
   apply (rule spec_of_cont) apply auto
  apply (rule entails_trans)
   apply (rule ode_c_unique[OF assms])
  by (rule entails_triv)

lemma Valid_cont_unique_sp:
  assumes "spec_of c Q"
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows "spec_of (Cont ode b; c)
                 (wait_sol_c (\<lambda>s t. updr s (p s t)) d (\<lambda>d' s. Q (updr s (p s d'))))"
  apply (rule spec_of_post)
   apply (rule Valid_cont_sp[OF assms(1)]) apply auto
  apply (rule entails_trans)
  apply (rule ode_c_unique[OF assms(2,3)])
  by (rule entails_triv)

lemma updr_rpart_simp:
  "updr s ((rpart s)(X := v)) = upd s X v"
  apply (cases s) by (auto simp add: updr.simps rpart.simps upd.simps)

lemma updr_rpart_simp2:
  "updr s ((rpart s)(X := v, Y := w)) = upd (upd s X v) Y w"
  apply (cases s) by (auto simp add: updr.simps rpart.simps upd.simps)

lemma test1:
  assumes "spec_of c Q"
  shows
  "spec_of (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. val s X < 1); c)
           (wait_sol_c (\<lambda>s t. upd s X (val s X + t)) (\<lambda>s. 1 - val s X)
                       (\<lambda>d s. Q (upd s X (val s X + d))))"
proof -
  have 1: "paramODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>s. val s X < 1)
                       (\<lambda>s t. (rpart s)(X := val s X + t)) (\<lambda>s. 1 - val s X)"
    unfolding paramODEsol_def apply clarify
    subgoal for s
      apply (rule conjI)
      subgoal apply (cases s)
        by (auto simp add: rpart.simps val.simps)
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
     apply (rule Valid_cont_unique_sp)
    apply (rule assms)
      apply (rule 1) apply (rule 2)
    apply clarify apply (simp only: updr_rpart_simp)
    apply (rule wait_sol_mono) subgoal for _ d' s
      by (rule entails_triv)
    done
qed

subsection \<open>Interrupt\<close>

text \<open>We define the general form of assertion for interrupt

  Each input/output is specified by channel name, communicated function,
  and ensuing assertion.
\<close>
datatype 'a comm_spec =
  InSpec cname var "'a assn2"
| OutSpec cname "'a eexp" "'a assn2"

fun rdy_of_comm_spec :: "'a comm_spec list \<Rightarrow> rdy_info" where
  "rdy_of_comm_spec [] = ({}, {})"
| "rdy_of_comm_spec (InSpec ch var P # rest) = (
    let rdy = rdy_of_comm_spec rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_comm_spec (OutSpec ch e P # rest) = (
    let rdy = rdy_of_comm_spec rest in
      (fst rdy, insert ch (snd rdy)))"

inductive interrupt_c :: "ODE \<Rightarrow> 'a eform \<Rightarrow> 'a assn2 \<Rightarrow> 'a comm_spec list \<Rightarrow> 'a assn2" where
  "\<not>b s0 \<Longrightarrow> P s0 s tr \<Longrightarrow> interrupt_c ode b P specs s0 s tr"
| "0 < d \<Longrightarrow> P (updr s0 (p d)) s tr \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   p 0 = rpart s0 \<Longrightarrow>
   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (updr s0 (p t))) \<Longrightarrow>
   \<not>b (updr s0 (p d)) \<Longrightarrow> rdy = rdy_of_comm_spec specs \<Longrightarrow>
   interrupt_c ode b P specs s0 s (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. updr s0 (p \<tau>)) rdy # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec ch var Q \<Longrightarrow>
   Q (upd s0 var v) s tr \<Longrightarrow> interrupt_c ode b P specs s0 s (InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec ch var Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q (updr s0 ((p d)(var := v))) s tr \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   p 0 = rpart s0 \<Longrightarrow>
   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (updr s0 (p t))) \<Longrightarrow>
   rdy = rdy_of_comm_spec specs \<Longrightarrow>
   interrupt_c ode b P specs s0 s (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. updr s0 (p \<tau>)) rdy # InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec ch e Q \<Longrightarrow>
   Q s0 s tr \<Longrightarrow> interrupt_c ode b P specs s0 s (OutBlock ch (e s0) # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec ch e Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q (updr s0 (p d)) s tr \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   p 0 = rpart s0 \<Longrightarrow>
   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (updr s0 (p t))) \<Longrightarrow>
   rdy = rdy_of_comm_spec specs \<Longrightarrow>
   interrupt_c ode b P specs s0 s (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. updr s0 (p \<tau>)) rdy # OutBlock ch (e (updr s0 (p d))) # tr)"

text \<open>Hoare rules for interrupt\<close>

inductive spec_of_es :: "'a comm \<times> 'a proc \<Rightarrow> 'a comm_spec \<Rightarrow> bool" where
  "spec_of c Q \<Longrightarrow> spec_of_es (ch[?]var, c) (InSpec ch var Q)"
| "spec_of c Q \<Longrightarrow> spec_of_es (ch[!]e, c) (OutSpec ch e Q)"

lemma rdy_of_comm_spec_correct:
  assumes "\<forall>i. i < length es \<longrightarrow> spec_of_es (es ! i) (specs ! i)"
    shows "rdy_of_echoice es = rdy_of_comm_spec specs"
  sorry

lemma spec_of_interrupt:
  assumes "length es = length specs"
    and "\<forall>i. i < length es \<longrightarrow> spec_of_es (es ! i) (specs ! i)"
  shows
  "spec_of (Interrupt ode b es)
           (interrupt_c ode b init specs)"
  unfolding Valid_def spec_of_def init_def apply clarify
  apply (auto elim!: interruptE)
  subgoal premises pre for s0 s2 i ch e p2 tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using assms(2) pre(1) by auto
    then obtain Q where Q: "specs ! i = OutSpec ch e Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(5))
      using assms pre(1) apply auto[1]
      using Q(1) apply auto[1]
      using pre(3) Q(2) unfolding spec_of_def Valid_def init_def by auto
  qed
  subgoal premises pre for s0 s2 d p i ch e p2 tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using assms(2) pre(5) by auto
    then obtain Q where Q: "specs ! i = OutSpec ch e Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(6))
      using assms pre(5) apply auto[1]
      using Q(1) apply auto[1]
      using pre(1) apply auto[1]
      using pre(7) Q(2) unfolding spec_of_def Valid_def init_def apply auto[1]
      using pre assms(2) rdy_of_comm_spec_correct by auto
  qed
  subgoal premises pre for s0 s2 i ch var p2 v tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using assms(2) pre(1) by auto
    then obtain Q where Q: "specs ! i = InSpec ch var Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(3))
      using assms pre(1) apply auto[1]
      using Q(1) apply auto[1]
      using pre(3) Q(2) unfolding spec_of_def Valid_def init_def by auto
  qed
  subgoal premises pre for s0 s2 d p i ch var p2 v tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using assms(2) pre(5) by auto
    then obtain Q where Q: "specs ! i = InSpec ch var Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(4))
      using assms pre(5) apply auto[1]
      using Q(1) apply auto[1]
      using pre(1) apply auto[1]
      using pre(7) Q(2) unfolding spec_of_def Valid_def init_def apply auto[1]
      using pre assms(2) rdy_of_comm_spec_correct by auto
  qed
  subgoal premises pre for s0
    apply (rule interrupt_c.intros(1))
    using pre by auto
  subgoal premises pre for s0 d p
    apply (rule interrupt_c.intros(2))
    using pre assms(2) rdy_of_comm_spec_correct by auto
  done

text \<open>Unique solution rule for interrupt\<close>

datatype 'a comm_spec2 =
  InSpec2 cname "real \<Rightarrow> real \<Rightarrow> 'a assn2"
| OutSpec2 cname "real \<Rightarrow> 'a eexp" "real \<Rightarrow> 'a assn2"

fun spec2_of :: "('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> 'a comm_spec \<Rightarrow> 'a comm_spec2" where
  "spec2_of p (InSpec ch var Q) = InSpec2 ch (\<lambda>d v s0. Q (updr s0 ((p s0 d)(var := v))))"
| "spec2_of p (OutSpec ch e Q) = OutSpec2 ch (\<lambda>d s0. e (updr s0 (p s0 d))) (\<lambda>d s0. Q (updr s0 (p s0 d)))"

fun rdy_of_comm_spec2 :: "'a comm_spec2 list \<Rightarrow> rdy_info" where
  "rdy_of_comm_spec2 [] = ({}, {})"
| "rdy_of_comm_spec2 (InSpec2 ch P # rest) = (
    let rdy = rdy_of_comm_spec2 rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_comm_spec2 (OutSpec2 ch e P # rest) = (
    let rdy = rdy_of_comm_spec2 rest in
      (fst rdy, insert ch (snd rdy)))"

lemma rdy_of_comm_spec2_of:
  "rdy_of_comm_spec specs = rdy_of_comm_spec2 (map (spec2_of p) specs)"
  sorry

inductive interrupt_sol_c :: "('a estate \<Rightarrow> real \<Rightarrow> 'a estate) \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow>
  'a comm_spec2 list \<Rightarrow> 'a assn2" where
  "d s0 > 0 \<Longrightarrow> P (d s0) s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s (WaitBlock (d s0) (\<lambda>\<tau>\<in>{0..d s0}. p s0 \<tau>) rdy # tr)"
| "\<not>d s0 > 0 \<Longrightarrow> P 0 s0 s tr \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s tr"
| "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s (InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   0 < d' \<Longrightarrow> d' \<le> d s0 \<Longrightarrow> Q d' v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s (WaitBlock d' (\<lambda>\<tau>\<in>{0..d'}. p s0 \<tau>) rdy # InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch e Q \<Longrightarrow> v = e 0 s0 \<Longrightarrow>
   Q 0 s0 s tr \<Longrightarrow> interrupt_sol_c p d P specs s0 s (OutBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch e Q \<Longrightarrow>
   0 < d' \<Longrightarrow> d' \<le> d s0 \<Longrightarrow> Q d' s0 s tr \<Longrightarrow> v = e d' s0 \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s (WaitBlock d' (\<lambda>\<tau>\<in>{0..d'}. p s0 \<tau>) rdy # OutBlock ch v # tr)"

lemma interrupt_c_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "interrupt_c ode b P specs s0 \<Longrightarrow>\<^sub>A
     interrupt_sol_c (\<lambda>s t. updr s (p s t)) d (\<lambda>d' s. P (updr s (p s d'))) (map (spec2_of p) specs) s0"
proof -
  \<comment> \<open>The key result is to show that, for any other solution satisfying
      the ODE, it must be equal to the solution given by d, p.\<close>
  have main:
    "d2 = d s \<and> p s (d s) = p2 d2 \<and>
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
      using that by (auto simp add: state2vec_def paramODEsolD[OF assms(1) cond(1)] paramODEsolD2[OF assms(1)])
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
    show ?thesis using s7 s9 s10 by auto
  qed
  have main2:
    "d2 \<le> d s \<and> p s d2 = p2 d2 \<and>
     WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p s t)) = WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p2 t))"
    if cond: "b s" "0 < d2"
      "ODEsol ode p2 d2"
      "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (updr s (p2 t))"
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
      using that by (auto simp add: state2vec_def paramODEsolD[OF assms(1) cond(1)] paramODEsolD2[OF assms(1)])
    have s3: "((\<lambda>t. state2vec (p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d2} UNIV"
      using cond(3) ODEsol_old unfolding ODEsol_def solves_ode_def by auto
    have s4: "loc.flow 0 (state2vec (rpart s)) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s3])
      using cond that by auto
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
    have s7: "t\<in>{0..d2} \<Longrightarrow> loc.flow 0 (state2vec (rpart s)) t = state2vec (p s t)" for t
      using s2 s6 by auto
    have s8: "t\<in>{0..d2} \<Longrightarrow> p2 t = p s t" for t
      using s7 s4 by (metis vec_state_map1)
    have s9: "p s d2 = p2 d2"
      using s8 that(2) by fastforce
    have s10: "WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p s t)) = WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p2 t))"
      using s7 s8 by fastforce
    show ?thesis using s6 s9 s10 by auto
  qed
  have p0: "p s0 0 = rpart s0"
    using paramODEsolD2[OF assms(1)] by auto
  let ?specs2 = "map (spec2_of p) specs"
  have length: "length ?specs2 = length specs"
    by auto
  have speci: "?specs2 ! i = spec2_of p (specs ! i)" if "i < length specs" for i
    using that by auto
  show ?thesis
    unfolding entails_def apply auto
    subgoal for s tr
      apply (auto simp add: interrupt_c.simps)
      subgoal
        apply (rule interrupt_sol_c.intros(2))
        using assms(1) unfolding paramODEsol_def by auto
      subgoal premises pre for d' p' tr'
      proof -
        have "b (updr s0 (p' 0))"
          using pre(2,5,6) by auto
        then have "b s0" by (auto simp add: pre(5))
        have a: "d' = d s0"
              "p s0 (d s0) = p' d'"
              "WaitBlock (d s0) (\<lambda>t\<in>{0..d s0}. updr s0 (p s0 t)) = WaitBlock d' (\<lambda>t\<in>{0..d'}. updr s0 (p' t))"
          using main[of s0 d' p', OF \<open>b s0\<close> pre(2,4,6,7,5)] by auto
        show ?thesis
          unfolding a(3)[symmetric]
          apply (rule interrupt_sol_c.intros(1))
          using pre(2,3) a(1,2) rdy_of_comm_spec2_of by auto
      qed
      subgoal premises pre for i ch var Q v tr'
      proof -
        let ?Q' = "\<lambda>d v s0. Q (updr s0 ((p s0 d)(var := v)))"
        have Q: "?specs2 ! i = InSpec2 ch ?Q'"
          using speci[OF pre(2)] unfolding pre(3) by auto
        show ?thesis
          apply (rule interrupt_sol_c.intros(3)[of i _ _ ?Q'])
          using pre Q length p0 by (auto simp add: updr_rpart_simp)
      qed
      subgoal premises pre for i ch var Q d' p' v tr'
      proof -
        have "b (updr s0 (p' 0))"
          using pre by auto
        then have "b s0" using pre by auto
        have a: "d' \<le> d s0"
              "p s0 d' = p' d'"
              "WaitBlock d' (\<lambda>t\<in>{0..d'}. updr s0 (p s0 t)) = WaitBlock d' (\<lambda>t\<in>{0..d'}. updr s0 (p' t))"
          using main2[of s0 d' p', OF \<open>b s0\<close> pre(4,6,8,7)] by auto
        let ?Q' = "\<lambda>d v s0. Q (updr s0 ((p s0 d)(var := v)))"
        have Q: "?specs2 ! i = InSpec2 ch ?Q'"
          using speci[OF pre(2)] unfolding pre(3) by auto
        show ?thesis
          unfolding a(3)[symmetric]
          apply (rule interrupt_sol_c.intros(4)[of i _ _ ?Q'])
          using pre(2,3,4,5) a(1,2) Q length rdy_of_comm_spec2_of by auto
      qed
      subgoal premises pre for i ch e Q tr'
      proof -
        let ?Q' = "\<lambda>d s0. Q (updr s0 (p s0 d))"
        let ?e' = "\<lambda>d s0. e (updr s0 (p s0 d))"
        have Q: "?specs2 ! i = OutSpec2 ch ?e' ?Q'"
          using speci[OF pre(2)] unfolding pre(3) by auto
        show ?thesis
          apply (rule interrupt_sol_c.intros(5)[of i _ _ ?e' ?Q'])
          using pre(2,3,4) Q length p0 by auto
      qed
      subgoal premises pre for i ch e Q d' p' tr'
      proof -
        have "b (updr s0 (p' 0))"
          using pre by auto
        then have "b s0" using pre by auto
        have a: "d' \<le> d s0"
              "p s0 d' = p' d'"
              "WaitBlock d' (\<lambda>t\<in>{0..d'}. updr s0 (p s0 t)) = WaitBlock d' (\<lambda>t\<in>{0..d'}. updr s0 (p' t))"
          using main2[of s0 d' p', OF \<open>b s0\<close> pre(4,6,8,7)] by auto
        let ?Q' = "\<lambda>d s0. Q (updr s0 (p s0 d))"
        let ?e' = "\<lambda>d s0. e (updr s0 (p s0 d))"
        have Q: "?specs2 ! i = OutSpec2 ch ?e' ?Q'"
          using speci[OF pre(2)] unfolding pre(3) by auto
        show ?thesis
          unfolding a(3)[symmetric] a(2)[symmetric]
          apply (rule interrupt_sol_c.intros(6)[of i _ _ ?e' ?Q'])
          using pre(2,3,4,5) a(1,2) Q length rdy_of_comm_spec2_of by auto
      qed
      done
    done
qed

lemma spec_of_interrupt_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "length es = length specs"
    "\<forall>i. i < length es \<longrightarrow> spec_of_es (es ! i) (specs ! i)"
  shows
    "spec_of (Interrupt ode b es)
             (interrupt_sol_c (\<lambda>s t. updr s (p s t)) d (\<lambda>d' s. init (updr s (p s d'))) (map (spec2_of p) specs))"
  apply (rule spec_of_post)
   apply (rule spec_of_interrupt[OF assms(3,4)]) apply auto
  apply (rule entails_trans)
   apply (rule interrupt_c_unique[OF assms(1,2)])
  by (rule entails_triv)

inductive spec2_entails :: "'a comm_spec2 \<Rightarrow> 'a comm_spec2 \<Rightarrow> bool" where
  "(\<And>d v s0. P1 d v s0 \<Longrightarrow>\<^sub>A P2 d v s0) \<Longrightarrow> spec2_entails (InSpec2 ch P1) (InSpec2 ch P2)"
| "(\<And>d s0. Q1 d s0 \<Longrightarrow>\<^sub>A Q2 d s0) \<Longrightarrow> spec2_entails (OutSpec2 ch e Q1) (OutSpec2 ch e Q2)"

inductive_cases spec2_entails_inE: "spec2_entails (InSpec2 ch P1) spec2"
inductive_cases spec2_entails_outE: "spec2_entails (OutSpec2 ch e Q1) spec2"

lemma rdy_of_spec2_entails:
  assumes "\<And>i. i < length specs \<Longrightarrow> spec2_entails (specs ! i) (specs2 ! i)"
  shows "rdy_of_comm_spec2 specs = rdy_of_comm_spec2 specs2"
  sorry

lemma interrupt_sol_mono:
  assumes "\<And>d s0. P d s0 \<Longrightarrow>\<^sub>A P2 d s0"
    and "length specs = length specs2"
    and "\<And>i. i < length specs \<Longrightarrow> spec2_entails (specs ! i) (specs2 ! i)"
  shows "interrupt_sol_c p d P specs s0 \<Longrightarrow>\<^sub>A interrupt_sol_c p d P2 specs2 s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (induct rule: interrupt_sol_c.cases) apply auto
    subgoal for tr' a b
      apply (rule interrupt_sol_c.intros(1))
      using assms(1) unfolding entails_def apply auto
      apply (rule rdy_of_spec2_entails) using assms(3) by auto
    subgoal
      apply (rule interrupt_sol_c.intros(2))
      using assms(1) unfolding entails_def by auto
    subgoal for i ch Q v tr'
      using assms(3)[of i] apply simp
      apply (elim spec2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_sol_c.intros(3)[of i _ _ Q2])
        using assms(2) unfolding entails_def by auto
      done
    subgoal for i ch Q d' v tr' a b
      using assms(3)[of i] apply simp
      apply (elim spec2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_sol_c.intros(4)[of i _ _ Q2])
        using assms(2) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) using assms(3) by auto
      done
    subgoal for i ch e Q tr'
      using assms(3)[of i] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_sol_c.intros(5)[of i _ _ _ Q2])
        using assms(2) unfolding entails_def by auto
      done
    subgoal for i ch e Q d' tr' a b
      using assms(3)[of i] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_sol_c.intros(6)[of i _ _ _ Q2])
        using assms(2) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) using assms(3) by auto
      done
    done
  done

lemma test2:
  "spec_of (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. val s X < 1)
                      [(dh[?]Y, Skip)])
           (interrupt_sol_c (\<lambda>s t. upd s X (val s X + t)) (\<lambda>s. 1 - val s X)
                            (\<lambda>d s. init (upd s X (val s X + d)))
                            [InSpec2 dh (\<lambda>d v s. init (upd (upd s X (val s X + d)) Y v))])"
proof -
  have 1: "paramODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>s. val s X < 1)
                       (\<lambda>s0 t. (rpart s0)(X := val s0 X + t)) (\<lambda>s0. 1 - val s0 X)"
    unfolding paramODEsol_def apply clarify
    subgoal for s
      apply (rule conjI)
      subgoal apply (cases s)
        by (auto simp add: rpart.simps val.simps)
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
  let ?specs = "[InSpec dh Y init]"
  show ?thesis
    apply (rule spec_of_post)
     apply (rule spec_of_interrupt_unique[where specs="?specs"])
        apply (rule 1) apply (rule 2)
      apply auto apply (rule spec_of_es.intros)
     apply (rule spec_of_skip)
    subgoal for s0
      apply (simp only: updr_rpart_simp)
      apply (rule interrupt_sol_mono)
      subgoal by (rule entails_triv)
      subgoal by auto
      subgoal for i
        apply auto apply (intro spec2_entails.intros)
        subgoal for d v s0 apply (simp only: updr_rpart_simp2)
          by (rule entails_triv)
        done
      done
    done
qed

inductive interrupt_solInf_c :: "('a estate \<Rightarrow> real \<Rightarrow> 'a estate) \<Rightarrow> 'a comm_spec2 list \<Rightarrow> 'a assn2" where
  "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow> interrupt_solInf_c p specs s0 s (InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_solInf_c p specs s0 s (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p s0 \<tau>) rdy # InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch e Q \<Longrightarrow> v = e 0 s0 \<Longrightarrow>
   Q 0 s0 s tr \<Longrightarrow> interrupt_solInf_c p specs s0 s (OutBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch e Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d s0 s tr \<Longrightarrow> v = e d s0 \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_solInf_c p specs s0 s (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p s0 \<tau>) rdy # OutBlock ch v # tr)"

definition paramODEsolInf :: "ODE \<Rightarrow> ('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> bool" where
  "paramODEsolInf ode p \<longleftrightarrow>
    (\<forall>s. p s 0 = rpart s \<and> ODEsolInf ode (p s))"

lemma interrupt_inf_c_unique:
  assumes
    "paramODEsolInf ode p"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "interrupt_c ode (\<lambda>_. True) P specs s0 \<Longrightarrow>\<^sub>A
     interrupt_solInf_c (\<lambda>s t. updr s (p s t)) (map (spec2_of p) specs) s0"
proof -
  have main:
    "p s d2 = p2 d2 \<and>
     WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p s t)) = WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p2 t))"
    if cond: "0 < d2" "ODEsol ode p2 d2" "p2 0 = rpart s" for s p2 d2
  proof -
    interpret loc:ll_on_open_it "{-1<..}"
      "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
      apply standard
      using assms(2) by auto
    have s1: "((\<lambda>t. state2vec (p s t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..} UNIV"
      using assms(1) ODEsolInf_old unfolding paramODEsolInf_def solves_ode_def by auto
    have s2: "(loc.flow 0 (state2vec (rpart s))) t = (\<lambda>t. state2vec (p s t)) t" if "t \<in> {0..d2}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s1])
      using that assms(1) unfolding paramODEsolInf_def
      by (auto simp add: state2vec_def)
    have s3: "((\<lambda>t. state2vec (p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d2} UNIV"
      using cond(2) ODEsol_old unfolding ODEsol_def solves_ode_def by auto
    have s4: "loc.flow 0 (state2vec (rpart s)) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s3])
      using cond that by auto
    have s7: "t\<in>{0..d2} \<Longrightarrow> loc.flow 0 (state2vec (rpart s)) t = state2vec (p s t)" for t
      using s2 by auto
    have s8: "t\<in>{0..d2} \<Longrightarrow> p2 t = p s t" for t
      using s7 s4 by (metis vec_state_map1)
    have s9: "p s d2 = p2 d2"
      using s8 that(1) by fastforce
    have s10: "WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p s t)) = WaitBlock d2 (\<lambda>t\<in>{0..d2}. updr s (p2 t))"
      using s7 s8 by fastforce
    show ?thesis using s8 s9 s10 by auto
  qed
  have p0: "p s0 0 = rpart s0"
    using assms(1) unfolding paramODEsolInf_def by auto
  let ?specs2 = "map (spec2_of p) specs"
  have length: "length ?specs2 = length specs"
    by auto
  have speci: "?specs2 ! i = spec2_of p (specs ! i)" if "i < length specs" for i
    using that by auto
  show ?thesis
    unfolding entails_def apply auto
    subgoal for s tr
      apply (auto simp add: interrupt_c.simps)
      subgoal premises pre for i ch var Q v tr'
      proof -
        let ?Q' = "\<lambda>d v s0. Q (updr s0 ((p s0 d)(var := v)))"
        show ?thesis
          apply (rule interrupt_solInf_c.intros(1)[of i _ _ ?Q'])
          using pre length p0 by (auto simp add: updr_rpart_simp)
      qed
      subgoal premises pre for i ch var Q d p2 v tr'
      proof -
        have a: "p s0 d = p2 d"
             "WaitBlock d (\<lambda>t\<in>{0..d}. updr s0 (p s0 t)) = WaitBlock d (\<lambda>t\<in>{0..d}. updr s0 (p2 t))"
          using main[of d p2 s0, OF pre(4,6,7)] by auto
        let ?Q' = "\<lambda>d v s0. Q (updr s0 ((p s0 d)(var := v)))"
        show ?thesis
          unfolding a(2)[symmetric]
          apply (rule interrupt_solInf_c.intros(2)[of i _ _ ?Q'])
          using pre a length rdy_of_comm_spec2_of by auto
      qed
      subgoal premises pre for i ch e Q tr'
      proof -
        let ?Q' = "\<lambda>d s0. Q (updr s0 (p s0 d))"
        let ?e' = "\<lambda>d s0. e (updr s0 (p s0 d))"
        show ?thesis
          apply (rule interrupt_solInf_c.intros(3)[of i _ _ ?e' ?Q'])
          using pre length p0 by auto
      qed
      subgoal premises pre for i ch e Q d p2 tr'
      proof -
        have a: "p s0 d = p2 d"
             "WaitBlock d (\<lambda>t\<in>{0..d}. updr s0 (p s0 t)) = WaitBlock d (\<lambda>t\<in>{0..d}. updr s0 (p2 t))"
          using main[of d p2 s0, OF pre(4,6,7)] by auto
        let ?Q' = "\<lambda>d s0. Q (updr s0 (p s0 d))"
        let ?e' = "\<lambda>d s0. e (updr s0 (p s0 d))"
        show ?thesis
          unfolding a(2)[symmetric] a(1)[symmetric]
          apply (rule interrupt_solInf_c.intros(4)[of i _ _ ?e' ?Q'])
          using pre length a(1) rdy_of_comm_spec2_of by auto
      qed
      done
    done
qed

lemma spec_of_interrupt_inf_unique:
  assumes
    "paramODEsolInf ode p"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "length es = length specs"
    "\<forall>i. i < length es \<longrightarrow> spec_of_es (es ! i) (specs ! i)"
  shows
    "spec_of (Interrupt ode (\<lambda>_. True) es)
             (interrupt_solInf_c (\<lambda>s t. updr s (p s t)) (map (spec2_of p) specs))"
  apply (rule spec_of_post)
   apply (rule spec_of_interrupt[OF assms(3,4)]) apply auto
  apply (rule entails_trans)
   apply (rule interrupt_inf_c_unique[OF assms(1,2)])
  by (rule entails_triv)

lemma interrupt_solInf_mono:
  assumes "length specs = length specs2"
    and "\<And>i. i < length specs \<Longrightarrow> spec2_entails (specs ! i) (specs2 ! i)"
  shows "interrupt_solInf_c p specs s0 \<Longrightarrow>\<^sub>A interrupt_solInf_c p specs2 s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (induct rule: interrupt_solInf_c.cases) apply auto
    subgoal for i ch Q v tr'
      using assms(2)[of i] apply simp
      apply (elim spec2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_solInf_c.intros(1)[of i _ _ Q2])
        using assms(1) unfolding entails_def by auto
      done
    subgoal for i ch Q d' v tr' a b
      using assms(2)[of i] apply simp
      apply (elim spec2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_solInf_c.intros(2)[of i _ _ Q2])
        using assms(1) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) using assms(2) by auto
      done
    subgoal for i ch e Q tr'
      using assms(2)[of i] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_solInf_c.intros(3)[of i _ _ _ Q2])
        using assms(1) unfolding entails_def by auto
      done
    subgoal for i ch E Q d tr' a b
      using assms(2)[of i] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_solInf_c.intros(4)[of i _ _ _ Q2])
        using assms(1) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) using assms(2) by auto
      done
    done
  done

definition disj_assn2 :: "'a assn2 \<Rightarrow> 'a assn2 \<Rightarrow> 'a assn2" (infixr "\<or>\<^sub>a" 35) where
  "(P \<or>\<^sub>a Q) s0 = (\<lambda>s tr. P s0 s tr \<or> Q s0 s tr)"

lemma spec_of_ichoice:
  assumes "spec_of c1 Q1"
    and "spec_of c2 Q2"
  shows "spec_of (IChoice c1 c2) (Q1 \<or>\<^sub>a Q2)"
  unfolding Valid_def spec_of_def
  apply (auto elim!: ichoiceE)
  using assms unfolding spec_of_def Valid_def disj_assn2_def by auto

end
