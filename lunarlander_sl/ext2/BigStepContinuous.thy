theory BigStepContinuous
  imports BigStepSimple
begin

subsection \<open>Preliminary\<close>

text \<open>Parameterized solution to ODE\<close>
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

text \<open>Parameterized solution to ODE, infinite version\<close>
definition paramODEsolInf :: "ODE \<Rightarrow> ('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> bool" where
  "paramODEsolInf ode p \<longleftrightarrow>
    (\<forall>s. p s 0 = rpart s \<and> ODEsolInf ode (p s))"

text \<open>The key result is to show that, for any other solution satisfying
  the ODE, it must be equal to the solution given by d, p.
\<close>
lemma paramODEsol_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "b s" "0 < d2" 
    "ODEsol ode p2 d2"
    "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (updr s (p2 t))"
    "\<not>b (updr s (p2 d2))"
    "p2 0 = rpart s"
  shows
    "d2 = d s \<and> p s (d s) = p2 d2 \<and>
     WaitBlk (d s) (\<lambda>t. updr s (p s t)) = WaitBlk d2 (\<lambda>t. updr s (p2 t))"
proof -
  interpret loc:ll_on_open_it "{-1<..}"
    "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
    apply standard
    using assms(2) by auto
  have s0: "0 < d s"
    using assms(1) unfolding paramODEsol_def using assms(3) by auto
  have s1: "((\<lambda>t. state2vec (p s t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d s} UNIV"
    using paramODEsolD(2)[OF assms(1,3)] ODEsol_old unfolding ODEsol_def solves_ode_def by auto
  have s2: "(loc.flow 0 (state2vec (rpart s))) t = (\<lambda>t. state2vec (p s t)) t" if "t \<in> {0..d s}" for t
    apply (rule loc.maximal_existence_flow(2)[OF s1])
    using that by (auto simp add: state2vec_def paramODEsolD[OF assms(1,3)] paramODEsolD2[OF assms(1)])
  have s3: "((\<lambda>t. state2vec (p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d2} UNIV"
    using assms(5) ODEsol_old unfolding ODEsol_def solves_ode_def by auto
  have s4: "loc.flow 0 (state2vec (rpart s)) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
    apply (rule loc.maximal_existence_flow(2)[OF s3])
    using assms(4,8) that by auto
  have s5: "d s \<le> d2"
  proof (rule ccontr)
    assume 0: "\<not>(d s \<le> d2)"
    from 0 have 1: "(\<lambda>t. state2vec (p s t)) d2 = (\<lambda>t. state2vec (p2 t)) d2"
      using s2[of d2] s4[of d2] assms(4) by auto
    from 1 have "p s d2 = p2 d2"
      by (auto simp add: state2vec_def)
    show False
      using "0" \<open>p s d2 = p2 d2\<close> paramODEsolD(3)[OF assms(1,3)] assms(4,7)
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
      using "0" \<open>p s (d s) = p2 (d s)\<close> paramODEsolD[OF assms(1,3)] assms(3,6)
      by auto
  qed
  have s7: "d s = d2" using s5 s6 by auto
  have s8: "t\<in>{0..d s} \<Longrightarrow> p2 t = p s t" for t
    using s2 s4 s7 by (metis vec_state_map1)
  have s9: "p s (d s) = p2 (d s)"
    using s8 by (simp add: s0 less_eq_real_def)
  have s10: "WaitBlk (d s) (\<lambda>t. updr s (p s t)) = WaitBlk d2 (\<lambda>t. updr s (p2 t))"
    apply (rule ext) apply (rule WaitBlk_eqI) using s7 s8 by auto
  show ?thesis using s7 s9 s10 by auto
qed

lemma paramODEsol_unique2:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "b s" "0 < d2"
    "ODEsol ode p2 d2"
    "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (updr s (p2 t))"
    "p2 0 = rpart s"
  shows
    "d2 \<le> d s \<and> p s d2 = p2 d2 \<and>
     WaitBlk d2 (\<lambda>t. updr s (p s t)) = WaitBlk d2 (\<lambda>t. updr s (p2 t))"
proof -
  interpret loc:ll_on_open_it "{-1<..}"
    "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
    apply standard
    using assms(2) by auto
  have s0: "0 < d s"
    using assms(1) unfolding paramODEsol_def using assms(3) by auto
  have s1: "((\<lambda>t. state2vec (p s t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d s} UNIV"
    using paramODEsolD(2)[OF assms(1,3)] ODEsol_old unfolding ODEsol_def solves_ode_def by auto
  have s2: "(loc.flow 0 (state2vec (rpart s))) t = (\<lambda>t. state2vec (p s t)) t" if "t \<in> {0..d s}" for t
    apply (rule loc.maximal_existence_flow(2)[OF s1])
    using that by (auto simp add: state2vec_def paramODEsolD[OF assms(1,3)] paramODEsolD2[OF assms(1)])
  have s3: "((\<lambda>t. state2vec (p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d2} UNIV"
    using assms(5) ODEsol_old unfolding ODEsol_def solves_ode_def by auto
  have s4: "loc.flow 0 (state2vec (rpart s)) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
    apply (rule loc.maximal_existence_flow(2)[OF s3])
    using assms that by auto
  have s6: "d2 \<le> d s"
  proof (rule ccontr)
    assume 0: "\<not>(d2 \<le> d s)"
    from 0 have 1: "(\<lambda>t. state2vec (p s t)) (d s) = (\<lambda>t. state2vec (p2 t)) (d s)"
      using s2[of "d s"] s4[of "d s"] s0 by auto
    from 1 have "p s (d s) = p2 (d s)"
      by (auto simp add: state2vec_def)
    show False
      using "0" \<open>p s (d s) = p2 (d s)\<close> paramODEsolD[OF assms(1,3)] assms(3,6)
      by auto
  qed
  have s7: "t\<in>{0..d2} \<Longrightarrow> loc.flow 0 (state2vec (rpart s)) t = state2vec (p s t)" for t
    using s2 s6 by auto
  have s8: "t\<in>{0..d2} \<Longrightarrow> p2 t = p s t" for t
    using s7 s4 by (metis vec_state_map1)
  have s9: "p s d2 = p2 d2"
    using s8 assms(4) by fastforce
  have s10: "WaitBlk d2 (\<lambda>t. updr s (p s t)) = WaitBlk d2 (\<lambda>t. updr s (p2 t))"
    apply (rule ext) apply (rule WaitBlk_eqI) using s7 s8 by auto
  show ?thesis using s6 s9 s10 by auto
qed

lemma paramODEsolInf_unique:
  assumes
    "paramODEsolInf ode p"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "0 < d2" "ODEsol ode p2 d2" "p2 0 = rpart s"
  shows
    "p s d2 = p2 d2 \<and>
     WaitBlk d2 (\<lambda>t. updr s (p s t)) = WaitBlk d2 (\<lambda>t. updr s (p2 t))"
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
    using assms(4) ODEsol_old unfolding ODEsol_def solves_ode_def by auto
  have s4: "loc.flow 0 (state2vec (rpart s)) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
    apply (rule loc.maximal_existence_flow(2)[OF s3])
    using assms that by auto
  have s7: "t\<in>{0..d2} \<Longrightarrow> loc.flow 0 (state2vec (rpart s)) t = state2vec (p s t)" for t
    using s2 by auto
  have s8: "t\<in>{0..d2} \<Longrightarrow> p2 t = p s t" for t
    using s7 s4 by (metis vec_state_map1)
  have s9: "p s d2 = p2 d2"
    using s8 assms(3) by fastforce
  have s10: "WaitBlk d2 (\<lambda>t. updr s (p s t)) = WaitBlk d2 (\<lambda>t. updr s (p2 t))"
    apply (rule ext) apply (rule WaitBlk_eqI) using s7 s8 by auto
  show ?thesis using s8 s9 s10 by auto
qed

subsection \<open>Continuous evolution\<close>

inductive ode_c :: "ODE \<Rightarrow> 'a eform \<Rightarrow> 'a assn2 \<Rightarrow> 'a assn2" where
  "\<not>b s0 \<Longrightarrow> P s0 s tr \<Longrightarrow> ode_c ode b P s0 s tr"
| "0 < d \<Longrightarrow> P (updr s0 (p d)) s tr \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   p 0 = rpart s0 \<Longrightarrow>
   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (updr s0 (p t))) \<Longrightarrow>
   \<not>b (updr s0 (p d)) \<Longrightarrow>
   ode_c ode b P s0 s (WaitBlk d (\<lambda>\<tau>. updr s0 (p \<tau>)) ({}, {}) # tr)"

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
   wait_sol_c p d P s0 s (WaitBlk (d s0) (\<lambda>t. p s0 t) ({}, {}) # tr)"
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

lemma ode_c_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "ode_c ode b P s0 \<Longrightarrow>\<^sub>A wait_sol_c (\<lambda>s t. updr s (p s t)) d (\<lambda>d' s. P (updr s (p s d'))) s0"
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
        "WaitBlk (d s0) (\<lambda>t. updr s0 (p s0 t)) = WaitBlk d' (\<lambda>t. updr s0 (p' t))"
        using paramODEsol_unique[OF assms \<open>b s0\<close> pre(2,4,6,7,5)] by auto
      show ?thesis
        unfolding a(3)[symmetric]
        apply (rule wait_sol_c.intros(1))
        using pre(2,3) a(1,2) by auto
    qed
    done
  done

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

subsection \<open>Interrupt\<close>

text \<open>We define the general form of assertion for interrupt

  Each input/output is specified by channel name, communicated function,
  and ensuing assertion.
\<close>
datatype 'a comm_spec =
  InSpec cname var "'a assn2"
| OutSpec cname "'a eexp" "'a assn2"

definition rdy_of_comm_spec :: "'a comm_spec list \<Rightarrow> rdy_info" where
  "rdy_of_comm_spec = rdy_info_of_list (\<lambda>spec.
    case spec of InSpec ch var P \<Rightarrow> ({}, {ch})
               | OutSpec ch e P \<Rightarrow> ({ch}, {}))"

inductive interrupt_c :: "ODE \<Rightarrow> 'a eform \<Rightarrow> 'a assn2 \<Rightarrow> 'a comm_spec list \<Rightarrow> 'a assn2" where
  "\<not>b s0 \<Longrightarrow> P s0 s tr \<Longrightarrow> interrupt_c ode b P specs s0 s tr"
| "0 < d \<Longrightarrow> P (updr s0 (p d)) s tr \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   p 0 = rpart s0 \<Longrightarrow>
   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (updr s0 (p t))) \<Longrightarrow>
   \<not>b (updr s0 (p d)) \<Longrightarrow> rdy = rdy_of_comm_spec specs \<Longrightarrow>
   interrupt_c ode b P specs s0 s (WaitBlk d (\<lambda>\<tau>. updr s0 (p \<tau>)) rdy # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec ch var Q \<Longrightarrow>
   Q (upd s0 var v) s tr \<Longrightarrow> interrupt_c ode b P specs s0 s (InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec ch var Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q (updr s0 ((p d)(var := v))) s tr \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   p 0 = rpart s0 \<Longrightarrow>
   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (updr s0 (p t))) \<Longrightarrow>
   rdy = rdy_of_comm_spec specs \<Longrightarrow>
   interrupt_c ode b P specs s0 s (WaitBlk d (\<lambda>\<tau>. updr s0 (p \<tau>)) rdy # InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec ch e Q \<Longrightarrow>
   Q s0 s tr \<Longrightarrow> interrupt_c ode b P specs s0 s (OutBlock ch (e s0) # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec ch e Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q (updr s0 (p d)) s tr \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   p 0 = rpart s0 \<Longrightarrow>
   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (updr s0 (p t))) \<Longrightarrow>
   rdy = rdy_of_comm_spec specs \<Longrightarrow>
   interrupt_c ode b P specs s0 s (WaitBlk d (\<lambda>\<tau>. updr s0 (p \<tau>)) rdy # OutBlock ch (e (updr s0 (p d))) # tr)"

text \<open>Hoare rules for interrupt\<close>

inductive spec_of_es :: "'a comm \<times> 'a proc \<Rightarrow> 'a comm_spec \<Rightarrow> bool" where
  "spec_of c Q \<Longrightarrow> spec_of_es (ch[?]var, c) (InSpec ch var Q)"
| "spec_of c Q \<Longrightarrow> spec_of_es (ch[!]e, c) (OutSpec ch e Q)"

inductive rel_list :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool" for r where
  "rel_list r [] []"
| "r a b \<Longrightarrow> rel_list r as bs \<Longrightarrow> rel_list r (a # as) (b # bs)"

lemma rel_listD1:
  "rel_list r xs ys \<Longrightarrow> length xs = length ys"
  apply (induct rule: rel_list.induct) by auto

lemma rel_listD2:
  "rel_list r xs ys \<Longrightarrow> i < length xs \<Longrightarrow> r (xs ! i) (ys ! i)"
  apply (induct arbitrary: i rule: rel_list.induct) apply auto
  unfolding less_Suc_eq_0_disj by auto

lemma rel_list_mono:
  assumes "\<And>x y. r x y \<Longrightarrow> r2 x y"
  shows "rel_list r xs ys \<Longrightarrow> rel_list r2 xs ys"
  apply (induct rule: rel_list.induct)
  using assms by (auto intro!: rel_list.intros)

lemma rdy_info_of_list_cong:
  "rel_list (\<lambda>x y. f x = g y) xs ys \<Longrightarrow> rdy_info_of_list f xs = rdy_info_of_list g ys"
  apply (induct xs ys rule: rel_list.induct)
  by (auto simp add: Let_def)

lemma rdy_of_comm_spec_correct:
  assumes "rel_list spec_of_es es specs"
  shows "rdy_of_echoice es = rdy_of_comm_spec specs"
  unfolding rdy_of_echoice_def rdy_of_comm_spec_def
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_mono[OF _ assms])
  apply (elim spec_of_es.cases) by auto

lemma spec_of_interrupt:
  assumes "rel_list spec_of_es es specs"
  shows "spec_of (Interrupt ode b es)
                 (interrupt_c ode b init specs)"
  unfolding Valid_def spec_of_def init_def apply clarify
  apply (auto elim!: interruptE)
  subgoal premises pre for s0 s2 i ch e p2 tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using rel_listD2[OF assms pre(1)] by auto
    then obtain Q where Q: "specs ! i = OutSpec ch e Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(5))
      using rel_listD1[OF assms] pre(1) apply auto[1]
      using Q(1) apply auto[1]
      using pre(3) Q(2) unfolding spec_of_def Valid_def init_def by auto
  qed
  subgoal premises pre for s0 s2 d p i ch e p2 tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using rel_listD2[OF assms pre(5)] by auto
    then obtain Q where Q: "specs ! i = OutSpec ch e Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(6))
      using rel_listD1[OF assms] pre(5) apply auto[1]
      using Q(1) apply auto[1]
      using pre(1) apply auto[1]
      using pre(7) Q(2) unfolding spec_of_def Valid_def init_def apply auto[1]
      using pre assms rdy_of_comm_spec_correct by auto
  qed
  subgoal premises pre for s0 s2 i ch var p2 v tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using rel_listD2[OF assms pre(1)] by auto
    then obtain Q where Q: "specs ! i = InSpec ch var Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(3))
      using rel_listD1[OF assms] pre(1) apply auto[1]
      using Q(1) apply auto[1]
      using pre(3) Q(2) unfolding spec_of_def Valid_def init_def by auto
  qed
  subgoal premises pre for s0 s2 d p i ch var p2 v tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using rel_listD2[OF assms pre(5)] by auto
    then obtain Q where Q: "specs ! i = InSpec ch var Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(4))
      using rel_listD1[OF assms] pre(5) apply auto[1]
      using Q(1) apply auto[1]
      using pre(1) apply auto[1]
      using pre(7) Q(2) unfolding spec_of_def Valid_def init_def apply auto[1]
      using pre assms rdy_of_comm_spec_correct by auto
  qed
  subgoal premises pre for s0
    apply (rule interrupt_c.intros(1))
    using pre by auto
  subgoal premises pre for s0 d p
    apply (rule interrupt_c.intros(2))
    using pre assms rdy_of_comm_spec_correct by auto
  done

text \<open>Unique solution rule for interrupt\<close>

datatype 'a comm_spec2 =
  InSpec2 cname "real \<Rightarrow> real \<Rightarrow> 'a assn2"
| OutSpec2 cname "real \<Rightarrow> 'a eexp" "real \<Rightarrow> 'a assn2"

fun spec2_of :: "('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> 'a comm_spec \<Rightarrow> 'a comm_spec2" where
  "spec2_of p (InSpec ch var Q) = InSpec2 ch (\<lambda>d v s0. Q (updr s0 ((p s0 d)(var := v))))"
| "spec2_of p (OutSpec ch e Q) = OutSpec2 ch (\<lambda>d s0. e (updr s0 (p s0 d))) (\<lambda>d s0. Q (updr s0 (p s0 d)))"

definition rdy_of_comm_spec2 :: "'a comm_spec2 list \<Rightarrow> rdy_info" where
  "rdy_of_comm_spec2 = rdy_info_of_list (\<lambda>spec2.
    case spec2 of InSpec2 ch P \<Rightarrow> ({}, {ch})
                | OutSpec2 ch e P \<Rightarrow> ({ch}, {}))"

lemma rel_list_map:
  assumes "\<And>x. r x (f x)"
  shows "rel_list r xs (map f xs)"
  apply (induct xs)
  using assms by (auto intro: rel_list.intros)

lemma rdy_of_comm_spec2_of:
  "rdy_of_comm_spec specs = rdy_of_comm_spec2 (map (spec2_of p) specs)"
  unfolding rdy_of_comm_spec_def rdy_of_comm_spec2_def
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_map) subgoal for spec
    apply (cases spec) by auto
  done

inductive interrupt_sol_c :: "('a estate \<Rightarrow> real \<Rightarrow> 'a estate) \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow>
  'a comm_spec2 list \<Rightarrow> 'a assn2" where
  "d s0 > 0 \<Longrightarrow> P (d s0) s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s (WaitBlk (d s0) (\<lambda>\<tau>. p s0 \<tau>) rdy # tr)"
| "\<not>d s0 > 0 \<Longrightarrow> P 0 s0 s tr \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s tr"
| "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s (InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   0 < d' \<Longrightarrow> d' \<le> d s0 \<Longrightarrow> Q d' v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s (WaitBlk d' (\<lambda>\<tau>. p s0 \<tau>) rdy # InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch e Q \<Longrightarrow> v = e 0 s0 \<Longrightarrow>
   Q 0 s0 s tr \<Longrightarrow> interrupt_sol_c p d P specs s0 s (OutBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch e Q \<Longrightarrow>
   0 < d' \<Longrightarrow> d' \<le> d s0 \<Longrightarrow> Q d' s0 s tr \<Longrightarrow> v = e d' s0 \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_sol_c p d P specs s0 s (WaitBlk d' (\<lambda>\<tau>. p s0 \<tau>) rdy # OutBlock ch v # tr)"

lemma interrupt_c_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "interrupt_c ode b P specs s0 \<Longrightarrow>\<^sub>A
     interrupt_sol_c (\<lambda>s t. updr s (p s t)) d (\<lambda>d' s. P (updr s (p s d'))) (map (spec2_of p) specs) s0"
proof -
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
              "WaitBlk (d s0) (\<lambda>t. updr s0 (p s0 t)) = WaitBlk d' (\<lambda>t. updr s0 (p' t))"
          using paramODEsol_unique[OF assms \<open>b s0\<close> pre(2,4,6,7,5)] by auto
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
          using pre Q length p0 by (auto simp add: updr_rpart_simp1)
      qed
      subgoal premises pre for i ch var Q d' p' v tr'
      proof -
        have "b (updr s0 (p' 0))"
          using pre by auto
        then have "b s0" using pre by auto
        have a: "d' \<le> d s0"
              "p s0 d' = p' d'"
              "WaitBlk d' (\<lambda>t. updr s0 (p s0 t)) = WaitBlk d' (\<lambda>t. updr s0 (p' t))"
          using paramODEsol_unique2[OF assms \<open>b s0\<close> pre(4,6,8,7)] by auto
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
              "WaitBlk d' (\<lambda>t. updr s0 (p s0 t)) = WaitBlk d' (\<lambda>t. updr s0 (p' t))"
          using paramODEsol_unique2[OF assms \<open>b s0\<close> pre(4,6,8,7)] by auto
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
    "rel_list spec_of_es es specs"
  shows
    "spec_of (Interrupt ode b es)
             (interrupt_sol_c (\<lambda>s t. updr s (p s t)) d (\<lambda>d' s. init (updr s (p s d'))) (map (spec2_of p) specs))"
  apply (rule spec_of_post)
   apply (rule spec_of_interrupt[OF assms(3)]) apply auto
  apply (rule entails_trans)
   apply (rule interrupt_c_unique[OF assms(1,2)])
  by (rule entails_triv)

inductive spec2_entails :: "'a comm_spec2 \<Rightarrow> 'a comm_spec2 \<Rightarrow> bool" where
  "(\<And>d v s0. P1 d v s0 \<Longrightarrow>\<^sub>A P2 d v s0) \<Longrightarrow> spec2_entails (InSpec2 ch P1) (InSpec2 ch P2)"
| "(\<And>d s0. Q1 d s0 \<Longrightarrow>\<^sub>A Q2 d s0) \<Longrightarrow> spec2_entails (OutSpec2 ch e Q1) (OutSpec2 ch e Q2)"

inductive_cases spec2_entails_inE: "spec2_entails (InSpec2 ch P1) spec2"
inductive_cases spec2_entails_outE: "spec2_entails (OutSpec2 ch e Q1) spec2"

lemma rdy_of_spec2_entails:
  assumes "rel_list spec2_entails specs specs2"
  shows "rdy_of_comm_spec2 specs = rdy_of_comm_spec2 specs2"
  unfolding rdy_of_comm_spec2_def
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_mono[OF _ assms])
  apply (elim spec2_entails.cases) by auto

lemma interrupt_sol_mono:
  assumes "\<And>d s0. P d s0 \<Longrightarrow>\<^sub>A P2 d s0"
    and "rel_list spec2_entails specs specs2"
  shows "interrupt_sol_c p d P specs s0 \<Longrightarrow>\<^sub>A interrupt_sol_c p d P2 specs2 s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (induct rule: interrupt_sol_c.cases) apply auto
    subgoal for tr' a b
      apply (rule interrupt_sol_c.intros(1))
      using assms(1) unfolding entails_def apply auto
      apply (rule rdy_of_spec2_entails) using assms(2) by auto
    subgoal
      apply (rule interrupt_sol_c.intros(2))
      using assms(1) unfolding entails_def by auto
    subgoal for i ch Q v tr'
      using rel_listD2[OF assms(2), of i] rel_listD1[OF assms(2)] apply simp
      apply (elim spec2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_sol_c.intros(3)[of i _ _ Q2])
        using assms(2) unfolding entails_def by auto
      done
    subgoal for i ch Q d' v tr' a b
      using rel_listD2[OF assms(2), of i] rel_listD1[OF assms(2)] apply simp
      apply (elim spec2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_sol_c.intros(4)[of i _ _ Q2])
        using assms(2) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) by auto
      done
    subgoal for i ch e Q tr'
      using rel_listD2[OF assms(2), of i] rel_listD1[OF assms(2)] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_sol_c.intros(5)[of i _ _ _ Q2])
        using assms(2) unfolding entails_def by auto
      done
    subgoal for i ch e Q d' tr' a b
      using rel_listD2[OF assms(2), of i] rel_listD1[OF assms(2)] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_sol_c.intros(6)[of i _ _ _ Q2])
        using assms(2) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) by auto
      done
    done
  done

inductive interrupt_solInf_c :: "('a estate \<Rightarrow> real \<Rightarrow> 'a estate) \<Rightarrow> 'a comm_spec2 list \<Rightarrow> 'a assn2" where
  "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow> interrupt_solInf_c p specs s0 s (InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_solInf_c p specs s0 s (WaitBlk d (\<lambda>\<tau>. p s0 \<tau>) rdy # InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch e Q \<Longrightarrow> v = e 0 s0 \<Longrightarrow>
   Q 0 s0 s tr \<Longrightarrow> interrupt_solInf_c p specs s0 s (OutBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch e Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d s0 s tr \<Longrightarrow> v = e d s0 \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow>
   interrupt_solInf_c p specs s0 s (WaitBlk d (\<lambda>\<tau>. p s0 \<tau>) rdy # OutBlock ch v # tr)"

lemma interrupt_inf_c_unique:
  assumes
    "paramODEsolInf ode p"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "interrupt_c ode (\<lambda>_. True) P specs s0 \<Longrightarrow>\<^sub>A
     interrupt_solInf_c (\<lambda>s t. updr s (p s t)) (map (spec2_of p) specs) s0"
proof -
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
          using pre length p0 by (auto simp add: updr_rpart_simp1)
      qed
      subgoal premises pre for i ch var Q d p2 v tr'
      proof -
        have a: "p s0 d = p2 d"
             "WaitBlk d (\<lambda>t. updr s0 (p s0 t)) = WaitBlk d (\<lambda>t. updr s0 (p2 t))"
          using paramODEsolInf_unique[OF assms pre(4,6,7)] by auto
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
             "WaitBlk d (\<lambda>t. updr s0 (p s0 t)) = WaitBlk d (\<lambda>t. updr s0 (p2 t))"
          using paramODEsolInf_unique[OF assms pre(4,6,7)] by auto
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
    "rel_list spec_of_es es specs"
  shows
    "spec_of (Interrupt ode (\<lambda>_. True) es)
             (interrupt_solInf_c (\<lambda>s t. updr s (p s t)) (map (spec2_of p) specs))"
  apply (rule spec_of_post)
   apply (rule spec_of_interrupt[OF assms(3)]) apply auto
  apply (rule entails_trans)
   apply (rule interrupt_inf_c_unique[OF assms(1,2)])
  by (rule entails_triv)

lemma interrupt_solInf_mono:
  assumes "rel_list spec2_entails specs specs2"
  shows "interrupt_solInf_c p specs s0 \<Longrightarrow>\<^sub>A interrupt_solInf_c p specs2 s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (induct rule: interrupt_solInf_c.cases) apply auto
    subgoal for i ch Q v tr'
      using rel_listD2[OF assms, of i] rel_listD1[OF assms] apply simp
      apply (elim spec2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_solInf_c.intros(1)[of i _ _ Q2])
        using assms(1) unfolding entails_def by auto
      done
    subgoal for i ch Q d' v tr' a b
      using rel_listD2[OF assms, of i] rel_listD1[OF assms] apply simp
      apply (elim spec2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_solInf_c.intros(2)[of i _ _ Q2])
        using assms(1) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) by auto
      done
    subgoal for i ch e Q tr'
      using rel_listD2[OF assms, of i] rel_listD1[OF assms] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_solInf_c.intros(3)[of i _ _ _ Q2])
        using assms(1) unfolding entails_def by auto
      done
    subgoal for i ch E Q d tr' a b
      using rel_listD2[OF assms, of i] rel_listD1[OF assms] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_solInf_c.intros(4)[of i _ _ _ Q2])
        using assms(1) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) by auto
      done
    done
  done

subsection \<open>More definition of paths\<close>

text \<open>Mapping from path on a single state to path on general states\<close>
definition single_path :: "pname \<Rightarrow> ('a estate \<Rightarrow> real \<Rightarrow> 'a estate) \<Rightarrow> 'a gstate \<Rightarrow> real \<Rightarrow> 'a gstate" where
  "single_path pn p gs t = gs (pn \<mapsto> p (the (gs pn)) t)"

lemma single_path_State:
  "single_path pn p (State pn s) t = State pn (p s t)"
  unfolding single_path_def
  by (auto simp add: State_def)

text \<open>Merging two paths\<close>
definition restrict_state :: "pname set \<Rightarrow> 'a gstate \<Rightarrow> 'a gstate" where
  "restrict_state pns gs = (\<lambda>pn. if pn \<in> pns then gs pn else None)"

definition merge_path :: "pname set \<Rightarrow> pname set \<Rightarrow>
                          ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow>
                          ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate)" where
  "merge_path pns1 pns2 p1 p2 = (\<lambda>gs t.
     merge_state (p1 (restrict_state pns1 gs) t) (p2 (restrict_state pns2 gs) t))"

fun delay_path :: "real \<Rightarrow> ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate)" where
  "delay_path d p gs d' = p gs (d' + d)"

lemma restrict_state_eval1:
  assumes "proc_set gs1 = pns1"
  shows "restrict_state pns1 (merge_state gs1 gs2) = gs1"
  apply (rule ext) subgoal for pn
    unfolding restrict_state_def apply auto
     apply (subst merge_state_eval1) using assms apply auto
    unfolding proc_set_def by auto
  done

lemma restrict_state_eval2:
  assumes "proc_set gs1 = pns1"
    and "proc_set gs2 = pns2"
    and "pns1 \<inter> pns2 = {}"
  shows "restrict_state pns2 (merge_state gs1 gs2) = gs2"
  apply (rule ext) subgoal for pn
    unfolding restrict_state_def apply auto
     apply (subst merge_state_eval2) using assms apply auto
    unfolding proc_set_def by auto
  done

lemma merge_path_eval:
  assumes "proc_set gs1 = pns1"
    and "proc_set gs2 = pns2"
    and "pns1 \<inter> pns2 = {}"
  shows
  "merge_path pns1 pns2 p1 p2 (merge_state gs1 gs2) t = merge_state (p1 gs1 t) (p2 gs2 t)"
  unfolding merge_path_def
  by (auto simp add: restrict_state_eval1 restrict_state_eval2 assms)

fun id_path :: "'a gstate \<Rightarrow> real \<Rightarrow> 'a gstate" where
  "id_path gs t = gs"

fun single_val :: "pname \<Rightarrow> 'a eexp \<Rightarrow> 'a gstate \<Rightarrow> real" where
  "single_val pn e gs = e (the (gs pn))"

subsection \<open>Interrupt specification for global states\<close>

datatype 'a comm_specg2 =
  InSpecg2 cname "real \<Rightarrow> real \<Rightarrow> 'a gassn2"
| OutSpecg2 cname "real \<Rightarrow> 'a gstate \<Rightarrow> real" "real \<Rightarrow> 'a gassn2"

text \<open>Mapping from specification on single state to specification
  on general states.
\<close>
fun comm_spec_gassn_of :: "pname \<Rightarrow> 'a comm_spec2 \<Rightarrow> 'a comm_specg2" where
  "comm_spec_gassn_of pn (InSpec2 ch Q) = InSpecg2 ch (\<lambda>d v. single_assn pn (Q d v))"
| "comm_spec_gassn_of pn (OutSpec2 ch e Q) = OutSpecg2 ch (\<lambda>d. single_val pn (e d)) (\<lambda>d. single_assn pn (Q d))"

definition rdy_of_comm_specg2 :: "'a comm_specg2 list \<Rightarrow> rdy_info" where
  "rdy_of_comm_specg2 = rdy_info_of_list (\<lambda>specg.
     case specg of InSpecg2 ch P \<Rightarrow> ({}, {ch})
                 | OutSpecg2 ch e P \<Rightarrow> ({ch}, {}))"

lemma rdy_of_comm_spec_gassn_of:
  "rdy_of_comm_spec2 specs = rdy_of_comm_specg2 (map (comm_spec_gassn_of pn) specs)"
  unfolding rdy_of_comm_spec2_def rdy_of_comm_specg2_def
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_map)
  subgoal for spec2 apply (cases spec2) by auto
  done

inductive interrupt_solInf_cg :: "('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> 'a comm_specg2 list \<Rightarrow> 'a gassn2" where
  "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   Q 0 v gs0 gs tr \<Longrightarrow> interrupt_solInf_cg p specs gs0 gs (InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d v gs0 gs tr \<Longrightarrow> p' = (\<lambda>\<tau>. p gs0 \<tau>) \<Longrightarrow>
   rdy = rdy_of_comm_specg2 specs \<Longrightarrow>
   interrupt_solInf_cg p specs gs0 gs (WaitBlkP d p' rdy # InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch e Q \<Longrightarrow>
   v = e 0 gs0 \<Longrightarrow>
   Q 0 gs0 gs tr \<Longrightarrow> interrupt_solInf_cg p specs gs0 gs (OutBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch e Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d gs0 gs tr \<Longrightarrow> p' = (\<lambda>\<tau>. p gs0 \<tau>) \<Longrightarrow>
   v = e d gs0 \<Longrightarrow>
   rdy = rdy_of_comm_specg2 specs \<Longrightarrow>
   interrupt_solInf_cg p specs gs0 gs (WaitBlkP d p' rdy # OutBlockP ch v # tr)"

lemma single_assn_interrupt_solInf:
  "single_assn pn (interrupt_solInf_c p specs) =
   interrupt_solInf_cg (single_path pn p) (map (comm_spec_gassn_of pn) specs)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0' s' tr'
        apply (elim interrupt_solInf_c.cases) apply auto
        subgoal for i ch Q v tr''
          apply (rule interrupt_solInf_cg.intros(1)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch Q d v tr'' a b
          apply (rule interrupt_solInf_cg.intros(2)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          unfolding single_path_State
          using pre rdy_of_comm_spec_gassn_of by (auto intro: single_assn.intros)
        subgoal for i ch e Q tr''
          apply (rule interrupt_solInf_cg.intros(3)[of i _ _ "(\<lambda>d. single_val pn (e d))" "(\<lambda>d. single_assn pn (Q d))" ])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch e Q d tr'' a b
          apply (rule interrupt_solInf_cg.intros(4)[of i _ _ "(\<lambda>d. single_val pn (e d))" "(\<lambda>d. single_assn pn (Q d))"])
          unfolding single_path_State
          using pre rdy_of_comm_spec_gassn_of by (auto intro: single_assn.intros)
        done
      done
    subgoal apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for i ch Q v tr'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0' s' tr''
          apply (subst ptrace_of.simps[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(1)[of i _ _ Q']) by auto
        done
      subgoal for i ch Q d v tr' a b
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          unfolding single_path_State
          apply (subst ptrace_of.simps(2)[symmetric])
          apply (subst ptrace_of_simp3[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(2)[of i _ _ Q']) apply auto
          unfolding rdy_of_comm_spec_gassn_of[symmetric] by auto
        done
      subgoal for i ch e Q tr'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for e' Q' s0'' s' tr''
          apply (subst ptrace_of.simps[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(3)[of i _ _ _ Q']) by auto
        done
      subgoal for i ch e Q d tr' a b
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for e' Q' s0'' s' tr''
          unfolding single_path_State
          apply (subst ptrace_of.simps[symmetric])
          apply (subst ptrace_of_simp3[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(4)[of i _ _ _ Q']) apply auto
          unfolding rdy_of_comm_spec_gassn_of[symmetric] by auto
        done
      done
    done
  done

fun spec_wait_of :: "real \<Rightarrow> ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> 'a comm_specg2 \<Rightarrow> 'a comm_specg2" where
  "spec_wait_of d p (InSpecg2 ch P) = InSpecg2 ch (\<lambda>d' v. P (d + d') v)"
| "spec_wait_of d p (OutSpecg2 ch e P) = OutSpecg2 ch (\<lambda>d' gs. e (d + d') gs) (\<lambda>d'. P (d + d'))"

inductive wait_sol_cg :: "('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> pname \<Rightarrow> 'a eexp \<Rightarrow>
                          (real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" where
  "e (the (gs0 pn)) > 0 \<Longrightarrow> d = e (the (gs0 pn)) \<Longrightarrow> p' = (\<lambda>t. p gs0 t) \<Longrightarrow>
   P d gs0 gs tr \<Longrightarrow> rdy = ({}, {}) \<Longrightarrow>
   wait_sol_cg p pn e P gs0 gs (WaitBlkP d p' rdy # tr)"
| "\<not>e (the (gs0 pn)) > 0 \<Longrightarrow> P 0 gs0 gs tr \<Longrightarrow> wait_sol_cg p pn e P gs0 gs tr"

lemma wait_sol_cg_mono:
  assumes "\<And>d s0. P1 d s0 \<Longrightarrow>\<^sub>g P2 d s0"
  shows "wait_sol_cg p pn e P1 s0 \<Longrightarrow>\<^sub>g wait_sol_cg p pn e P2 s0"
  apply (auto simp add: entails_g_def)
  subgoal for s tr
    apply (elim wait_sol_cg.cases) apply auto
    subgoal apply (rule wait_sol_cg.intros)
      using assms unfolding entails_g_def by auto
    subgoal apply (rule wait_sol_cg.intros)
      using assms unfolding entails_g_def by auto
    done
  done

lemma compat_rdy_empty [simp]:
  "compat_rdy rdy ({}, {})"
  apply (cases rdy) by auto

fun ch_of_specg2 :: "'a comm_specg2 \<Rightarrow> cname" where
  "ch_of_specg2 (InSpecg2 ch P) = ch"
| "ch_of_specg2 (OutSpecg2 ch e P) = ch"

lemma merge_rdy_simp1:
  assumes "\<And>i. i < length specs \<Longrightarrow> ch_of_specg2 (specs ! i) \<in> chs"
  shows "merge_rdy chs (rdy_of_comm_specg2 specs) ({}, {}) = ({}, {})"
  sorry

lemma rdy_of_spec_wait_of [simp]:
  "rdy_of_comm_specg2 (map (spec_wait_of d p) specs) = rdy_of_comm_specg2 specs"
  unfolding rdy_of_comm_specg2_def apply (rule sym)
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_map)
  subgoal for specg2 apply (cases specg2) by auto
  done

subsection \<open>Synchronization rules for interrupt\<close>

lemma sync_gassn_interrupt_solInf_wait:
  assumes "pn2 \<in> pns2"
    and "pns1 \<inter> pns2 = {}"
    and "\<And>i. i < length specs \<Longrightarrow> ch_of_specg2 (specs ! i) \<in> chs"
  shows
  "sync_gassn chs pns1 pns2 (interrupt_solInf_cg p specs) (wait_cg pn2 e Q) s0 \<Longrightarrow>\<^sub>g
   wait_sol_cg (merge_path pns1 pns2 p id_path) pn2 e
    (\<lambda>d. sync_gassn chs pns1 pns2 (interrupt_solInf_cg (delay_path d p) (map (spec_wait_of d p) specs)) Q) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for i ch Q' v tr'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2)
          using assms(3)[of i] by auto
        subgoal
          apply (rule wait_sol_cg.intros(2))
          apply (subst merge_state_eval2)
          using assms apply auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(1)[of i _ _ Q'])
          by auto
        done
      subgoal for i ch Q' d' v tr' a b
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (cases rule: linorder_cases[of d' "e (the (s12 pn2))"])
          subgoal
            apply (elim combine_blocks_waitE3) apply auto
            apply (elim combine_blocks_pairE2)
            using assms(3)[of i] by auto
          subgoal apply auto
            apply (elim combine_blocks_waitE2) apply auto
            subgoal for tr'''
              apply (rule wait_sol_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_path_eval)
                using assms by auto
              apply (rule sync_gassn.intros) apply auto
              apply (rule interrupt_solInf_cg.intros(1)[of i _ _ "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
              apply auto apply (rule merge_rdy_simp1) using assms(3) by auto
            done
          subgoal
            apply (elim combine_blocks_waitE4) apply auto
            subgoal for tr'''
              apply (rule wait_sol_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_path_eval)
                using assms by auto
              apply (rule sync_gassn.intros) apply auto
              apply (rule interrupt_solInf_cg.intros(2)[of i _ _ "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
              apply auto apply (rule merge_rdy_simp1) using assms(3) by auto
            done
          done
        subgoal
          apply (rule wait_sol_cg.intros(2))
          subgoal apply (subst merge_state_eval2)
            using assms(1,2) by auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(2)[of i _ _ Q'])
          by auto
        done
      subgoal for i ch e Q' tr'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2)
          using assms(3)[of i] by auto
        subgoal
          apply (rule wait_sol_cg.intros(2))
          apply (subst merge_state_eval2)
          using assms apply auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(3)[of i _ _ e Q'])
          by auto
        done
      subgoal for i ch e' Q' d' tr' a b
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (cases rule: linorder_cases[of d' "e (the (s12 pn2))"])
          subgoal
            apply (elim combine_blocks_waitE3) apply auto
            apply (elim combine_blocks_pairE2)
            using assms(3)[of i] by auto
          subgoal apply auto
            apply (elim combine_blocks_waitE2) apply auto
            subgoal for tr'''
              apply (rule wait_sol_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_path_eval)
                using assms by auto
              apply (rule sync_gassn.intros) apply auto
              apply (rule interrupt_solInf_cg.intros(3)[of i _ _ "\<lambda>d'. e' (e (the (s12 pn2)) + d')"
                                                                 "\<lambda>d'. Q' (e (the (s12 pn2)) + d')"])
              apply auto apply (rule merge_rdy_simp1) using assms(3) by auto
            done
          subgoal
            apply (elim combine_blocks_waitE4) apply auto
            subgoal for tr'''
              apply (rule wait_sol_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_path_eval)
                using assms by auto
              apply (rule sync_gassn.intros) apply auto
              apply (rule interrupt_solInf_cg.intros(4)[of i _ _ "\<lambda>d'. e' (e (the (s12 pn2)) + d')"
                                                                 "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
              apply auto apply (rule merge_rdy_simp1) using assms(3) by auto
            done
          done
        subgoal
          apply (rule wait_sol_cg.intros(2))
          subgoal apply (subst merge_state_eval2)
            using assms(1,2) by auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(4)[of i _ _ e' Q'])
          by auto
        done
      done
    done
  done

lemma not_compat_rdy_comm_specg2:
  assumes "i < length specs"
    and "specs ! i = InSpecg2 ch P"
  shows
    "\<not> compat_rdy (rdy_of_comm_specg2 specs) ({ch}, {})"
  sorry

text \<open>Synchronization between interrupt and synchronized output
  Assume there is a corresponding input in the interrupt. Then
  the communication happens immediately.
\<close>
lemma sync_gassn_interrupt_solInf_out:
  assumes "pn2 \<in> pns2"
    and "pns1 \<inter> pns2 = {}"
    and "\<And>i. i < length specs \<Longrightarrow> ch_of_specg2 (specs ! i) \<in> chs"
    and "\<And>i j. i < length specs \<Longrightarrow> j < length specs \<Longrightarrow> i \<noteq> j \<Longrightarrow>
               ch_of_specg2 (specs ! i) \<noteq> ch_of_specg2 (specs ! j)"
    and "i < length specs"
    and "specs ! i = InSpecg2 ch P"
  shows
  "sync_gassn chs pns1 pns2 (interrupt_solInf_cg p specs)
                            (wait_out_cg pn2 ch e Q) s0 \<Longrightarrow>\<^sub>g
   sync_gassn chs pns1 pns2 (P 0 (e (the (s0 pn2)))) (Q 0) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for i' ch' Q' v tr'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr''
          apply (cases "i = i'")
          subgoal using assms(5,6) apply auto
            apply (elim combine_blocks_pairE)
            using assms(3) apply fastforce
            using assms(3) apply fastforce
            apply (rule sync_gassn.intros)
            using assms by (auto simp add: assms merge_state_eval2)
          subgoal
            apply (elim combine_blocks_pairE)
            using assms(3) apply fastforce
            apply (metis assms(3,5,6) ch_of_specg2.simps(1))
            by (metis assms(4,5,6) ch_of_specg2.simps(1))
          done
        subgoal for d tr''
          apply (elim combine_blocks_pairE2)
          using assms(3) by fastforce
        done
      subgoal for i ch' Q' d v tr' a b
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2')
          by (metis assms(3,5,6) ch_of_specg2.simps(1))
        subgoal for d' tr''
          apply (elim combine_blocks_waitE1)
          apply (rule not_compat_rdy_comm_specg2) using assms(5,6) by auto
        done
      subgoal for i ch' e' Q' tr'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE)
          using assms(3) apply fastforce
           apply (metis assms(3,5,6) ch_of_specg2.simps(1))
          by auto
        subgoal for d' tr''
          apply (elim combine_blocks_pairE2)
          using assms(3) by fastforce
        done
      subgoal for i ch' e' Q' d tr' a b
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2')
          by (metis assms(3,5,6) ch_of_specg2.simps(1))
        subgoal for d' tr''
          apply (elim combine_blocks_waitE1)
          apply (rule not_compat_rdy_comm_specg2) using assms(5,6) by auto
        done
      done
    done
  done

subsection \<open>Invariant assertions\<close>

text \<open>Basic assertion for invariants: wait for the specified amount of time,
  while all states in the path satisfy the given invariant, then the remaining
  trace satisfy the following assertion.
\<close>
inductive wait_inv_cg :: "('a gstate \<Rightarrow> bool) \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2" where
  "d > 0 \<Longrightarrow> rdy = ({}, {}) \<Longrightarrow> \<forall>t\<in>{0..d}. I (p t) \<Longrightarrow> P gs0 gs tr \<Longrightarrow>
   wait_inv_cg I P gs0 gs (WaitBlkP d (\<lambda>t. p t) rdy # tr)"

lemma wait_inv_cg_state:
  "wait_inv_cg I P (updg s0 pn var x) \<Longrightarrow>\<^sub>g wait_inv_cg I (\<lambda>s. P (updg s pn var x)) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim wait_inv_cg.cases) apply auto
    subgoal for p tr'
      apply (rule wait_inv_cg.intros) by auto
    done
  done

lemma wait_inv_cgI:
  assumes "e (the (gs0 pn)) = d"
    and "d > 0"
    and "\<forall>t\<in>{0..d}. I (p gs0 t)"
  shows "wait_sol_cg p pn e P gs0 \<Longrightarrow>\<^sub>g wait_inv_cg I (P d) gs0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim wait_sol_cg.cases) apply auto
    using assms by (auto intro: wait_inv_cg.intros)
  done

lemma wait_inv_cg_mono:
  assumes "P1 s0 \<Longrightarrow>\<^sub>g P2 s0"
  shows "wait_inv_cg I P1 s0 \<Longrightarrow>\<^sub>g wait_inv_cg I P2 s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim wait_inv_cg.cases) apply auto
    apply (rule wait_inv_cg.intros) apply auto
    using assms unfolding entails_g_def by auto
  done

lemma merge_restrict:
  assumes "proc_set s = pns1 \<union> pns2"
    and "pns1 \<inter> pns2 = {}"
  shows "merge_state (restrict_state pns1 s) (restrict_state pns2 s) = s"
  unfolding merge_state_def restrict_state_def
  apply (rule ext) apply auto
  using assms(1,2) unfolding proc_set_def apply auto
  subgoal for p apply (cases "s p") by auto
  subgoal for p apply (cases "s p") by auto
  done

lemma proc_set_restrict_state:
  assumes "pns1 \<subseteq> proc_set s"
  shows "proc_set (restrict_state pns1 s) = pns1"
  using assms unfolding restrict_state_def proc_set_def by auto

lemma merge_state_elim:
  assumes "proc_set s = pns1 \<union> pns2"
    and "pns1 \<inter> pns2 = {}"
    and "\<And>s1 s2. s = merge_state s1 s2 \<Longrightarrow> proc_set s1 = pns1 \<Longrightarrow> proc_set s2 = pns2 \<Longrightarrow> P"
  shows P
  apply (rule assms(3)[of "restrict_state pns1 s" "restrict_state pns2 s"])
  by (auto simp add: merge_restrict proc_set_restrict_state assms)  

lemma merge_state_updg_left:
  assumes "pn \<in> proc_set s1"
  shows "merge_state (updg s1 pn v e) s2 = updg (merge_state s1 s2) pn v e"
  apply (rule ext)
  using assms by (auto simp add: proc_set_def merge_state_def updg_def)

lemma valg_merge_state_left:
  assumes "pn \<in> proc_set s1"
  shows "valg (merge_state s1 s2) pn v = valg s1 pn v"
  using assms by (auto simp add: proc_set_def merge_state_def valg_def)

end
