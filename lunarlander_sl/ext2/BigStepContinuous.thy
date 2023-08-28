theory BigStepContinuous
  imports BigStepSequential
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

lemma ode_c_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "ode_c ode b P s0 \<Longrightarrow>\<^sub>A wait_c (\<lambda>s0 t s. s = updr s0 (p s0 t)) d (\<lambda>d' s. P (updr s (p s d'))) s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (auto simp add: ode_c.simps)
    subgoal
      apply (rule wait_c.intros)
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
        apply (rule wait_c.intros(1))
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
             (wait_c (\<lambda>s0 t s. s = updr s0 (p s0 t)) d (\<lambda>d' s. init (updr s (p s d'))))"
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
                 (wait_c (\<lambda>s0 t s. s = updr s0 (p s0 t)) d (\<lambda>d' s. Q (updr s (p s d'))))"
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

lemma rdy_of_comm_spec_correct:
  assumes "rel_list spec_of_es es specs"
  shows "rdy_of_echoice es = rdy_of_comm_spec specs"
  unfolding rdy_of_echoice_def rdy_of_comm_spec_def
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_mono[OF _ assms])
  apply (elim spec_of_es.cases) by auto

lemma spec_of_interrupt:
  assumes "rel_list spec_of_es es specs"
    and "spec_of pr P"
  shows "spec_of (Interrupt ode b es pr)
                 (interrupt_c ode b P specs)"
  unfolding Valid_def spec_of_def init_def apply clarify
  apply (auto elim!: interruptE)
  subgoal premises pre for s0 s2 i ch e p2 tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using rel_listD2[OF assms(1) pre(1)] by auto
    then obtain Q where Q: "specs ! i = OutSpec ch e Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(5))
      using rel_listD1[OF assms(1)] pre(1) apply auto[1]
      using Q(1) apply auto[1]
      using pre(3) Q(2) unfolding spec_of_def Valid_def init_def by auto
  qed
  subgoal premises pre for s0 s2 d p i ch e p2 tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using rel_listD2[OF assms(1) pre(5)] by auto
    then obtain Q where Q: "specs ! i = OutSpec ch e Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(6))
      using rel_listD1[OF assms(1)] pre(5) apply auto[1]
      using Q(1) apply auto[1]
      using pre(1) apply auto[1]
      using pre(7) Q(2) unfolding spec_of_def Valid_def init_def apply auto[1]
      using pre assms rdy_of_comm_spec_correct by auto
  qed
  subgoal premises pre for s0 s2 i ch var p2 v tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using rel_listD2[OF assms(1) pre(1)] by auto
    then obtain Q where Q: "specs ! i = InSpec ch var Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(3))
      using rel_listD1[OF assms(1)] pre(1) apply auto[1]
      using Q(1) apply auto[1]
      using pre(3) Q(2) unfolding spec_of_def Valid_def init_def by auto
  qed
  subgoal premises pre for s0 s2 d p i ch var p2 v tr2
  proof -
    have "spec_of_es (es ! i) (specs ! i)"
      using rel_listD2[OF assms(1) pre(5)] by auto
    then obtain Q where Q: "specs ! i = InSpec ch var Q" "spec_of p2 Q"
      apply (cases rule: spec_of_es.cases) using pre by auto
    show ?thesis
      apply (rule interrupt_c.intros(4))
      using rel_listD1[OF assms(1)] pre(5) apply auto[1]
      using Q(1) apply auto[1]
      using pre(1) apply auto[1]
      using pre(7) Q(2) unfolding spec_of_def Valid_def init_def apply auto[1]
      using pre assms rdy_of_comm_spec_correct by auto
  qed
  subgoal premises pre for s0 s2 tr2
    apply (rule interrupt_c.intros(1))
    using pre assms(2) unfolding spec_of_def Valid_def init_def by auto
  subgoal premises pre for s0 s2 d p tr2
    apply (rule interrupt_c.intros(2))
    using pre assms(1) rdy_of_comm_spec_correct apply auto
    using pre assms(2) unfolding spec_of_def Valid_def init_def by auto
  done

text \<open>Unique solution rule for interrupt\<close>

datatype 'a comm_spec2 =
  InSpec2 cname "real \<Rightarrow> real \<Rightarrow> 'a assn2"
| OutSpec2 cname "real \<Rightarrow> real \<Rightarrow> 'a assn2"

fun spec2_of :: "('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> 'a comm_spec \<Rightarrow> 'a comm_spec2" where
  "spec2_of p (InSpec ch var Q) = InSpec2 ch (\<lambda>d v. Q {{ (\<lambda>s0. (p s0 d)(var := v)) }}\<^sub>r )"
| "spec2_of p (OutSpec ch e Q) = OutSpec2 ch (\<lambda>d v. !\<^sub>a[(\<lambda>s0. v = e (updr s0 (p s0 d)))] \<and>\<^sub>a Q {{ (\<lambda>s0. (p s0 d)) }}\<^sub>r )"

definition rdy_of_comm_spec2 :: "'a comm_spec2 list \<Rightarrow> rdy_info" where
  "rdy_of_comm_spec2 = rdy_info_of_list (\<lambda>spec2.
    case spec2 of InSpec2 ch P \<Rightarrow> ({}, {ch})
                | OutSpec2 ch P \<Rightarrow> ({ch}, {}))"

lemma rdy_of_comm_spec2_of:
  "rdy_of_comm_spec specs = rdy_of_comm_spec2 (map (spec2_of p) specs)"
  unfolding rdy_of_comm_spec_def rdy_of_comm_spec2_def
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_map) subgoal for spec
    apply (cases spec) by auto
  done

inductive interrupt_sol_c :: "('a estate \<Rightarrow> real \<Rightarrow> 'a estate \<Rightarrow> bool) \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow>
  'a comm_spec2 list \<Rightarrow> 'a assn2" where
  "d s0 > 0 \<Longrightarrow> P (d s0) s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow> \<forall>t\<in>{0..d s0}. I s0 t (p t) \<Longrightarrow>
   interrupt_sol_c I d P specs s0 s (WaitBlk (d s0) (\<lambda>\<tau>. p \<tau>) rdy # tr)"
| "\<not>d s0 > 0 \<Longrightarrow> P 0 s0 s tr \<Longrightarrow>
   interrupt_sol_c I d P specs s0 s tr"
| "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow>
   interrupt_sol_c I d P specs s0 s (InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   0 < d' \<Longrightarrow> d' \<le> d s0 \<Longrightarrow> Q d' v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow> \<forall>t\<in>{0..d s0}. I s0 t (p t) \<Longrightarrow>
   interrupt_sol_c I d P specs s0 s (WaitBlk d' (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow> interrupt_sol_c I d P specs s0 s (OutBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch Q \<Longrightarrow>
   0 < d' \<Longrightarrow> d' \<le> d s0 \<Longrightarrow> Q d' v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow> \<forall>t\<in>{0..d s0}. I s0 t (p t) \<Longrightarrow>
   interrupt_sol_c I d P specs s0 s (WaitBlk d' (\<lambda>\<tau>. p \<tau>) rdy # OutBlock ch v # tr)"

lemma interrupt_c_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "interrupt_c ode b P specs s0 \<Longrightarrow>\<^sub>A
     interrupt_sol_c (\<lambda>s0 t s. s = updr s0 (p s0 t)) d (\<lambda>d' s. P (updr s (p s d')))
                     (map (spec2_of p) specs) s0"
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
      let ?Q' = "\<lambda>d v. Q {{ (\<lambda>s0. ((p s0 d)(var := v))) }}\<^sub>r"
      have Q: "map (spec2_of p) specs ! i = InSpec2 ch ?Q'"
        using pre(2) by (simp add: pre(3))
      show ?thesis
        apply (rule interrupt_sol_c.intros(3)[of i _ _ ?Q'])
        using pre Q paramODEsolD2[OF assms(1)]
        by (auto simp add: substr_assn2_def updr_rpart_simp1)
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
      let ?Q' = "\<lambda>d v. Q {{ (\<lambda>s0. ((p s0 d)(var := v))) }}\<^sub>r"
      have Q: "map (spec2_of p) specs ! i = InSpec2 ch ?Q'"
        using pre(2) by (simp add: pre(3))
      show ?thesis
        unfolding a(3)[symmetric]
        apply (rule interrupt_sol_c.intros(4)[of i _ _ ?Q'])
        using pre(2,3,4,5) a(1,2) Q rdy_of_comm_spec2_of
        unfolding substr_assn2_def by auto
    qed
    subgoal premises pre for i ch e Q tr'
    proof -
      let ?Q' = "\<lambda>d v. !\<^sub>a[(\<lambda>s0. v = e (updr s0 (p s0 d)))] \<and>\<^sub>a Q {{ (\<lambda>s0. (p s0 d)) }}\<^sub>r"
      have Q: "map (spec2_of p) specs ! i = OutSpec2 ch ?Q'"
        using pre(2) by (simp add: pre(3))
      show ?thesis
        apply (rule interrupt_sol_c.intros(5)[of i _ _ ?Q'])
        using pre(2,3,4) Q paramODEsolD2[OF assms(1)]
        unfolding substr_assn2_def conj_assn_def pure_assn_def by auto
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
      let ?Q' = "\<lambda>d v. !\<^sub>a[(\<lambda>s0. v = e (updr s0 (p s0 d)))] \<and>\<^sub>a Q {{ (\<lambda>s0. (p s0 d)) }}\<^sub>r"
      have Q: "map (spec2_of p) specs ! i = OutSpec2 ch ?Q'"
        using pre(2) by (simp add: pre(3))
      show ?thesis
        unfolding a(3)[symmetric] a(2)[symmetric]
        apply (rule interrupt_sol_c.intros(6)[of i _ _ ?Q'])
        using pre(2,3,4,5) a(1,2) Q rdy_of_comm_spec2_of
        unfolding substr_assn2_def conj_assn_def pure_assn_def by auto
    qed
    done
  done

lemma spec_of_interrupt_unique:
  assumes
    "paramODEsol ode b p d"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "rel_list spec_of_es es specs"
    "spec_of pr P"
  shows
    "spec_of (Interrupt ode b es pr)
             (interrupt_sol_c (\<lambda>s0 t s. s = updr s0 (p s0 t)) d (\<lambda>d' s. P (updr s (p s d')))
                              (map (spec2_of p) specs))"
  apply (rule spec_of_post)
   apply (rule spec_of_interrupt[OF assms(3,4)]) apply auto
  apply (rule entails_trans)
   apply (rule interrupt_c_unique[OF assms(1,2)])
  by (rule entails_triv)

inductive spec2_entails :: "'a comm_spec2 \<Rightarrow> 'a comm_spec2 \<Rightarrow> bool" where
  "(\<And>d v s0. P1 d v s0 \<Longrightarrow>\<^sub>A P2 d v s0) \<Longrightarrow> spec2_entails (InSpec2 ch P1) (InSpec2 ch P2)"
| "(\<And>d v s0. Q1 d v s0 \<Longrightarrow>\<^sub>A Q2 d v s0) \<Longrightarrow> spec2_entails (OutSpec2 ch Q1) (OutSpec2 ch Q2)"

inductive_cases spec2_entails_inE: "spec2_entails (InSpec2 ch P1) spec2"
inductive_cases spec2_entails_outE: "spec2_entails (OutSpec2 ch Q1) spec2"

lemma rdy_of_spec2_entails:
  assumes "rel_list spec2_entails specs specs2"
  shows "rdy_of_comm_spec2 specs = rdy_of_comm_spec2 specs2"
  unfolding rdy_of_comm_spec2_def
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_mono[OF _ assms])
  apply (elim spec2_entails.cases) by auto

lemma interrupt_sol_mono:
  assumes "\<And>d s0. P1 d s0 \<Longrightarrow>\<^sub>A P2 d s0"
    and "rel_list spec2_entails specs specs2"
  shows "interrupt_sol_c I d P1 specs s0 \<Longrightarrow>\<^sub>A interrupt_sol_c I d P2 specs2 s0"
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
        apply (rule interrupt_sol_c.intros(5)[of i _ _ Q2])
        using assms(2) unfolding entails_def by auto
      done
    subgoal for i ch e Q d' tr' a b
      using rel_listD2[OF assms(2), of i] rel_listD1[OF assms(2)] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_sol_c.intros(6)[of i _ _ Q2])
        using assms(2) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) by auto
      done
    done
  done

inductive interrupt_solInf_c :: "('a estate \<Rightarrow> real \<Rightarrow> 'a estate \<Rightarrow> bool) \<Rightarrow> 'a comm_spec2 list \<Rightarrow> 'a assn2" where
  "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow> interrupt_solInf_c I specs s0 s (InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpec2 ch Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow> \<forall>t\<in>{0..}. I s0 t (p t) \<Longrightarrow>
   interrupt_solInf_c I specs s0 s (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow> interrupt_solInf_c I specs s0 s (OutBlock ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpec2 ch Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_spec2 specs \<Longrightarrow> \<forall>t\<in>{0..}. I s0 t (p t) \<Longrightarrow>
   interrupt_solInf_c I specs s0 s (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # OutBlock ch v # tr)"

lemma interrupt_inf_c_unique:
  assumes
    "paramODEsolInf ode p"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows
    "interrupt_c ode (\<lambda>_. True) P specs s0 \<Longrightarrow>\<^sub>A
     interrupt_solInf_c (\<lambda>s0 t s. s = updr s0 (p s0 t)) (map (spec2_of p) specs) s0"
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
        let ?Q' = "\<lambda>d v. Q {{ (\<lambda>s0. ((p s0 d)(var := v))) }}\<^sub>r"
        show ?thesis
          apply (rule interrupt_solInf_c.intros(1)[of i _ _ ?Q'])
          using pre length p0
          by (auto simp add: substr_assn2_def updr_rpart_simp1)
      qed
      subgoal premises pre for i ch var Q d p2 v tr'
      proof -
        have a: "p s0 d = p2 d"
             "WaitBlk d (\<lambda>t. updr s0 (p s0 t)) = WaitBlk d (\<lambda>t. updr s0 (p2 t))"
          using paramODEsolInf_unique[OF assms pre(4,6,7)] by auto
        let ?Q' = "\<lambda>d v. Q {{ (\<lambda>s0. ((p s0 d)(var := v))) }}\<^sub>r"
        show ?thesis
          unfolding a(2)[symmetric]
          apply (rule interrupt_solInf_c.intros(2)[of i _ _ ?Q'])
          using pre a length rdy_of_comm_spec2_of
          by (auto simp add: substr_assn2_def)
      qed
      subgoal premises pre for i ch e Q tr'
      proof -
        let ?Q' = "\<lambda>d v. !\<^sub>a[(\<lambda>s0. v = e (updr s0 (p s0 d)))] \<and>\<^sub>a Q {{ (\<lambda>s0. (p s0 d)) }}\<^sub>r"
        show ?thesis
          apply (rule interrupt_solInf_c.intros(3)[of i _ _ ?Q'])
          using pre length p0
          by (auto simp add: substr_assn2_def conj_assn_def pure_assn_def)
      qed
      subgoal premises pre for i ch e Q d p2 tr'
      proof -
        have a: "p s0 d = p2 d"
             "WaitBlk d (\<lambda>t. updr s0 (p s0 t)) = WaitBlk d (\<lambda>t. updr s0 (p2 t))"
          using paramODEsolInf_unique[OF assms pre(4,6,7)] by auto
        let ?Q' = "\<lambda>d v. !\<^sub>a[(\<lambda>s0. v = e (updr s0 (p s0 d)))] \<and>\<^sub>a Q {{ (\<lambda>s0. (p s0 d)) }}\<^sub>r"
        show ?thesis
          unfolding a(2)[symmetric] a(1)[symmetric]
          apply (rule interrupt_solInf_c.intros(4)[of i _ _ ?Q'])
          using pre length a(1) rdy_of_comm_spec2_of
          by (auto simp add: substr_assn2_def conj_assn_def pure_assn_def)
      qed
      done
    done
qed

lemma spec_of_interrupt_inf_unique:
  assumes
    "paramODEsolInf ode p"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "rel_list spec_of_es es specs"
    "spec_of pr P"
  shows
    "spec_of (Interrupt ode (\<lambda>_. True) es pr)
             (interrupt_solInf_c (\<lambda>s0 t s. s = updr s0 (p s0 t)) (map (spec2_of p) specs))"
  apply (rule spec_of_post)
   apply (rule spec_of_interrupt[OF assms(3,4)]) apply auto
  apply (rule entails_trans)
   apply (rule interrupt_inf_c_unique[OF assms(1,2)])
  by (rule entails_triv)

lemma interrupt_solInf_mono:
  assumes "rel_list spec2_entails specs specs2"
  shows "interrupt_solInf_c I specs s0 \<Longrightarrow>\<^sub>A interrupt_solInf_c I specs2 s0"
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
        apply (rule interrupt_solInf_c.intros(3)[of i _ _ Q2])
        using assms(1) unfolding entails_def by auto
      done
    subgoal for i ch E Q d tr' a b
      using rel_listD2[OF assms, of i] rel_listD1[OF assms] apply simp
      apply (elim spec2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_solInf_c.intros(4)[of i _ _ Q2])
        using assms(1) unfolding entails_def apply auto
        apply (rule rdy_of_spec2_entails) by auto
      done
    done
  done

fun comm_spec2_updg :: "var \<Rightarrow> ('a estate \<Rightarrow> real) \<Rightarrow> 'a comm_spec2 \<Rightarrow> 'a comm_spec2" where
  "comm_spec2_updg var e (InSpec2 ch P) = InSpec2 ch (\<lambda>d v. P d v {{ var := e }})"
| "comm_spec2_updg var e (OutSpec2 ch P) = OutSpec2 ch (\<lambda>d v. P d v {{ var := e }})"

lemma rdy_of_comm_spec2_updg [simp]:
  "rdy_of_comm_spec2 (map (comm_spec2_updg var e) specs) = rdy_of_comm_spec2 specs"
  unfolding rdy_of_comm_spec2_def apply (rule sym)
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_map)
  subgoal for spec apply (cases spec) by auto
  done

lemma interrupt_solInf_c_updg:
  "(interrupt_solInf_c I specs {{ var := e }}) s0 \<Longrightarrow>\<^sub>A
   interrupt_solInf_c (\<lambda>s0 t s. I (upd s0 var (e s0)) t s) (map (comm_spec2_updg var e) specs) s0"
  unfolding entails_def apply clarify
  subgoal for s tr unfolding subst_assn2_def
    apply (induct rule: interrupt_solInf_c.cases) apply auto
    subgoal for i ch Q v tr'
      apply (rule interrupt_solInf_c.intros(1)[of i _ _ "\<lambda>d v. Q d v {{ var := e }}"])
      by (auto simp add: subst_assn2_def)
    subgoal for i ch Q d v tr' a b p'
      apply (rule interrupt_solInf_c.intros(2)[of i _ _ "\<lambda>d v. Q d v {{ var := e }}"])
      by (auto simp add: subst_assn2_def)
    subgoal for i ch Q v tr'
      apply (rule interrupt_solInf_c.intros(3)[of i _ _ "\<lambda>d v. Q d v {{ var := e }}"])
      by (auto simp add: subst_assn2_def)
    subgoal for i ch Q d v tr' a b p'
      apply (rule interrupt_solInf_c.intros(4)[of i _ _ "\<lambda>d v. Q d v {{ var := e }}"])
      by (auto simp add: subst_assn2_def)
    done
  done

lemma interrupt_sol_c_updg:
  "(interrupt_sol_c I d P specs {{ var := e }}) s0 \<Longrightarrow>\<^sub>A
   interrupt_sol_c (\<lambda>s0 t s. I (upd s0 var (e s0)) t s) (\<lambda>s0. d (upd s0 var (e s0)))
                   (\<lambda>d. P d {{ var := e }}) (map (comm_spec2_updg var e) specs) s0"
  unfolding entails_def apply clarify
  subgoal for s tr unfolding subst_assn2_def
    apply (induct rule: interrupt_sol_c.cases) apply auto
    subgoal for tr' a b p
      apply (rule interrupt_sol_c.intros(1)) by auto
    subgoal 
      apply (rule interrupt_sol_c.intros(2)) by auto
    subgoal for i ch Q v tr'
      apply (rule interrupt_sol_c.intros(3)[of i _ _ "\<lambda>d v. Q d v {{ var := e }}"])
      by (auto simp add: subst_assn2_def)
    subgoal for i ch Q d v tr' a b p'
      apply (rule interrupt_sol_c.intros(4)[of i _ _ "\<lambda>d v. Q d v {{ var := e }}"])
      by (auto simp add: subst_assn2_def)
    subgoal for i ch Q v tr'
      apply (rule interrupt_sol_c.intros(5)[of i _ _ "\<lambda>d v. Q d v {{ var := e }}"])
      by (auto simp add: subst_assn2_def)
    subgoal for i ch Q d v tr' a b p'
      apply (rule interrupt_sol_c.intros(6)[of i _ _ "\<lambda>d v. Q d v {{ var := e }}"])
      by (auto simp add: subst_assn2_def)
    done
  done

subsection \<open>Simplification of interrupt assertions\<close>

lemma interrupt_solInf_c_in:
  "interrupt_solInf_c I [InSpec2 ch P] = wait_in_c I ch P"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr apply (rule iffI)
    subgoal apply (elim interrupt_solInf_c.cases) apply auto
      subgoal for v tr'
        by (intro wait_in_c.intros(1)) 
      subgoal for d v tr' a b p
        unfolding rdy_of_comm_spec2_def apply simp
        by (auto intro: wait_in_c.intros(2))
      done
    subgoal apply (elim wait_in_c.cases) apply auto
      subgoal for v tr'
        apply (intro interrupt_solInf_c.intros(1)[of 0 _ _ P]) by auto
      subgoal for d v tr' p
        apply (intro interrupt_solInf_c.intros(2)[of 0 _ _ P]) apply auto
        unfolding rdy_of_comm_spec2_def by auto
      done
    done
  done

end
