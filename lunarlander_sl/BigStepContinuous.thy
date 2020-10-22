theory BigStepContinuous
  imports BigStepSimple Analysis_More
begin


subsection \<open>Hoare rules for ODE\<close>

inductive_cases contE: "big_step (Cont ode b) s1 tr s2"
thm contE

inductive_cases interruptE: "big_step (Interrupt ode b cs) s1 tr s2"
thm interruptE

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
theorem Valid_ode_sp:
  assumes "b st"
  shows "Valid
    (\<lambda>s t. s = st \<and> t = tr)
    (Cont ode b)
    (\<lambda>s t. (\<exists>d p. 0 < d \<and> ODEsol ode p d \<and> p 0 = st \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d) \<and>
                  s = p d \<and> t = tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})]))"
  apply (rule Valid_weaken_pre)
  prefer 2 apply (rule Valid_ode)
  by (auto simp add: entails_def assms)

text \<open>Unique solution form\<close>
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


subsection \<open>Hoare rules for ODE\<close>

text \<open>Weakest precondition form\<close>
theorem Valid_interrupt:
  assumes "\<forall>i<length cs.
    case cs ! i of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                        (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                        Q (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs),
                                       OutBlock ch (e (p d))]))))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                        (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                        Q ((p d)(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs),
                                                   InBlock ch v]))))"
    and "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<not>b s \<longrightarrow> R s tr)"
    and "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                   R (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs)])))"
  shows "Valid P (Interrupt ode b cs) R"
proof -
  have a: "R s2 (tr1 @ OutBlock ch (e s1) # tr2)"
    if *: "P s1 tr1"
          "i < length cs"
          "cs ! i = (ch[!]e, p2)"
          "big_step p2 s1 tr2 s2" for s1 tr1 s2 i ch e p2 tr2
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))"
      using *(2,3) by fastforce
    have 2: "Q s1 (tr1 @ [OutBlock ch (e s1)])"
      using 1(2) *(1) unfolding entails_def by auto
    then show ?thesis
      using *(4) 1(1) unfolding Valid_def by fastforce
  qed
  have b: "R s2 (tr1 @ WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (p d)) # tr2)"
    if *: "P (p 0) tr1"
          "0 < d"
          "ODEsol ode p d"
          "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)"
          "i < length cs"
          "cs ! i = (ch[!]e, p2)"
          "big_step p2 (p d) tr2 s2" for tr1 s2 d p i ch e p2 tr2
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                 (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                 Q (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs),
                                OutBlock ch (e (p d))]))"
      using *(5,6) by fastforce
    have "Q (p d) (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs),
                          OutBlock ch (e (p d))])"
      using 1(2) *(1-4) unfolding entails_def by auto
    then show ?thesis
      using *(7) 1(1) unfolding Valid_def by fastforce
  qed
  have c: "R s2 (tr1 @ InBlock ch v # tr2)"
    if *: "P s1 tr1"
          "i < length cs"
          "cs ! i = (ch[?]var, p2)"
          "big_step p2 (s1(var := v)) tr2 s2" for s1 tr1 s2 i ch var p2 v tr2
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))"
      using *(2,3) by fastforce
    have 2: "Q (s1(var := v)) (tr1 @ [InBlock ch v])"
      using 1(2) *(1) unfolding entails_def by auto
    then show ?thesis
      using *(4) 1(1) unfolding Valid_def by fastforce
  qed
  have d: "R s2 (tr1 @ WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr2a)"
    if *: "P (p 0) tr1"
          "0 < d"
          "ODEsol ode p d"
          "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)"
          "i < length cs"
          "cs ! i = (ch[?]var, p2)"
          "big_step p2 ((p d)(var := v)) tr2a s2" for tr1 s2 d p i ch var p2 v tr2a
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                 (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                 Q ((p d)(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs),
                                            InBlock ch v]))"
      using *(5,6) by fastforce
    have "Q ((p d)(var := v)) (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs), InBlock ch v])"
      using 1(2) *(1-4) unfolding entails_def by auto
    then show ?thesis
      using *(7) 1(1) unfolding Valid_def by fastforce
  qed
  show ?thesis
    unfolding Valid_def
    apply (auto elim!: interruptE)
    using a b c d assms(2-3) unfolding entails_def by auto
qed

text \<open>Simpler versions with one input/output\<close>

theorem Valid_interrupt_In:
  assumes "Valid Q p R"
  shows "Valid
    (\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
            (\<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                Q ((p d)(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {ch}),
                                           InBlock ch v])) \<and>
            (\<not>b s \<longrightarrow> R s tr) \<and>
            (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                R (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {ch})])))
      (Interrupt ode b [(ch[?]var, p)])
    R"
  apply (rule Valid_interrupt)
  apply auto apply (rule exI[where x=Q])
  by (auto simp add: assms entails_def)

text \<open>Versions with two communications\<close>

theorem Valid_interrupt_InIn:
  assumes "Valid Q1 p1 R"
    and "Valid Q2 p2 R"
  shows "Valid
    (\<lambda>s tr. (\<forall>v. Q1 (s(var1 := v)) (tr @ [InBlock ch1 v])) \<and>
            (\<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                Q1 ((p d)(var1 := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {ch1, ch2}),
                                             InBlock ch1 v])) \<and>
            (\<forall>v. Q2 (s(var2 := v)) (tr @ [InBlock ch2 v])) \<and>
            (\<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                Q2 ((p d)(var2 := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {ch1, ch2}),
                                             InBlock ch2 v])) \<and>
            (\<not>b s \<longrightarrow> R s tr) \<and>
            (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                R (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {ch1, ch2})])))
      (Interrupt ode b [(ch1[?]var1, p1), (ch2[?]var2, p2)])
    R"
  apply (rule Valid_interrupt)
  apply (rule InIn_lemma)
  subgoal apply (rule exI[where x=Q1])
    by (auto simp add: assms entails_def)
  apply (rule exI[where x=Q2])
  unfolding entails_def using assms by auto  

subsection \<open>Assertions for ODEs\<close>

text \<open>ODE without interrupt\<close>
inductive ode_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> tassn" ("ODE\<^sub>A") where
  "\<not>b s \<Longrightarrow> ODE\<^sub>A s ode b s []"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow> \<not>b (p d) \<Longrightarrow>
     ODE\<^sub>A s ode b (p d) [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})]"

text \<open>ODE interrupted by communication\<close>
inductive ode_in_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("ODEin\<^sub>A") where
  "ODEin\<^sub>A s ode b (s(var := v)) ch v rdy [InBlock ch v]"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t) \<Longrightarrow>
    ODEin\<^sub>A s ode b ((p d)(var := v)) ch v rdy
      [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy, InBlock ch v]"

text \<open>ODE with interrupt, but reached boundary\<close>
inductive ode_rdy_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> rdy_info \<Rightarrow> tassn" ("ODErdy\<^sub>A") where
  "\<not>b s \<Longrightarrow> ODErdy\<^sub>A s ode b s rdy []"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t) \<Longrightarrow> \<not>b (p d) \<Longrightarrow>
    ODErdy\<^sub>A s ode b (p d) rdy
      [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy]"

subsection \<open>Restate previous rules in simpler form\<close>

theorem Valid_ode':
  "Valid
    (\<lambda>s tr. \<forall>s'. (ODE\<^sub>A s ode b s' @- Q s') tr)
    (Cont ode b)
    Q"
proof -
  have 1: "Q s tr"
    if "\<forall>s'. (ODE\<^sub>A s ode b s' @- Q s') tr" "\<not> b s" for s tr
  proof -
    have "(ODE\<^sub>A s ode b s @- Q s) tr"
      using that(1) by auto
    moreover have "ODE\<^sub>A s ode b s []"
      using that(2) by (auto intro: ode_assn.intros)
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  have 2: "Q (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})])"
    if "\<forall>s'. (ODE\<^sub>A (p 0) ode b s' @- Q s') tr"
       "0 < d" "ODEsol ode p d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "\<not> b (p d)" for p d tr
  proof -
    have "(ODE\<^sub>A (p 0) ode b (p d) @- Q (p d)) tr"
      using that(1) by auto
    moreover have "ODE\<^sub>A (p 0) ode b (p d) [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})]"
      apply (rule ode_assn.intros)
      using that by auto
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  show ?thesis
    apply (rule Valid_weaken_pre)
     prefer 2 apply (rule Valid_ode)
    unfolding entails_def using 1 2 by auto
qed

theorem Valid_ode_sp':
  assumes "b st"
  shows "Valid
    (\<lambda>s tr. s = st \<and> Q tr)
    (Cont ode b)
    (\<lambda>s tr. (Q @\<^sub>t ODE\<^sub>A st ode b s) tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_ode')
  apply (auto simp add: entails_def)
  using entails_mp by (simp add: entails_tassn_def)

theorem Valid_interrupt_In':
  assumes "Valid Q p R"
  shows "Valid
    (\<lambda>s tr. (\<forall>s' v. (ODEin\<^sub>A s ode b s' ch v ({}, {ch}) @- Q s') tr) \<and>
            (\<forall>s'. (ODErdy\<^sub>A s ode b s' ({}, {ch}) @- R s') tr))
      (Interrupt ode b [(ch[?]var, p)])
    R"
proof -
  have 1: "Q (s(var := v)) (tr @ [InBlock ch v])"
    if "\<forall>s'. (ODEin\<^sub>A s ode b s' ch v ({}, {ch}) @- Q s') tr" for s tr v
  proof -
    have "(ODEin\<^sub>A s ode b (s(var := v)) ch v ({}, {ch}) @- Q (s(var := v))) tr"
      using that(1) by auto
    moreover have "ODEin\<^sub>A s ode b (s(var := v)) ch v ({}, {ch}) [InBlock ch v]"
      by (auto intro: ode_in_assn.intros)
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  have 2: "Q ((p d)(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {ch}), InBlock ch v])"
    if "\<forall>s' v. (ODEin\<^sub>A (p 0) ode b s' ch v ({}, {ch}) @- Q s') tr"
       "0 < d" "ODEsol ode p d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" for tr d p v
  proof -
    have "(ODEin\<^sub>A (p 0) ode b ((p d)(var := v)) ch v ({}, {ch}) @- Q ((p d)(var := v))) tr"
      using that(1) by auto
    moreover have "ODEin\<^sub>A (p 0) ode b ((p d)(var := v)) ch v ({}, {ch})
                    [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {ch}), InBlock ch v]"
      apply (rule ode_in_assn.intros)
      using that by auto
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  have 3: "R s tr"
    if "\<forall>s'. (ODErdy\<^sub>A s ode b s' ({}, {ch}) @- R s') tr" "\<not> b s" for s tr
  proof -
    have "(ODErdy\<^sub>A s ode b s ({}, {ch}) @- R s) tr"
      using that(1) by auto
    moreover have "ODErdy\<^sub>A s ode b s ({}, {ch}) []"
      apply (rule ode_rdy_assn.intros)
      using that(2) by auto
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  have 4: "R (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {ch})])"
    if "\<forall>s'. (ODErdy\<^sub>A (p 0) ode b s' ({}, {ch}) @- R s') tr"
       "0 < d" "ODEsol ode p d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "\<not> b (p d)" for tr d p
  proof -
    have "(ODErdy\<^sub>A (p 0) ode b (p d) ({}, {ch}) @- R (p d)) tr"
      using that(1) by auto
    moreover have "ODErdy\<^sub>A (p 0) ode b (p d) ({}, {ch})
                    [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {ch})]"
      thm ode_rdy_assn.intros(2)
      apply (rule ode_rdy_assn.intros(2))
      using that by auto
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  show ?thesis
    apply (rule Valid_weaken_pre)
     prefer 2 apply (rule Valid_interrupt_In[OF assms])
    apply (auto simp add: entails_def)
    using 1 2 3 4 by auto
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
