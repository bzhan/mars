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


subsection \<open>Hoare rules for ODE\<close>

text \<open>Weakest precondition form\<close>
theorem Valid_interrupt:
  assumes "\<And>i. i < length cs \<Longrightarrow>
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

theorem Valid_interrupt_Out:
  assumes "Valid Q p R"
  shows "Valid
    (\<lambda>s tr. (Q s (tr @ [OutBlock ch (e s)])) \<and>
            (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                Q (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({ch}, {}),
                               OutBlock ch (e (p d))])) \<and>
            (\<not>b s \<longrightarrow> R s tr) \<and>
            (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                R (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({ch}, {})])))
      (Interrupt ode b [(ch[!]e, p)])
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
inductive ode_in_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> cname \<Rightarrow> var \<Rightarrow> rdy_info \<Rightarrow> tassn" ("ODEin\<^sub>A") where
  "ODEin\<^sub>A s ode b (s(var := v)) ch var rdy [InBlock ch v]"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t) \<Longrightarrow>
    ODEin\<^sub>A s ode b ((p d)(var := v)) ch var rdy
      [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy, InBlock ch v]"

inductive ode_out_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> cname \<Rightarrow> exp \<Rightarrow> rdy_info \<Rightarrow> tassn" ("ODEout\<^sub>A") where
  "ODEout\<^sub>A s ode b s ch e rdy [OutBlock ch (e s)]"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t) \<Longrightarrow>
    ODEout\<^sub>A s ode b (p d) ch e rdy
      [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy, OutBlock ch (e (p d))]"

text \<open>ODE with interrupt, but reached boundary\<close>
inductive ode_rdy_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> rdy_info \<Rightarrow> tassn" ("ODErdy\<^sub>A") where
  "\<not>b s \<Longrightarrow> ODErdy\<^sub>A s ode b s rdy []"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t) \<Longrightarrow> \<not>b (p d) \<Longrightarrow>
    ODErdy\<^sub>A s ode b (p d) rdy
      [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy]"


subsection \<open>Simpler rules for ODE\<close>

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

theorem Valid_ode_sp:
  assumes "b st"
  shows "Valid
    (\<lambda>s tr. s = st \<and> Q s tr)
    (Cont ode b)
    (\<lambda>s tr. \<exists>s'. s = s' \<and> (Q st @\<^sub>t ODE\<^sub>A st ode b s') tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_ode')
  apply (auto simp add: entails_def)
  using entails_mp by (simp add: entails_tassn_def)

theorem Valid_ode_unique_solution_aux:
  assumes
    "d > 0" "ODEsol ode p d" "\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)"
    "\<not> b (p d)" "p 0 = st"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "ODE\<^sub>A st ode b st' tr"
  shows
    "st' = p d \<and> WaitS\<^sub>A d p tr"
proof -
  have "b st"
    using assms(1,3,5) by auto
  have main: "d2 = d \<and> p d = p2 d2 \<and> (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) = (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) \<and>
              WaitS\<^sub>A d p [WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) ({}, {})]"
    if cond: "0 < d2"
       "ODEsol ode p2 d2"
       "(\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t))"
       "\<not> b (p2 d2)"
       "p2 0 = st" for p2 d2
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
    have s9: "(\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) = (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>))"
      using s7 s8 unfolding restrict_def by auto
    have s10: "p d = p2 d"
      using s8 by (simp add: assms(1) less_eq_real_def)
    have s11: "WaitS\<^sub>A d p [WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) ({}, {})]"
      apply (subst s9[symmetric])
      apply (subst s7[symmetric])
      by (rule wait_assn.intros)
    show ?thesis using s7 s9 s10 s11 by auto
  qed
  show ?thesis
    using assms(7) apply (auto simp add: ode_assn.simps)
    subgoal using \<open>b st\<close> by auto
    subgoal using \<open>b st\<close> by auto
    subgoal for d1 p1
      using main[of d1 p1] by auto
    subgoal for d1 p1
      using main[of d1 p1] by auto
    done
qed

theorem Valid_ode_unique_solution':
  assumes
    "d > 0" "ODEsol ode p d" "\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)"
    "\<not> b (p d)" "p 0 = st"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
  shows "Valid
    (\<lambda>s tr. s = st \<and> Q s tr)
    (Cont ode b)
    (\<lambda>s tr. s = p d \<and> (Q st @\<^sub>t WaitS\<^sub>A d p) tr)"
proof -
  have "b st"
    using assms(1,3,5) by auto
  have *: "ODE\<^sub>A st ode b s tr2 \<Longrightarrow> s = p d \<and> WaitS\<^sub>A d p tr2" for s tr2
    using Valid_ode_unique_solution_aux[OF assms(1-6)] by auto
  show ?thesis
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_ode_sp)
    by (auto simp add: \<open>b st\<close> entails_def join_assn_def *)
qed

theorem Valid_ode_exit:
  assumes "\<not> b st"
  shows "Valid
    (\<lambda>s tr. s = st \<and> Q tr)
    (Cont ode b)
    (\<lambda>s tr. s = st \<and> Q tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_ode)
  using assms by (auto simp add: entails_def)

subsection \<open>Simpler rules for interrupt\<close>

theorem Valid_interrupt':
  assumes "\<And>i. i < length cs \<Longrightarrow>
    case cs ! i of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODEout\<^sub>A s ode b s' ch e (rdy_of_echoice cs) @- Q s') tr)))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODEin\<^sub>A s ode b s' ch var (rdy_of_echoice cs) @- Q s') tr)))"
    and "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODErdy\<^sub>A s ode b s' (rdy_of_echoice cs) @- R s') tr)"
  shows "Valid P (Interrupt ode b cs) R"
proof -
  have 1: "\<exists>Q. Valid Q p R \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
           (P \<Longrightarrow>\<^sub>A
            (\<lambda>s tr.
                \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow>
                          p 0 = s \<longrightarrow>
                          (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                          Q (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (p d))])))"
    if *: "i < length cs" "cs ! i = (ch[!]e, p)" for i ch e p
  proof -
    from assms(1) obtain Q where
      Q: "Valid Q p R \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODEout\<^sub>A s ode b s' ch e (rdy_of_echoice cs) @- Q s') tr))"
      using * by fastforce
    show ?thesis
      apply (rule exI[where x=Q])
      using Q by (auto simp add: entails_def magic_wand_assn_def ode_out_assn.intros)
  qed
  have 2: "\<exists>Q. Valid Q p R \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
           (P \<Longrightarrow>\<^sub>A
            (\<lambda>s tr.
                \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow>
                          p 0 = s \<longrightarrow>
                          (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                          (\<forall>v. Q ((p d)(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs), InBlock ch v]))))"
    if *: "i < length cs" "cs ! i = (ch[?]var, p)" for i ch var p
  proof -
    from assms(1) obtain Q where
      Q: "Valid Q p R \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODEin\<^sub>A s ode b s' ch var (rdy_of_echoice cs) @- Q s') tr))"
      using * by fastforce
    show ?thesis
      apply (rule exI[where x=Q])
      using Q by (auto simp add: entails_def magic_wand_assn_def ode_in_assn.intros)
  qed
  have 3: "R s tr"
    if "\<forall>s'. (ODErdy\<^sub>A s ode b s' (rdy_of_echoice cs) @- R s') tr" "\<not> b s" for s tr
  proof -
    have "(ODErdy\<^sub>A s ode b s (rdy_of_echoice cs) @- R s) tr"
      using that(1) by auto
    moreover have "ODErdy\<^sub>A s ode b s (rdy_of_echoice cs) []"
      using that(2) by (auto intro: ode_rdy_assn.intros)
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  have 4: "R (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs)])"
    if "\<forall>s'. (ODErdy\<^sub>A (p 0) ode b s' (rdy_of_echoice cs) @- R s') tr"
       "0 < d" "ODEsol ode p d"
       "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "\<not> b (p d)" for p d tr
  proof -
    have "(ODErdy\<^sub>A (p 0) ode b (p d) (rdy_of_echoice cs) @- R (p d)) tr"
      using that(1) by auto
    moreover have "ODErdy\<^sub>A (p 0) ode b (p d) (rdy_of_echoice cs) [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs)]"
      apply (rule ode_rdy_assn.intros)
      using that by auto
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  show ?thesis
    apply (rule Valid_interrupt)
    subgoal for i apply (cases "cs ! i")
      subgoal for ch p apply (cases ch)
        using 1 2 by auto
      done
    subgoal apply (rule entails_trans[OF assms(2)])
      by (auto simp add: entails_def 3)
    subgoal apply (rule entails_trans[OF assms(2)])
      by (auto simp add: entails_def 4)
    done
qed

theorem Valid_interrupt_In':
  assumes "Valid Q p R"
  shows "Valid
    (\<lambda>s tr. (\<forall>s'. (ODEin\<^sub>A s ode b s' ch var ({}, {ch}) @- Q s') tr) \<and>
            (\<forall>s'. (ODErdy\<^sub>A s ode b s' ({}, {ch}) @- R s') tr))
      (Interrupt ode b [(ch[?]var, p)])
    R"
  apply (rule Valid_interrupt')
  using assms by (auto simp add: entails_def)

theorem Valid_interrupt_Out':
  assumes "Valid Q p R"
  shows "Valid
    (\<lambda>s tr. (\<forall>s'. (ODEout\<^sub>A s ode b s' ch e ({ch}, {}) @- Q s') tr) \<and>
            (\<forall>s'. (ODErdy\<^sub>A s ode b s' ({ch}, {}) @- R s') tr))
      (Interrupt ode b [(ch[!]e, p)])
    R"
  apply (rule Valid_interrupt')
  using assms by (auto simp add: entails_def)

theorem Valid_interrupt_sp:
  assumes "\<And>i. i < length cs \<Longrightarrow>
    case cs ! i of
      (ch[!]e, p2) \<Rightarrow>
        Valid (\<lambda>s tr. (P st @\<^sub>t ODEout\<^sub>A st ode b s ch e (rdy_of_echoice cs)) tr) p2 Q
    | (ch[?]var, p2) \<Rightarrow>
        Valid (\<lambda>s tr. (P st @\<^sub>t ODEin\<^sub>A st ode b s ch var (rdy_of_echoice cs)) tr) p2 Q"
  assumes "(\<lambda>s tr. (P st @\<^sub>t (ODErdy\<^sub>A st ode b s (rdy_of_echoice cs))) tr) \<Longrightarrow>\<^sub>A Q"
  shows "Valid
    (\<lambda>s tr. s = st \<and> P s tr)
    (Interrupt ode b cs)
    Q"
  apply (rule Valid_interrupt')
  subgoal for i
    apply (cases "cs ! i") apply auto
    subgoal for comm p2
      apply (cases comm)
      subgoal for ch e
        apply auto
        apply (rule exI[where x="\<lambda>s tr. (P st @\<^sub>t ODEout\<^sub>A st ode b s ch e (rdy_of_echoice cs)) tr"])
        using assms(1)[of i]
        by (auto simp add: entails_def magic_wand_assn_def join_assn_def)
      subgoal for ch var
        apply auto
        apply (rule exI[where x="\<lambda>s tr. (P st @\<^sub>t ODEin\<^sub>A st ode b s ch var (rdy_of_echoice cs)) tr"])
        using assms(1)[of i]
        by (auto simp add: entails_def magic_wand_assn_def join_assn_def)
      done
    done
  using assms(2) apply (auto simp add: entails_def magic_wand_assn_def)
  using join_assn_def by fastforce

theorem Valid_interrupt_In_sp:
  assumes "Valid (\<lambda>s tr. (P st @\<^sub>t ODEin\<^sub>A st ode b s ch var ({}, {ch})) tr) p Q"
  shows "Valid
    (\<lambda>s tr. s = st \<and> P s tr)
    (Interrupt ode b [(ch[?]var, p)])
    (\<lambda>s tr. Q s tr \<or> (P st @\<^sub>t (ODErdy\<^sub>A st ode b s ({}, {ch}))) tr)"
  apply (rule Valid_interrupt_sp)
  using assms by (auto simp add: Valid_def entails_def)

theorem Valid_interrupt_Out_sp:
  assumes "Valid (\<lambda>s tr. (P st @\<^sub>t ODEout\<^sub>A st ode b s ch e ({ch}, {})) tr) p Q"
  shows "Valid
    (\<lambda>s tr. s = st \<and> P s tr)
    (Interrupt ode b [(ch[!]e, p)])
    (\<lambda>s tr. Q s tr \<or> (P st @\<^sub>t (ODErdy\<^sub>A st ode b s ({ch}, {}))) tr)"
  apply (rule Valid_interrupt_sp)
  using assms by (auto simp add: Valid_def entails_def)


inductive wait_in_assn :: "real \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("WaitIn\<^sub>A") where
  "WaitIn\<^sub>A 0 p ch v rdy [InBlock ch v]"
| "d > 0 \<Longrightarrow> WaitIn\<^sub>A d p ch v rdy [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy, InBlock ch v]"

inductive wait_out_assn :: "real \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> cname \<Rightarrow> exp \<Rightarrow> rdy_info \<Rightarrow> tassn" ("WaitOut\<^sub>A") where
  "WaitOut\<^sub>A 0 p ch e rdy [OutBlock ch (e (p 0))]"
| "d > 0 \<Longrightarrow> WaitOut\<^sub>A d p ch e rdy [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy, OutBlock ch (e (p d))]"

theorem Valid_ode_out_unique_solution_aux:
  assumes
    "ODEsolInf ode p" "\<forall>t\<ge>0. b (p t)" "p 0 = st"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "ODEout\<^sub>A st ode b st' ch e rdy tr"
  shows
    "\<exists>d. st' = p d \<and> WaitOut\<^sub>A d p ch e rdy tr"
proof -
  have main: "p2 d = p d \<and> (\<lambda>\<tau>\<in>{0..d}. State (p2 \<tau>)) = (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>))"
    if cond: "0 < d"
       "ODEsol ode p2 d"
       "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p2 t)"
       "p2 0 = st" for d p2
  proof -
    interpret loc:ll_on_open_it "{-1<..}"
      "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
      apply standard
      using assms(4) by auto
    have s1: "((\<lambda>t. state2vec (p t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..} UNIV"
      using assms(1) unfolding ODEsolInf_def solves_ode_def by auto
    have s2: "(loc.flow 0 (state2vec st)) t = (\<lambda>t. state2vec (p t)) t" if "t \<in> {0..d}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s1])
      using that by (auto simp add: state2vec_def assms(3))
    have s3: "((\<lambda>t. state2vec(p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d} UNIV"
      using cond(2) unfolding ODEsol_def solves_ode_def by auto
    have s4: "loc.flow 0 (state2vec st) t = state2vec (p2 t)" if "t\<in>{0..d}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s3])
      using cond that by auto
    have s8: "t\<in>{0..d} \<Longrightarrow> p2 t = p t" for t
      using s2 s4 by (metis vec_state_map1)
    have s9: "(\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) = (\<lambda>\<tau>\<in>{0..d}. State (p2 \<tau>))"
      using s8 unfolding restrict_def by auto
    have s10: "p d = p2 d"
      using s8 that(1) by auto
    show ?thesis using s9 s10 by auto
  qed
  show ?thesis
    using assms(5) apply (elim ode_out_assn.cases)
     apply auto
     apply (rule exI[where x=0])
    subgoal for rdy1 rdy2
      by (auto simp add: assms(3) wait_out_assn.simps)
    subgoal for d p2 rdy1 rdy2
      apply (rule exI[where x=d])
      apply (auto simp add: wait_out_assn.simps)
      using main[of d p2] by auto
    done
qed

theorem Valid_ode_rdy_unique_solution_aux:
  assumes
    "ODEsolInf ode p" "\<forall>t\<ge>0. b (p t)" "p 0 = st"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "ODErdy\<^sub>A st ode b st' rdy tr"
  shows
    "False"
proof -
  have "b st"
    using assms(2,3) by auto
  have main: "False"
    if cond: "0 < d1"
       "ODEsol ode p1 d1"
       "st = p1 0"
       "\<forall>t. 0 \<le> t \<and> t < d1 \<longrightarrow> b (p1 t)"
       "\<not> b (p1 d1)" for d1 p1
  proof -
    interpret loc:ll_on_open_it "{-1<..}"
      "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
      apply standard
      using assms(4) by auto
    have s1: "((\<lambda>t. state2vec (p t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..} UNIV"
      using assms(1) unfolding ODEsolInf_def solves_ode_def by auto
    have s2: "(loc.flow 0 (state2vec st)) t = (\<lambda>t. state2vec (p t)) t" if "t \<in> {0..d1}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s1])
      using that by (auto simp add: state2vec_def assms(3))
    have s3: "((\<lambda>t. state2vec(p1 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d1} UNIV"
      using cond(2) unfolding ODEsol_def solves_ode_def by auto
    have s4: "loc.flow 0 (state2vec st) t = state2vec (p1 t)" if "t\<in>{0..d1}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s3])
      using cond that by auto
    have s8: "t\<in>{0..d1} \<Longrightarrow> p1 t = p t" for t
      using s2 s4 by (metis vec_state_map1)
    have s10: "p d1 = p1 d1"
      using s8 that(1) by auto
    show ?thesis using assms(2) cond(1,5) s10
      using less_eq_real_def by auto
  qed    
  show ?thesis
    using assms(5) apply (auto simp add: ode_rdy_assn.simps)
    subgoal using \<open>b st\<close> by auto
    subgoal for d1 p1
      using main by auto
    done
qed

theorem Valid_ode_out_unique_solution:
  assumes
    "ODEsolInf ode p" "\<forall>t\<ge>0. b (p t)" "p 0 = st"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "Valid (\<lambda>s tr. \<exists>d. s = p d \<and> (P st @\<^sub>t WaitOut\<^sub>A d p ch e ({ch}, {})) tr) p2 Q"
  shows "Valid
    (\<lambda>s tr. s = st \<and> P s tr)
    (Interrupt ode b [(ch[!]e, p2)])
    Q"
proof -
  have *: "ODEout\<^sub>A st ode b s ch e ({ch}, {}) tr2 \<Longrightarrow>
           \<exists>d. s = p d \<and> WaitOut\<^sub>A d p ch e ({ch}, {}) tr2" for s tr2
    using Valid_ode_out_unique_solution_aux[OF assms(1-4)] by auto
  have **: "ODErdy\<^sub>A st ode b s ({ch}, {}) tr2 \<Longrightarrow> False" for s tr2
    using Valid_ode_rdy_unique_solution_aux[OF assms(1-4)] by auto
  show ?thesis
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_interrupt_Out_sp[where Q=Q])
    subgoal
      apply (auto simp add: Valid_def join_assn_def)
      apply (drule *)
      using assms(5) apply (auto simp add: Valid_def join_assn_def join_assoc)
      by fastforce
    apply (auto simp add: entails_def join_assn_def)
    using ** by auto
qed


subsection \<open>Tests for ODE\<close>

lemma testHL12:
  assumes "a < 1"
  shows "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> Q tr)
    (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := 1)) \<and> (Q @\<^sub>t WaitS\<^sub>A (1 - a) (\<lambda>t. (\<lambda>_. 0)(X := t + a))) tr)"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + a)) (1 - a)"
     unfolding ODEsol_def solves_ode_def has_vderiv_on_def
     using assms apply auto
     apply (rule has_vector_derivative_projI)
     apply (auto simp add: state2vec_def)
     apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     by simp
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
     prefer 2 apply (rule Valid_ode_unique_solution'[OF _ 1 _ _ _ 2])
    using assms by (auto simp add: entails_def)
qed


subsection \<open>Test with ODE, loop and parallel\<close>

lemma testHL13a':
  assumes "a < 1"
  shows "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> Q tr)
    (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
     Cm (''ch1''[!](\<lambda>s. s X));
     Cm (''ch2''[?]X))
    (\<lambda>s tr. \<exists>v. s = (\<lambda>_. 0)(X := v) \<and>
            (Q @\<^sub>t WaitS\<^sub>A (1 - a) (\<lambda>t. (\<lambda>_. 0)(X := t + a))
               @\<^sub>t Out\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch1'' 1
               @\<^sub>t In\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch2'' v) tr)"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + a)) (1 - a)"
     unfolding ODEsol_def solves_ode_def has_vderiv_on_def
     using assms apply auto
     apply (rule has_vector_derivative_projI)
     apply (auto simp add: state2vec_def)
     apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     by simp
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
    apply (rule Valid_seq)
     apply (rule Valid_ode_unique_solution'[OF _ 1 _ _ _ 2])
        using assms apply auto apply (rule Valid_seq)
     apply (rule Valid_send_sp)
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_receive_sp)
    by (auto simp add: entails_def join_assoc)
qed

lemma testHL13a'':
  assumes "\<not>a < 1"
  shows "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> Q tr)
    (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
     Cm (''ch1''[!](\<lambda>s. s X));
     Cm (''ch2''[?]X))
    (\<lambda>s tr. \<exists>v. s = (\<lambda>_. 0)(X := v) \<and>
            (Q @\<^sub>t Out\<^sub>A ((\<lambda>_. 0)(X := a)) ''ch1'' a
               @\<^sub>t In\<^sub>A ((\<lambda>_. 0)(X := a)) ''ch2'' v) tr)"
  apply (rule Valid_seq)
   apply (rule Valid_ode_exit)
  using assms apply auto[1]
  apply (rule Valid_seq)
  apply (rule Valid_send_sp)
  apply (rule Valid_strengthen_post)
   prefer 2 apply (rule Valid_receive_sp)
  by (auto simp add: entails_def join_assoc)


text \<open>a is the initial value of X\<close>
fun left_blocks :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "left_blocks a [] = emp\<^sub>A"
| "left_blocks a (v # rest) =
    (if a < 1 then
       WaitS\<^sub>A (1 - a) (\<lambda>t. (\<lambda>_. 0)(X := t + a)) @\<^sub>t
       Out\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch1'' 1 @\<^sub>t
       In\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch2'' v @\<^sub>t left_blocks v rest
     else
       Out\<^sub>A ((\<lambda>_. 0)(X := a)) ''ch1'' a @\<^sub>t
       In\<^sub>A ((\<lambda>_. 0)(X := a)) ''ch2'' v @\<^sub>t left_blocks v rest)"

lemma left_blocks_snoc:
  "left_blocks a (vs @ [v]) =
    (if last_val a vs < 1 then
      left_blocks a vs @\<^sub>t
      WaitS\<^sub>A (1 - last_val a vs) (\<lambda>t. (\<lambda>_. 0)(X := t + last_val a vs)) @\<^sub>t
      Out\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch1'' 1 @\<^sub>t
      In\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch2'' v
    else
      left_blocks a vs @\<^sub>t
      Out\<^sub>A ((\<lambda>_. 0)(X := last_val a vs)) ''ch1'' (last_val a vs) @\<^sub>t
      In\<^sub>A ((\<lambda>_. 0)(X := last_val a vs)) ''ch2'' v)"
  apply (induct vs arbitrary: a)
  by (auto simp add: join_assoc)

lemma testHL13a:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> tr = [])
    (Rep (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
          Cm (''ch1''[!](\<lambda>s. s X));
          Cm (''ch2''[?]X)))
    (\<lambda>s tr. \<exists>vs. s = ((\<lambda>_. 0)(X := last_val a vs)) \<and> left_blocks a vs tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for vs
    apply (cases "last_val a vs < 1")
    apply (rule Valid_strengthen_post)
      prefer 2 apply (rule testHL13a') apply auto[1]
    subgoal apply (auto simp add: entails_def)
      subgoal for tr v apply (rule exI[where x="vs@[v]"])
        by (auto simp add: left_blocks_snoc)
      done
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule testHL13a'') apply auto[1]
    apply (auto simp add: entails_def)
    subgoal for tr v apply (rule exI[where x="vs@[v]"])
      by (auto simp add: left_blocks_snoc)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

fun right_blocks :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "right_blocks a [] = emp\<^sub>A"
| "right_blocks a (v # rest) =
    In\<^sub>A ((\<lambda>_. 0)(Y := a)) ''ch1'' v @\<^sub>t
    Out\<^sub>A ((\<lambda>_. 0)(Y := v)) ''ch2'' (v - 1) @\<^sub>t
    right_blocks v rest"

lemma right_blocks_snoc:
  "right_blocks a (vs @ [v]) =
    right_blocks a vs @\<^sub>t
    In\<^sub>A ((\<lambda>_. 0)(Y := last_val a vs)) ''ch1'' v @\<^sub>t
    Out\<^sub>A ((\<lambda>_. 0)(Y := v)) ''ch2'' (v - 1)"
  apply (induct vs arbitrary: a)
  by (auto simp add: join_assoc)

lemma testHL13b:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(Y := a)) \<and> tr = [])
    (Rep (Cm (''ch1''[?]Y);
          Cm (''ch2''[!](\<lambda>s. s Y - 1))))
    (\<lambda>s tr. \<exists>ws. s = ((\<lambda>_. 0)(Y := last_val a ws)) \<and> right_blocks a ws tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for ws
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp)
    apply (rule Valid_ex_pre)
    subgoal for w
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_send_sp)
    apply (auto simp add: entails_def)
    subgoal for tr
      apply (rule exI[where x="ws@[w]"])
      by (auto simp add: right_blocks_snoc join_assoc)
    done
  done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

fun tot_blocks :: "nat \<Rightarrow> tassn" where
  "tot_blocks 0 = emp\<^sub>A"
| "tot_blocks (Suc n) = (
    Wait\<^sub>A 1 (\<lambda>t\<in>{0..1}. ParState (State ((\<lambda>_. 0)(X := t))) (State ((\<lambda>_. 0)(Y := 1)))) @\<^sub>t
    IO\<^sub>A ''ch1'' 1 @\<^sub>t IO\<^sub>A ''ch2'' 0 @\<^sub>t tot_blocks n)"

lemma combineHL13:
  "combine_assn {''ch1'', ''ch2''} (left_blocks 0 vs) (right_blocks 1 ws) \<Longrightarrow>\<^sub>t
   tot_blocks (length vs)"
proof (induct vs arbitrary: ws)
  case Nil
  then show ?case
  proof (cases ws)
    case Nil
    then show ?thesis by auto
  next
    case (Cons w ws')
    then show ?thesis
      by (auto simp add: combine_assn_emp_in)
  qed
next
  case (Cons a vs)
  note Cons1 = Cons
  then show ?case
  proof (cases ws)
    case Nil
    then show ?thesis
      apply auto
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_wait_emp)
      by (rule false_assn_entails)
  next
    case (Cons b list)
    show ?thesis
      apply (auto simp add: Cons)
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_wait_in)
       apply auto[1]
      apply (rule entails_tassn_cancel_left)
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_out_in)
       apply auto apply (rule entails_tassn_cancel_left)
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_in_out)
       apply auto apply (rule entails_tassn_cancel_left)
      by (rule Cons1)
  qed
qed

lemma testHL13:
  "ParValid
    (pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(X := 0))) (\<lambda>s. s = ((\<lambda>_. 0)(Y := 1))))
    (Parallel
       (Single (Rep (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
                Cm (''ch1''[!](\<lambda>s. s X));
                Cm (''ch2''[?]X)))) {''ch1'', ''ch2''}
       (Single (Rep (Cm (''ch1''[?]Y);
                Cm (''ch2''[!](\<lambda>s. s Y - 1))))))
    (\<lambda>s tr. \<exists>n. tot_blocks n tr)"
  apply (rule ParValid_Parallel'')
  apply (rule ParValid_Single[OF testHL13a])
  apply (rule ParValid_Single[OF testHL13b])
   apply (auto simp add: pair_assn_def par_assn_def sing_assn_def)
  apply (rule combine_assn_ex_pre_left)
  apply (rule combine_assn_ex_pre_right)
  subgoal for s vs ws
    apply (rule entails_tassn_ex_post)
    apply (rule exI[where x="length vs"])
    apply (rule entails_tassn_trans)
     prefer 2 apply (rule combineHL13)
    apply (rule combine_assn_mono)
    by (auto simp add: entails_tassn_def)
  done

subsection \<open>Test with interrupt, loop and parallel\<close>

lemma testHL14o:
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0)(X := a) \<and> P tr)
    (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
               [(''ch1''[!](\<lambda>s. s X), Skip)])
    (\<lambda>s tr. \<exists>d. s = (\<lambda>_. 0)(X := d + a) \<and> (P @\<^sub>t WaitOut\<^sub>A d (\<lambda>t. (\<lambda>_. 0)(X := t + a)) ''ch1'' (\<lambda>s. s X) ({''ch1''}, {})) tr)"
proof -
  have 1: "ODEsolInf (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + a))"
     unfolding ODEsolInf_def solves_ode_def has_vderiv_on_def
     apply auto
     apply (rule has_vector_derivative_projI)
     apply (auto simp add: state2vec_def)
     apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     by simp
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
     prefer 2 apply (rule Valid_ode_out_unique_solution[OF 1 _ _ 2])
    apply auto
     apply (rule Valid_skip) by auto
qed

fun ileft_blocks :: "real \<Rightarrow> (real \<times> real) list \<Rightarrow> tassn" where
  "ileft_blocks a [] = emp\<^sub>A"
| "ileft_blocks a ((d, v) # rest) =
   WaitOut\<^sub>A d (\<lambda>t. (\<lambda>_. 0)(X := t + a)) ''ch1'' (\<lambda>s. s X) ({''ch1''}, {}) @\<^sub>t
   In\<^sub>A ((\<lambda>_. 0)(X := a + d)) ''ch2'' v @\<^sub>t
   ileft_blocks v rest"

fun last_ileft_blocks :: "real \<Rightarrow> (real \<times> real) list \<Rightarrow> real" where
  "last_ileft_blocks a [] = a"
| "last_ileft_blocks a ((d, v) # rest) = last_ileft_blocks v rest"

lemma ileft_blocks_snoc:
  "ileft_blocks a (ps @ [(d, v)]) =
   ileft_blocks a ps @\<^sub>t
     WaitOut\<^sub>A d (\<lambda>t. (\<lambda>_. 0)(X := t + last_ileft_blocks a ps)) ''ch1'' (\<lambda>s. s X) ({''ch1''}, {}) @\<^sub>t
     In\<^sub>A ((\<lambda>_. 0)(X := d + last_ileft_blocks a ps)) ''ch2'' v"
  apply (induct ps arbitrary: a)
  by (auto simp add: join_assoc add.commute)

lemma last_ileft_blocks_snoc [simp]:
  "last_ileft_blocks a (ps @ [(d, v)]) = v"
  apply (induct ps arbitrary: a) by auto

lemma testHL14a:
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0)(X := a) \<and> tr = [])
    (Rep (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True) [(''ch1''[!](\<lambda>s. s X), Skip)];
          Cm (''ch2''[?]X)))
    (\<lambda>s tr. \<exists>ps. s = (\<lambda>_. 0)(X := last_ileft_blocks a ps) \<and> ileft_blocks a ps tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for ps
    apply (rule Valid_seq)
     apply (rule testHL14o)
    apply (rule Valid_ex_pre)
    subgoal for d
      apply (rule Valid_strengthen_post)
       prefer 2 apply (rule Valid_receive_sp)
      apply (auto simp add: entails_def)
      subgoal for tr v
        apply (rule exI[where x="ps@[(d,v)]"])
        by (auto simp add: ileft_blocks_snoc join_assoc)
      done
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

fun iright_blocks :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "iright_blocks a [] = emp\<^sub>A"
| "iright_blocks a (v # rest) =
   WaitS\<^sub>A 1 (\<lambda>t. (\<lambda>_. 0)(Y := a)) @\<^sub>t
   In\<^sub>A ((\<lambda>_. 0)(Y := a)) ''ch1'' v @\<^sub>t
   Out\<^sub>A ((\<lambda>_. 0)(Y := v)) ''ch2'' (v - 1) @\<^sub>t iright_blocks v rest"

fun last_iright_blocks :: "real \<Rightarrow> real list \<Rightarrow> real" where
  "last_iright_blocks a [] = a"
| "last_iright_blocks a (v # rest) = last_iright_blocks v rest"

lemma iright_blocks_snoc:
  "iright_blocks a (vs @ [v]) =
   iright_blocks a vs @\<^sub>t WaitS\<^sub>A 1 (\<lambda>t. (\<lambda>_. 0)(Y := last_iright_blocks a vs)) @\<^sub>t
   In\<^sub>A ((\<lambda>_. 0)(Y := last_iright_blocks a vs)) ''ch1'' v @\<^sub>t
   Out\<^sub>A ((\<lambda>_. 0)(Y := v)) ''ch2'' (v - 1)"
  apply (induct vs arbitrary: a)
  by (auto simp add: join_assoc)

lemma last_iright_blocks_snoc [simp]:
  "last_iright_blocks a (vs @ [v]) = v"
  apply (induct vs arbitrary: a) by auto

lemma testHL14b:
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0)(Y := a) \<and> tr = [])
    (Rep (Wait 1; Cm (''ch1''[?]Y); Cm (''ch2''[!](\<lambda>s. s Y - 1))))
    (\<lambda>s tr. \<exists>vs. s = (\<lambda>_. 0)(Y := last_iright_blocks a vs) \<and> iright_blocks a vs tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for vs
    apply (rule Valid_seq)
    apply (rule Valid_wait_sp)
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp)
    apply (rule Valid_ex_pre)
    subgoal for v
      apply (rule Valid_strengthen_post)
       prefer 2 apply (rule Valid_send_sp)
      apply (auto simp add: entails_def)
      apply (rule exI[where x="vs@[v]"])
      by (auto simp add: iright_blocks_snoc join_assoc)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

lemma combine_assn_waitout_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (WaitOut\<^sub>A d p ch e rdy @\<^sub>t P) emp\<^sub>A \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def wait_out_assn.simps)
  using assms by (auto elim!: combine_blocks_elim2i combine_blocks_elim4b)

lemma combine_assn_waitout_wait:
  assumes "ch \<in> chs"
  shows "combine_assn chs (WaitOut\<^sub>A d p ch e rdy @\<^sub>t P) (Wait\<^sub>A d2 p2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         (\<up>(d \<ge> d2) \<and>\<^sub>t (Wait\<^sub>A d2 (\<lambda>t\<in>{0..d2}. ParState (State (p t)) (p2 t)) @\<^sub>t
                        combine_assn chs (WaitOut\<^sub>A (d - d2) (\<lambda>t\<in>{0..d-d2}. p (t + d2)) ch e rdy @\<^sub>t P) Q))"
  sorry

lemma combine_assn_waitout_in:
  assumes "ch \<in> chs"
  shows "combine_assn chs (WaitOut\<^sub>A d p ch e rdy @\<^sub>t P) (In\<^sub>A s ch v @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         (\<up>(d = 0) \<and>\<^sub>t \<up>(v = e (p 0)) \<and>\<^sub>t
          (IO\<^sub>A ch v @\<^sub>t combine_assn chs P Q))"
  sorry

lemma combineHL14:
  "combine_assn {''ch1'', ''ch2''} (ileft_blocks 0 ps) (iright_blocks 1 ws) \<Longrightarrow>\<^sub>t
   tot_blocks (length ps)"
proof (induct ps arbitrary: ws)
  case Nil
  then show ?case
  proof (cases ws)
    case Nil
    then show ?thesis by auto
  next
    case (Cons w ws')
    then show ?thesis
      apply auto
      apply (rule entails_tassn_trans)
      apply (rule combine_assn_emp_wait)
      by (rule false_assn_entails)
  qed
next
  case (Cons p ps')
  note Cons1 = Cons
  then show ?case
  proof (cases p)
    case (Pair d v)
    then show ?thesis
    proof (cases ws)
      case Nil
      then show ?thesis
        apply (auto simp add: Pair)
        apply (rule entails_tassn_trans)
        apply (rule combine_assn_waitout_emp)
        by auto
    next
      case (Cons a list)
      then show ?thesis
        apply (auto simp add: Pair)
        apply (rule entails_tassn_trans)
        apply (rule combine_assn_waitout_wait)
         apply auto
        apply (rule entails_tassn_cancel_left)
        apply (rule entails_tassn_trans)
        apply (rule combine_assn_waitout_in)
        apply auto
        apply (rule entails_tassn_cancel_left)
        apply (rule entails_tassn_trans)
         apply (rule combine_assn_in_out)
         apply auto
        apply (rule entails_tassn_cancel_left)
        by (rule Cons1)
    qed
  qed
qed

lemma testHL14:
  "ParValid
    (pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(X := 0))) (\<lambda>s. s = ((\<lambda>_. 0)(Y := 1))))
    (Parallel
      (Single (Rep (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True) [(''ch1''[!](\<lambda>s. s X), Skip)];
               Cm (''ch2''[?]X)))) {''ch1'', ''ch2''}
      (Single (Rep (Wait 1; Cm (''ch1''[?]Y); Cm (''ch2''[!](\<lambda>s. s Y - 1))))))
    (\<lambda>s tr. \<exists>n. tot_blocks n tr)"
  apply (rule ParValid_Parallel'')
  apply (rule ParValid_Single[OF testHL14a])
  apply (rule ParValid_Single[OF testHL14b])
  apply (auto simp add: pair_assn_def par_assn_def sing_assn_def)
  apply (rule combine_assn_ex_pre_left)
  apply (rule combine_assn_ex_pre_right)
  subgoal for s ps vs
    apply (rule entails_tassn_ex_post)
    apply (rule exI[where x="length ps"])
    apply (rule entails_tassn_trans)
    prefer 2 apply (rule combineHL14)
    apply (rule combine_assn_mono)
    by (auto simp add: entails_tassn_def)
  done


end
