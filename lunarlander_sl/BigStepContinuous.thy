theory BigStepContinuous
  imports BigStepSimple
begin


subsection \<open>Hoare rules for ODE\<close>

text \<open>Weakest precondition form\<close>
theorem Valid_ode:
  "Valid
    (\<lambda>s tr. (\<not>b s \<longrightarrow> Q s tr) \<and>
            (\<forall>d p. 0 < d \<longrightarrow> ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                   Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])))
    (Cont ode b)
    Q"
  unfolding Valid_def
  by (auto elim!: contE)


subsection \<open>Hoare rules for interrupt\<close>

text \<open>Weakest precondition form\<close>
theorem Valid_interrupt:
  assumes "\<And>i. i < length cs \<Longrightarrow>
    case cs ! i of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. \<Turnstile> {Q} p2 {R} \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                        (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                        Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs),
                                       OutBlock ch (e (p d))]))))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. \<Turnstile> {Q} p2 {R} \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                        (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                        Q ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs),
                                                   InBlock ch v]))))"
    and "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<not>b s \<longrightarrow> R s tr)"
    and "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                   (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                   R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs)])))"
  shows "\<Turnstile> {P} Interrupt ode b cs {R}"
proof -
  have a: "R s2 (tr1 @ OutBlock ch (e s1) # tr2)"
    if *: "P s1 tr1"
          "i < length cs"
          "cs ! i = (ch[!]e, p2)"
          "big_step p2 s1 tr2 s2" for s1 tr1 s2 i ch e p2 tr2
  proof -
    from assms obtain Q where 1:
      "\<Turnstile> {Q} p2 {R}"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))"
      using *(2,3) by fastforce
    have 2: "Q s1 (tr1 @ [OutBlock ch (e s1)])"
      using 1(2) *(1) unfolding entails_def by auto
    then show ?thesis
      using *(4) 1(1) unfolding Valid_def by fastforce
  qed
  have b: "R s2 (tr1 @ WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (p d)) # tr2)"
    if *: "P (p 0) tr1"
          "0 < d"
          "ODEsol ode p d"
          "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)"
          "i < length cs"
          "cs ! i = (ch[!]e, p2)"
          "big_step p2 (p d) tr2 s2" for tr1 s2 d p i ch e p2 tr2
  proof -
    from assms obtain Q where 1:
      "\<Turnstile> {Q} p2 {R}"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                 (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                 Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs),
                                OutBlock ch (e (p d))]))"
      using *(5,6) by fastforce
    have "Q (p d) (tr1 @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs),
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
      "\<Turnstile> {Q} p2 {R}"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))"
      using *(2,3) by fastforce
    have 2: "Q (s1(var := v)) (tr1 @ [InBlock ch v])"
      using 1(2) *(1) unfolding entails_def by auto
    then show ?thesis
      using *(4) 1(1) unfolding Valid_def by fastforce
  qed
  have d: "R s2 (tr1 @ WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr2a)"
    if *: "P (p 0) tr1"
          "0 < d"
          "ODEsol ode p d"
          "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)"
          "i < length cs"
          "cs ! i = (ch[?]var, p2)"
          "big_step p2 ((p d)(var := v)) tr2a s2" for tr1 s2 d p i ch var p2 v tr2a
  proof -
    from assms obtain Q where 1:
      "\<Turnstile> {Q} p2 {R}"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                 (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                 Q ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs),
                                            InBlock ch v]))"
      using *(5,6) by fastforce
    have "Q ((p d)(var := v)) (tr1 @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs), InBlock ch v])"
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
  assumes "\<Turnstile> {Q} p {R}"
  shows "\<Turnstile>
    {\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
            (\<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                Q ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {ch}),
                                           InBlock ch v])) \<and>
            (\<not>b s \<longrightarrow> R s tr) \<and>
            (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {ch})]))}
      Interrupt ode b [(ch[?]var, p)]
    {R}"
  apply (rule Valid_interrupt)
  apply auto apply (rule exI[where x=Q])
  by (auto simp add: assms entails_def)

theorem Valid_interrupt_Out:
  assumes "\<Turnstile> {Q} p {R}"
  shows "\<Turnstile>
    {\<lambda>s tr. (Q s (tr @ [OutBlock ch (e s)])) \<and>
            (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({ch}, {}),
                               OutBlock ch (e (p d))])) \<and>
            (\<not>b s \<longrightarrow> R s tr) \<and>
            (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({ch}, {})]))}
      Interrupt ode b [(ch[!]e, p)]
    {R}"
  apply (rule Valid_interrupt)
  apply auto apply (rule exI[where x=Q])
  by (auto simp add: assms entails_def)


subsection \<open>Assertions for ODEs\<close>

text \<open>ODE without interrupt\<close>
inductive ode_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> tassn" ("ODE\<^sub>t") where
  "\<not>b s \<Longrightarrow> ODE\<^sub>t s ode b s []"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow> \<not>b (p d) \<Longrightarrow>
     ODE\<^sub>t s ode b (p d) [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"

text \<open>ODE interrupted by communication\<close>
inductive ode_in_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> cname \<Rightarrow> var \<Rightarrow> rdy_info \<Rightarrow> tassn" ("ODEin\<^sub>t") where
  "ODEin\<^sub>t s ode b (s(var := v)) ch var rdy [InBlock ch v]"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t) \<Longrightarrow>
    ODEin\<^sub>t s ode b ((p d)(var := v)) ch var rdy
      [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy, InBlock ch v]"

inductive ode_out_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> cname \<Rightarrow> exp \<Rightarrow> rdy_info \<Rightarrow> tassn" ("ODEout\<^sub>t") where
  "ODEout\<^sub>t s ode b s ch e rdy [OutBlock ch (e s)]"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t) \<Longrightarrow>
    ODEout\<^sub>t s ode b (p d) ch e rdy
      [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy, OutBlock ch (e (p d))]"

text \<open>ODE with interrupt, but reached boundary\<close>
inductive ode_rdy_assn :: "state \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> state \<Rightarrow> rdy_info \<Rightarrow> tassn" ("ODErdy\<^sub>t") where
  "\<not>b s \<Longrightarrow> ODErdy\<^sub>t s ode b s rdy []"
| "0 < d \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s \<Longrightarrow>
    \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t) \<Longrightarrow> \<not>b (p d) \<Longrightarrow>
    ODErdy\<^sub>t s ode b (p d) rdy
      [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy]"


subsection \<open>Simpler rules for ODE\<close>

theorem Valid_ode':
  "\<Turnstile> {\<lambda>s tr. \<forall>s'. (ODE\<^sub>t s ode b s' @- Q s') tr}
       Cont ode b
      {Q}"
proof -
  have 1: "Q s tr"
    if "\<forall>s'. (ODE\<^sub>t s ode b s' @- Q s') tr" "\<not> b s" for s tr
  proof -
    have "(ODE\<^sub>t s ode b s @- Q s) tr"
      using that(1) by auto
    moreover have "ODE\<^sub>t s ode b s []"
      using that(2) by (auto intro: ode_assn.intros)
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  have 2: "Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
    if "\<forall>s'. (ODE\<^sub>t (p 0) ode b s' @- Q s') tr"
       "0 < d" "ODEsol ode p d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "\<not> b (p d)" for p d tr
  proof -
    have "(ODE\<^sub>t (p 0) ode b (p d) @- Q (p d)) tr"
      using that(1) by auto
    moreover have "ODE\<^sub>t (p 0) ode b (p d) [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
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
  shows "\<Turnstile>
    {\<lambda>s tr. s = st \<and> Q s tr}
      Cont ode b
    {\<lambda>s tr. \<exists>s'. s = s' \<and> (Q st @\<^sub>t ODE\<^sub>t st ode b s') tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_ode')
  apply (auto simp add: entails_def)
  using entails_mp by (simp add: entails_tassn_def)

theorem Valid_ode_unique_solution_aux:
  assumes
    "d > 0" "ODEsol ode p d" "\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)"
    "\<not> b (p d)" "p 0 = st"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "ODE\<^sub>t st ode b st' tr"
  shows
    "st' = p d \<and> WaitS\<^sub>t d p ({}, {}) tr"
proof -
  have "b st"
    using assms(1,3,5) by auto
  have main: "d2 = d \<and> p d = p2 d2 \<and> (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) = (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) \<and>
              WaitS\<^sub>t d p ({}, {}) [WaitBlk d2 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})]"
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
    have s11: "WaitS\<^sub>t d p ({}, {}) [WaitBlk d2 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})]"
      unfolding WaitBlk_def
      apply (subst s9[symmetric])
      apply (subst s7[symmetric])
      unfolding WaitBlk_def[symmetric]
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
  shows "\<Turnstile>
    {\<lambda>s tr. s = st \<and> Q s tr}
      Cont ode b
    {\<lambda>s tr. s = p d \<and> (Q st @\<^sub>t WaitS\<^sub>t d p ({}, {})) tr}"
proof -
  have "b st"
    using assms(1,3,5) by auto
  have *: "ODE\<^sub>t st ode b s tr2 \<Longrightarrow> s = p d \<and> WaitS\<^sub>t d p ({}, {}) tr2" for s tr2
    using Valid_ode_unique_solution_aux[OF assms(1-6)] by auto
  show ?thesis
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_ode_sp)
    by (auto simp add: \<open>b st\<close> entails_def join_assn_def *)
qed

theorem Valid_ode_exit:
  assumes "\<not> b st"
  shows "\<Turnstile>
    {\<lambda>s tr. s = st \<and> Q tr}
      Cont ode b
    {\<lambda>s tr. s = st \<and> Q tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_ode)
  using assms by (auto simp add: entails_def)

subsection \<open>Simpler rules for interrupt\<close>

theorem Valid_interrupt':
  assumes "\<And>i. i < length cs \<Longrightarrow>
    case cs ! i of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. \<Turnstile> {Q} p2 {R} \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODEout\<^sub>t s ode b s' ch e (rdy_of_echoice cs) @- Q s') tr)))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. \<Turnstile> {Q} p2 {R} \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODEin\<^sub>t s ode b s' ch var (rdy_of_echoice cs) @- Q s') tr)))"
    and "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODErdy\<^sub>t s ode b s' (rdy_of_echoice cs) @- R s') tr)"
  shows "\<Turnstile> {P} Interrupt ode b cs {R}"
proof -
  have 1: "\<exists>Q. \<Turnstile> {Q} p {R} \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
           (P \<Longrightarrow>\<^sub>A
            (\<lambda>s tr.
                \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow>
                          p 0 = s \<longrightarrow>
                          (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                          Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (p d))])))"
    if *: "i < length cs" "cs ! i = (ch[!]e, p)" for i ch e p
  proof -
    from assms(1) obtain Q where
      Q: "\<Turnstile> {Q} p {R} \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODEout\<^sub>t s ode b s' ch e (rdy_of_echoice cs) @- Q s') tr))"
      using * by fastforce
    show ?thesis
      apply (rule exI[where x=Q])
      using Q by (auto simp add: entails_def magic_wand_assn_def ode_out_assn.intros)
  qed
  have 2: "\<exists>Q. \<Turnstile> {Q} p {R} \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
           (P \<Longrightarrow>\<^sub>A
            (\<lambda>s tr.
                \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow>
                          p 0 = s \<longrightarrow>
                          (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                          (\<forall>v. Q ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs), InBlock ch v]))))"
    if *: "i < length cs" "cs ! i = (ch[?]var, p)" for i ch var p
  proof -
    from assms(1) obtain Q where
      Q: "\<Turnstile> {Q} p {R} \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>s'. (ODEin\<^sub>t s ode b s' ch var (rdy_of_echoice cs) @- Q s') tr))"
      using * by fastforce
    show ?thesis
      apply (rule exI[where x=Q])
      using Q by (auto simp add: entails_def magic_wand_assn_def ode_in_assn.intros)
  qed
  have 3: "R s tr"
    if "\<forall>s'. (ODErdy\<^sub>t s ode b s' (rdy_of_echoice cs) @- R s') tr" "\<not> b s" for s tr
  proof -
    have "(ODErdy\<^sub>t s ode b s (rdy_of_echoice cs) @- R s) tr"
      using that(1) by auto
    moreover have "ODErdy\<^sub>t s ode b s (rdy_of_echoice cs) []"
      using that(2) by (auto intro: ode_rdy_assn.intros)
    ultimately show ?thesis
      by (auto simp add: magic_wand_assn_def)
  qed
  have 4: "R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs)])"
    if "\<forall>s'. (ODErdy\<^sub>t (p 0) ode b s' (rdy_of_echoice cs) @- R s') tr"
       "0 < d" "ODEsol ode p d"
       "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "\<not> b (p d)" for p d tr
  proof -
    have "(ODErdy\<^sub>t (p 0) ode b (p d) (rdy_of_echoice cs) @- R (p d)) tr"
      using that(1) by auto
    moreover have "ODErdy\<^sub>t (p 0) ode b (p d) (rdy_of_echoice cs) [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs)]"
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
  assumes "\<Turnstile> {Q} p {R}"
  shows "\<Turnstile>
    {\<lambda>s tr. (\<forall>s'. (ODEin\<^sub>t s ode b s' ch var ({}, {ch}) @- Q s') tr) \<and>
            (\<forall>s'. (ODErdy\<^sub>t s ode b s' ({}, {ch}) @- R s') tr)}
      Interrupt ode b [(ch[?]var, p)]
    {R}"
  apply (rule Valid_interrupt')
  using assms by (auto simp add: entails_def)

theorem Valid_interrupt_Out':
  assumes "\<Turnstile> {Q} p {R}"
  shows "\<Turnstile>
    {\<lambda>s tr. (\<forall>s'. (ODEout\<^sub>t s ode b s' ch e ({ch}, {}) @- Q s') tr) \<and>
            (\<forall>s'. (ODErdy\<^sub>t s ode b s' ({ch}, {}) @- R s') tr)}
      Interrupt ode b [(ch[!]e, p)]
    {R}"
  apply (rule Valid_interrupt')
  using assms by (auto simp add: entails_def)

theorem Valid_interrupt_sp:
  assumes "\<And>i. i < length cs \<Longrightarrow>
    case cs ! i of
      (ch[!]e, p2) \<Rightarrow>
        \<Turnstile> {\<lambda>s tr. (P st @\<^sub>t ODEout\<^sub>t st ode b s ch e (rdy_of_echoice cs)) tr} p2 {Q}
    | (ch[?]var, p2) \<Rightarrow>
        \<Turnstile> {\<lambda>s tr. (P st @\<^sub>t ODEin\<^sub>t st ode b s ch var (rdy_of_echoice cs)) tr} p2 {Q}"
  assumes "(\<lambda>s tr. (P st @\<^sub>t (ODErdy\<^sub>t st ode b s (rdy_of_echoice cs))) tr) \<Longrightarrow>\<^sub>A Q"
  shows "\<Turnstile>
    {\<lambda>s tr. s = st \<and> P s tr}
      Interrupt ode b cs
    {Q}"
  apply (rule Valid_interrupt')
  subgoal for i
    apply (cases "cs ! i") apply auto
    subgoal for comm p2
      apply (cases comm)
      subgoal for ch e
        apply auto
        apply (rule exI[where x="\<lambda>s tr. (P st @\<^sub>t ODEout\<^sub>t st ode b s ch e (rdy_of_echoice cs)) tr"])
        using assms(1)[of i]
        by (auto simp add: entails_def magic_wand_assn_def join_assn_def)
      subgoal for ch var
        apply auto
        apply (rule exI[where x="\<lambda>s tr. (P st @\<^sub>t ODEin\<^sub>t st ode b s ch var (rdy_of_echoice cs)) tr"])
        using assms(1)[of i]
        by (auto simp add: entails_def magic_wand_assn_def join_assn_def)
      done
    done
  using assms(2) apply (auto simp add: entails_def magic_wand_assn_def)
  using join_assn_def by fastforce

theorem Valid_interrupt_In_sp:
  assumes "\<Turnstile> {\<lambda>s tr. (P st @\<^sub>t ODEin\<^sub>t st ode b s ch var ({}, {ch})) tr} p {Q}"
  shows "\<Turnstile>
    {\<lambda>s tr. s = st \<and> P s tr}
      Interrupt ode b [(ch[?]var, p)]
    {\<lambda>s tr. Q s tr \<or> (P st @\<^sub>t (ODErdy\<^sub>t st ode b s ({}, {ch}))) tr}"
  apply (rule Valid_interrupt_sp)
  using assms by (auto simp add: Valid_def entails_def)

theorem Valid_interrupt_Out_sp:
  assumes "\<Turnstile> {\<lambda>s tr. (P st @\<^sub>t ODEout\<^sub>t st ode b s ch e ({ch}, {})) tr} p {Q}"
  shows "\<Turnstile>
    {\<lambda>s tr. s = st \<and> P s tr}
      Interrupt ode b [(ch[!]e, p)]
    {\<lambda>s tr. Q s tr \<or> (P st @\<^sub>t (ODErdy\<^sub>t st ode b s ({ch}, {}))) tr}"
  apply (rule Valid_interrupt_sp)
  using assms by (auto simp add: Valid_def entails_def)


inductive wait_in_assn :: "real \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("WaitIn\<^sub>t") where
  "WaitIn\<^sub>t 0 p ch v rdy [InBlock ch v]"
| "d > 0 \<Longrightarrow> WaitIn\<^sub>t d p ch v rdy [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy, InBlock ch v]"

inductive wait_out_assn :: "real \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> cname \<Rightarrow> exp \<Rightarrow> rdy_info \<Rightarrow> tassn" ("WaitOut\<^sub>t") where
  "WaitOut\<^sub>t 0 p ch e rdy [OutBlock ch (e (p 0))]"
| "d > 0 \<Longrightarrow> WaitOut\<^sub>t d p ch e rdy [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy, OutBlock ch (e (p d))]"

theorem Valid_ode_out_unique_solution_aux:
  assumes
    "ODEsolInf ode p" "\<forall>t\<ge>0. b (p t)" "p 0 = st"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "ODEout\<^sub>t st ode b st' ch e rdy tr"
  shows
    "\<exists>d. st' = p d \<and> WaitOut\<^sub>t d p ch e rdy tr"
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
      using main[of d p2] WaitBlk_def by auto
    done
qed

theorem Valid_ode_rdy_unique_solution_aux:
  assumes
    "ODEsolInf ode p" "\<forall>t\<ge>0. b (p t)" "p 0 = st"
    "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
    "ODErdy\<^sub>t st ode b st' rdy tr"
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
    "\<Turnstile> {\<lambda>s tr. \<exists>d. s = p d \<and> (P st @\<^sub>t WaitOut\<^sub>t d p ch e ({ch}, {})) tr} p2 {Q}"
  shows "\<Turnstile>
    {\<lambda>s tr. s = st \<and> P s tr}
      Interrupt ode b [(ch[!]e, p2)]
    {Q}"
proof -
  have *: "ODEout\<^sub>t st ode b s ch e ({ch}, {}) tr2 \<Longrightarrow>
           \<exists>d. s = p d \<and> WaitOut\<^sub>t d p ch e ({ch}, {}) tr2" for s tr2
    using Valid_ode_out_unique_solution_aux[OF assms(1-4)] by auto
  have **: "ODErdy\<^sub>t st ode b s ({ch}, {}) tr2 \<Longrightarrow> False" for s tr2
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

end
