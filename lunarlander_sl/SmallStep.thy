theory SmallStep
  imports BigStepSimple
begin


subsection \<open>Further results in analysis\<close>

lemma ODEsol_merge:
  assumes "ODEsol ode p d"
    and "ODEsol ode p2 d2"
    and "p2 0 = p d"
  shows "ODEsol ode (\<lambda>\<tau>. if \<tau> < d then p \<tau> else p2 (\<tau> - d)) (d + d2)"
  sorry

lemma ODEsol_split:
  assumes "ODEsol ode p d"
    and "0 < t1" and "t1 < d"
  shows "ODEsol ode p t1"
        "ODEsol ode (\<lambda>t. p (t + t1)) (d - t1)"
  sorry


subsection \<open>Small-step semantics\<close>

text \<open>small_step p s1 a p' s2 means executing p one step starting from
state s1, results in action a, remaining program p', and state s2.\<close>

inductive small_step :: "proc \<Rightarrow> state \<Rightarrow> trace_block option \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> bool" where
  assignB: "small_step (var ::= e) s None Skip (s(var := e s))"
| seqS1: "small_step c1 s ev c1' s2 \<Longrightarrow> small_step (Seq c1 c2) s ev (Seq c1' c2) s2"
| seqS2: "small_step (Seq Skip c) s None c s"
| condS1: "b s \<Longrightarrow> small_step (Cond b c1 c2) s None c1 s"
| condS2: "\<not>b s \<Longrightarrow> small_step (Cond b c1 c2) s None c2 s"
| waitS1: "d1 > 0 \<Longrightarrow> d1 < d \<Longrightarrow> small_step (Wait d) s (Some (WaitBlock d1 (\<lambda>\<tau>\<in>{0..d1}. State s) ({}, {})))
                                 (Wait (d - d1)) s"
| waitS2: "d > 0 \<Longrightarrow> small_step (Wait d) s (Some (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {}))) Skip s"
| sendS1: "small_step (Cm (ch[!]e)) s (Some (OutBlock ch (e s))) Skip s"
| sendS2: "d > 0 \<Longrightarrow> small_step (Cm (ch[!]e)) s (Some (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {})))
                                (Cm (ch[!]e)) s"
| receiveS1: "small_step (Cm (ch[?]var)) s (Some (InBlock ch v)) Skip (s(var := v))"
| receiveS2: "d > 0 \<Longrightarrow> small_step (Cm (ch[?]var)) s (Some (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch})))
                                   (Cm (ch[?]var)) s"
| IChoiceS1: "small_step (IChoice p1 p2) s None p1 s"
| IChoiceS2: "small_step (IChoice p1 p2) s None p2 s"
| EChoiceS1: "d > 0 \<Longrightarrow> small_step (EChoice cs) s (Some (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice cs)))
                                   (EChoice cs) s"
| EChoiceS2: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    small_step (EChoice cs) s (Some (OutBlock ch (e s))) p2 s"
| EChoiceS3: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    small_step (EChoice cs) s (Some (InBlock ch v)) p2 (s(var := v))"
| RepetitionS1: "small_step (Rep p) s None Skip s"
| RepetitionS2: "small_step (Rep p) s None (Seq p (Rep p)) s"
| ContS1: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    p 0 = s \<Longrightarrow> small_step (Cont ode b) s (Some (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})))
                           (Cont ode b) (p d)"
| ContS2: "\<not>b s \<Longrightarrow> small_step (Cont ode b) s None Skip s"
| InterruptS1: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    p 0 = s \<Longrightarrow> small_step (Interrupt ode b cs) s (Some (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs)))
                           (Interrupt ode b cs) (p d)"
| InterruptS2: "\<not>b s \<Longrightarrow> small_step (Interrupt ode b cs) s None Skip s"
| InterruptS3: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    small_step (Interrupt ode b cs) s (Some (OutBlock ch (e s))) p2 s"
| InterruptS4: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    small_step (Interrupt ode b cs) s (Some (InBlock ch v)) p2 (s(var := v))"


subsection \<open>Equivalence between big-step and small-step semantics\<close>

text \<open>First, we define the closure of the small-step semantics\<close>

inductive small_step_closure :: "proc \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> bool" where
  "small_step_closure p s [] p s"
| "small_step p s None p2 s2 \<Longrightarrow> small_step_closure p2 s2 evs p3 s3 \<Longrightarrow> small_step_closure p s evs p3 s3"
| "small_step p s (Some ev) p2 s2 \<Longrightarrow> small_step_closure p2 s2 evs p3 s3 \<Longrightarrow> small_step_closure p s (ev # evs) p3 s3"

text \<open>Further, we define equivalence between two traces\<close>

inductive equiv_trace :: "trace \<Rightarrow> trace \<Rightarrow> bool" where
  equiv_trace_empty: "equiv_trace [] []"
| equiv_trace_merge: "p1 d1 = p2 0 \<Longrightarrow>
   equiv_trace [WaitBlock d1 (\<lambda>\<tau>\<in>{0..d1}. p1 \<tau>) rdy, WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. p2 \<tau>) rdy]
               [WaitBlock (d1 + d2) (\<lambda>\<tau>\<in>{0..d}. if \<tau> < d1 then p1 \<tau> else p2 (\<tau> - d1)) rdy]"
| equiv_trace_sym: "equiv_trace tr1 tr2 \<Longrightarrow> equiv_trace tr2 tr1"
| equiv_trace_cons: "equiv_trace tr1 tr2 \<Longrightarrow> equiv_trace (ev # tr1) (ev # tr2)"
| equiv_trace_append: "equiv_trace tr1 tr2 \<Longrightarrow> equiv_trace (tr1 @ tr3) (tr2 @ tr3)"
| equiv_trace_trans: "equiv_trace tr1 tr2 \<Longrightarrow> equiv_trace tr2 tr3 \<Longrightarrow> equiv_trace tr1 tr3"

lemma equiv_trace_refl [simp]:
  "equiv_trace tr tr"
  apply (induct tr) by (auto intro: equiv_trace.intros)

lemma equiv_trace_append_left:
  "equiv_trace tr2 tr3 \<Longrightarrow> equiv_trace (tr1 @ tr2) (tr1 @ tr3)"
  apply (induct tr1) by (auto intro: equiv_trace.intros)

lemma small_step_closure_single_None:
  "small_step p s None p2 s2 \<Longrightarrow> small_step_closure p s [] p2 s2"
  by (auto intro: small_step_closure.intros)

lemma small_step_closure_single_Some:
  "small_step p s (Some ev) p2 s2 \<Longrightarrow> small_step_closure p s [ev] p2 s2"
  by (auto intro: small_step_closure.intros)

lemma small_step_closure_trans:
  "small_step_closure p1 s1 tr1 p2 s2 \<Longrightarrow> small_step_closure p2 s2 tr2 p3 s3 \<Longrightarrow>
   small_step_closure p1 s1 (tr1 @ tr2) p3 s3"
  apply (induction rule: small_step_closure.induct)
  apply simp
  using small_step_closure.intros(2) apply blast
  by (simp add: small_step_closure.intros(3))

lemma small_step_closure_last_None:
  "small_step_closure p1 s1 tr p2 s2 \<Longrightarrow> small_step p2 s2 None p3 s3 \<Longrightarrow>
   small_step_closure p1 s1 tr p3 s3"
  apply (induction rule: small_step_closure.induct)
  by (auto simp add: small_step_closure.intros)

lemma small_step_closure_last_Some:
  "small_step_closure p1 s1 tr p2 s2 \<Longrightarrow> small_step p2 s2 (Some ev) p3 s3 \<Longrightarrow>
   small_step_closure p1 s1 (tr @ [ev]) p3 s3"
  apply (induction rule: small_step_closure.induct)
  by (auto simp add: small_step_closure.intros)

lemma small_step_closure_seq:
  "small_step_closure p1 s1 tr p1' s2 \<Longrightarrow> small_step_closure (Seq p1 p2) s1 tr (Seq p1' p2) s2"
  apply (induction rule: small_step_closure.induct)
    apply (rule small_step_closure.intros)
  using seqS1 small_step_closure.intros(2) apply blast
  using seqS1 small_step_closure.intros(3) by blast

theorem big_to_small:
  "big_step p s1 tr s2 \<Longrightarrow> small_step_closure p s1 tr Skip s2"
proof (induction rule: big_step.induct)
  case (skipB s)
  then show ?case
    by (rule small_step_closure.intros)
next
  case (assignB var e s)
  then show ?case
    apply (rule small_step_closure.intros)
     apply (rule small_step.intros)
    by (rule small_step_closure.intros)
next
  case (seqB p1 s1 tr1 s2 p2 tr2 s3)
  show ?case
    apply (rule small_step_closure_trans)
     prefer 2 apply (rule seqB(4))
    apply (rule small_step_closure_last_None)
     apply (rule small_step_closure_seq[OF seqB(3)])
    by (rule seqS2)
next
  case (condB1 b s1 p1 tr s2 p2)
  show ?case
    apply (rule small_step_closure.intros(2))
     apply (rule condS1) apply (rule condB1(1))
    by (rule condB1(3))
next
  case (condB2 b s1 p2 tr s2 p1)
  show ?case
    apply (rule small_step_closure.intros(2))
     apply (rule condS2) apply (rule condB2(1))
    by (rule condB2(3))
next
  case (waitB d s)
  show ?case
    apply (rule small_step_closure_single_Some)
    apply (rule waitS2) by (rule waitB)
next
  case (sendB1 ch e s)
  then show ?case
    apply (rule small_step_closure_single_Some)
    by (rule sendS1)
next
  case (sendB2 d ch e s)
  show ?case
    apply (rule small_step_closure.intros(3))
     apply (rule sendS2) apply (rule sendB2)
    apply (rule small_step_closure_single_Some)
    by (rule sendS1)
next
  case (receiveB1 ch var s v)
  then show ?case
    apply (rule small_step_closure_single_Some)
    by (rule receiveS1)
next
  case (receiveB2 d ch var s v)
  show ?case
    apply (rule small_step_closure.intros(3))
     apply (rule receiveS2) apply (rule receiveB2)
    apply (rule small_step_closure_single_Some)
    by (rule receiveS1)
next
  case (IChoiceB1 p1 s1 tr s2 p2)
  show ?case
    apply (rule small_step_closure.intros(2))
     prefer 2 apply (rule IChoiceB1(2))
    by (rule IChoiceS1)
next
  case (IChoiceB2 p2 s1 tr s2 p1)
  show ?case
    apply (rule small_step_closure.intros(2))
     prefer 2 apply (rule IChoiceB2(2))
    by (rule IChoiceS2)
next
  case (EChoiceSendB1 i cs ch e p2 s1 tr2 s2)
  show ?case
    apply (rule small_step_closure.intros(3))
     apply (rule EChoiceS2[OF EChoiceSendB1(1,2)])
    by (rule EChoiceSendB1(4))
next
  case (EChoiceSendB2 d i cs ch e p2 s1 tr2 s2)
  show ?case
    apply (rule small_step_closure.intros(3))
    apply (rule EChoiceS1[OF EChoiceSendB2(1)])
    apply (rule small_step_closure.intros(3))
     apply (rule EChoiceS2[OF EChoiceSendB2(2,3)])
    by (rule EChoiceSendB2(5))
next
  case (EChoiceReceiveB1 i cs ch var p2 s1 v tr2 s2)
  show ?case
    apply (rule small_step_closure.intros(3))
     apply (rule EChoiceS3[OF EChoiceReceiveB1(1,2)])
    by (rule EChoiceReceiveB1(4))
next
  case (EChoiceReceiveB2 d i cs ch var p2 s1 v tr2 s2)
  show ?case
    apply (rule small_step_closure.intros(3))
    apply (rule EChoiceS1[OF EChoiceReceiveB2(1)])
    apply (rule small_step_closure.intros(3))
     apply (rule EChoiceS3[OF EChoiceReceiveB2(2,3)])
    by (rule EChoiceReceiveB2(5))
next
  case (RepetitionB1 p s)
  then show ?case
    apply (rule small_step_closure_single_None)
    by (rule RepetitionS1)
next
  case (RepetitionB2 p s1 tr1 s2 tr2 s3 tr)
  show ?case
    apply (subst RepetitionB2(3))
    apply (rule small_step_closure.intros(2))
     apply (rule RepetitionS2)
    apply (rule small_step_closure_trans)
     apply (rule small_step_closure_seq[OF RepetitionB2(4)])
    apply (rule small_step_closure.intros(2))
     apply (rule seqS2)
    by (rule RepetitionB2(5))
next
  case (ContB1 b s ode)
  show ?case
    apply (rule small_step_closure_single_None)
    apply (rule ContS2) by (rule ContB1)
next
  case (ContB2 d ode p b s1)
  show ?case
    apply (rule small_step_closure.intros(3))
     apply (rule ContS1[OF ContB2(1-3,5)])
    apply (rule small_step_closure_single_None)
    apply (rule ContS2) by (rule ContB2(4))
next
  case (InterruptSendB1 i cs ch e p2 s tr2 s2 ode b)
  show ?case
    apply (rule small_step_closure.intros(3))
     apply (rule InterruptS3[OF InterruptSendB1(1,2)])
    by (rule InterruptSendB1(4))
next
  case (InterruptSendB2 d ode p s1 b i cs ch e p2 rdy tr2 s2)
  show ?case
    apply (subst InterruptSendB2(7))
    apply (rule small_step_closure.intros(3))
     apply (rule InterruptS1)
        apply (auto simp add: InterruptSendB2)
    apply (rule small_step_closure.intros(3))
     apply (rule InterruptS3[OF InterruptSendB2(5,6)])
    by (rule InterruptSendB2(9))
next
  case (InterruptReceiveB1 i cs ch var p2 s v tr2 s2 ode b)
  show ?case
    apply (rule small_step_closure.intros(3))
     apply (rule InterruptS4[OF InterruptReceiveB1(1,2)])
    by (rule InterruptReceiveB1(4))
next
  case (InterruptReceiveB2 d ode p s1 b i cs ch var p2 rdy v tr2 s2)
  show ?case
    apply (subst InterruptReceiveB2(7))
    apply (rule small_step_closure.intros(3))
     apply (rule InterruptS1)
        apply (auto simp add: InterruptReceiveB2)
    apply (rule small_step_closure.intros(3))
     apply (rule InterruptS4[OF InterruptReceiveB2(5,6)])
    by (rule InterruptReceiveB2(9))
next
  case (InterruptB1 b s ode cs)
  show ?case
    apply (rule small_step_closure_single_None)
    apply (rule InterruptS2) by (rule InterruptB1)
next
  case (InterruptB2 d ode p b s1 s2 rdy cs)
  show ?case
    apply (subst InterruptB2(7))
    apply (rule small_step_closure.intros(3))
     apply (rule InterruptS1)
        apply (auto simp add: InterruptB2)
    apply (rule small_step_closure_single_None)
    apply (rule InterruptS2)
    apply (subst InterruptB2(6)[symmetric])
    by (auto simp add: InterruptB2(4))
qed

text \<open>Divide into two parts: first event is None, and first event is Some ev\<close>

lemma small1_big_continue:
  "small_step p1 s1 ev p2 s2 \<Longrightarrow> ev = None \<Longrightarrow> big_step p2 s2 tr2 s3 \<Longrightarrow>
   big_step p1 s1 tr2 s3"
proof (induction arbitrary: tr2 s3 rule: small_step.induct)
  case (assignB var e s)
  have tr2: "tr2 = []"
    using assignB(2) apply (rule skipE) by auto
  have s3: "s3 = s(var := e s)"
    using assignB(2) apply (rule skipE) by auto
  show ?case
    apply (simp only: tr2 s3) by (rule big_step.assignB)
next
  case (seqS1 p1 s ev p1' s2 p2)
  obtain tr21 s2' tr22 where
    a: "tr2 = tr21 @ tr22" "big_step p1' s2 tr21 s2'" "big_step p2 s2' tr22 s3"
    using seqE[OF seqS1(4)] by metis
  have b: "big_step p1 s tr21 s2'"
    by (auto simp add: seqS1 a)
  show ?case
    using a b seqB by auto
next
  case (seqS2 p s)
  show ?case
    using seqB seqS2.prems(2) skipB by fastforce
next
  case (condS1 b s p1 p2)
  then show ?case
    using condB1 by auto
next
  case (condS2 b s p1 p2)
  then show ?case
    using condB2 by auto
next
  case (IChoiceS1 p1 p2 s)
  then show ?case
    using IChoiceB1 by auto
next
  case (IChoiceS2 p1 p2 s)
  then show ?case
    using IChoiceB2 by auto
next
  case (RepetitionS1 p s)
  then show ?case
    using RepetitionB1 skipE by blast
next
  case (RepetitionS2 p s)
  then show ?case
    by (metis RepetitionB2 seqE)
next
  case (ContS2 b s ode)
  then show ?case
    using ContB1 skipE by blast
next
  case (InterruptS2 b s ode cs)
  then show ?case
    using InterruptB1 skipE by blast
qed (auto)


lemma small1_big_continue2:
  "small_step p1 s1 evt p2 s2 \<Longrightarrow> evt = Some ev \<Longrightarrow> big_step p2 s2 tr2 s3 \<Longrightarrow>
   \<exists>tr2'. equiv_trace (ev # tr2) tr2' \<and> big_step p1 s1 tr2' s3"
proof (induction arbitrary: tr2 s3 rule: small_step.induct)
  case (seqS1 p1 s ev2 p1' s2 p2)
  obtain tr21 s2' tr22 where
    a: "tr2 = tr21 @ tr22" "big_step p1' s2 tr21 s2'" "big_step p2 s2' tr22 s3"
    using seqE[OF seqS1(4)] by metis
  obtain tr2' where
    b: "equiv_trace (ev # tr21) tr2'" "big_step p1 s tr2' s2'"
    using seqS1(2)[OF seqS1(3) a(2)] by blast
  show ?case
    apply (rule exI[where x="tr2' @ tr22"])
    apply auto
    unfolding a(1)
    using b(1) equiv_trace.intros(5) apply fastforce
    by (rule seqB[OF b(2) a(3)])
next
  case (waitS1 d1 d s)
  have a: "tr2 = [WaitBlock (d - d1) (\<lambda>\<tau>\<in>{0..d - d1}. State s) ({}, {})]" "s3 = s" "0 < d - d1"
    using waitE[OF waitS1(4)] by auto
  have b: "ev = WaitBlock d1 (\<lambda>\<tau>\<in>{0..d1}. State s) ({}, {})"
    using waitS1(3) by auto
  have c: "WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {}) =
           WaitBlock (d1 + (d - d1)) (\<lambda>\<tau>\<in>{0..d1+(d-d1)}. if \<tau> < d1 then State s else State s) ({}, {})"
    by auto
  show ?case
    apply (rule exI[where x="[WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})]"])
    unfolding a b apply auto
    unfolding c apply (rule equiv_trace_merge) apply auto
     apply (rule waitB)
    using waitS1 by auto
next
  case (waitS2 d s)
  have a: "ev = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})"
    using waitS2(2) by auto
  have b: "tr2 = []"
    using waitS2(3) apply (rule skipE) by auto
  have c: "s3 = s"
    using waitS2(3) apply (rule skipE) by auto
  show ?case
    unfolding a b c
    apply (rule exI[where x="[WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})]"])
    apply auto
    apply (rule waitB) by (rule waitS2(1))
next
  case (sendS1 ch e s)
  have a: "ev = OutBlock ch (e s)"
    using sendS1(1) by auto
  have b: "tr2 = []"
    using sendS1(2) apply (rule skipE) by auto
  have c: "s3 = s"
    using sendS1(2) apply (rule skipE) by auto
  show ?case
    unfolding a b c
    apply (rule exI[where x="[OutBlock ch (e s)]"])
    apply auto
    by (rule sendB1)
next
  case (sendS2 d ch e s)
  have a: "ev = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {})"
    using sendS2(2) by auto
  have b: "equiv_trace [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) ({ch}, {}), OutBlock ch (e s)]
           [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State s) ({ch}, {}), OutBlock ch (e s)]" (is "equiv_trace ?lhs ?rhs") for d2
  proof -
    have b1: "?lhs = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) ({ch}, {})] @ [OutBlock ch (e s)]"
      by auto
    have b2: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State s else State s) ({ch}, {})] @ [OutBlock ch (e s)]"
      by auto
    show ?thesis
      unfolding b1 b2 apply (rule equiv_trace_append)
      apply (rule equiv_trace_merge) by auto
  qed
  show ?case
    using sendS2(3) apply (elim sendE)
    subgoal
      apply (rule exI[where x="[WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), OutBlock ch (e s)]"])
      apply (auto simp add: a)
      apply (rule sendB2) by (rule sendS2(1))
    subgoal for d2
      apply (rule exI[where x="[WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d+d2}. State s) ({ch}, {}), OutBlock ch (e s)]"])
      apply (auto simp add: a)
      subgoal by (rule b)
      apply (rule sendB2) using sendS2(1) by auto
    done
next
  case (receiveS1 ch var s v)
  have a: "ev = InBlock ch v"
    using receiveS1(1) by auto
  have b: "tr2 = []"
    using receiveS1(2) apply (rule skipE) by auto
  have c: "s3 = s(var := v)"
    using receiveS1(2) apply (rule skipE) by auto
  show ?case
    unfolding a b c
    apply (rule exI[where x="[InBlock ch v]"])
    using equiv_trace_refl receiveB1 by blast
next
  case (receiveS2 d ch var s)
  have a: "ev = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch})"
    using receiveS2(2) by auto
  have b: "equiv_trace [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) ({}, {ch}), InBlock ch v]
           [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State s) ({}, {ch}), InBlock ch v]" (is "equiv_trace ?lhs ?rhs") for v d2
  proof -
    have b1: "?lhs = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) ({}, {ch})] @ [InBlock ch v]"
      by auto
    have b2: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State s else State s) ({}, {ch})] @ [InBlock ch v]"
      by auto
    show ?thesis
      unfolding b1 b2 apply (rule equiv_trace_append)
      apply (rule equiv_trace_merge) by auto
  qed
  show ?case
    using receiveS2(3) apply (elim receiveE)
    subgoal for v
      apply (rule exI[where x="[WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), InBlock ch v]"])
      apply (auto simp add: a)
      apply (subst fun_upd_def[symmetric])
      apply (rule receiveB2) by (rule receiveS2(1))
    subgoal for d2 v
      apply (rule exI[where x="[WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d+d2}. State s) ({}, {ch}), InBlock ch v]"])
      apply (auto simp add: a)
      subgoal by (rule b)
      apply (subst fun_upd_def[symmetric])
      apply (rule receiveB2) using receiveS2(1) by auto
    done
next
  case (EChoiceS1 d cs s)
  have a: "ev = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice cs)"
    using EChoiceS1(2) by auto
  have b: "equiv_trace
     (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice cs) #
      WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) (rdy_of_echoice cs) # OutBlock ch (e s) # tr2')
     (WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State s) (rdy_of_echoice cs) # OutBlock ch (e s) # tr2')"
    (is "equiv_trace ?lhs ?rhs") for d2 ch e tr2'
  proof -
    have b1: "?lhs = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice cs), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) (rdy_of_echoice cs)]
                @ (OutBlock ch (e s) # tr2')"
      by auto
    have b2: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State s else State s) (rdy_of_echoice cs)]
                @ (OutBlock ch (e s) # tr2')"
      by auto
    show ?thesis
      unfolding b1 b2 apply (rule equiv_trace_append)
      apply (rule equiv_trace_merge) by auto
  qed
  have c: "equiv_trace
     (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice cs) #
      WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) (rdy_of_echoice cs) # InBlock ch v # tr2')
     (WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State s) (rdy_of_echoice cs) # InBlock ch v # tr2')"
    (is "equiv_trace ?lhs ?rhs") for d2 ch v tr2'
  proof -
    have c1: "?lhs = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice cs), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) (rdy_of_echoice cs)]
                @ (InBlock ch v # tr2')"
      by auto
    have c2: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State s else State s) (rdy_of_echoice cs)] @ (InBlock ch v # tr2')"
      by auto
    show ?thesis
      unfolding c1 c2
      apply (rule equiv_trace_append)
      apply (rule equiv_trace_merge) by auto
  qed
  show ?case
    using EChoiceS1(3) apply (elim echoiceE)
    subgoal for i ch e p2 tr2'
      apply (rule exI[where x="WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice cs) # OutBlock ch (e s) # tr2'"])
      unfolding a apply auto apply (rule EChoiceSendB2)
      by (auto simp add: EChoiceS1)
    subgoal for d2 i ch e p2 tr2'
      apply (rule exI[where x="WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d+d2}. State s) (rdy_of_echoice cs) # OutBlock ch (e s) # tr2'"])
      unfolding a apply auto subgoal by (rule b)
      apply (rule EChoiceSendB2)
         apply (auto simp add: EChoiceS1)
      using EChoiceS1(1) by auto
    subgoal for i ch var p2 v tr2'
      apply (rule exI[where x="WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice cs) # InBlock ch v # tr2'"])
      unfolding a apply auto apply (rule EChoiceReceiveB2)
      by (auto simp add: EChoiceS1)
    subgoal for d2 i ch var p2 v tr2'
      apply (rule exI[where x="WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d+d2}. State s) (rdy_of_echoice cs) # InBlock ch v # tr2'"])
      unfolding a apply auto subgoal by (rule c)
      apply (rule EChoiceReceiveB2)
         apply (auto simp add: EChoiceS1)
      using EChoiceS1(1) by auto
    done
next
  case (EChoiceS2 i cs ch e p2 s)
  have a: "ev = OutBlock ch (e s)"
    using EChoiceS2(3) by auto
  show ?case
    unfolding a
    apply (rule exI[where x="OutBlock ch (e s) # tr2"])
    apply auto
    by (rule EChoiceSendB1[OF EChoiceS2(1,2,4)])
next
  case (EChoiceS3 i cs ch var p2 s v)
  have a: "ev = InBlock ch v"
    using EChoiceS3(3) by auto
  show ?case
    unfolding a
    apply (rule exI[where x="InBlock ch v # tr2"])
    apply auto
    by (rule EChoiceReceiveB1[OF EChoiceS3(1,2,4)])
next
  case (ContS1 d ode p b s)
  have a: "ev = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})"
    using ContS1(5) by auto
  have b: "big_step (Cont ode b) s [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) ({}, {})] (p2 d2)"
    if "d2 > 0" "ODEsol ode p2 d2" "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t)" "\<not> b (p2 d2)" "p2 0 = p d" for p2 d2
  proof -
    let ?p3="\<lambda>\<tau>. if \<tau> < d then p \<tau> else p2 (\<tau> - d)"
    have c: "p2 d2 = ?p3 (d + d2)"
      using that by auto
    show ?thesis
      unfolding c apply (rule ContB2)
      subgoal using ContS1(1) that by auto
      subgoal using ContS1(2) that(2,5) by (rule ODEsol_merge)
      subgoal using ContS1(1,3) that(1,3) by auto
      subgoal using that(1,4) by auto
      subgoal using ContS1(1,4) by auto
      done
  qed
  have c: "equiv_trace [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {}), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) ({}, {})]
     [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) ({}, {})]"
    (is "equiv_trace ?lhs ?rhs") if "p2 0 = p d" for d2 p2       
  proof -
    have c1: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State (p \<tau>) else State (p2 (\<tau> - d))) ({}, {})]"
      by auto
    show ?thesis
      unfolding c1 apply (rule equiv_trace_merge)
      using that by auto
  qed
  show ?case
    using ContS1(6) apply (elim contE)
    subgoal
      apply (rule exI[where x="[WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})]"])
      unfolding a apply auto
      apply (rule ContB2) using ContS1 by auto
    subgoal for d2 p2
      apply (rule exI[where x="[WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d+d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) ({}, {})]"])
      unfolding a apply auto
      subgoal by (rule c)
      using b by auto
    done
next
  case (InterruptS1 d ode p b s cs)
  have a: "ev = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs)"
    using InterruptS1(5) by auto
  have b: "big_step (Interrupt ode b cs) s
     (WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs) # OutBlock ch (e (p2 d2)) # tr2') s3"
    if "d2 > 0" "ODEsol ode p2 d2" "p2 0 = p d" "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t)"
       "i < length cs" "cs ! i = (ch[!]e, p3)" "big_step p3 (p2 d2) tr2' s3" for d2 p2 ch e tr2' i p3
  proof -
    let ?p3="\<lambda>\<tau>. if \<tau> < d then p \<tau> else p2 (\<tau> - d)"
    have b1: "p2 d2 = ?p3 (d + d2)"
      using that by auto
    show ?thesis
      unfolding b1 apply (rule InterruptSendB2[OF _ _ _ _ that(5,6)])
      subgoal using that(1) InterruptS1(1) by auto
      subgoal using InterruptS1(2) that(2,3) by (rule ODEsol_merge)
      subgoal using InterruptS1(1,4) by auto
      subgoal using that(4) InterruptS1(3) by auto
      subgoal by simp
      subgoal using that(1,7) by auto
      done 
  qed
  have c: "big_step (Interrupt ode b cs) s
     (WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs) # InBlock ch v # tr2') s3"
    if "0 < d2" "ODEsol ode p2 d2" "p2 0 = p d" "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t)"
       "i < length cs" "cs ! i = (ch[?]var, p3)" "big_step p3 ((p2 d2)(var := v)) tr2' s3" for d2 p2 ch v tr2' i var p3
  proof -
    let ?p3="\<lambda>\<tau>. if \<tau> < d then p \<tau> else p2 (\<tau> - d)"
    have c1: "p2 d2 = ?p3 (d + d2)"
      using that by auto
    show ?thesis
      unfolding c1 apply (rule InterruptReceiveB2[OF _ _ _ _ that(5,6)])
      subgoal using that(1) InterruptS1(1) by auto
      subgoal using InterruptS1(2) that(2,3) by (rule ODEsol_merge)
      subgoal using InterruptS1(1,4) by auto
      subgoal using that(4) InterruptS1(3) by auto
      subgoal by simp
      subgoal using that(1,7) by auto
      done
  qed
  have d: "big_step (Interrupt ode b cs) s
     [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs)] (p2 d2)"
    if "0 < d2" "ODEsol ode p2 d2" "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t)" "\<not> b (p2 d2)" "p2 0 = p d" for d2 p2
  proof -
    let ?p3="\<lambda>\<tau>. if \<tau> < d then p \<tau> else p2 (\<tau> - d)"
    have d1: "p2 d2 = ?p3 (d + d2)"
      using that by auto
    show ?thesis
      unfolding d1 apply (rule InterruptB2)
      subgoal using that(1) InterruptS1(1) by auto
      subgoal using InterruptS1(2) that(2,5) by (rule ODEsol_merge)
      subgoal using that(3) InterruptS1(3) by auto
      subgoal using that(1,4) by auto
      subgoal using InterruptS1(1,4) by auto
      by auto
  qed
  have e: "equiv_trace
     (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs) #
      WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (p2 d2)) # tr2')
     (WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs) # OutBlock ch (e (p2 d2)) # tr2')"
    (is "equiv_trace ?lhs ?rhs") if "p2 0 = p d" for d2 p2 ch e tr2'
  proof -
    have e1: "?lhs = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) (rdy_of_echoice cs)]
                @ (OutBlock ch (e (p2 d2)) # tr2')"
      by auto
    have e2: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State (p \<tau>) else State (p2 (\<tau> - d))) (rdy_of_echoice cs)]
                @ (OutBlock ch (e (p2 d2)) # tr2')"
      by auto
    show ?thesis
      unfolding e1 e2 apply (rule equiv_trace_append)
      apply (rule equiv_trace_merge)
      using that by auto
  qed
  have f: "equiv_trace
     (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs) # WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr2')
     (WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs) # InBlock ch v # tr2')"
    (is "equiv_trace ?lhs ?rhs") if "p2 0 = p d" for d2 p2 ch v tr2'
  proof -
    have f1: "?lhs = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) (rdy_of_echoice cs)]
                @ (InBlock ch v # tr2')"
      by auto
    have f2: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State (p \<tau>) else State (p2 (\<tau> - d))) (rdy_of_echoice cs)]
                @ (InBlock ch v # tr2')"
      by auto
    show ?thesis
      unfolding f1 f2 apply (rule equiv_trace_append)
      apply (rule equiv_trace_merge)
      using that by auto
  qed
  have g: "equiv_trace [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) (rdy_of_echoice cs)]
     [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs)]"
    (is "equiv_trace ?lhs ?rhs") if "p2 0 = p d" for d2 p2
  proof -
    have g1: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State (p \<tau>) else State (p2 (\<tau> - d))) (rdy_of_echoice cs)]"
      by auto
    show ?thesis
      unfolding g1 apply (rule equiv_trace_merge)
      using that by auto
  qed
  show ?case
    using InterruptS1(6) apply (elim interruptE)
    subgoal for i ch e p2 tr2'
      apply (rule exI[where x="WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (p d)) # tr2'"])
      unfolding a apply auto apply (rule InterruptSendB2)
      by (auto simp add: InterruptS1)
    subgoal for d2 p2 i ch e p3 tr2'
      apply (rule exI[where x="WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d+d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs) #
                               OutBlock ch (e (p2 d2)) # tr2'"])
      unfolding a apply auto
      subgoal by (rule e)
      using b by auto
    subgoal for i ch var p2 v tr2'
      apply (rule exI[where x="WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr2'"])
      unfolding a apply auto apply (rule InterruptReceiveB2)
      by (auto simp add: InterruptS1)
    subgoal for d2 p2 i ch var p3 v tr2'
      apply (rule exI[where x="WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d+d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs) #
                               InBlock ch v # tr2'"])
      unfolding a apply auto
      subgoal by (rule f)
      using c by auto
    subgoal
      apply (rule exI[where x="[WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs)]"])
      unfolding a apply auto
      apply (rule InterruptB2)
      by (auto simp add: InterruptS1)
    subgoal for d2 p2
      apply (rule exI[where x="[WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d+d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs)]"])
      unfolding a apply auto
      subgoal by (rule g)
      using d by auto
    done
next
  case (InterruptS3 i cs ch e p2 ode b s)
  have a: "ev = OutBlock ch (e s)"
    using InterruptS3(3) by auto
  show ?case
    unfolding a
    apply (rule exI[where x="OutBlock ch (e s) # tr2"])
    apply auto
    by (rule InterruptSendB1[OF InterruptS3(1,2,4)])
next
  case (InterruptS4 i cs ch var p2 ode b s v)
  have a: "ev = InBlock ch v"
    using InterruptS4(3) by auto
  show ?case
    unfolding a
    apply (rule exI[where x="InBlock ch v # tr2"])
    apply auto
    by (rule InterruptReceiveB1[OF InterruptS4(1,2,4)])
qed (auto)


theorem small_to_big:
  "small_step_closure p s1 tr q s2 \<Longrightarrow> q = Skip \<Longrightarrow> \<exists>tr'. equiv_trace tr tr' \<and> big_step p s1 tr' s2"
proof (induction rule: small_step_closure.induct)
  case (1 p s)
  show ?case
    apply (rule exI[where x="[]"])
    by (auto simp add: 1 skipB)
next
  case (2 p s p2 s2 evs p3 s3)
  then show ?case
    using small1_big_continue by auto    
next
  case (3 p s ev p2 s2 evs p3 s3)
  obtain tr' where tr: "equiv_trace evs tr'" "big_step p2 s2 tr' s3"
    using 3(3,4) by auto
  obtain tr2' where tr2: "equiv_trace (ev # tr') tr2'" "big_step p s tr2' s3"
    using small1_big_continue2[OF 3(1) _ tr(2)] by auto
  show ?case
    apply (rule exI[where x=tr2'])
    apply auto
    using equiv_trace_cons equiv_trace_trans tr(1) tr2(1) apply blast
    by (rule tr2(2))    
qed

text \<open>Small-step generating WaitBlock can always be split into two smaller WaitBlocks\<close>

lemma small_step_split:
  "small_step p1 s1 (Some (WaitBlock t2 hist rdy)) p2 s2 \<Longrightarrow>
   0 < t1 \<Longrightarrow> t1 < t2 \<Longrightarrow>
   \<exists>p' s'. small_step p1 s1 (Some (WaitBlock t1 (\<lambda>\<tau>\<in>{0..t1}. hist \<tau>) rdy)) p' s' \<and>
           small_step p' s' (Some (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2-t1}. hist (\<tau> + t1)) rdy)) p2 s2"
proof (induct p1 s1 "Some (WaitBlock t2 hist rdy)" p2 s2 rule: small_step.induct)
  case (seqS1 c1 s c1' s2 c2)
  obtain p' s' where a:
    "small_step c1 s (Some (WaitBlock t1 (restrict hist {0..t1}) rdy)) p' s'"
    "small_step p' s' (Some (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2 - t1}. hist (\<tau> + t1)) rdy)) c1' s2"
    using seqS1 by auto
  show ?case
    apply (rule exI[where x="p'; c2"]) apply (rule exI[where x=s'])
    apply auto 
     apply (rule small_step.seqS1[OF a(1)])
    by (rule small_step.seqS1[OF a(2)])
next
  case (waitS1 d s)
  have a: "restrict hist {0..t1} = (\<lambda>\<tau>\<in>{0..t1}. State s)"
    unfolding waitS1(3)[symmetric] using waitS1(5,6) by auto
  have b: "(\<lambda>\<tau>\<in>{0..t2-t1}. hist (\<tau> + t1)) = (\<lambda>\<tau>\<in>{0..t2-t1}. State s)"
    unfolding waitS1(3)[symmetric] using waitS1(5,6) by auto
  have c: "d - t2 = (d - t1) - (t2 - t1)" by auto
  show ?case
    apply (rule exI[where x="Wait (d - t1)"]) apply (rule exI[where x=s])
    unfolding a b waitS1(4)[symmetric] apply auto
    subgoal
      apply (rule small_step.waitS1) using waitS1 by auto
    subgoal
      unfolding c apply (rule small_step.waitS1) using waitS1 by auto
    done
next
  case (waitS2 s)
  have a: "restrict hist {0..t1} = (\<lambda>\<tau>\<in>{0..t1}. State s)"
    unfolding waitS2(2)[symmetric] using waitS2(4,5) by auto
  have b: "(\<lambda>\<tau>\<in>{0..t2-t1}. hist (\<tau> + t1)) = (\<lambda>\<tau>\<in>{0..t2-t1}. State s)"
    unfolding waitS2(2)[symmetric] using waitS2(4,5) by auto
  show ?case
    apply (rule exI[where x="Wait (t2 - t1)"])
    apply (rule exI[where x=s])
    unfolding a b waitS2(3)[symmetric] apply auto
    subgoal
      apply (rule small_step.waitS1) using waitS2 by auto
    subgoal
      apply (rule small_step.waitS2) using waitS2 by auto
    done
next
  case (sendS2 ch e s)
  have a: "restrict hist {0..t1} = (\<lambda>\<tau>\<in>{0..t1}. State s)"
    unfolding sendS2(2)[symmetric] using sendS2(4,5) by auto
  have b: "(\<lambda>\<tau>\<in>{0..t2-t1}. hist (\<tau> + t1)) = (\<lambda>\<tau>\<in>{0..t2-t1}. State s)"
    unfolding sendS2(2)[symmetric] using sendS2(4,5) by auto
  show ?case
    apply (rule exI[where x="Cm (ch[!]e)"])
    apply (rule exI[where x=s])
    unfolding a b sendS2(3)[symmetric] apply auto
    subgoal
      apply (rule small_step.sendS2) using sendS2 by auto
    subgoal
      apply (rule small_step.sendS2) using sendS2 by auto
    done
next
  case (receiveS2 ch var s)
  have a: "restrict hist {0..t1} = (\<lambda>\<tau>\<in>{0..t1}. State s)"
    unfolding receiveS2(2)[symmetric] using receiveS2(4,5) by auto
  have b: "(\<lambda>\<tau>\<in>{0..t2-t1}. hist (\<tau> + t1)) = (\<lambda>\<tau>\<in>{0..t2-t1}. State s)"
    unfolding receiveS2(2)[symmetric] using receiveS2(4,5) by auto
  show ?case
    apply (rule exI[where x="Cm (ch[?]var)"])
    apply (rule exI[where x=s])
    unfolding a b receiveS2(3)[symmetric] apply auto
    subgoal
      apply (rule small_step.receiveS2) using receiveS2 by auto
    subgoal
      apply (rule small_step.receiveS2) using receiveS2 by auto
    done
next
  case (EChoiceS1 cs s)
  have a: "restrict hist {0..t1} = (\<lambda>\<tau>\<in>{0..t1}. State s)"
    unfolding EChoiceS1(2)[symmetric] using EChoiceS1(4,5) by auto
  have b: "(\<lambda>\<tau>\<in>{0..t2-t1}. hist (\<tau> + t1)) = (\<lambda>\<tau>\<in>{0..t2-t1}. State s)"
    unfolding EChoiceS1(2)[symmetric] using EChoiceS1(4,5) by auto
  show ?case
    apply (rule exI[where x="EChoice cs"])
    apply (rule exI[where x=s])
    unfolding a b EChoiceS1(3)[symmetric] apply auto
    subgoal
      apply (rule small_step.EChoiceS1) using EChoiceS1 by auto
    subgoal
      apply (rule small_step.EChoiceS1) using EChoiceS1 by auto
    done
next
  case (ContS1 ode p b s)
  have a: "restrict hist {0..t1} = (\<lambda>\<tau>\<in>{0..t1}. State (p \<tau>))"
    unfolding ContS1(5)[symmetric] using ContS1(7,8) by auto
  have b: "(\<lambda>\<tau>\<in>{0..t2 - t1}. hist (\<tau> + t1)) = (\<lambda>\<tau>\<in>{0..t2-t1}. State (p (\<tau> + t1)))"
    unfolding ContS1(5)[symmetric] using ContS1(7,8) by auto
  have c: "p t2 = (\<lambda>t. p (t + t1)) (t2 - t1)"
    by auto
  show ?case
    apply (rule exI[where x="Cont ode b"])
    apply (rule exI[where x="p t1"])
    unfolding a b ContS1(6)[symmetric] apply auto
    subgoal
      apply (rule small_step.ContS1)
         apply (simp add: ContS1.prems(1))
      using ContS1 ODEsol_split(1) apply auto[1]
      using ContS1 apply auto[1]
      by (simp add: ContS1.hyps(4))
    subgoal
      unfolding c apply (rule small_step.ContS1)
         apply (simp add: ContS1.prems(2))
        apply (simp add: ContS1 ODEsol_split(2))
      using ContS1 apply auto[1]
      by simp
    done
next
  case (InterruptS1 ode p b s cs)
  have a: "restrict hist {0..t1} = (\<lambda>\<tau>\<in>{0..t1}. State (p \<tau>))"
    unfolding InterruptS1(5)[symmetric] using InterruptS1(7,8) by auto
  have b: "(\<lambda>\<tau>\<in>{0..t2 - t1}. hist (\<tau> + t1)) = (\<lambda>\<tau>\<in>{0..t2-t1}. State (p (\<tau> + t1)))"
    unfolding InterruptS1(5)[symmetric] using InterruptS1(7,8) by auto
  have c: "p t2 = (\<lambda>t. p (t + t1)) (t2 - t1)"
    by auto
  show ?case
    apply (rule exI[where x="Interrupt ode b cs"])
    apply (rule exI[where x="p t1"])
    unfolding a b InterruptS1(6)[symmetric] apply auto
    subgoal
      apply (rule small_step.InterruptS1)
         apply (simp add: InterruptS1.prems(1))
      using InterruptS1 ODEsol_split(1) apply auto[1]
      using InterruptS1 apply auto[1]
      by (simp add: InterruptS1.hyps(4))
    subgoal
      unfolding c apply (rule small_step.InterruptS1)
         apply (simp add: InterruptS1.prems(2))
        apply (simp add: InterruptS1 ODEsol_split(2))
      using InterruptS1 apply auto[1]
      by simp
    done
qed


subsection \<open>Parallel case\<close>

text \<open>Small step semantics for parallel processes.\<close>

inductive par_small_step :: "pproc \<Rightarrow> gstate \<Rightarrow> trace_block option \<Rightarrow> pproc \<Rightarrow> gstate \<Rightarrow> bool" where
  SingleS: "small_step p s1 ev p' s2 \<Longrightarrow> par_small_step (Single p) (State s1) ev (Single p') (State s2)"
| ParDelayS:
    "compat_rdy rdy1 rdy2 \<Longrightarrow>
     hist = (\<lambda>\<tau>\<in>{0..t}. ParState (hist1 \<tau>) (hist2 \<tau>)) \<Longrightarrow>
     rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
     par_small_step p1 s1 (Some (WaitBlock t hist1 rdy1)) p2 s2 \<Longrightarrow>
     par_small_step p3 s3 (Some (WaitBlock t hist2 rdy2)) p4 s4 \<Longrightarrow>
     par_small_step (Parallel p1 chs p3) (ParState s1 s3) (Some (WaitBlock t hist rdy)) (Parallel p2 chs p4) (ParState s2 s4)"
| ParTauS1:
    "par_small_step p1 s1 None p2 s2 \<Longrightarrow>
     par_small_step (Parallel p1 chs p3) (ParState s1 s3) None (Parallel p2 chs p3) (ParState s2 s3)"
| ParTauS2:
    "par_small_step p2 s2 None p3 s3 \<Longrightarrow>
     par_small_step (Parallel p1 chs p2) (ParState s1 s2) None (Parallel p1 chs p3) (ParState s1 s3)"
| ParPairS1:
    "ch \<in> chs \<Longrightarrow>
     par_small_step p1 s1 (Some (InBlock ch v)) p2 s2 \<Longrightarrow>
     par_small_step p3 s3 (Some (OutBlock ch v)) p4 s4 \<Longrightarrow>
     par_small_step (Parallel p1 chs p3) (ParState s1 s3) (Some (IOBlock ch v)) (Parallel p2 chs p4) (ParState s2 s4)"
| ParPairS2:
    "ch \<in> chs \<Longrightarrow>
     par_small_step p1 s1 (Some (OutBlock ch v)) p2 s2 \<Longrightarrow>
     par_small_step p3 s3 (Some (InBlock ch v)) p4 s4 \<Longrightarrow>
     par_small_step (Parallel p1 chs p3) (ParState s1 s3) (Some (IOBlock ch v)) (Parallel p2 chs p4) (ParState s2 s4)"
| ParUnpairS1:
    "ch \<notin> chs \<Longrightarrow>
     par_small_step p1 s1 (Some (InBlock ch v)) p2 s2 \<Longrightarrow>
     par_small_step (Parallel p1 chs p3) (ParState s1 s3) (Some (InBlock ch v)) (Parallel p2 chs p3) (ParState s2 s3)"
| ParUnpairS2:
    "ch \<notin> chs \<Longrightarrow>
     par_small_step p1 s1 (Some (OutBlock ch v)) p2 s2 \<Longrightarrow>
     par_small_step (Parallel p1 chs p3) (ParState s1 s3) (Some (OutBlock ch v)) (Parallel p2 chs p3) (ParState s2 s3)"
| ParUnpairS3:
    "ch \<notin> chs \<Longrightarrow>
     par_small_step p2 s2 (Some (InBlock ch v)) p3 s3 \<Longrightarrow>
     par_small_step (Parallel p1 chs p2) (ParState s1 s2) (Some (InBlock ch v)) (Parallel p1 chs p3) (ParState s1 s3)"
| ParUnpairS4:
    "ch \<notin> chs \<Longrightarrow>
     par_small_step p2 s2 (Some (OutBlock ch v)) p3 s3 \<Longrightarrow>
     par_small_step (Parallel p1 chs p2) (ParState s1 s2) (Some (OutBlock ch v)) (Parallel p1 chs p3) (ParState s1 s3)"
| ParUnpairS5:
    "ch \<notin> chs \<Longrightarrow>
     par_small_step p1 s1 (Some (IOBlock ch v)) p2 s2 \<Longrightarrow>
     par_small_step (Parallel p1 chs p3) (ParState s1 s3) (Some (IOBlock ch v)) (Parallel p2 chs p3) (ParState s2 s3)"
| ParUnpairS6:
    "ch \<notin> chs \<Longrightarrow>
     par_small_step p2 s2 (Some (IOBlock ch v)) p3 s3 \<Longrightarrow>
     par_small_step (Parallel p1 chs p2) (ParState s1 s2) (Some (IOBlock ch v)) (Parallel p1 chs p3) (ParState s1 s3)"


text \<open>Transitive closure of small step semantics\<close>
inductive par_small_step_closure :: "pproc \<Rightarrow> gstate \<Rightarrow> trace \<Rightarrow> pproc \<Rightarrow> gstate \<Rightarrow> bool" where
  "par_small_step_closure p s [] p s"
| "par_small_step p s None p2 s2 \<Longrightarrow> par_small_step_closure p2 s2 evs p3 s3 \<Longrightarrow> par_small_step_closure p s evs p3 s3"
| "par_small_step p s (Some ev) p2 s2 \<Longrightarrow> par_small_step_closure p2 s2 evs p3 s3 \<Longrightarrow> par_small_step_closure p s (ev # evs) p3 s3"

lemma par_small_step_closure_trans:
  "par_small_step_closure p1 s1 tr1 p2 s2 \<Longrightarrow>
   par_small_step_closure p2 s2 tr2 p3 s3 \<Longrightarrow>
   par_small_step_closure p1 s1 (tr1 @ tr2) p3 s3"
  apply (induction rule: par_small_step_closure.induct)
  apply simp
  using par_small_step_closure.intros(2) apply blast
  by (simp add: par_small_step_closure.intros(3))


text \<open>Definition of reachable through a sequence of tau steps\<close>
inductive par_small_step_tau_closure :: "pproc \<Rightarrow> gstate \<Rightarrow> pproc \<Rightarrow> gstate \<Rightarrow> bool" where
  "par_small_step_tau_closure p s p s"
| "par_small_step p s None p2 s2 \<Longrightarrow> par_small_step_tau_closure p2 s2 p3 s3 \<Longrightarrow> par_small_step_tau_closure p s p3 s3"


lemma par_small_step_closure_empty_to_tau [simp]:
  assumes "par_small_step_closure p1 s1 [] p2 s2"
  shows "par_small_step_tau_closure p1 s1 p2 s2"
proof -
  have "par_small_step_closure p1 s1 tr p2 s2 \<Longrightarrow> tr = [] \<Longrightarrow> par_small_step_tau_closure p1 s1 p2 s2" for tr
    apply (induct rule: par_small_step_closure.induct)
    by (auto intro: par_small_step_tau_closure.intros)
  then show ?thesis
    using assms by auto
qed

lemma par_small_step_closure_cons_to_tau:
  "par_small_step_closure p1 s1 (ev # evs) p2 s2 \<Longrightarrow>
   \<exists>p1' s1' p1'' s1''.
     par_small_step_tau_closure p1 s1 p1' s1' \<and> par_small_step p1' s1' (Some ev) p1'' s1'' \<and>
     par_small_step_closure p1'' s1'' evs p2 s2"
proof (induct p1 s1 "ev # evs" p2 s2 rule: par_small_step_closure.induct)
  case (2 p s p2 s2 p3 s3)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p2 s2 p1' s1'" "par_small_step p1' s1' (Some ev) p1'' s1''" "par_small_step_closure p1'' s1'' evs p3 s3"
    using 2(3) by auto
  show ?case
    apply (rule exI[where x=p1']) apply (rule exI[where x=s1'])
    apply (rule exI[where x=p1'']) apply (rule exI[where x=s1''])
    apply auto
    apply (rule par_small_step_tau_closure.intros(2)[OF 2(1) a(1)])
    using a by auto  
next
  case (3 p s p2 s2 p3 s3)
  show ?case
    apply (rule exI[where x=p]) apply (rule exI[where x=s])
    apply (rule exI[where x=p2]) apply (rule exI[where x=s2])
    by (auto intro: par_small_step_tau_closure.intros 3(1,2))
qed

lemma par_small_step_closure_left:
  "par_small_step_tau_closure p1 s1 p2 s2 \<Longrightarrow>
   par_small_step_closure (Parallel p1 chs p3) (ParState s1 s3) [] (Parallel p2 chs p3) (ParState s2 s3)"
proof (induct rule: par_small_step_tau_closure.induct)
  case (1 p s)
  then show ?case
    by (auto intro: par_small_step_closure.intros)
next
  case (2 p s p2 s2 p2' s2')
  show ?case
    apply (rule par_small_step_closure.intros(2))
     apply (rule ParTauS1[OF 2(1)])
    by (rule 2(3))
qed

lemma par_small_step_closure_right:
  "par_small_step_tau_closure p3 s3 p4 s4 \<Longrightarrow>
   par_small_step_closure (Parallel p2 chs p3) (ParState s2 s3) [] (Parallel p2 chs p4) (ParState s2 s4)"
proof (induct rule: par_small_step_tau_closure.induct)
  case (1 p s)
  then show ?case
    by (auto intro: par_small_step_closure.intros)
next
  case (2 p s p2 s2 p3 s3)
  show ?case 
    apply (rule par_small_step_closure.intros(2))
     apply (rule ParTauS2[OF 2(1)])
    by (rule 2(3))
qed

lemma par_small_step_closure_merge:
  assumes "par_small_step_tau_closure p1 s1 p2 s2"
   and "par_small_step_tau_closure p3 s3 p4 s4"
  shows "par_small_step_closure (Parallel p1 chs p3) (ParState s1 s3) [] (Parallel p2 chs p4) (ParState s2 s4)"
  using par_small_step_closure_left[OF assms(1)] par_small_step_closure_right[OF assms(2)]
        par_small_step_closure_trans by fastforce

lemma small_step_to_par_small_step_closure:
  "small_step_closure p1 s1 tr p2 s2 \<Longrightarrow> par_small_step_closure (Single p1) (State s1) tr (Single p2) (State s2)"
proof (induct rule: small_step_closure.induct)
  case (1 p s)
  then show ?case
    by (rule par_small_step_closure.intros)
next
  case (2 p s p2 s2 evs p3 s3)
  show ?case
    apply (rule par_small_step_closure.intros(2))
     apply (rule SingleS[OF 2(1)])
    by (rule 2(3))
next
  case (3 p s ev p2 s2 evs p3 s3)
  show ?case
    apply (rule par_small_step_closure.intros(3))
     apply (rule SingleS[OF 3(1)])
    by (rule 3(3))
qed

text \<open>Analogous result to small_step_split for the parallel case\<close>

lemma par_small_step_split:
  "par_small_step p1 s1 (Some (WaitBlock t2 hist rdy)) p2 s2 \<Longrightarrow>
   0 < t1 \<Longrightarrow> t1 < t2 \<Longrightarrow>
   \<exists>p' s'. par_small_step p1 s1 (Some (WaitBlock t1 (\<lambda>\<tau>\<in>{0..t1}. hist \<tau>) rdy)) p' s' \<and>
           par_small_step p' s' (Some (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2-t1}. hist (\<tau> + t1)) rdy)) p2 s2"
proof (induct p1 s1 "Some (WaitBlock t2 hist rdy)" p2 s2 arbitrary: hist rdy rule: par_small_step.induct)
  case (SingleS p s1 p' s2)
  obtain pp ss where a:
    "small_step p s1 (Some (WaitBlock t1 (restrict hist {0..t1}) rdy)) pp ss"
    "small_step pp ss (Some (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2 - t1}. hist (\<tau> + t1)) rdy)) p' s2"
    using small_step_split[OF SingleS(1-3)] by auto
  show ?case
    apply (rule exI[where x="Single pp"])
    apply (rule exI[where x="State ss"])
    apply auto apply (rule par_small_step.SingleS[OF a(1)])
    by (rule par_small_step.SingleS[OF a(2)])
next
  case (ParDelayS rdy1 rdy2 hist hist1 hist2 rdy p1 s1 p2 s2 p3 s3 p4 s4 chs)
  obtain p1' s1' where a:
    "par_small_step p1 s1 (Some (WaitBlock t1 (restrict hist1 {0..t1}) rdy1)) p1' s1'"
    "par_small_step p1' s1' (Some (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2 - t1}. hist1 (\<tau> + t1)) rdy1)) p2 s2"
    using ParDelayS(5,8,9) by auto
  obtain p3' s3' where b:
    "par_small_step p3 s3 (Some (WaitBlock t1 (restrict hist2 {0..t1}) rdy2)) p3' s3'"
    "par_small_step p3' s3' (Some (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2 - t1}. hist2 (\<tau> + t1)) rdy2)) p4 s4"
    using ParDelayS(7,8,9) by auto
  show ?case
    apply (rule exI[where x="Parallel p1' chs p3'"])
    apply (rule exI[where x="ParState s1' s3'"])
    apply auto
    subgoal
      apply (rule par_small_step.ParDelayS[OF ParDelayS(1) _ ParDelayS(3) a(1) b(1)])
      using ParDelayS(2,8,9) by auto
    subgoal
      apply (rule par_small_step.ParDelayS[OF ParDelayS(1) _ ParDelayS(3) a(2) b(2)])
      using ParDelayS(2,8,9) by auto
    done
qed  


inductive is_skip :: "pproc \<Rightarrow> bool" where
  "is_skip (Single Skip)"
| "is_skip p1 \<Longrightarrow> is_skip p2 \<Longrightarrow> is_skip (Parallel p1 chs p2)"

lemma combine_blocks_to_par_small_step:
  "combine_blocks chs tr1 tr2 tr \<Longrightarrow>
   par_small_step_closure p1 s11 tr1 p3 s12 \<Longrightarrow>
   par_small_step_closure p2 s21 tr2 p4 s22 \<Longrightarrow>
   par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) tr (Parallel p3 chs p4) (ParState s12 s22)"
proof (induction arbitrary: p1 p2 s11 s21 rule: combine_blocks.induct)
  case (combine_blocks_empty chs)
  have a: "par_small_step_tau_closure p1 s11 p3 s12"
    using combine_blocks_empty(1) by simp
  have b: "par_small_step_tau_closure p2 s21 p4 s22"
    using combine_blocks_empty(2) by simp
  show ?case
    by (rule par_small_step_closure_merge[OF a b])
next
  case (combine_blocks_pair1 ch chs blks1 blks2 blks v)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p1 s11 p1' s1'"
    "par_small_step p1' s1' (Some (InBlock ch v)) p1'' s1''"
    "par_small_step_closure p1'' s1'' blks1 p3 s12"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_pair1(4)] by auto
  obtain p2' s2' p2'' s2'' where b:
    "par_small_step_tau_closure p2 s21 p2' s2'"
    "par_small_step p2' s2' (Some (OutBlock ch v)) p2'' s2''"
    "par_small_step_closure p2'' s2'' blks2 p4 s22"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_pair1(5)] by auto
  have c: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1' chs p2') (ParState s1' s2')"
    by (rule par_small_step_closure_merge[OF a(1) b(1)])
  have d: "par_small_step (Parallel p1' chs p2') (ParState s1' s2') (Some (IOBlock ch v)) (Parallel p1'' chs p2'') (ParState s1'' s2'')"
    by (rule ParPairS1[OF combine_blocks_pair1(1) a(2) b(2)])
  have e: "par_small_step_closure (Parallel p1'' chs p2'') (ParState s1'' s2'') blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_pair1(3)[OF a(3) b(3)])
  show ?case
    using c d e par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce
next
  case (combine_blocks_pair2 ch chs blks1 blks2 blks v)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p1 s11 p1' s1'"
    "par_small_step p1' s1' (Some (OutBlock ch v)) p1'' s1''"
    "par_small_step_closure p1'' s1'' blks1 p3 s12"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_pair2(4)] by auto
  obtain p2' s2' p2'' s2'' where b:
    "par_small_step_tau_closure p2 s21 p2' s2'"
    "par_small_step p2' s2' (Some (InBlock ch v)) p2'' s2''"
    "par_small_step_closure p2'' s2'' blks2 p4 s22"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_pair2(5)] by auto
  have c: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1' chs p2') (ParState s1' s2')"
    by (rule par_small_step_closure_merge[OF a(1) b(1)])
  have d: "par_small_step (Parallel p1' chs p2') (ParState s1' s2') (Some (IOBlock ch v)) (Parallel p1'' chs p2'') (ParState s1'' s2'')"
    by (rule ParPairS2[OF combine_blocks_pair2(1) a(2) b(2)])
  have e: "par_small_step_closure (Parallel p1'' chs p2'') (ParState s1'' s2'') blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_pair2(3)[OF a(3) b(3)])
  show ?case
    using c d e par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce
next
  case (combine_blocks_unpair1 ch chs blks1 blks2 blks v)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p1 s11 p1' s1'"
    "par_small_step p1' s1' (Some (InBlock ch v)) p1'' s1''"
    "par_small_step_closure p1'' s1'' blks1 p3 s12"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_unpair1(4)] by auto
  have b: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1' chs p2) (ParState s1' s21)"
    by (rule par_small_step_closure_left[OF a(1)])
  have c: "par_small_step (Parallel p1' chs p2) (ParState s1' s21) (Some (InBlock ch v)) (Parallel p1'' chs p2) (ParState s1'' s21)"
    by (rule ParUnpairS1[OF combine_blocks_unpair1(1) a(2)])
  have d: "par_small_step_closure (Parallel p1'' chs p2) (ParState s1'' s21) blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_unpair1(3)[OF a(3) combine_blocks_unpair1(5)])
  show ?case
    using b c d par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce
next
  case (combine_blocks_unpair2 ch chs blks1 blks2 blks v)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p1 s11 p1' s1'"
    "par_small_step p1' s1' (Some (OutBlock ch v)) p1'' s1''"
    "par_small_step_closure p1'' s1'' blks1 p3 s12"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_unpair2(4)] by auto
  have b: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1' chs p2) (ParState s1' s21)"
    by (rule par_small_step_closure_left[OF a(1)])
  have c: "par_small_step (Parallel p1' chs p2) (ParState s1' s21) (Some (OutBlock ch v)) (Parallel p1'' chs p2) (ParState s1'' s21)"
    by (rule ParUnpairS2[OF combine_blocks_unpair2(1) a(2)])
  have d: "par_small_step_closure (Parallel p1'' chs p2) (ParState s1'' s21) blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_unpair2(3)[OF a(3) combine_blocks_unpair2(5)])
  show ?case
    using b c d par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce
next
  case (combine_blocks_unpair3 ch chs blks1 blks2 blks v)
  obtain p2' s2' p2'' s2'' where a:
    "par_small_step_tau_closure p2 s21 p2' s2'"
    "par_small_step p2' s2' (Some (InBlock ch v)) p2'' s2''"
    "par_small_step_closure p2'' s2'' blks2 p4 s22"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_unpair3(5)] by auto
  have b: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1 chs p2') (ParState s11 s2')"
    by (rule par_small_step_closure_right[OF a(1)])
  have c: "par_small_step (Parallel p1 chs p2') (ParState s11 s2') (Some (InBlock ch v)) (Parallel p1 chs p2'') (ParState s11 s2'')"
    by (rule ParUnpairS3[OF combine_blocks_unpair3(1) a(2)])
  have d: "par_small_step_closure (Parallel p1 chs p2'') (ParState s11 s2'') blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_unpair3(3)[OF combine_blocks_unpair3(4) a(3)])
  show ?case
    using b c d par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce 
next
  case (combine_blocks_unpair4 ch chs blks1 blks2 blks v)
  obtain p2' s2' p2'' s2'' where a:
    "par_small_step_tau_closure p2 s21 p2' s2'"
    "par_small_step p2' s2' (Some (OutBlock ch v)) p2'' s2''"
    "par_small_step_closure p2'' s2'' blks2 p4 s22"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_unpair4(5)] by auto
  have b: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1 chs p2') (ParState s11 s2')"
    by (rule par_small_step_closure_right[OF a(1)])
  have c: "par_small_step (Parallel p1 chs p2') (ParState s11 s2') (Some (OutBlock ch v)) (Parallel p1 chs p2'') (ParState s11 s2'')"
    by (rule ParUnpairS4[OF combine_blocks_unpair4(1) a(2)])
  have d: "par_small_step_closure (Parallel p1 chs p2'') (ParState s11 s2'') blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_unpair4(3)[OF combine_blocks_unpair4(4) a(3)])
  show ?case
    using b c d par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce 
next
  case (combine_blocks_unpair5 ch chs blks1 blks2 blks v)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p1 s11 p1' s1'"
    "par_small_step p1' s1' (Some (IOBlock ch v)) p1'' s1''"
    "par_small_step_closure p1'' s1'' blks1 p3 s12"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_unpair5(4)] by auto
  have b: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1' chs p2) (ParState s1' s21)"
    by (rule par_small_step_closure_left[OF a(1)])
  have c: "par_small_step (Parallel p1' chs p2) (ParState s1' s21) (Some (IOBlock ch v)) (Parallel p1'' chs p2) (ParState s1'' s21)"
    by (rule ParUnpairS5[OF combine_blocks_unpair5(1) a(2)])
  have d: "par_small_step_closure (Parallel p1'' chs p2) (ParState s1'' s21) blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_unpair5(3)[OF a(3) combine_blocks_unpair5(5)])
  show ?case
    using b c d par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce
next
  case (combine_blocks_unpair6 ch chs blks1 blks2 blks v)
  obtain p2' s2' p2'' s2'' where a:
    "par_small_step_tau_closure p2 s21 p2' s2'"
    "par_small_step p2' s2' (Some (IOBlock ch v)) p2'' s2''"
    "par_small_step_closure p2'' s2'' blks2 p4 s22"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_unpair6(5)] by auto
  have b: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1 chs p2') (ParState s11 s2')"
    by (rule par_small_step_closure_right[OF a(1)])
  have c: "par_small_step (Parallel p1 chs p2') (ParState s11 s2') (Some (IOBlock ch v)) (Parallel p1 chs p2'') (ParState s11 s2'')"
    by (rule ParUnpairS6[OF combine_blocks_unpair6(1) a(2)])
  have d: "par_small_step_closure (Parallel p1 chs p2'') (ParState s11 s2'') blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_unpair6(3)[OF combine_blocks_unpair6(4) a(3)])
  show ?case
    using b c d par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce 
next
  case (combine_blocks_wait1 chs blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 t rdy)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p1 s11 p1' s1'"
    "par_small_step p1' s1' (Some (WaitBlock t hist1 rdy1)) p1'' s1''"
    "par_small_step_closure p1'' s1'' blks1 p3 s12"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_wait1(6)] by auto
  obtain p2' s2' p2'' s2'' where b:
    "par_small_step_tau_closure p2 s21 p2' s2'"
    "par_small_step p2' s2' (Some (WaitBlock t hist2 rdy2)) p2'' s2''"
    "par_small_step_closure p2'' s2'' blks2 p4 s22"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_wait1(7)] by auto
  have c: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1' chs p2') (ParState s1' s2')"
    by (rule par_small_step_closure_merge[OF a(1) b(1)])
  have d: "par_small_step (Parallel p1' chs p2') (ParState s1' s2') (Some (WaitBlock t hist rdy))
           (Parallel p1'' chs p2'') (ParState s1'' s2'')"
    apply (rule ParDelayS)
    using combine_blocks_wait1 a(2) b(2) by auto
  have e: "par_small_step_closure (Parallel p1'' chs p2'') (ParState s1'' s2'') blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_wait1(5)[OF a(3) b(3)])
  show ?case
    using c d e par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce
next
  case (combine_blocks_wait2 chs blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p1 s11 p1' s1'"
    "par_small_step p1' s1' (Some (WaitBlock t1 hist1 rdy1)) p1'' s1''"
    "par_small_step_closure p1'' s1'' blks1 p3 s12"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_wait2(8)] by auto
  obtain p2' s2' p2'' s2'' where b:
    "par_small_step_tau_closure p2 s21 p2' s2'"
    "par_small_step p2' s2' (Some (WaitBlock t2 hist2 rdy2)) p2'' s2''"
    "par_small_step_closure p2'' s2'' blks2 p4 s22"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_wait2(9)] by auto
  have c: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1' chs p2') (ParState s1' s2')"
    by (rule par_small_step_closure_merge[OF a(1) b(1)])
  obtain p2a s2a where d:
    "par_small_step p2' s2' (Some (WaitBlock t1 (\<lambda>\<tau>\<in>{0..t1}. hist2 \<tau>) rdy2)) p2a s2a"
    "par_small_step p2a s2a (Some (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2-t1}. hist2 (\<tau> + t1)) rdy2)) p2'' s2''"
    using par_small_step_split[OF b(2) combine_blocks_wait2(4,3)] by auto
  have e: "par_small_step (Parallel p1' chs p2') (ParState s1' s2') (Some (WaitBlock t1 hist rdy))
                          (Parallel p1'' chs p2a) (ParState s1'' s2a)"
    apply (rule ParDelayS)
    using combine_blocks_wait2(2,5,6) a(2) d(1) by auto
  have f: "par_small_step_closure (Parallel p1'' chs p2a) (ParState s1'' s2a) blks (Parallel p3 chs p4) (ParState s12 s22)"
    apply (rule combine_blocks_wait2(7)[OF a(3)])
    apply (rule par_small_step_closure.intros(3))
    apply (rule d(2)) by (rule b(3))
  show ?case
    using c e f par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce
next
  case (combine_blocks_wait3 chs t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p1 s11 p1' s1'"
    "par_small_step p1' s1' (Some (WaitBlock t1 hist1 rdy1)) p1'' s1''"
    "par_small_step_closure p1'' s1'' blks1 p3 s12"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_wait3(8)] by auto
  obtain p2' s2' p2'' s2'' where b:
    "par_small_step_tau_closure p2 s21 p2' s2'"
    "par_small_step p2' s2' (Some (WaitBlock t2 hist2 rdy2)) p2'' s2''"
    "par_small_step_closure p2'' s2'' blks2 p4 s22"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_wait3(9)] by auto
  have c: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1' chs p2') (ParState s1' s2')"
    by (rule par_small_step_closure_merge[OF a(1) b(1)])
  obtain p1a s1a where d:
    "par_small_step p1' s1' (Some (WaitBlock t2 (\<lambda>\<tau>\<in>{0..t2}. hist1 \<tau>) rdy1)) p1a s1a"
    "par_small_step p1a s1a (Some (WaitBlock (t1 - t2) (\<lambda>\<tau>\<in>{0..t1-t2}. hist1 (\<tau> + t2)) rdy1)) p1'' s1''"
    using par_small_step_split[OF a(2) combine_blocks_wait3(4,3)] by auto
  have e: "par_small_step (Parallel p1' chs p2') (ParState s1' s2') (Some (WaitBlock t2 hist rdy))
                          (Parallel p1a chs p2'') (ParState s1a s2'')"
    apply (rule ParDelayS)
    using combine_blocks_wait3(2,5,6) b(2) d(1) by auto
  have f: "par_small_step_closure (Parallel p1a chs p2'') (ParState s1a s2'') blks (Parallel p3 chs p4) (ParState s12 s22)"
    apply (rule combine_blocks_wait3(7)[OF _ b(3)])
    apply (rule par_small_step_closure.intros(3))
    apply (rule d(2)) by (rule a(3))
  show ?case
    using c e f par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce
qed


theorem big_to_small_par:
  "par_big_step p1 s1 tr s2 \<Longrightarrow> \<exists>p2. is_skip p2 \<and> par_small_step_closure p1 s1 tr p2 s2"
proof (induction rule: par_big_step.induct)
  case (SingleB p s1 tr s2)
  show ?case
    apply (rule exI[where x="Single Skip"])
    apply (auto intro: is_skip.intros)
    apply (rule small_step_to_par_small_step_closure)
    apply (rule big_to_small)
    by (rule SingleB)
next
  case (ParallelB p1 s11 tr1 s12 p2 s21 tr2 s22 chs tr)
  obtain p3 where p3: "is_skip p3" "par_small_step_closure p1 s11 tr1 p3 s12"
    using ParallelB(4) by auto
  obtain p4 where p4: "is_skip p4" "par_small_step_closure p2 s21 tr2 p4 s22"
    using ParallelB(5) by auto
  have skip: "is_skip (Parallel p3 chs p4)"
    by (auto intro: is_skip.intros p3 p4)
  show ?case
    apply (rule exI[where x="Parallel p3 chs p4"])
    apply (auto simp add: skip)
    apply (rule combine_blocks_to_par_small_step)
    using ParallelB(3) p3 p4 by auto
qed


end
