theory SmallStep
  imports BigStepParallel
begin


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
| waitS3: "\<not>d > 0 \<Longrightarrow> small_step (Wait d) s None Skip s"
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
| equiv_trace_merge: "d1 > 0 \<Longrightarrow> d2 > 0 \<Longrightarrow> p1 d1 = p2 0 \<Longrightarrow>
   equiv_trace (WaitBlock d1 (\<lambda>\<tau>\<in>{0..d1}. p1 \<tau>) rdy # WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. p2 \<tau>) rdy # tr)
               (WaitBlock (d1 + d2) (\<lambda>\<tau>\<in>{0..d1+d2}. if \<tau> < d1 then p1 \<tau> else p2 (\<tau> - d1)) rdy # tr)"
| equiv_trace_cons: "equiv_trace tr1 tr2 \<Longrightarrow> equiv_trace (ev # tr1) (ev # tr2)"
| equiv_trace_trans: "equiv_trace tr1 tr2 \<Longrightarrow> equiv_trace tr2 tr3 \<Longrightarrow> equiv_trace tr1 tr3"

lemma equiv_trace_refl [simp]:
  "equiv_trace tr tr"
  apply (induct tr) by (auto intro: equiv_trace.intros)

lemma equiv_trace_append_left:
  "equiv_trace tr2 tr3 \<Longrightarrow> equiv_trace (tr1 @ tr2) (tr1 @ tr3)"
  apply (induct tr1) by (auto intro: equiv_trace.intros)

lemma equiv_trace_append:
  "equiv_trace tr1 tr2 \<Longrightarrow> equiv_trace (tr1 @ tr3) (tr2 @ tr3)"
  apply (induct rule: equiv_trace.induct)
  by (auto intro: equiv_trace.intros)

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

lemma equiv_trace_merge':
  assumes "d1 > 0" "d2 > 0"
   "\<forall>\<tau>\<in>{0..d1}. hist1 \<tau> = hist \<tau>"
   "\<forall>\<tau>\<in>{0..d2}. hist2 \<tau> = hist (\<tau> + d1)"
  shows "equiv_trace (WaitBlock d1 (\<lambda>\<tau>\<in>{0..d1}. hist1 \<tau>) rdy # WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. hist2 \<tau>) rdy # tr)
                     (WaitBlock (d1 + d2) (\<lambda>\<tau>\<in>{0..d1+d2}. hist \<tau>) rdy # tr)"
proof -
  have a: "(\<lambda>\<tau>\<in>{0..d1+d2}. hist \<tau>) = (\<lambda>\<tau>\<in>{0..d1+d2}. if \<tau> < d1 then hist1 \<tau> else hist2 (\<tau> - d1))"
    using assms by auto
  show ?thesis
    unfolding a apply (rule equiv_trace_merge)
    using assms by auto
qed

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
  case (waitB1 d s)
  show ?case
    apply (rule small_step_closure_single_Some)
    apply (rule waitS2) by (rule waitB1)
next
  case (waitB2 d s)
  show ?case
    apply (rule small_step_closure_single_None)
    apply (rule waitS3) by (rule waitB2)
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
  case (waitS2 d s)
  then show ?case
    using waitB2 by auto
next
  case (waitS3 d s)
  then show ?case
    using skipE waitB2 by blast
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
    using b(1) equiv_trace_append apply fastforce
    by (rule seqB[OF b(2) a(3)])
next
  case (waitS1 d1 d s)
  have a: "tr2 = [WaitBlock (d - d1) (\<lambda>\<tau>\<in>{0..d - d1}. State s) ({}, {})]" "s3 = s" "0 < d - d1"
    using waitE[OF waitS1(4)] by (auto simp add: waitS1(1,2))
  have b: "ev = WaitBlock d1 (\<lambda>\<tau>\<in>{0..d1}. State s) ({}, {})"
    using waitS1(3) by auto
  have c: "WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {}) =
           WaitBlock (d1 + (d - d1)) (\<lambda>\<tau>\<in>{0..d1+(d-d1)}. if \<tau> < d1 then State s else State s) ({}, {})"
    by auto
  show ?case
    apply (rule exI[where x="[WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})]"])
    unfolding a b apply auto
    unfolding c apply (rule equiv_trace_merge)
       apply (auto simp add: waitS1)
     apply (rule waitB1)
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
    apply (rule waitB1) by (rule waitS2(1))
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
           [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State s) ({ch}, {}), OutBlock ch (e s)]" (is "equiv_trace ?lhs ?rhs") if "d2 > 0" for d2
  proof -
    have b2: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State s else State s) ({ch}, {}), OutBlock ch (e s)]"
      by auto
    show ?thesis
      unfolding b2 apply (rule equiv_trace_merge)
      by (auto simp add: sendS2 that)
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
           [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State s) ({}, {ch}), InBlock ch v]" (is "equiv_trace ?lhs ?rhs") if "d2 > 0" for v d2
  proof -
    have b2: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State s else State s) ({}, {ch}), InBlock ch v]"
      by auto
    show ?thesis
      unfolding b2 apply (rule equiv_trace_merge)
      by (auto simp add: receiveS2 that)
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
    (is "equiv_trace ?lhs ?rhs") if "d2 > 0" for d2 ch e tr2'
  proof -
    have b2: "?rhs = WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State s else State s) (rdy_of_echoice cs) #
                     OutBlock ch (e s) # tr2'"
      by auto
    show ?thesis
      unfolding b2 apply (rule equiv_trace_merge)
      by (auto simp add: EChoiceS1 that)
  qed
  have c: "equiv_trace
     (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice cs) #
      WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) (rdy_of_echoice cs) # InBlock ch v # tr2')
     (WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State s) (rdy_of_echoice cs) # InBlock ch v # tr2')"
    (is "equiv_trace ?lhs ?rhs") if "d2 > 0" for d2 ch v tr2'
  proof -
    have c2: "?rhs = WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State s else State s) (rdy_of_echoice cs) # InBlock ch v # tr2'"
      by auto
    show ?thesis
      unfolding c2 apply (rule equiv_trace_merge)
      by (auto simp add: EChoiceS1 that)
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
    (is "equiv_trace ?lhs ?rhs") if "p2 0 = p d" "d2 > 0" for d2 p2       
  proof -
    have c1: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State (p \<tau>) else State (p2 (\<tau> - d))) ({}, {})]"
      by auto
    show ?thesis
      unfolding c1 apply (rule equiv_trace_merge)
      by (auto simp add: that ContS1)
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
    (is "equiv_trace ?lhs ?rhs") if "p2 0 = p d" "d2 > 0" for d2 p2 ch e tr2'
  proof -
    have e2: "?rhs = WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State (p \<tau>) else State (p2 (\<tau> - d))) (rdy_of_echoice cs) #
                     OutBlock ch (e (p2 d2)) # tr2'"
      by auto
    show ?thesis
      unfolding e2 apply (rule equiv_trace_merge)
      by (auto simp add: InterruptS1 that)
  qed
  have f: "equiv_trace
     (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs) # WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr2')
     (WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs) # InBlock ch v # tr2')"
    (is "equiv_trace ?lhs ?rhs") if "p2 0 = p d" "d2 > 0" for d2 p2 ch v tr2'
  proof -
    have f2: "?rhs = WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State (p \<tau>) else State (p2 (\<tau> - d))) (rdy_of_echoice cs) #
                     InBlock ch v # tr2'"
      by auto
    show ?thesis
      unfolding f2 apply (rule equiv_trace_merge)
      by (auto simp add: that InterruptS1)
  qed
  have g: "equiv_trace [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs), WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State (p2 \<tau>)) (rdy_of_echoice cs)]
     [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. State (if \<tau> < d then p \<tau> else p2 (\<tau> - d))) (rdy_of_echoice cs)]"
    (is "equiv_trace ?lhs ?rhs") if "p2 0 = p d" "d2 > 0" for d2 p2
  proof -
    have g1: "?rhs = [WaitBlock (d + d2) (\<lambda>\<tau>\<in>{0..d + d2}. if \<tau> < d then State (p \<tau>) else State (p2 (\<tau> - d))) (rdy_of_echoice cs)]"
      by auto
    show ?thesis
      unfolding g1 apply (rule equiv_trace_merge)
      by (auto simp add: that InterruptS1)
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

inductive wf_pair :: "pproc \<Rightarrow> gstate \<Rightarrow> bool" where
  "wf_pair (Single p) (State s)"
| "wf_pair p1 s1 \<Longrightarrow> wf_pair p2 s2 \<Longrightarrow> wf_pair (Parallel p1 chs p2) (ParState s1 s2)"

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
    "wf_pair p3 s3 \<Longrightarrow>
     par_small_step p1 s1 None p2 s2 \<Longrightarrow>
     par_small_step (Parallel p1 chs p3) (ParState s1 s3) None (Parallel p2 chs p3) (ParState s2 s3)"
| ParTauS2:
    "wf_pair p1 s1 \<Longrightarrow>
     par_small_step p2 s2 None p3 s3 \<Longrightarrow>
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
    "wf_pair p3 s3 \<Longrightarrow>
     ch \<notin> chs \<Longrightarrow>
     par_small_step p1 s1 (Some (CommBlock ch_type ch v)) p2 s2 \<Longrightarrow>
     par_small_step (Parallel p1 chs p3) (ParState s1 s3) (Some (CommBlock ch_type ch v)) (Parallel p2 chs p3) (ParState s2 s3)"
| ParUnpairS2:
    "wf_pair p1 s1 \<Longrightarrow>
     ch \<notin> chs \<Longrightarrow>
     par_small_step p2 s2 (Some (CommBlock ch_type ch v)) p3 s3 \<Longrightarrow>
     par_small_step (Parallel p1 chs p2) (ParState s1 s2) (Some (CommBlock ch_type ch v)) (Parallel p1 chs p3) (ParState s1 s3)"


text \<open>Transitive closure of small step semantics\<close>

lemma par_small_step_wf_pair:
  "par_small_step p s ev p2 s2 \<Longrightarrow> wf_pair p s \<and> wf_pair p2 s2"
  apply (induct rule: par_small_step.induct)
  by (auto intro: wf_pair.intros)

inductive par_small_step_closure :: "pproc \<Rightarrow> gstate \<Rightarrow> trace \<Rightarrow> pproc \<Rightarrow> gstate \<Rightarrow> bool" where
  "wf_pair p s \<Longrightarrow> par_small_step_closure p s [] p s"
| "par_small_step p s None p2 s2 \<Longrightarrow> par_small_step_closure p2 s2 evs p3 s3 \<Longrightarrow> par_small_step_closure p s evs p3 s3"
| "par_small_step p s (Some ev) p2 s2 \<Longrightarrow> par_small_step_closure p2 s2 evs p3 s3 \<Longrightarrow> par_small_step_closure p s (ev # evs) p3 s3"

lemma par_small_step_closure_wf_pair:
  "par_small_step_closure p s ev p2 s2 \<Longrightarrow> wf_pair p s \<and> wf_pair p2 s2"
  apply (induct rule: par_small_step_closure.induct)
  apply auto
  apply (simp add: par_small_step_wf_pair)
  using par_small_step_wf_pair by blast

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
  "wf_pair p s \<Longrightarrow> par_small_step_tau_closure p s p s"
| "par_small_step p s None p2 s2 \<Longrightarrow> par_small_step_tau_closure p2 s2 p3 s3 \<Longrightarrow> par_small_step_tau_closure p s p3 s3"

lemma par_small_step_tau_closure_wf_pair:
  "par_small_step_tau_closure p s p2 s2 \<Longrightarrow> wf_pair p s \<and> wf_pair p2 s2"
  apply (induct rule: par_small_step_tau_closure.induct)
  apply auto
  using par_small_step_wf_pair by blast

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
    using 3(1,2) apply auto
    apply (rule par_small_step_tau_closure.intros(1))
    using par_small_step_wf_pair by auto
qed

lemma par_small_step_closure_left:
  "par_small_step_tau_closure p1 s1 p2 s2 \<Longrightarrow>
   wf_pair p3 s3 \<Longrightarrow>
   par_small_step_closure (Parallel p1 chs p3) (ParState s1 s3) [] (Parallel p2 chs p3) (ParState s2 s3)"
proof (induct rule: par_small_step_tau_closure.induct)
  case (1 p s)
  then show ?case
    by (simp add: par_small_step_closure.intros(1) wf_pair.intros(2))
next
  case (2 p s p2 s2 p2' s2')
  show ?case
    apply (rule par_small_step_closure.intros(2))
     apply (rule ParTauS1[OF _ 2(1)])
    using 2 by auto
qed

lemma par_small_step_closure_right:
  "par_small_step_tau_closure p3 s3 p4 s4 \<Longrightarrow>
   wf_pair p2 s2 \<Longrightarrow>
   par_small_step_closure (Parallel p2 chs p3) (ParState s2 s3) [] (Parallel p2 chs p4) (ParState s2 s4)"
proof (induct rule: par_small_step_tau_closure.induct)
  case (1 p s)
  then show ?case
    by (simp add: par_small_step_closure_left par_small_step_tau_closure.intros(1))
next
  case (2 p s p2 s2 p3 s3)
  show ?case 
    apply (rule par_small_step_closure.intros(2))
     apply (rule ParTauS2[OF _ 2(1)])
    using 2 by auto
qed

lemma par_small_step_closure_merge:
  assumes "par_small_step_tau_closure p1 s1 p2 s2"
   and "par_small_step_tau_closure p3 s3 p4 s4"
  shows "par_small_step_closure (Parallel p1 chs p3) (ParState s1 s3) [] (Parallel p2 chs p4) (ParState s2 s4)"
proof -
  have a: "wf_pair p1 s1"
    using assms(1) par_small_step_tau_closure_wf_pair by auto
  have b: "wf_pair p3 s3"
    using assms(2) par_small_step_tau_closure_wf_pair by auto
  have c: "([]::trace) = [] @ []"
    by auto
  show ?thesis
    apply (subst c)
    apply (rule par_small_step_closure_trans)
     apply (rule par_small_step_closure_left[OF assms(1) b])
    apply (rule par_small_step_closure_right[OF assms(2)])
    using assms(1) par_small_step_tau_closure_wf_pair by auto
qed

lemma small_step_to_par_small_step_closure:
  "small_step_closure p1 s1 tr p2 s2 \<Longrightarrow> par_small_step_closure (Single p1) (State s1) tr (Single p2) (State s2)"
proof (induct rule: small_step_closure.induct)
  case (1 p s)
  then show ?case
    by (simp add: par_small_step_closure.intros(1) wf_pair.intros(1))
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
  case (combine_blocks_unpair1 ch chs blks1 blks2 blks ch_type v)
  obtain p1' s1' p1'' s1'' where a:
    "par_small_step_tau_closure p1 s11 p1' s1'"
    "par_small_step p1' s1' (Some (CommBlock ch_type ch v)) p1'' s1''"
    "par_small_step_closure p1'' s1'' blks1 p3 s12"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_unpair1(4)] by auto
  have b: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1' chs p2) (ParState s1' s21)"
    apply (rule par_small_step_closure_left[OF a(1)])
    using par_small_step_closure_wf_pair combine_blocks_unpair1(5) by auto
  have c: "par_small_step (Parallel p1' chs p2) (ParState s1' s21)
                          (Some (CommBlock ch_type ch v)) (Parallel p1'' chs p2) (ParState s1'' s21)"
    apply (rule ParUnpairS1[OF _ combine_blocks_unpair1(1) a(2)])
    using par_small_step_closure_wf_pair combine_blocks_unpair1(5) by auto
  have d: "par_small_step_closure (Parallel p1'' chs p2) (ParState s1'' s21) blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_unpair1(3)[OF a(3) combine_blocks_unpair1(5)])
  show ?case
    using b c d par_small_step_closure.intros(3) par_small_step_closure_trans by fastforce
next
  case (combine_blocks_unpair2 ch chs blks1 blks2 blks ch_type v)
  obtain p2' s2' p2'' s2'' where a:
    "par_small_step_tau_closure p2 s21 p2' s2'"
    "par_small_step p2' s2' (Some (CommBlock ch_type ch v)) p2'' s2''"
    "par_small_step_closure p2'' s2'' blks2 p4 s22"
    using par_small_step_closure_cons_to_tau[OF combine_blocks_unpair2(5)] by auto
  have b: "par_small_step_closure (Parallel p1 chs p2) (ParState s11 s21) [] (Parallel p1 chs p2') (ParState s11 s2')"
    apply (rule par_small_step_closure_right[OF a(1)])
    using par_small_step_closure_wf_pair combine_blocks_unpair2(4) by auto
  have c: "par_small_step (Parallel p1 chs p2') (ParState s11 s2') (Some (CommBlock ch_type ch v))
                          (Parallel p1 chs p2'') (ParState s11 s2'')"
    apply (rule ParUnpairS2[OF _ combine_blocks_unpair2(1) a(2)])
    using par_small_step_closure_wf_pair combine_blocks_unpair2(4) by auto
  have d: "par_small_step_closure (Parallel p1 chs p2'') (ParState s11 s2'') blks (Parallel p3 chs p4) (ParState s12 s22)"
    by (rule combine_blocks_unpair2(3)[OF combine_blocks_unpair2(4) a(3)])
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


lemma par_big_step_empty:
  "wf_pair p s \<Longrightarrow> is_skip p \<Longrightarrow> par_big_step p s [] s"
proof (induct rule: wf_pair.induct)
  case (1 p s)
  then show ?case
    using SingleB is_skip.cases skipB by blast
next
  case (2 p1 s1 p2 s2 chs)
  have a: "is_skip p1 \<and> is_skip p2"
    using 2(5) apply (cases rule: is_skip.cases) by auto
  show ?case
    apply (rule ParallelB)
      apply (rule 2(2)) using a apply auto[1]
     apply (rule 2(4)) using a apply auto[1]
    by (rule combine_blocks.intros)
qed

lemma par_small1_big_continue:
  "par_small_step p s None p2 s2 \<Longrightarrow>
   par_big_step p2 s2 evs s3 \<Longrightarrow>
   par_big_step p s evs s3"
proof (induction p s "None::trace_block option" p2 s2 arbitrary: evs s3 rule: par_small_step.induct)
  case (SingleS p s1 p' s2)
  show ?case
    using SingleS(2) apply (elim SingleE)
    apply auto
    apply (rule SingleB)
    apply (rule small1_big_continue[OF SingleS(1)])
    by auto
next
  case (ParTauS1 p3 s3' p1 s1 p2 s2 chs)
  show ?case
    using ParTauS1(4) apply (elim ParallelE)
    using ParTauS1.hyps(3) ParallelB by blast
next
  case (ParTauS2 p1 s1 p2 s2 p3 s3' chs)
  show ?case
    using ParTauS2(4) apply (elim ParallelE)
    using ParTauS2.hyps(3) ParallelB by blast
qed

lemma combine_blocks_cons_left:
  "combine_blocks chs (ev # tr1) tr2 tr \<Longrightarrow>
   (\<And>tr3 tr'. combine_blocks chs tr1 tr3 tr' \<Longrightarrow> (\<exists>tr''. equiv_trace tr' tr'' \<and> combine_blocks chs tr2' tr3 tr'')) \<Longrightarrow> 
   \<exists>tr'. equiv_trace tr tr' \<and> combine_blocks chs (ev # tr2') tr2 tr'"
proof (induct chs "ev # tr1" tr2 tr arbitrary: tr1 ev rule: combine_blocks.induct)
  case (combine_blocks_pair1 ch comms blks1 blks2 blks v)
  then show ?case
    by (meson combine_blocks.combine_blocks_pair1 equiv_trace_cons)
next
  case (combine_blocks_pair2 ch comms blks1 blks2 blks v)
  then show ?case
    by (meson combine_blocks.combine_blocks_pair2 equiv_trace_cons)
next
  case (combine_blocks_unpair1 ch comms blks1 blks2 blks ch_type v)
  then show ?case
    by (meson combine_blocks.combine_blocks_unpair1 equiv_trace_cons)
next
  case (combine_blocks_unpair2 ch comms blks1 blks2 blks ch_type v)
  then show ?case
    by (meson combine_blocks.combine_blocks_unpair2 equiv_trace_cons)
next
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 t rdy)
  obtain tr'' where a: "equiv_trace blks tr''" "combine_blocks comms tr2' blks2 tr''"
    using combine_blocks_wait1(1,6) by auto
  show ?case
    apply (rule exI[where x="WaitBlock t hist rdy # tr''"])
    apply auto
    apply (rule equiv_trace_cons[OF a(1)])
    by (rule combine_blocks.combine_blocks_wait1[OF a(2) combine_blocks_wait1(3-5)])
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  obtain tr'' where a:
    "equiv_trace blks tr''"
    "combine_blocks comms tr2' (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2 - t1}. hist2 (\<tau> + t1)) rdy2 # blks2) tr''"
    using combine_blocks_wait2(8)[OF combine_blocks_wait2(1)] by auto
  show ?case
    apply (rule exI[where x="WaitBlock t1 hist rdy # tr''"])
    apply auto
    apply (rule equiv_trace_cons[OF a(1)])
    apply (rule combine_blocks.combine_blocks_wait2)
    using combine_blocks_wait2(3-7) a(2) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  obtain tr' where a:
    "equiv_trace blks tr'" "combine_blocks comms (WaitBlock (t1 - t2) (\<lambda>\<tau>\<in>{0..t1-t2}. hist1 (\<tau> + t2)) rdy1 # tr2') blks2 tr'"
    using combine_blocks_wait3(2,8) by auto
  show ?case
    apply (rule exI[where x="WaitBlock t2 hist rdy # tr'"])
    apply auto
    apply (rule equiv_trace_cons[OF a(1)])
    apply (rule combine_blocks.combine_blocks_wait3)
    using combine_blocks_wait3(3-7) a(2) by auto
qed

lemma combine_blocks_cons_right:
  "combine_blocks chs tr1 (ev # tr2) tr \<Longrightarrow>
   (\<And>tr3 tr'. combine_blocks chs tr3 tr2 tr' \<Longrightarrow> (\<exists>tr''. equiv_trace tr' tr'' \<and> combine_blocks chs tr3 tr2' tr'')) \<Longrightarrow>
   \<exists>tr'. equiv_trace tr tr' \<and> combine_blocks chs tr1 (ev # tr2') tr'"
proof (induct chs tr1 "ev # tr2" tr arbitrary: tr2 ev rule: combine_blocks.induct)
  case (combine_blocks_pair1 ch comms blks1 blks2 blks v)
  then show ?case
    by (meson combine_blocks.combine_blocks_pair1 equiv_trace_cons)
next
  case (combine_blocks_pair2 ch comms blks1 blks2 blks v)
  then show ?case
    by (meson combine_blocks.combine_blocks_pair2 equiv_trace_cons)
next
  case (combine_blocks_unpair1 ch comms blks1 blks ch_type v)
  then show ?case
    by (meson combine_blocks.combine_blocks_unpair1 equiv_trace_cons)
next
  case (combine_blocks_unpair2 ch comms blks1 blks ch_type v)
  then show ?case
    by (meson combine_blocks.combine_blocks_unpair2 equiv_trace_cons)
next
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 t rdy)
  obtain tr'' where a: "equiv_trace blks tr''" "combine_blocks comms blks1 tr2' tr''"
    using combine_blocks_wait1(1,6) by auto
  show ?case
    apply (rule exI[where x="WaitBlock t hist rdy # tr''"])
    apply auto
    apply (rule equiv_trace_cons[OF a(1)])
    by (rule combine_blocks.combine_blocks_wait1[OF a(2) combine_blocks_wait1(3-5)])
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  obtain tr' where a:
    "equiv_trace blks tr'"
    "combine_blocks comms blks1 (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2-t1}. hist2 (\<tau> + t1)) rdy2 # tr2') tr'"
    using combine_blocks_wait2(2,8) by auto
  show ?case
    apply (rule exI[where x="WaitBlock t1 hist rdy # tr'"])
    apply auto
    apply (rule equiv_trace_cons[OF a(1)])
    apply (rule combine_blocks.combine_blocks_wait2)
    using combine_blocks_wait2(3-7) a(2) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  obtain tr'' where a:
    "equiv_trace blks tr''"
    "combine_blocks comms (WaitBlock (t1 - t2) (\<lambda>\<tau>\<in>{0..t1-t2}. hist1 (\<tau> + t2)) rdy1 # blks1) tr2' tr''"
    using combine_blocks_wait3(8)[OF combine_blocks_wait3(1)] by auto
  show ?case
    apply (rule exI[where x="WaitBlock t2 hist rdy # tr''"])
    apply auto
    apply (rule equiv_trace_cons[OF a(1)])
    apply (rule combine_blocks.combine_blocks_wait3)
    using combine_blocks_wait3(3-7) a(2) by auto
qed


lemma combine_blocks_merge_left:
  "combine_blocks chs (WaitBlock d1 (restrict p1 {0..d1}) rdy # WaitBlock d2 (restrict p2 {0..d2}) rdy # tr') tr2 tr \<Longrightarrow>
   p1 d1 = p2 0 \<Longrightarrow>
   d1 > 0 \<Longrightarrow> d2 > 0 \<Longrightarrow>
   \<exists>tr''. equiv_trace tr tr'' \<and>
   combine_blocks chs (WaitBlock (d1 + d2) (\<lambda>\<tau>\<in>{0..d1+d2}. if \<tau> < d1 then p1 \<tau> else p2 (\<tau> - d1)) rdy # tr') tr2 tr''"
proof (induct chs "WaitBlock d1 (restrict p1 {0..d1}) rdy # WaitBlock d2 (restrict p2 {0..d2}) rdy # tr'" tr2 tr
       arbitrary: d1 p1 rule: combine_blocks.induct)
  case (combine_blocks_unpair2 ch comms blks2 blks ch_type v)
  then show ?case
    using combine_blocks.combine_blocks_unpair2 equiv_trace_cons by blast
next
  case (combine_blocks_wait1 chs blks2 blks rdy2 hist hist2 t rdy')
  have a: "(\<lambda>\<tau>\<in>{0..d2}. if 0 \<le> \<tau> + t \<and> \<tau> \<le> d2 then if \<tau> + t < t then p1 (\<tau> + t) else p2 (\<tau> + t - t) else undefined) =
           (\<lambda>\<tau>\<in>{0..d2}. p2 \<tau>)" if "t > 0"
    apply (rule restrict_ext)
    using combine_blocks_wait1 that by auto
  show ?case
    apply (rule exI[where x="WaitBlock t hist rdy' # blks"])
    apply auto
    apply (rule combine_blocks_wait3)
    subgoal apply (auto simp add: combine_blocks_wait1)
      unfolding a
      by (simp add: a combine_blocks_wait1.hyps(1) combine_blocks_wait1.prems(2))
    using combine_blocks_wait1 by auto
next
  case (combine_blocks_wait2 comms t2 t1 hist2 rdy2 blks2 blks hist rdy')
  have a: ?case if "t1 + d2 = t2"
  proof -
    have a1: "t2 - t1 = d2"
      using that by auto
    obtain blks' where a2:
      "blks = WaitBlock d2 (\<lambda>t\<in>{0..d2}. ParState (restrict p2 {0..d2} t) ((\<lambda>\<tau>\<in>{0..d2}. hist2 (\<tau> + t1)) t)) rdy' # blks'"
      "combine_blocks comms tr' blks2 blks'"
      using combine_blocks_elim4[OF combine_blocks_wait2(1)[unfolded a1]]
            combine_blocks_wait2(3,7) by auto
    show ?thesis
      unfolding a2(1)
      apply (rule exI[where x="WaitBlock (t1 + d2) (\<lambda>\<tau>\<in>{0..t1+d2}. ParState (if \<tau> < t1 then p1 \<tau> else p2 (\<tau> - t1)) (hist2 \<tau>)) rdy' # blks'"])
      apply auto
      subgoal
        unfolding combine_blocks_wait2(6)
        apply (rule equiv_trace_merge')
        using combine_blocks_wait2(8-10) by auto
      subgoal
        unfolding that
        apply (rule combine_blocks.combine_blocks_wait1)
        using combine_blocks_wait2(3,7) a2(2) by auto
      done
  qed
  have b: ?case if "t1 + d2 < t2"
  proof -
    have b1: "d2 < t2 - t1"
      using that by auto
    obtain blks' where b2:
      "blks = WaitBlock d2 (\<lambda>t\<in>{0..d2}. ParState (restrict p2 {0..d2} t) ((\<lambda>\<tau>\<in>{0..t2-t1}. hist2 (\<tau> + t1)) t)) rdy' # blks'"
      "combine_blocks comms tr' (WaitBlock (t2-t1-d2) (\<lambda>t\<in>{0..t2-t1-d2}. (\<lambda>\<tau>\<in>{0..t2-t1}. hist2 (\<tau> + t1)) (t + d2)) rdy2 # blks2) blks'"
      using combine_blocks_elim4d[OF combine_blocks_wait2(1) b1 combine_blocks_wait2(3)]
            combine_blocks_wait2(7) by auto
    have b3: "t2 - t1 - d2 = t2 - (t1 + d2)"
      by auto
    have b4:
      "(\<lambda>t\<in>{0..t2-t1-d2}. (\<lambda>\<tau>\<in>{0..t2-t1}. hist2 (\<tau> + t1)) (t + d2)) = (\<lambda>\<tau>\<in>{0..t2-(t1+d2)}. hist2 (\<tau> + (t1 + d2)))"
      unfolding b3 apply (rule restrict_ext)
      apply auto
       apply (metis add.assoc add.commute)
      using combine_blocks_wait2.prems(3) by auto
    show ?thesis
      unfolding b2(1)
      apply (rule exI[where x="WaitBlock (t1 + d2) (\<lambda>\<tau>\<in>{0..t1+d2}. ParState (if \<tau> < t1 then p1 \<tau> else p2 (\<tau> - t1)) (hist2 \<tau>)) rdy' # blks'"])
      apply auto
      subgoal
        unfolding combine_blocks_wait2(6)
        apply (rule equiv_trace_merge')
        using combine_blocks_wait2(8-10) b1 by auto
      subgoal
        apply (rule combine_blocks.combine_blocks_wait2)
        using combine_blocks_wait2(3,7-10) that b2(2)
        unfolding b4 unfolding b3 by auto
      done
  qed
  have c: ?case if "t1 + d2 > t2"
  proof -
    have c1: "t2 - t1 < d2"
      using that by auto
    obtain blks' where c2:
      "blks = WaitBlock (t2 - t1) (\<lambda>t\<in>{0..t2-t1}. ParState (restrict p2 {0..d2} t) ((\<lambda>\<tau>\<in>{0..t2-t1}. hist2 (\<tau> + t1)) t)) rdy' # blks'"
      "combine_blocks comms (WaitBlock (d2 - (t2 - t1)) (\<lambda>t\<in>{0..d2-(t2-t1)}. restrict p2 {0..d2} (t + (t2 - t1))) rdy # tr') blks2 blks'"
      using combine_blocks_elim4e[OF combine_blocks_wait2(1) c1 combine_blocks_wait2(3)]
            combine_blocks_wait2(7) by auto
    have c3: "WaitBlock t2 (\<lambda>\<tau>\<in>{0..t2}. ParState (if \<tau> < t1 then p1 \<tau> else p2 (\<tau> - t1)) (hist2 \<tau>)) rdy' =
              WaitBlock (t1 + (t2 - t1)) (\<lambda>\<tau>\<in>{0..t1+(t2-t1)}. ParState (if \<tau> < t1 then p1 \<tau> else p2 (\<tau> - t1)) (hist2 \<tau>)) rdy'"
      by auto
    have c4: "d2 - (t2 - t1) = t1 + d2 - t2"
      by auto
    have c5: "(\<lambda>t\<in>{0..d2-(t2-t1)}. restrict p2 {0..d2} (t + (t2 - t1))) =
              (\<lambda>\<tau>\<in>{0..t1+d2-t2}. if 0 \<le> \<tau> + t2 \<and> \<tau> + t2 \<le> t1 + d2 then if \<tau> + t2 < t1 then p1 (\<tau> + t2) else p2 (\<tau> + t2 - t1) else undefined)"
      unfolding c4 apply (rule restrict_ext)
      using combine_blocks_wait2 apply auto
      by (simp add: group_cancel.sub1)
    show ?thesis
      unfolding c2(1)
      apply (rule exI[where x="WaitBlock t2 (\<lambda>\<tau>\<in>{0..t2}. ParState (if \<tau> < t1 then p1 \<tau> else p2 (\<tau> - t1)) (hist2 \<tau>)) rdy' # blks'"])
      apply auto
      subgoal
        unfolding combine_blocks_wait2(6) c3
        apply (rule equiv_trace_merge')
        using combine_blocks_wait2(4,8-10) c1 by auto
      subgoal
        apply (rule combine_blocks.combine_blocks_wait3)
        using combine_blocks_wait2(3-10) that c2
        unfolding c5 unfolding c4 by auto
      done
  qed
  show ?case
    using a b c by fastforce
next
  case (combine_blocks_wait3 comms t1 t2 blks2 blks rdy2 hist hist2 rdy')
  have "\<exists>tr''.
   equiv_trace blks tr'' \<and>
   combine_blocks comms (WaitBlock (t1 - t2 + d2) (\<lambda>\<tau>\<in>{0..t1-t2+d2}. if \<tau> < t1 - t2 then p1 (\<tau> + t2) else p2 (\<tau> - (t1 - t2))) rdy # tr') blks2 tr''"
    apply (rule combine_blocks_wait3(2))
    using combine_blocks_wait3(3-10) by auto
  then obtain tr'' where a:
    "equiv_trace blks tr''"
    "combine_blocks comms (WaitBlock (t1 - t2 + d2) (\<lambda>\<tau>\<in>{0..t1-t2+d2}. if \<tau> < t1 - t2 then p1 (\<tau> + t2) else p2 (\<tau> - (t1 - t2))) rdy # tr') blks2 tr''"
    by auto
  have b: "t1 - t2 + d2 = t1 + d2 - t2"
    by auto
  have b2: "\<tau> - (t1 - t2) = \<tau> + t2 - t1" for \<tau>
    by auto
  have c: "WaitBlock (t1 - t2 + d2) (\<lambda>\<tau>\<in>{0..t1-t2+d2}. if \<tau> < t1 - t2 then p1 (\<tau> + t2) else p2 (\<tau> - (t1 - t2))) rdy =
           WaitBlock (t1 + d2 - t2) (\<lambda>\<tau>\<in>{0..t1+d2-t2}. (\<lambda>\<tau>\<in>{0..t1+d2}. if \<tau> < t1 then p1 \<tau> else p2 (\<tau> - t1)) (\<tau> + t2)) rdy"
    unfolding b apply auto
    apply (rule restrict_ext)
    using combine_blocks_wait3(3-10) by (auto simp add: b2)
  show ?case
    apply (rule exI[where x="WaitBlock t2 hist rdy' # tr''"])
    apply auto
    subgoal apply (rule equiv_trace_cons) by (rule a(1))
    apply (rule combine_blocks.combine_blocks_wait3)
    subgoal using a(2) unfolding c by auto
    using combine_blocks_wait3(3-10) by auto
qed

lemma combine_blocks_merge_right:
  "combine_blocks chs tr1 (WaitBlock d1 (restrict p1 {0..d1}) rdy # WaitBlock d2 (restrict p2 {0..d2}) rdy # tr') tr \<Longrightarrow>
   p1 d1 = p2 0 \<Longrightarrow>
   d1 > 0 \<Longrightarrow> d2 > 0 \<Longrightarrow>
   \<exists>tr''. equiv_trace tr tr'' \<and>
   combine_blocks chs tr1 (WaitBlock (d1 + d2) (\<lambda>\<tau>\<in>{0..d1+d2}. if \<tau> < d1 then p1 \<tau> else p2 (\<tau> - d1)) rdy # tr') tr''"
proof (induct chs tr1 "WaitBlock d1 (restrict p1 {0..d1}) rdy # WaitBlock d2 (restrict p2 {0..d2}) rdy # tr'" tr
       arbitrary: d1 p1 rule: combine_blocks.induct)
  case (combine_blocks_unpair1 ch comms blks1 blks ch_type v)
  then show ?case
    using combine_blocks.combine_blocks_unpair1 equiv_trace_cons by blast
next
  case (combine_blocks_wait1 comms blks1 blks rdy1 hist hist1 t rdy')
  have a: "(\<lambda>\<tau>\<in>{0..d2}. if 0 \<le> \<tau> + t \<and> \<tau> \<le> d2 then if \<tau> + t < t then p1 (\<tau> + t) else p2 (\<tau> + t - t) else undefined) =
           (\<lambda>\<tau>\<in>{0..d2}. p2 \<tau>)" if "t > 0"
    apply (rule restrict_ext)
    using combine_blocks_wait1 that by auto
  show ?case
    apply (rule exI[where x="WaitBlock t hist rdy' # blks"])
    apply auto
    apply (rule combine_blocks_wait2)
    subgoal apply (auto simp add: combine_blocks_wait1)
      unfolding a
      by (simp add: a combine_blocks_wait1.hyps(1) combine_blocks_wait1.prems(2))
    using combine_blocks_wait1 by auto
next
  case (combine_blocks_wait2 comms blks1 t2 t1 blks rdy1 hist hist1 rdy')
  have "\<exists>tr''.
   equiv_trace blks tr'' \<and>
   combine_blocks comms blks1 (WaitBlock (t2 - t1 + d2) (\<lambda>\<tau>\<in>{0..t2-t1+d2}. if \<tau> < t2 - t1 then p1 (\<tau> + t1) else p2 (\<tau> - (t2 - t1))) rdy # tr') tr''"
    apply (rule combine_blocks_wait2(2))
    using combine_blocks_wait2(3-10) by auto
  then obtain tr'' where a:
    "equiv_trace blks tr''"
    "combine_blocks comms blks1 (WaitBlock (t2 - t1 + d2) (\<lambda>\<tau>\<in>{0..t2-t1+d2}. if \<tau> < t2 - t1 then p1 (\<tau> + t1) else p2 (\<tau> - (t2 - t1))) rdy # tr') tr''"
    by auto
  have b: "t2 - t1 + d2 = t2 + d2 - t1"
    by auto
  have b2: "\<tau> - (t2 - t1) = \<tau> + t1 - t2" for \<tau>
    by auto
  have c: "WaitBlock (t2 - t1 + d2) (\<lambda>\<tau>\<in>{0..t2-t1+d2}. if \<tau> < t2 - t1 then p1 (\<tau> + t1) else p2 (\<tau> - (t2 - t1))) rdy =
           WaitBlock (t2 + d2 - t1) (\<lambda>\<tau>\<in>{0..t2+d2-t1}. (\<lambda>\<tau>\<in>{0..t2+d2}. if \<tau> < t2 then p1 \<tau> else p2 (\<tau> - t2)) (\<tau> + t1)) rdy"
    unfolding b apply auto
    apply (rule restrict_ext)
    using combine_blocks_wait2(3-10) by (auto simp add: b2)
  show ?case
    apply (rule exI[where x="WaitBlock t1 hist rdy' # tr''"])
    apply auto
    subgoal apply (rule equiv_trace_cons) by (rule a(1))
    apply (rule combine_blocks.combine_blocks_wait2)
    subgoal using a(2) unfolding c by auto
    using combine_blocks_wait2(3-10) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks hist rdy')
  have a: ?case if "t2 + d2 = t1"
  proof -
    have a1: "t1 - t2 = d2"
      using that by auto
    obtain blks' where a2:
      "blks = WaitBlock d2 (\<lambda>t\<in>{0..d2}. ParState ((\<lambda>\<tau>\<in>{0..d2}. hist1 (\<tau> + t2)) t) (restrict p2 {0..d2} t)) rdy' # blks'"
      "combine_blocks comms blks1 tr' blks'"
      using combine_blocks_elim4[OF combine_blocks_wait3(1)[unfolded a1]]
            combine_blocks_wait3(3,7) by auto
    show ?thesis
      unfolding a2(1)
      apply (rule exI[where x="WaitBlock (t2 + d2) (\<lambda>\<tau>\<in>{0..t2+d2}. ParState (hist1 \<tau>) (if \<tau> < t2 then p1 \<tau> else p2 (\<tau> - t2))) rdy' # blks'"])
      apply auto
      subgoal
        unfolding combine_blocks_wait3(6)
        apply (rule equiv_trace_merge')
        using combine_blocks_wait3(8-10) by auto
      subgoal
        unfolding that
        apply (rule combine_blocks.combine_blocks_wait1)
        using combine_blocks_wait3(3,7) a2(2) by auto
      done
  qed
  have b: ?case if "t2 + d2 < t1"
  proof -
    have b1: "d2 < t1 - t2"
      using that by auto
    obtain blks' where b2:
      "blks = WaitBlock d2 (\<lambda>t\<in>{0..d2}. ParState ((\<lambda>\<tau>\<in>{0..t1-t2}. hist1 (\<tau> + t2)) t) (restrict p2 {0..d2} t)) rdy' # blks'"
      "combine_blocks comms (WaitBlock (t1-t2-d2) (\<lambda>t\<in>{0..t1-t2-d2}. (\<lambda>\<tau>\<in>{0..t1-t2}. hist1 (\<tau> + t2)) (t + d2)) rdy1 # blks1) tr' blks'"
      using combine_blocks_elim4e[OF combine_blocks_wait3(1) b1 combine_blocks_wait3(3)]
            combine_blocks_wait3(7) by auto
    have b3: "t1 - t2 - d2 = t1 - (t2 + d2)"
      by auto
    have b4:
      "(\<lambda>t\<in>{0..t1-t2-d2}. (\<lambda>\<tau>\<in>{0..t1-t2}. hist1 (\<tau> + t2)) (t + d2)) = (\<lambda>\<tau>\<in>{0..t1-(t2+d2)}. hist1 (\<tau> + (t2 + d2)))"
      unfolding b3 apply (rule restrict_ext)
      apply auto
       apply (metis add.assoc add.commute)
      using combine_blocks_wait3.prems(3) by auto
    show ?thesis
      unfolding b2(1)
      apply (rule exI[where x="WaitBlock (t2 + d2) (\<lambda>\<tau>\<in>{0..t2+d2}. ParState (hist1 \<tau>) (if \<tau> < t2 then p1 \<tau> else p2 (\<tau> - t2))) rdy' # blks'"])
      apply auto
      subgoal
        unfolding combine_blocks_wait3(6)
        apply (rule equiv_trace_merge')
        using combine_blocks_wait3(8-10) b1 by auto
      subgoal
        apply (rule combine_blocks.combine_blocks_wait3)
        using combine_blocks_wait3(3,7-10) that b2(2)
        unfolding b4 unfolding b3 by auto
      done
  qed
  have c: ?case if "t2 + d2 > t1"
  proof -
    have c1: "t1 - t2 < d2"
      using that by auto
    obtain blks' where c2:
      "blks = WaitBlock (t1 - t2) (\<lambda>t\<in>{0..t1-t2}. ParState ((\<lambda>\<tau>\<in>{0..t1-t2}. hist1 (\<tau> + t2)) t) (restrict p2 {0..d2} t)) rdy' # blks'"
      "combine_blocks comms blks1 (WaitBlock (d2 - (t1 - t2)) (\<lambda>t\<in>{0..d2-(t1-t2)}. restrict p2 {0..d2} (t + (t1 - t2))) rdy # tr') blks'"
      using combine_blocks_elim4d[OF combine_blocks_wait3(1) c1 combine_blocks_wait3(3)]
            combine_blocks_wait3(7) by auto
    have c3: "WaitBlock t1 (\<lambda>\<tau>\<in>{0..t1}. ParState (hist1 \<tau>) (if \<tau> < t2 then p1 \<tau> else p2 (\<tau> - t2))) rdy' =
              WaitBlock (t2 + (t1 - t2)) (\<lambda>\<tau>\<in>{0..t2+(t1-t2)}. ParState (hist1 \<tau>) (if \<tau> < t2 then p1 \<tau> else p2 (\<tau> - t2))) rdy'"
      by auto
    have c4: "d2 - (t1 - t2) = t2 + d2 - t1"
      by auto
    have c5: "(\<lambda>t\<in>{0..d2-(t1-t2)}. restrict p2 {0..d2} (t + (t1 - t2))) =
              (\<lambda>\<tau>\<in>{0..t2+d2-t1}. if 0 \<le> \<tau> + t1 \<and> \<tau> + t1 \<le> t2 + d2 then if \<tau> + t1 < t2 then p1 (\<tau> + t1) else p2 (\<tau> + t1 - t2) else undefined)"
      unfolding c4 apply (rule restrict_ext)
      using combine_blocks_wait3 apply auto
      by (simp add: group_cancel.sub1)
    show ?thesis
      unfolding c2(1)
      apply (rule exI[where x="WaitBlock t1 (\<lambda>\<tau>\<in>{0..t1}. ParState (hist1 \<tau>) (if \<tau> < t2 then p1 \<tau> else p2 (\<tau> - t2))) rdy' # blks'"])
      apply auto
      subgoal
        unfolding combine_blocks_wait3(6) c3
        apply (rule equiv_trace_merge')
        using combine_blocks_wait3(4,8-10) c1 by auto
      subgoal
        apply (rule combine_blocks.combine_blocks_wait2)
        using combine_blocks_wait3(3-10) that c2
        unfolding c5 unfolding c4 by auto
      done
  qed
  show ?case
    using a b c by fastforce
qed


lemma combine_blocks_equiv_left:
  "equiv_trace tr1 tr1' \<Longrightarrow> combine_blocks chs tr1 tr2 tr \<Longrightarrow>
   \<exists>tr'. equiv_trace tr tr' \<and> combine_blocks chs tr1' tr2 tr'"
proof (induct arbitrary: tr2 tr rule: equiv_trace.induct)
  case equiv_trace_empty
  show ?case
    apply (rule exI[where x="tr"])
    using equiv_trace_empty by auto 
next
  case (equiv_trace_merge p1 d1 p2 rdy d2 tr' d)
  show ?case
    using combine_blocks_merge_left equiv_trace_merge by blast
next
  case (equiv_trace_cons tr1 tr2' ev)
  have "\<exists>tr'. equiv_trace tr tr' \<and> combine_blocks chs (ev # tr2') tr2 tr'"
    apply (rule combine_blocks_cons_left)
    apply (rule equiv_trace_cons(3))
    using equiv_trace_cons(2) by auto
  then obtain tr' where a: "equiv_trace tr tr'" "combine_blocks chs (ev # tr2') tr2 tr'"
    by auto
  show ?case
    apply (rule exI[where x="tr'"])
    using a by auto
next
  case (equiv_trace_trans tr1 tr2' tr3)
  then show ?case
    using equiv_trace.equiv_trace_trans by blast
qed

lemma combine_blocks_equiv_right:
  "equiv_trace tr2 tr2' \<Longrightarrow> combine_blocks chs tr1 tr2 tr \<Longrightarrow>
   \<exists>tr'. equiv_trace tr tr' \<and> combine_blocks chs tr1 tr2' tr'"
proof (induct arbitrary: tr1 tr rule: equiv_trace.induct)
  case equiv_trace_empty
  show ?case
    apply (rule exI[where x="tr"])
    using equiv_trace_empty by auto 
next
  case (equiv_trace_merge d1 d2 p1 p2 rdy tr)
  then show ?case
    using combine_blocks_merge_right by blast
next
  case (equiv_trace_cons tr1' tr2 ev)
  have "\<exists>tr'. equiv_trace tr tr' \<and> combine_blocks chs tr1 (ev # tr2) tr'"
    apply (rule combine_blocks_cons_right)
     apply (rule equiv_trace_cons(3))
    using equiv_trace_cons(2) by auto
  then obtain tr' where a: "equiv_trace tr tr'" "combine_blocks chs tr1 (ev # tr2) tr'"
    by auto
  show ?case
    apply (rule exI[where x="tr'"])
    using a by auto
next
  case (equiv_trace_trans tr1 tr2 tr3)
  then show ?case
    using equiv_trace.equiv_trace_trans by blast
qed

lemma combine_blocks_equiv:
  "equiv_trace tr1 tr1' \<Longrightarrow> equiv_trace tr2 tr2' \<Longrightarrow>
   combine_blocks chs tr1 tr2 tr \<Longrightarrow>
   \<exists>tr'. equiv_trace tr tr' \<and> combine_blocks chs tr1' tr2' tr'"
  using combine_blocks_equiv_left combine_blocks_equiv_right equiv_trace_trans by blast

lemma par_small1_big_continue2:
  "par_small_step p s (Some ev) p2 s2 \<Longrightarrow>
   par_big_step p2 s2 evs s3 \<Longrightarrow>
   \<exists>evs'. equiv_trace (ev # evs) evs' \<and> par_big_step p s evs' s3"
proof (induction p s "Some ev" p2 s2 arbitrary: ev evs s3 rule: par_small_step.induct)
  case (SingleS p s1 p' s2)
  show ?case
    using SingleS(2) apply (elim SingleE)
    by (metis SingleB SingleS.hyps gstate.inject(1) small1_big_continue2)
next
  case (ParDelayS rdy1 rdy2 hist hist1 hist2 t rdy p1 s1 p2 s2 p3 s3' p4 s4 chs)
  have a: "\<exists>evs'. equiv_trace (WaitBlock t hist rdy # evs) evs' \<and>
                  par_big_step (Parallel p1 chs p3) (ParState s1 s3') evs' (ParState s12 s22)"
    if aH: "s3 = ParState s12 s22"
       "par_big_step p2 s2 tr1 s12"
       "par_big_step p4 s4 tr2 s22"
       "combine_blocks chs tr1 tr2 evs" for s12 s22 tr1 tr2
  proof -
    obtain evs1 where b: "equiv_trace (WaitBlock t hist1 rdy1 # tr1) evs1" "par_big_step p1 s1 evs1 s12"
      using ParDelayS(5)[OF aH(2)] by auto
    obtain evs2 where c: "equiv_trace (WaitBlock t hist2 rdy2 # tr2) evs2" "par_big_step p3 s3' evs2 s22"
      using ParDelayS(7)[OF aH(3)] by auto
    have d: "combine_blocks chs (WaitBlock t hist1 rdy1 # tr1) (WaitBlock t hist2 rdy2 # tr2) (WaitBlock t hist rdy # evs)"
      apply (rule combine_blocks_wait1[OF aH(4)])
      using ParDelayS by auto
    obtain tr' where e:
      "equiv_trace (WaitBlock t hist rdy # evs) tr'"
      "combine_blocks chs evs1 evs2 tr'"
      using b(1) c(1) d combine_blocks_equiv by blast
    show ?thesis
      apply (rule exI[where x="tr'"]) apply auto
      apply (rule e(1))
      apply (rule ParallelB[OF b(2) c(2)])
      by (rule e(2))
  qed
  show ?case
    using ParDelayS(8) apply (elim ParallelE)
    using a by auto
next
  case (ParPairS1 ch chs p1 s1 v p2 s2 p3 s3' p4 s4)
  have a: "\<exists>evs'. equiv_trace (IOBlock ch v # evs) evs' \<and> par_big_step (Parallel p1 chs p3) (ParState s1 s3') evs' (ParState s12 s22)"
    if aH: "s3 = ParState s12 s22"
       "par_big_step p2 s2 tr1 s12"
       "par_big_step p4 s4 tr2 s22"
       "combine_blocks chs tr1 tr2 evs" for s12 s22 tr1 tr2
  proof -
    obtain evs1 where b: "equiv_trace (InBlock ch v # tr1) evs1" "par_big_step p1 s1 evs1 s12"
      using ParPairS1(3)[OF aH(2)] by auto
    obtain evs2 where c: "equiv_trace (OutBlock ch v # tr2) evs2" "par_big_step p3 s3' evs2 s22"
      using ParPairS1(5)[OF aH(3)] by auto
    have d: "combine_blocks chs (InBlock ch v # tr1) (OutBlock ch v # tr2) (IOBlock ch v # evs)"
      by (rule combine_blocks_pair1[OF ParPairS1(1) aH(4)])
    obtain tr' where e:
      "equiv_trace (IOBlock ch v # evs) tr'"
      "combine_blocks chs evs1 evs2 tr'"
      using b(1) c(1) d combine_blocks_equiv by blast
    show ?thesis
      apply (rule exI[where x="tr'"]) apply auto
       apply (rule e(1))
      apply (rule ParallelB[OF b(2) c(2)])
      by (rule e(2))
  qed
  show ?case
    using ParPairS1(6) apply (elim ParallelE)
    using a by auto
next
  case (ParPairS2 ch chs p1 s1 v p2 s2 p3 s3' p4 s4)
  have a: "\<exists>evs'. equiv_trace (IOBlock ch v # evs) evs' \<and> par_big_step (Parallel p1 chs p3) (ParState s1 s3') evs' (ParState s12 s22)"
    if aH: "s3 = ParState s12 s22"
       "par_big_step p2 s2 tr1 s12"
       "par_big_step p4 s4 tr2 s22"
       "combine_blocks chs tr1 tr2 evs" for s12 s22 tr1 tr2
  proof -
    obtain evs1 where b: "equiv_trace (OutBlock ch v # tr1) evs1" "par_big_step p1 s1 evs1 s12"
      using ParPairS2(3)[OF aH(2)] by auto
    obtain evs2 where c: "equiv_trace (InBlock ch v # tr2) evs2" "par_big_step p3 s3' evs2 s22"
      using ParPairS2(5)[OF aH(3)] by auto
    have d: "combine_blocks chs (OutBlock ch v # tr1) (InBlock ch v # tr2) (IOBlock ch v # evs)"
      by (rule combine_blocks_pair2[OF ParPairS2(1) aH(4)])
    obtain tr' where e:
      "equiv_trace (IOBlock ch v # evs) tr'"
      "combine_blocks chs evs1 evs2 tr'"
      using b(1) c(1) d combine_blocks_equiv by blast
    show ?thesis
      apply (rule exI[where x="tr'"]) apply auto
       apply (rule e(1))
      apply (rule ParallelB[OF b(2) c(2)])
      by (rule e(2))
  qed
  show ?case
    using ParPairS2(6) apply (elim ParallelE)
    using a by auto
next
  case (ParUnpairS1 p3 s3' ch chs p1 s1 ch_type v p2 s2)
  have a: "\<exists>evs'. equiv_trace (CommBlock ch_type ch v # evs) evs' \<and> par_big_step (Parallel p1 chs p3) (ParState s1 s3') evs' (ParState s12 s22)"
    if aH: "s3 = ParState s12 s22"
       "par_big_step p2 s2 tr1 s12"
       "par_big_step p3 s3' tr2 s22"
       "combine_blocks chs tr1 tr2 evs" for s12 s22 tr1 tr2
  proof -
    obtain evs' where b:
      "equiv_trace (CommBlock ch_type ch v # tr1) evs'" "par_big_step p1 s1 evs' s12"
      using ParUnpairS1(4)[OF aH(2)] by auto
    have c: "combine_blocks chs (CommBlock ch_type ch v # tr1) tr2 (CommBlock ch_type ch v # evs)"
      by (rule combine_blocks_unpair1[OF ParUnpairS1(2) aH(4)])
    obtain tr' where d:
      "equiv_trace (CommBlock ch_type ch v # evs) tr'"
      "combine_blocks chs evs' tr2 tr'"
      using b(1) combine_blocks_equiv_left c by blast
    show ?thesis
      apply (rule exI[where x="tr'"]) apply auto
      apply (rule d(1))
      by (rule ParallelB[OF b(2) aH(3) d(2)])
  qed
  show ?case
    using ParUnpairS1(5) apply (elim ParallelE)
    using a by auto
next
  case (ParUnpairS2 p1 s1 ch chs p2 s2 ch_type v p3 s3')
  have a: "\<exists>evs'. equiv_trace (CommBlock ch_type ch v # evs) evs' \<and> par_big_step (Parallel p1 chs p2) (ParState s1 s2) evs' (ParState s12 s22)"
    if aH: "s3 = ParState s12 s22"
       "par_big_step p1 s1 tr1 s12"
       "par_big_step p3 s3' tr2 s22"
       "combine_blocks chs tr1 tr2 evs" for s12 s22 tr1 tr2
  proof -
    obtain evs' where b:
      "equiv_trace (CommBlock ch_type ch v # tr2) evs'" "par_big_step p2 s2 evs' s22"
      using ParUnpairS2(4)[OF aH(3)] by auto
    have c: "combine_blocks chs tr1 (CommBlock ch_type ch v # tr2) (CommBlock ch_type ch v # evs)"
      by (rule combine_blocks_unpair2[OF ParUnpairS2(2) aH(4)])
    obtain tr' where d:
      "equiv_trace (CommBlock ch_type ch v # evs) tr'"
      "combine_blocks chs tr1 evs' tr'"
      using b(1) combine_blocks_equiv_right c by blast
    show ?thesis
      apply (rule exI[where x="tr'"]) apply auto
      apply (rule d(1))
      by (rule ParallelB[OF aH(2) b(2) d(2)])
  qed
  show ?case
    using ParUnpairS2(5) apply (elim ParallelE)
    using a by auto
qed


theorem small_to_big_par:
  "par_small_step_closure p s1 tr q s2 \<Longrightarrow>
   is_skip q \<Longrightarrow> 
   \<exists>tr'. equiv_trace tr tr' \<and> par_big_step p s1 tr' s2"
proof (induction rule: par_small_step_closure.induct)
  case (1 p s)
  show ?case
    apply (rule exI[where x="[]"])
    using par_big_step_empty 1 by auto
next
  case (2 p s p2 s2 evs p3 s3)
  obtain tr' where a: "equiv_trace evs tr'" "par_big_step p2 s2 tr' s3"
    using 2(3,4) by auto
  show ?case
    using 2(1) a par_small1_big_continue by auto
next
  case (3 p s ev p2 s2 evs p3 s3)
  obtain tr' where a: "equiv_trace evs tr'" "par_big_step p2 s2 tr' s3"
    using 3(3,4) by auto
  show ?case
    by (meson 3(1) a equiv_trace_cons equiv_trace_trans par_small1_big_continue2)
qed


end
