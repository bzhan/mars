theory SmallStep
  imports BigStepSimple
begin


subsection \<open>Small-step semantics\<close>

text \<open>small_step p s1 a p' s2 means executing p one step starting from
state s1, results in action a, remaining program p', and state s2.\<close>

inductive small_step :: "proc \<Rightarrow> state \<Rightarrow> trace_block option \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> bool" where
  assignB: "small_step (var ::= e) s None Skip (s(var := e s))"
| seqS1: "small_step p1 s ev p1' s2 \<Longrightarrow> small_step (Seq p1 p2) s ev (Seq p1' p2) s2"
| seqS2: "small_step (Seq Skip p) s None p s"
| condS1: "b s \<Longrightarrow> small_step (Cond b p1 p2) s None p1 s"
| condS2: "\<not>b s \<Longrightarrow> small_step (Cond b p1 p2) s None p2 s"
| waitS1: "d1 > 0 \<Longrightarrow> d1 < d \<Longrightarrow> small_step (Wait d) s (Some (WaitBlock d1 (\<lambda>\<tau>\<in>{0..d1}. State s) ({}, {})))
                                 (Wait (d - d1)) s"
| waitS2: "small_step (Wait d) s (Some (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {}))) Skip s"
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

text \<open>Small step semantics for parallel processes.\<close>

inductive par_small_step :: "pproc \<Rightarrow> gstate \<Rightarrow> trace_block option \<Rightarrow> pproc \<Rightarrow> gstate \<Rightarrow> bool" where
  SingleS: "small_step p s1 ev p' s2 \<Longrightarrow> par_small_step (Single p) (State s1) ev (Single p') (State s2)"
(* Add parallel steps *)


subsection \<open>Equivalence between big-step and small-step semantics\<close>

text \<open>First, we define the closure of the small-step semantics\<close>

inductive small_step_closure :: "proc \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> bool" where
  "small_step_closure p s [] p s"
| "small_step p s None p2 s2 \<Longrightarrow> small_step_closure p2 s2 evs p3 s3 \<Longrightarrow> small_step_closure p s evs p3 s3"
| "small_step p s (Some ev) p2 s2 \<Longrightarrow> small_step_closure p2 s2 evs p3 s3 \<Longrightarrow> small_step_closure p s (ev # evs) p3 s3"

text \<open>Further, we define equivalence between two traces\<close>

inductive equiv_trace :: "trace \<Rightarrow> trace \<Rightarrow> bool" where
  "equiv_trace tr1 tr2"

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
    by (rule waitS2)
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



end
