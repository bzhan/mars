theory Complete
  imports BigStepParallel
begin

subsection \<open>Proof system\<close>

inductive hoare :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50) 
  and echoice_hoare :: "assn \<Rightarrow> nat \<Rightarrow> (comm \<times> proc) list \<Rightarrow> assn \<Rightarrow> bool"
  and interrupt_hoare :: "assn \<Rightarrow> nat \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> (comm \<times> proc) list \<Rightarrow> assn \<Rightarrow> bool" where
  SkipH: "\<turnstile> {P} Skip {P}"
| AssignH: "\<turnstile> {\<lambda>s. Q (s(var := e s))} (var ::= e) {Q}"
| SendH:
    "\<turnstile> {\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and>
               (\<forall>d::real>0. Q s (tr @ [WaitBlk d (\<lambda>_. State s) ({ch}, {}), OutBlock ch (e s)])) \<and>
               Q s (tr @ [WaitBlk \<infinity> (\<lambda>_. State s) ({ch}, {})])}
         (Cm (ch[!]e))
       {Q}"
| ReceiveH: 
    "\<turnstile> {\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
               (\<forall>d::real>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlk d (\<lambda>_. State s) ({}, {ch}), InBlock ch v])) \<and>
               Q s (tr @ [WaitBlk \<infinity> (\<lambda>_. State s) ({}, {ch})])}
         (Cm (ch[?]var))
       {Q}"
| SeqH:
    "\<turnstile> {P} c1 {Q} \<Longrightarrow> \<turnstile> {Q} c2 {R} \<Longrightarrow> \<turnstile> {P} c1; c2 {R}"
| CondH:
    "\<turnstile> {P1} c1 {Q} \<Longrightarrow> \<turnstile> {P2} c2 {Q} \<Longrightarrow>
     \<turnstile> {\<lambda>s. if b s then P1 s else P2 s} (Cond b c1 c2) {Q}"
| WaitH:
    "\<turnstile> {\<lambda>s tr. if e s > 0 then Q s (tr @ [WaitBlk (e s) (\<lambda>_. State s) ({}, {})]) else Q s tr}
         (Wait e)
       {Q}"
| RepH:
    "\<turnstile> {P} c {P} \<Longrightarrow> \<turnstile> {P} (Rep c) {P}"
| IChoiceH:
    "\<turnstile> {P1} c1 {Q} \<Longrightarrow> \<turnstile> {P2} c2 {Q} \<Longrightarrow>
     \<turnstile> {\<lambda>s tr. P1 s tr \<and> P2 s tr} IChoice c1 c2 {Q}"
| EChoiceH1:
    "echoice_hoare P 0 es R"
| EChoiceH2:
    "\<turnstile> {Q} p2 {R} \<Longrightarrow>
     es ! n = (ch[!]e, p2) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)])) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d::real>0. Q s (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), OutBlock ch (e s)])) \<Longrightarrow>
     echoice_hoare P n es R \<Longrightarrow>
     echoice_hoare P (Suc n) es R"
| EChoiceH3:
    "\<turnstile> {Q} p2 {R} \<Longrightarrow>
     es ! n = (ch[?]var, p2) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d::real>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), InBlock ch v])) \<Longrightarrow>
     echoice_hoare P n es R \<Longrightarrow>
     echoice_hoare P (Suc n) es R"
| EChoiceH4:
    "echoice_hoare P (length es) es R \<Longrightarrow> \<turnstile> {P} EChoice es {R}"
| EChoiceH5:
    "P' \<Longrightarrow>\<^sub>A P \<Longrightarrow> echoice_hoare P n es R \<Longrightarrow> echoice_hoare P' n es R"
| ContH:
    "\<turnstile> {\<lambda>s tr. (\<not>b s \<longrightarrow> Q s tr) \<and>
             (\<forall>d p. 0 < d \<longrightarrow> ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                   Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]))}
         (Cont ode b)
       {Q}"
| InterruptH1:
    "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<not>b s \<longrightarrow> R s tr) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
               (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
               R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es)]))) \<Longrightarrow>
     interrupt_hoare P 0 ode b es R"
| InterruptH2:
    "\<turnstile> {Q} p2 {R} \<Longrightarrow>
     es ! n = (ch[!]e, p2) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)])) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
               (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
               Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es),
                              OutBlock ch (e (p d))])) \<Longrightarrow>
     interrupt_hoare P n ode b es R \<Longrightarrow>
     interrupt_hoare P (Suc n) ode b es R"
| InterruptH3:
    "\<turnstile> {Q} p2 {R} \<Longrightarrow>
     es ! n = (ch[?]var, p2) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
               (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
               Q ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es),
                                          InBlock ch v])) \<Longrightarrow>
     interrupt_hoare P n ode b es R \<Longrightarrow>
     interrupt_hoare P (Suc n) ode b es R"
| InterruptH4:
    "interrupt_hoare P (length es) ode b es R \<Longrightarrow> \<turnstile> {P} Interrupt ode b es {R}"
| InterruptH5:
    "P' \<Longrightarrow>\<^sub>A P \<Longrightarrow> interrupt_hoare P n ode b es R \<Longrightarrow> interrupt_hoare P' n ode b es R"
| ConseqH:
    "P' \<Longrightarrow>\<^sub>A P \<Longrightarrow> Q \<Longrightarrow>\<^sub>A Q' \<Longrightarrow> \<turnstile> {P} c {Q} \<Longrightarrow> \<turnstile> {P'} c {Q'}"

inductive big_step_echoice :: "nat \<Rightarrow> (comm \<times> proc) list \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  "i < n \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step_echoice n cs s1 (OutBlock ch (e s1) # tr2) s2"
| "(d::real) > 0 \<Longrightarrow> i < n \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step_echoice n cs s1 (WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice cs) #
                              OutBlock ch (e s1) # tr2) s2"
| "i < n \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step_echoice n cs s1 (InBlock ch v # tr2) s2"
| "(d::real) > 0 \<Longrightarrow> i < n \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step_echoice n cs s1 (WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"

inductive_cases big_step_echoiceE: "big_step_echoice n cs s1 tr s2"

lemma big_step_echoice_next_rev1:
  "big_step_echoice (Suc n) es s1 tr s2 \<Longrightarrow>
   es ! n = (Send ch e, p2) \<Longrightarrow>
   (big_step_echoice n es s1 tr s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>tr2. tr = OutBlock ch (e s1) # tr2 \<Longrightarrow> big_step p2 s1 tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>d tr2. (d::real) > 0 \<Longrightarrow>
       tr = WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice es) #
            OutBlock ch (e s1) # tr2 \<Longrightarrow> big_step p2 s1 tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (auto elim!: big_step_echoiceE)
  subgoal for i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(1))
    by (metis Pair_inject comm.inject(1) less_antisym)
  subgoal for d i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(2))
    by (metis Pair_inject comm.inject(1) less_antisym)
  subgoal for i ch' var p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(3))
    by (metis Pair_inject comm.distinct(1) less_SucE)
  subgoal for d i ch' var p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(4))
    by (metis Pair_inject comm.distinct(1) less_SucE)
  done
   
lemma big_step_echoice_next_rev2:
  "big_step_echoice (Suc n) es s1 tr s2 \<Longrightarrow>
   es ! n = (Receive ch var, p2) \<Longrightarrow>
   (big_step_echoice n es s1 tr s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>tr2 v. tr = InBlock ch v # tr2 \<Longrightarrow> big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>d tr2 v. (d::real) > 0 \<Longrightarrow>
       tr = WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice es) #
            InBlock ch v # tr2 \<Longrightarrow> big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (auto elim!: big_step_echoiceE)
  subgoal for i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(1))
    by (metis Pair_inject comm.distinct(1) less_SucE)
  subgoal for d i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(2))
    by (metis Pair_inject comm.distinct(1) less_SucE)
  subgoal for i ch' var' p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(3))
    by (metis comm.inject(2) less_antisym old.prod.inject)
  subgoal for d i ch' var' p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(4))
    by (metis Pair_inject comm.inject(2) less_SucE)
  done

lemma big_step_echoice_final:
  "big_step_echoice (length cs) cs s1 tr s2 \<longleftrightarrow> big_step (EChoice cs) s1 tr s2"
  apply (rule iffI)
  apply (auto elim!: echoiceE big_step_echoiceE)
  by (auto intro: big_step.intros big_step_echoice.intros)

lemma big_step_echoice_provable:
  assumes "\<forall>e\<in>set es. \<turnstile> {wp (snd e) Q} snd e {Q}"
  shows "n \<le> length es \<Longrightarrow> echoice_hoare
    (\<lambda>s tr. \<forall>i<n.
      case es ! i of
        (ch[!]e, p2) \<Rightarrow>
          wp p2 Q s (tr @ [OutBlock ch (e s)]) \<and>
          (\<forall>d::real>0. wp p2 Q s (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), OutBlock ch (e s)]))
      | (ch[?]var, p2) \<Rightarrow>
          (\<forall>v. wp p2 Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
          (\<forall>d::real>0. \<forall>v. wp p2 Q (s(var := v)) (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), InBlock ch v])))
    n es Q"
proof (induction n)
  case 0
  then show ?case
    by (auto intro: EChoiceH1)
next
  case (Suc n)
  have "es ! n \<in> set es"
    using Suc(2) by auto
  then have 1: "\<turnstile> {wp (snd (es ! n)) Q} (snd (es ! n)) {Q}"
    using assms(1) by auto
  show ?case
  proof (cases "es ! n")
    case (Pair cm p2)
    then show ?thesis
    proof (cases cm)
      case (Send ch e)
      show ?thesis
        apply (rule EChoiceH2[of "wp p2 Q" p2 _ es n ch e])
        subgoal using 1 Pair by auto
        subgoal using Pair Send by auto
        subgoal using Pair Send unfolding entails_def by auto
        subgoal using Pair Send unfolding entails_def by auto
        apply (rule EChoiceH5[OF _ Suc(1)])
         apply (auto simp add: entails_def)
        using Suc(2) by auto
    next
      case (Receive ch var)
      show ?thesis
        apply (rule EChoiceH3[of "wp p2 Q" p2 _ es n ch var])
        subgoal using 1 Pair by auto
        subgoal using Pair Receive by auto
        subgoal using Pair Receive unfolding entails_def by auto
        subgoal using Pair Receive unfolding entails_def by auto
        apply (rule EChoiceH5[OF _ Suc(1)])
         apply (auto simp add: entails_def)
        using Suc(2) by auto
    qed
  qed
qed

definition echoice_Valid :: "assn \<Rightarrow> nat \<Rightarrow> (comm \<times> proc) list \<Rightarrow> assn \<Rightarrow> bool" where
  "echoice_Valid P n cs Q \<longleftrightarrow>
    (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step_echoice n cs s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"


inductive big_step_interrupt :: "nat \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> (comm \<times> proc) list \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  "i < n \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
   big_step p2 s tr2 s2 \<Longrightarrow>
   big_step_interrupt n ode b cs s (OutBlock ch (e s) # tr2) s2"
| "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
   (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
   i < n \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
   rdy = rdy_of_echoice cs \<Longrightarrow>
   big_step p2 (p d) tr2 s2 \<Longrightarrow>
   big_step_interrupt n ode b cs s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                     OutBlock ch (e (p d)) # tr2) s2"
| "i < n \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
   big_step p2 (s(var := v)) tr2 s2 \<Longrightarrow>
   big_step_interrupt n ode b cs s (InBlock ch v # tr2) s2"
| "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
   (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
   i < n \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
   rdy = rdy_of_echoice cs \<Longrightarrow>
   big_step p2 ((p d)(var := v)) tr2 s2 \<Longrightarrow>
   big_step_interrupt n ode b cs s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                     InBlock ch v # tr2) s2"
| "\<not>b s \<Longrightarrow> big_step_interrupt n ode b cs s [] s"
| "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
   (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
   \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow> p d = s2 \<Longrightarrow>
   rdy = rdy_of_echoice cs \<Longrightarrow>
   big_step_interrupt n ode b cs s1 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy] s2"

inductive_cases big_step_interruptE: "big_step_interrupt n ode b cs s1 tr s2"

lemma big_step_interrupt_next_rev1:
  "big_step_interrupt (Suc n) ode b es s1 tr s2 \<Longrightarrow>
   es ! n = (Send ch e, p2) \<Longrightarrow>
   (big_step_interrupt n ode b es s1 tr s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>tr2. tr = OutBlock ch (e s1) # tr2 \<Longrightarrow>
      big_step p2 s1 tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>p d tr2.
      tr = WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es) #
           OutBlock ch (e (p d)) # tr2 \<Longrightarrow>
      d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
      (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
      big_step p2 (p d) tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (elim big_step_interruptE)
  subgoal for i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_interrupt.intros(1))
    using less_antisym by fastforce
  subgoal for d p i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_interrupt.intros(2))
    by (metis comm.inject(1) nat_neq_iff not_less_eq old.prod.inject)
  subgoal for i ch' var p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_interrupt.intros(3))
    using less_antisym by fastforce
  subgoal for d p i ch' var p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_interrupt.intros(4))
    by (metis Pair_inject comm.distinct(1) less_SucE)
  by (auto simp add: big_step_interrupt.intros(5,6))

lemma big_step_interrupt_next_rev2:
  "big_step_interrupt (Suc n) ode b es s1 tr s2 \<Longrightarrow>
   es ! n = (Receive ch var, p2) \<Longrightarrow>
   (big_step_interrupt n ode b es s1 tr s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>v tr2. tr = InBlock ch v # tr2 \<Longrightarrow>
      big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>p d v tr2.
      tr = WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es) #
           InBlock ch v # tr2 \<Longrightarrow>
      d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
      (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
      big_step p2 ((p d)(var := v)) tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
    P"
  apply (elim big_step_interruptE)
  subgoal for i ch' e p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_interrupt.intros(1))
    using less_antisym by fastforce
  subgoal for d p i ch' e p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_interrupt.intros(2))
    by (metis Pair_inject comm.distinct(1) less_SucE)
  subgoal for i ch' var' p2' v' tr2
    apply (cases "i < n")
     apply (simp add: big_step_interrupt.intros(3))
    using less_antisym by fastforce
  subgoal for d p i ch' var' p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_interrupt.intros(4))
    by (metis Pair_inject comm.inject(2) less_antisym)
  by (auto simp add: big_step_interrupt.intros(5,6))

lemma big_step_interrupt_final:
  "big_step_interrupt (length es) ode b es s1 tr s2 \<longleftrightarrow> big_step (Interrupt ode b es) s1 tr s2"
  apply (rule iffI)
  apply (auto elim!: interruptE big_step_interruptE)
  by (auto intro: big_step.intros big_step_interrupt.intros)

lemma big_step_interrupt_provable:
  assumes "\<forall>e\<in>set es. \<turnstile> {wp (snd e) R} snd e {R}"
  shows "n \<le> length es \<Longrightarrow> interrupt_hoare
    (\<lambda>s tr. (\<forall>i<n.
      case es ! i of
        (ch[!]e, p2) \<Rightarrow>
          wp p2 R s (tr @ [OutBlock ch (e s)]) \<and>
          (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
             (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
             wp p2 R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es),
                                  OutBlock ch (e (p d))]))
      | (ch[?]var, p2) \<Rightarrow>
          (\<forall>v. wp p2 R (s(var := v)) (tr @ [InBlock ch v])) \<and>
          (\<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
             (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
             wp p2 R ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es),
                                              InBlock ch v]))) \<and>
        (\<not>b s \<longrightarrow> R s tr) \<and>
        (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
           (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
           R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es)])))
    n ode b es R"
proof (induction n)
  case 0
  show ?case
    apply (rule InterruptH1)
    unfolding entails_def by auto
next
  case (Suc n)
  have "es ! n \<in> set es"
    using Suc(2) by auto
  then have 1: "\<turnstile> {wp (snd (es ! n)) R} (snd (es ! n)) {R}"
    using assms(1) by auto
  show ?case
  proof (cases "es ! n")
    case (Pair cm p2)
    then show ?thesis
    proof (cases cm)
      case (Send ch e)
      show ?thesis
        apply (rule InterruptH2[of "wp p2 R" p2 _ es n ch e])
        subgoal using 1 Pair by auto
        subgoal using Pair Send by auto
        subgoal using Pair Send unfolding entails_def by auto
        subgoal using Pair Send unfolding entails_def by auto
        apply (rule InterruptH5[OF _ Suc(1)])
         apply (auto simp add: entails_def)
        using Suc(2) by auto
    next
      case (Receive ch var)
      show ?thesis
        apply (rule InterruptH3[of "wp p2 R" p2 _ es n ch var])
        subgoal using 1 Pair by auto
        subgoal using Pair Receive by auto
        subgoal using Pair Receive unfolding entails_def by auto
        subgoal using Pair Receive unfolding entails_def by auto
        apply (rule InterruptH5[OF _ Suc(1)])
         apply (auto simp add: entails_def)
        using Suc(2) by auto
    qed
  qed
qed


definition interrupt_Valid :: "assn \<Rightarrow> nat \<Rightarrow> ODE \<Rightarrow> fform \<Rightarrow> (comm \<times> proc) list \<Rightarrow> assn \<Rightarrow> bool" where
  "interrupt_Valid P n ode b cs Q \<longleftrightarrow>
    (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step_interrupt n ode b cs s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"


theorem hoare_sound:
  "(\<turnstile> {P} c {Q} \<longrightarrow> \<Turnstile> {P} c {Q}) \<and>
   (echoice_hoare P n cs Q \<longrightarrow> echoice_Valid P n cs Q) \<and>
   (interrupt_hoare P n ode b cs Q \<longrightarrow> interrupt_Valid P n ode b cs Q)"
proof (induction rule: hoare_echoice_hoare_interrupt_hoare.induct)
  case (SkipH P)
  then show ?case
    by (simp add: Valid_skip)
next
  case (AssignH Q var e)
  then show ?case
    by (simp add: Valid_assign)
next
  case (SendH Q ch e)
  then show ?case
    by (simp add: Valid_send)
next
  case (ReceiveH Q var ch)
  then show ?case
    by (simp add: Valid_receive)
next
  case (SeqH P c1 Q c2 R)
  then show ?case
    by (simp add: Valid_seq)
next
  case (CondH P1 c1 Q P2 c2 b)
  then show ?case
    by (simp add: Valid_cond)
next
  case (WaitH Q d)
  then show ?case
    by (simp add: Valid_wait)
next
  case (RepH P c)
  then show ?case
    by (simp add: Valid_rep)
next
  case (IChoiceH P1 c1 Q P2 c2)
  then show ?case
    by (simp add: Valid_ichoice)
next
  case (EChoiceH1 P es R)
  then show ?case
    unfolding echoice_Valid_def
    by (auto elim: big_step_echoiceE)
next
  case (EChoiceH2 Q p2 R es n ch e P)
  have a: "R s2 (tr1 @ OutBlock ch (e s1) # tr2')"
    if "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))"
       "\<Turnstile> {Q} p2 {R}" "P s1 tr1" "big_step p2 s1 tr2' s2" for s1 tr1 s2 tr2'
  proof -
    have "Q s1 (tr1 @ [OutBlock ch (e s1)])"
      using that(1,3) unfolding entails_def by auto
    then show ?thesis
      using that(2,4) unfolding Valid_def by fastforce
  qed
  have b: "R s2 (tr1 @ WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice es) # OutBlock ch (e s1) # tr2')"
    if "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d::real>0. Q s (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), OutBlock ch (e s)]))"
       "\<Turnstile> {Q} p2 {R}" "P s1 tr1" "big_step p2 s1 tr2' s2" "(d::real) > 0" for d s1 tr1 s2 tr2'
  proof -
    have "Q s1 (tr1 @ [WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice es), OutBlock ch (e s1)])"
      using that(1,3,5) unfolding entails_def by auto
    then show ?thesis
      using that(2,4) unfolding Valid_def by fastforce
  qed
  show ?case
    using EChoiceH2 unfolding echoice_Valid_def
    apply (auto elim!: big_step_echoice_next_rev1)
    using a b by auto
next
  case (EChoiceH3 Q p2 R es n ch var P)
  have a: "R s2 (tr1 @ InBlock ch v # tr2')"
    if "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))"
       "\<Turnstile> {Q} p2 {R}" "P s1 tr1" "big_step p2 (s1(var := v)) tr2' s2" for s2 tr1 v tr2' s1
  proof -
    have "Q (s1(var := v)) (tr1 @ [InBlock ch v])"
      using that(1,3) unfolding entails_def by auto
    then show ?thesis
      using that(2,4) unfolding Valid_def by fastforce
  qed
  have b: "R s2 (tr1 @ WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice es) # InBlock ch v # tr2')"
    if "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d::real>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), InBlock ch v]))"
       "\<Turnstile> {Q} p2 {R}" "P s1 tr1" "big_step p2 (s1(var := v)) tr2' s2" "(d::real) > 0" for s2 tr1 d v tr2' s1
  proof -
    have "Q (s1(var := v)) (tr1 @ [WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice es), InBlock ch v])"
      using that(1,3,5) unfolding entails_def by auto
    then show ?thesis
      using that(2,4) unfolding Valid_def by fastforce
  qed
  show ?case
    using EChoiceH3 unfolding echoice_Valid_def
    apply (auto elim!: big_step_echoice_next_rev2)
    using a b by auto
next
  case (EChoiceH4 P es R)
  then show ?case
    unfolding echoice_Valid_def Valid_def big_step_echoice_final by auto
next
  case (EChoiceH5 P' P n es R)
  then show ?case
    unfolding echoice_Valid_def entails_def by blast
next
  case (ContH b Q ode)
  then show ?case
    using Valid_ode by blast
next
  case (InterruptH1 P b R ode es)
  then show ?case
    unfolding interrupt_Valid_def
    apply (auto elim!: big_step_interruptE)
    by (auto simp add: entails_def)
next
  case (InterruptH2 Q p2 R es n ch e P ode b)
  have a: "R s2 (tr1 @ OutBlock ch (e s1) # tr2')"
    if "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))"
       "\<Turnstile> {Q} p2 {R}" "P s1 tr1" "big_step p2 s1 tr2' s2" for s1 tr1 s2 tr2'
  proof -
    have "Q s1 (tr1 @ [OutBlock ch (e s1)])"
      using that(1,3) unfolding entails_def by auto
    then show ?thesis
      using that(2,4) unfolding Valid_def by fastforce
  qed
  have b: "R s2 (tr1 @ WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es) # OutBlock ch (e (p d)) # tr2')"
    if "P \<Longrightarrow>\<^sub>A
       (\<lambda>s tr.
           \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow>
                     p 0 = s \<longrightarrow>
                     (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                     Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es), OutBlock ch (e (p d))]))"
       "\<Turnstile> {Q} p2 {R}" "P (p 0) tr1" "0 < d" "ODEsol ode p d"
       "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "big_step p2 (p d) tr2' s2" for s2 tr1 d p tr2'
  proof -
    have "Q (p d) (tr1 @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es), OutBlock ch (e (p d))])"
      using that(1,3-6) unfolding entails_def by auto
    then show ?thesis
      using that(2,7) unfolding Valid_def by fastforce
  qed
  show ?case
    using InterruptH2 unfolding interrupt_Valid_def
    apply (auto elim!: big_step_interrupt_next_rev1)
    using a b by auto
next
  case (InterruptH3 Q p2 R es n ch var P ode b)
  have a: "R s2 (tr1 @ InBlock ch v # tr2')"
    if "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))"
      "\<Turnstile> {Q} p2 {R}" "P s1 tr1" "big_step p2 (s1(var := v)) tr2' s2" for s1 tr1 s2 tr2' v
  proof -
    have "Q (s1(var := v)) (tr1 @ [InBlock ch v])"
      using that(1,3) unfolding entails_def by auto
    then show ?thesis
      using that(2,4) unfolding Valid_def by fastforce
  qed
  have b: "R s2 (tr1 @ WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es) # InBlock ch v # tr2')"
    if "P \<Longrightarrow>\<^sub>A
       (\<lambda>s tr.
           \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow>
                     p 0 = s \<longrightarrow>
                     (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                     (\<forall>v. Q ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es), InBlock ch v])))"
       "\<Turnstile> {Q} p2 {R}" "P (p 0) tr1" "0 < d" "ODEsol ode p d"
       "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "big_step p2 ((p d)(var := v)) tr2' s2" for s2 tr1 d p v tr2'
  proof -
    have "Q ((p d)(var := v)) (tr1 @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es), InBlock ch v])"
      using that(1,3-6) unfolding entails_def by auto
    then show ?thesis
      using that(2,7) unfolding Valid_def by fastforce
  qed
  show ?case
    using InterruptH3 unfolding interrupt_Valid_def
    apply (auto elim!: big_step_interrupt_next_rev2)
    using a b by auto
next
  case (InterruptH4 P es ode b R)
  then show ?case
    unfolding interrupt_Valid_def Valid_def big_step_interrupt_final by auto
next
  case (InterruptH5 P' P n ode b es R)
  then show ?case
    unfolding interrupt_Valid_def entails_def by blast
next
  case (ConseqH P' P Q Q' c)
  then show ?case
    unfolding Valid_def entails_def by blast
qed


subsection \<open>Weakest precondition\<close>

definition wp :: "proc \<Rightarrow> assn \<Rightarrow> assn" where
  "wp c Q = (\<lambda>s tr. \<forall>s' tr'. big_step c s tr' s' \<longrightarrow> Q s' (tr @ tr'))"

lemma wp_Skip: "wp Skip Q = Q"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: skipE)
    using skipB by fastforce
  done

lemma wp_Assign: "wp (var ::= e) Q = (\<lambda>s. Q (s(var := e s)))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: assignE)
    using assignB by fastforce
  done

lemma wp_Send:
  "wp (Cm (ch[!]e)) Q =
    (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and>
            (\<forall>d::real>0. Q s (tr @ [WaitBlk d (\<lambda>_. State s) ({ch}, {}), OutBlock ch (e s)])) \<and>
            Q s (tr @ [WaitBlk \<infinity> (\<lambda>_. State s) ({ch}, {})]))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: sendE)
     apply (simp add: sendB1)
    using sendB2 apply blast
    using sendB3 by blast
  done

lemma wp_Receive:
  "wp (Cm (ch[?]var)) Q =
    (\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
            (\<forall>d::real>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlk d (\<lambda>_. State s) ({}, {ch}), InBlock ch v])) \<and>
            Q s (tr @ [WaitBlk \<infinity> (\<lambda>_. State s) ({}, {ch})]))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: receiveE)
     apply (simp add: receiveB1)
    using receiveB2 apply blast
    using receiveB3 by blast
  done   

lemma wp_Seq: "wp (c1; c2) Q = wp c1 (wp c2 Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: seqE)
    using seqB by fastforce
  done

lemma wp_Cond: "wp (Cond b c1 c2) Q = (\<lambda>s. if b s then wp c1 Q s else wp c2 Q s)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: condE)
    using condB1 condB2 by auto
  done

lemma wp_Wait:
  "wp (Wait e) Q =
    (\<lambda>s tr. if e s > 0 then Q s (tr @ [WaitBlk (e s) (\<lambda>_. State s) ({}, {})]) else Q s tr)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim!: waitE)
    using waitB1[of e s] waitB2[of e s] apply auto
    by fastforce
  done

lemma wp_IChoice:
  "wp (IChoice c1 c2) Q = (\<lambda>s tr. wp c1 Q s tr \<and> wp c2 Q s tr)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: ichoiceE)
    by (auto simp add: IChoiceB1 IChoiceB2)
  done

lemma wp_ODE:
  "wp (Cont ode b) Q =
    (\<lambda>s tr. (\<not>b s \<longrightarrow> Q s tr) \<and>
            (\<forall>d p. 0 < d \<longrightarrow> ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                   Q (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: contE)
    apply (auto simp add: ContB2)
    using ContB1[of b s] by fastforce
  done

lemma wp_echoice:
  "wp (EChoice es) R =
    (\<lambda>s tr. (\<forall>i<length es.
      case es ! i of
        (ch[!]e, p2) \<Rightarrow>
          wp p2 R s (tr @ [OutBlock ch (e s)]) \<and>
          (\<forall>d::real>0. wp p2 R s (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), OutBlock ch (e s)]))
      | (ch[?]var, p2) \<Rightarrow>
          (\<forall>v. wp p2 R (s(var := v)) (tr @ [InBlock ch v])) \<and>
          (\<forall>d::real>0. \<forall>v. wp p2 R (s(var := v)) (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), InBlock ch v]))))"
proof -
  have a: "R s' (tr @ tr')" if assms_a:
    "\<forall>i<length es.
       case es ! i of
       (ch[!]e, p2) \<Rightarrow>
         wp p2 R s (tr @ [OutBlock ch (e s)]) \<and>
         (\<forall>d::real>0. wp p2 R s (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), OutBlock ch (e s)]))
       | (ch[?]var, p2) \<Rightarrow>
           (\<forall>v. wp p2 R (s(var := v)) (tr @ [InBlock ch v])) \<and>
           (\<forall>d::real>0. \<forall>v. wp p2 R (s(var := v)) (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), InBlock ch v]))"
    "big_step (EChoice es) s tr' s'" for s s' tr tr'
  proof -
    have a1: "R s' (tr @ OutBlock ch (e s) # tr2)"
      if "i < length es" "es ! i = (ch[!]e, p2)" "big_step p2 s tr2 s'" for ch tr2 i e p2
    proof -
      have "wp p2 R s (tr @ [OutBlock ch (e s)])"
        using assms_a(1) that(1,2) by fastforce
      then show ?thesis
        unfolding wp_def using that(3) by auto
    qed
    have a2: "R s' (tr @ WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es) # OutBlock ch (e s) # tr2)"
      if "0 < (d::real)" "i < length es" "es ! i = (ch[!]e, p2)" "big_step p2 s tr2 s'" for d ch e tr2 i p2
    proof -
      have "wp p2 R s (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), OutBlock ch (e s)])"
        using assms_a(1) that(1-3) by fastforce
      then show ?thesis
        unfolding wp_def using that(4) by auto
    qed
    have a3: "R s' (tr @ InBlock ch v # tr2)"
      if "i < length es" "es ! i = (ch[?]var, p2)" "big_step p2 (s(var := v)) tr2 s'" for ch v tr2 i var p2
    proof -
      have "wp p2 R (s(var := v)) (tr @ [InBlock ch v])"
        using assms_a(1) that(1,2) by fastforce
      then show ?thesis
        unfolding wp_def using that(3) by auto
    qed
    have a4: "R s' (tr @ WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es) # InBlock ch v # tr2)"
      if "0 < (d::real)" "i < length es" "es ! i = (ch[?]var, p2)" "big_step p2 (s(var := v)) tr2 s'" for d ch v tr2 i var p2
    proof -
      have "wp p2 R (s(var := v)) (tr @ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), InBlock ch v])"
        using assms_a(1) that(1-3) by fastforce
      then show ?thesis
        unfolding wp_def using that(4) by auto
    qed
    from assms_a(2) show ?thesis
      apply (auto elim!: echoiceE)
      using a1 a2 a3 a4 by auto
  qed
  show ?thesis
    apply (rule ext) apply (rule ext)
    subgoal for s tr
      apply (auto simp add: wp_def)
      subgoal for i cm p2
        apply (cases cm)
        subgoal for ch e
          by (auto simp add: wp_def intro: big_step.intros)
        subgoal for ch var
          by (auto simp add: wp_def intro: big_step.intros)
        done
      subgoal for s' tr'
        using a by auto
      done
    done
qed

lemma wp_interrupt:
  "wp (Interrupt ode b es) R =
    (\<lambda>s tr. (\<forall>i<length es.
      case es ! i of
        (ch[!]e, p2) \<Rightarrow>
          wp p2 R s (tr @ [OutBlock ch (e s)]) \<and>
          (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
             (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
             wp p2 R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es),
                                  OutBlock ch (e (p d))]))
      | (ch[?]var, p2) \<Rightarrow>
          (\<forall>v. wp p2 R (s(var := v)) (tr @ [InBlock ch v])) \<and>
          (\<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
             (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
             wp p2 R ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es),
                                              InBlock ch v]))) \<and>
        (\<not>b s \<longrightarrow> R s tr) \<and>
        (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
           (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
           R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es)])))"
proof -
  have a: "R s tr" if "\<forall>s' tr'. big_step (Interrupt ode b es) s tr' s' \<longrightarrow> R s' (tr @ tr')" "\<not> b s" for s tr
  proof -
    have "big_step (Interrupt ode b es) s [] s"
      using that(2) by (auto intro: big_step.intros)
    then show ?thesis
      using that(1) by fastforce
  qed
  have b: "R s' (tr @ tr')" if assms_b:
    "\<forall>i<length es.
       case es ! i of
       (ch[!]e, p2) \<Rightarrow>
         wp p2 R s (tr @ [OutBlock ch (e s)]) \<and>
         (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow>
                    p 0 = s \<longrightarrow>
                    (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                    wp p2 R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es), OutBlock ch (e (p d))]))
       | (ch[?]var, p2) \<Rightarrow>
           (\<forall>v. wp p2 R (s(var := v)) (tr @ [InBlock ch v])) \<and>
           (\<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow>
                        p 0 = s \<longrightarrow>
                        (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                        wp p2 R ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es), InBlock ch v]))"
    "\<not> b s \<longrightarrow> R s tr"
    "\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow>
              p 0 = s \<longrightarrow>
              (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
              \<not> b (p d) \<longrightarrow> R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es)])"
    "big_step (Interrupt ode b es) s tr' s'" for s s' tr tr'
  proof -
    have b1: "R s' (tr @ OutBlock ch (e s) # tr2)"
      if "i < length es" "es ! i = (ch[!]e, p2)" "big_step p2 s tr2 s'" for ch e tr2 i p2
    proof -
      have "wp p2 R s (tr @ [OutBlock ch (e s)])"
        using assms_b(1) that(1,2) by fastforce
      then show ?thesis
        unfolding wp_def using that(3) by auto
    qed
    have b2: "R s' (tr @ WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es) # OutBlock ch (e (p d)) # tr2)"
      if "0 < d" "ODEsol ode p d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "i < length es" "es ! i = (ch[!]e, p2)"
         "big_step p2 (p d) tr2 s'" "s = p 0" for ch e p d tr2 p2 i
    proof -
      have "wp p2 R (p d) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es), OutBlock ch (e (p d))])"
        using assms_b(1) that(1-5,7) by fastforce
      then show ?thesis
        unfolding wp_def using that(6) by auto
    qed
    have b3: "R s' (tr @ InBlock ch v # tr2)"
      if "i < length es" "es ! i = (ch[?]var, p2)" "big_step p2 (s(var := v)) tr2 s'" for ch v tr2 i var p2
    proof -
      have "wp p2 R (s(var := v)) (tr @ [InBlock ch v])"
        using assms_b(1) that(1,2) by fastforce
      then show ?thesis
        unfolding wp_def using that(3) by auto
    qed
    have b4: "R s' (tr @ WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es) # InBlock ch v # tr2)"
      if "0 < d" "ODEsol ode p d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "i < length es" "es ! i = (ch[?]var, p2)"
       "big_step p2 ((p d)(var := v)) tr2 s'" "s = p 0" for d ch v tr2 i var p2 p
    proof -
      have "wp p2 R ((p d)(var := v)) (tr @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice es), InBlock ch v])"
        using assms_b(1) that(1-5,7) by fastforce
      then show ?thesis
        unfolding wp_def using that(6) by auto
    qed
    from assms_b(4) show ?thesis
      apply (auto elim!: interruptE)
      using b1 b2 b3 b4 assms_b(2,3) by auto
  qed
  show ?thesis
    apply (rule ext) apply (rule ext)
    subgoal for s tr
      apply (auto simp add: wp_def)
      subgoal for i cm p2
        apply (cases cm)
        subgoal for ch e
          by (auto simp add: wp_def intro: big_step.intros)
        subgoal for ch var
          by (auto simp add: wp_def intro: big_step.intros)
        done
      subgoal by (rule a)
      subgoal using InterruptB2 by blast
      subgoal for s' tr' using b by blast
      subgoal for s' tr' using b by blast
      done
    done
qed


lemma wp_is_pre: "\<turnstile> {wp c Q} c {Q}"
proof (induction c arbitrary: Q)
  case (Cm cm)
  then show ?case
  proof (cases cm)
    case (Send ch e)
    show ?thesis
      unfolding Send wp_Send
      by (rule SendH)
  next
    case (Receive ch v)
    show ?thesis
      unfolding Receive wp_Receive
      by (rule ReceiveH)
  qed
next
  case Skip
  then show ?case
    unfolding wp_Skip by (rule SkipH)
next
  case (Assign v e)
  then show ?case
    unfolding wp_Assign by (rule AssignH)
next
  case (Seq c1 c2)
  then show ?case
    unfolding wp_Seq by (rule SeqH)
next
  case (Cond x1a c1 c2)
  then show ?case
    unfolding wp_Cond by (rule CondH)
next
  case (Wait e)
  then show ?case
    unfolding wp_Wait by (rule WaitH)
next
  case (IChoice c1 c2)
  then show ?case
    unfolding wp_IChoice by (rule IChoiceH)
next
  case (EChoice es)
  show ?case
    unfolding wp_echoice
    apply (rule EChoiceH4)
    apply (rule big_step_echoice_provable)
    using EChoice by auto
next
  case (Rep c)
  show ?case
    apply (rule ConseqH[where P="wp (Rep c) Q" and Q="wp (Rep c) Q"])
    subgoal by simp
    subgoal unfolding entails_def wp_def apply auto
      using RepetitionB1 by fastforce
    apply (rule RepH)
    apply (rule ConseqH[where Q="wp (Rep c) Q"])
      prefer 2 apply simp
     prefer 2 apply (rule Rep)
    unfolding entails_def wp_def apply auto
    subgoal for s1 tr1 s2 tr2 s3 tr3
      using RepetitionB2 by auto
    done
next
  case (Cont ode b)
  then show ?case
    unfolding wp_ODE by (rule ContH)
next
  case (Interrupt ode b es)
  show ?case
    unfolding wp_interrupt
    apply (rule InterruptH4)
    apply (rule big_step_interrupt_provable)
    using Interrupt by auto
qed

theorem hoare_complete:
  "\<Turnstile> {P} c {Q} \<Longrightarrow> \<turnstile> {P} c {Q}"
  apply (rule ConseqH[where P="wp c Q" and Q=Q])
    apply (auto simp add: entails_def)
   apply (auto simp add: Valid_def wp_def)[1]
  by (rule wp_is_pre)

theorem hoare_sound_complete:
  "\<turnstile> {P} c {Q} \<longleftrightarrow> \<Turnstile> {P} c {Q}"
  using hoare_sound hoare_complete by auto


subsection \<open>Completeness for parallel programs\<close>

inductive par_hoare :: "gs_assn \<Rightarrow> pproc \<Rightarrow> gassn \<Rightarrow> bool" ("\<turnstile>\<^sub>p ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<turnstile> {\<lambda>s tr. P s \<and> tr = []} c {Q} \<Longrightarrow>
   \<turnstile>\<^sub>p {sing_assn P} (Single c) {sing_gassn Q}"
| "\<turnstile>\<^sub>p {P1} p1 {Q1} \<Longrightarrow> \<turnstile>\<^sub>p {P2} p2 {Q2} \<Longrightarrow>
   \<turnstile>\<^sub>p {par_assn P1 P2} (Parallel p1 chs p2) {sync_gassn chs Q1 Q2}"
| "\<turnstile>\<^sub>p {P} c {Q} \<Longrightarrow> \<forall>s. P' s \<longrightarrow> P s \<Longrightarrow> \<forall>s tr. Q s tr \<longrightarrow> Q' s tr \<Longrightarrow>
   \<turnstile>\<^sub>p {P'} c {Q'}"

theorem par_hoare_sound:
  "\<turnstile>\<^sub>p {P} c {Q} \<Longrightarrow> \<Turnstile>\<^sub>p {P} c {Q}"
proof (induction rule: par_hoare.induct)
  case (1 P c Q)
  show ?case
    apply (rule ParValid_Single)
    using hoare_sound_complete 1 by auto
next
  case (2 P1 p1 Q1 P2 p2 Q2 chs)
  show ?case
    apply (rule ParValid_Parallel)
    using 2 by auto
next
  case (3 P c Q P' Q')
  then show ?case
    unfolding ParValid_def by auto
qed


lemma ParValid_to_Valid:
  assumes "\<Turnstile>\<^sub>p {sing_assn P} Single c {sing_gassn Q}"
  shows "\<Turnstile> {\<lambda>s tr. P s \<and> tr = []} c {Q}"
  using assms unfolding Valid_def ParValid_def
  using SingleB by force


definition sp :: "proc \<Rightarrow> fform \<Rightarrow> assn" where
  "sp c P = (\<lambda>s' tr. \<exists>s. P s \<and> big_step c s tr s')"

lemma Valid_sp:
  "\<Turnstile> {\<lambda>s tr. P s \<and> tr = []} c {sp c P}"
  unfolding Valid_def sp_def by auto


definition par_sp :: "pproc \<Rightarrow> gs_assn \<Rightarrow> gassn" where
  "par_sp c P = (\<lambda>s' tr'. \<exists>s. P s \<and> par_big_step c s tr' s')"

lemma par_sp_single:
  "par_sp (Single c) (sing_assn P) = sing_gassn (sp c P)"
  unfolding par_sp_def apply (rule ext) apply (rule ext)
  subgoal for s' tr'
    apply (cases s')
    subgoal for s1
      apply (auto simp add: sp_def)
      using SingleE apply fastforce
      using SingleB sing_assn.simps(1) by blast
    subgoal for s1 s2
      using SingleE by fastforce
    done
  done

lemma par_sp_parallel:
  "par_sp (Parallel p1 chs p2) (par_assn P1 P2) =
   sync_gassn chs (par_sp p1 P1) (par_sp p2 P2)"
  unfolding par_sp_def apply (rule ext) apply (rule ext)
  subgoal for s' tr'
    apply (cases s')
    subgoal for s1
      using ParallelE by fastforce
    subgoal for s1 s2
      apply auto
      subgoal apply (elim ParallelE) by auto
      using ParallelB by force
    done
  done

inductive wf_pre :: "pproc \<Rightarrow> gs_assn \<Rightarrow> bool" where
  "wf_pre (Single c) (sing_assn P)"
| "wf_pre p1 P1 \<Longrightarrow> wf_pre p2 P2 \<Longrightarrow> wf_pre (Parallel p1 chs p2) (par_assn P1 P2)"

inductive_cases wf_pre_Single: "wf_pre (Single c) P"
inductive_cases wf_pre_Parallel: "wf_pre (Parallel p1 chs p2) P"

lemma par_sp_is_post: "wf_pre c P \<Longrightarrow> \<turnstile>\<^sub>p {P} c {par_sp c P}"
proof (induction c arbitrary: P)
  case (Single p)
  then show ?case
    apply (elim wf_pre_Single)
    apply (auto simp add: par_sp_single)
    apply (rule par_hoare.intros(1))
    apply (rule hoare_complete)
    by (rule Valid_sp)
next
  case (Parallel p1 chs p2)
  show ?case
    using Parallel(3) apply (elim wf_pre_Parallel)
    apply (auto simp add: par_sp_parallel)
    apply (rule par_hoare.intros(2))
    using Parallel(1,2) by auto
qed


theorem par_hoare_complete:
  "wf_pre c P \<Longrightarrow> \<Turnstile>\<^sub>p {P} c {Q} \<Longrightarrow> \<turnstile>\<^sub>p {P} c {Q}"
  apply (rule par_hoare.intros(3))
  apply (rule par_sp_is_post)
    apply assumption
   apply simp
  using ParValid_def par_sp_def by auto

theorem par_hoare_sound_complete:
  assumes "wf_pre c P"
  shows "\<turnstile>\<^sub>p {P} c {Q} \<longleftrightarrow> \<Turnstile>\<^sub>p {P} c {Q}"
  using par_hoare_sound par_hoare_complete assms by auto


end
