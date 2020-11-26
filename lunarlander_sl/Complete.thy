theory Complete
  imports BigStepContinuous
begin

subsection \<open>Proof system\<close>

inductive hoare :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50) where
  SkipH: "\<turnstile> {P} Skip {P}"
| AssignH: "\<turnstile> {\<lambda>s. Q (s(var := e s))} (var ::= e) {Q}"
| SendH:
    "\<turnstile> {\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and>
               (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), OutBlock ch (e s)]))}
         (Cm (ch[!]e))
       {Q}"
| ReceiveH: 
    "\<turnstile> {\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
           (\<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), InBlock ch v]))}
         (Cm (ch[?]var))
       {Q}"
| SeqH:
    "\<turnstile> {P} c1 {Q} \<Longrightarrow> \<turnstile> {Q} c2 {R} \<Longrightarrow> \<turnstile> {P} c1; c2 {R}"
| WaitH1:
    "d > 0 \<Longrightarrow>
     \<turnstile> {\<lambda>s tr. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})])}
         (Wait d)
       {Q}"
| WaitH2:
    "\<not>d > 0 \<Longrightarrow> \<turnstile> {Q} Wait d {Q}"
| RepH:
    "\<turnstile> {P} c {P} \<Longrightarrow> \<turnstile> {P} (Rep c) {P}"
| IChoiceH:
    "\<turnstile> {P1} c1 {Q} \<Longrightarrow> \<turnstile> {P2} c2 {Q} \<Longrightarrow>
     \<turnstile> {\<lambda>s tr. P1 s tr \<and> P2 s tr} IChoice c1 c2 {Q}"
| EChoiceH1:
    "(\<exists>Q. \<turnstile> {Q} p2 {R} \<and>
         (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
         (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)])))) \<Longrightarrow>
     \<turnstile> {P} EChoice es {R} \<Longrightarrow>
     \<turnstile> {P} EChoice ((ch[!]e, p2) # es) {R}"
| EChoiceH2:
    "(\<exists>Q. \<turnstile> {Q} p2 {R} \<and>
         (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
         (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v])))) \<Longrightarrow>
     \<turnstile> {P} EChoice es {R} \<Longrightarrow>
     \<turnstile> {P} EChoice ((ch[?]var, p2) # es) {R}"
| ContH:
    "\<turnstile> {\<lambda>s tr. (\<not>b s \<longrightarrow> Q s tr) \<and>
             (\<forall>d p. 0 < d \<longrightarrow> ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
                   Q (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})]))}
         (Cont ode b)
       {Q}"
| InterruptH1:
    "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<not>b s \<longrightarrow> R s tr) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. (\<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
               (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow> \<not>b (p d) \<longrightarrow>
               R (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs)]))) \<Longrightarrow>
     \<turnstile> {P} Interrupt ode b [] {R}"
| InterruptH2:
    "(\<exists>Q. \<turnstile> {Q} p2 {R} \<and>
         (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
         (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                    (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                    Q (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs),
                                   OutBlock ch (e (p d))])))) \<Longrightarrow>
     \<turnstile> {P} Interrupt ode b es {R} \<Longrightarrow>
     \<turnstile> {P} Interrupt ode b ((ch[!]e, p2) # es) {R}"
| InterruptH3:
    "(\<exists>Q. Valid Q p2 R \<and>
         (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
         (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>p v. ODEsol ode p d \<longrightarrow> p 0 = s \<longrightarrow>
                    (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
                    Q ((p d)(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (rdy_of_echoice cs),
                                               InBlock ch v])))) \<Longrightarrow>
     \<turnstile> {P} Interrupt ode b es {R} \<Longrightarrow>
     \<turnstile> {P} Interrupt ode b ((ch[?]var, p2) # es) {R}"

theorem hoare_sound:
  "\<turnstile> {P} c {Q} \<Longrightarrow> Valid P c Q"
proof (induction rule: hoare.induct)
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
  case (WaitH1 Q d)
  then show ?case
    by (simp add: Valid_wait)
next
  case (WaitH2 Q d)
  then show ?case
    by (simp add: Valid_wait2)
next
  case (RepH P c)
  then show ?case
    by (simp add: Valid_rep)
next
  case (IChoiceH P1 c1 Q P2 c2)
  then show ?case
    by (simp add: Valid_ichoice)
next
  case (EChoiceH1 p2 R P ch e es)
  then show ?case
    sorry
next
  case (EChoiceH2 p2 R P var ch es)
  then show ?case
    sorry
next
  case (ContH b Q ode)
  then show ?case
    using Valid_ode by blast
next
  case (InterruptH1 P b R ode cs)
  then show ?case
    sorry
next
  case (InterruptH2 p2 R P ch e ode b cs es)
  then show ?case
    sorry
next
  case (InterruptH3 p2 R P var ch ode b cs es)
  then show ?case
    sorry
qed


subsection \<open>Weakest precondition\<close>

term big_step

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
              (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), OutBlock ch (e s)])))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: sendE)
     apply (simp add: sendB1)
    using sendB2 by blast
  done

lemma wp_Receive:
  "wp (Cm (ch[?]var)) Q =
    (\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
           (\<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), InBlock ch v])))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: receiveE)
     apply (simp add: receiveB1)
    using receiveB2 by blast
  done   

lemma wp_Seq: "wp (c1; c2) Q = wp c1 (wp c2 Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: seqE)
    using seqB by fastforce
  done

lemma wp_Wait1:
  assumes "d > 0"
  shows "wp (Wait d) Q =
    (\<lambda>s tr. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})]))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: waitE)
    using assms waitB1 apply blast
    using assms waitE by blast
  done

lemma wp_Wait2:
  assumes "\<not>d > 0"
  shows "wp (Wait d) Q = Q"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: waitE)
    using assms waitB2 apply fastforce
    apply (elim waitE)
    using assms by auto
  done

lemma wp_Rep:
  "wp (Rep c) Q = wp (c; Rep C) Q"
  sorry


end