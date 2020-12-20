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
| CondH:
    "\<turnstile> {P1} c1 {Q} \<Longrightarrow> \<turnstile> {P2} c2 {Q} \<Longrightarrow>
     \<turnstile> {\<lambda>s. if b s then P1 s else P2 s} (Cond b c1 c2) {Q}"
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
| ConseqH:
    "P' \<Longrightarrow>\<^sub>A P \<Longrightarrow> Q \<Longrightarrow>\<^sub>A Q' \<Longrightarrow> \<turnstile> {P} c {Q} \<Longrightarrow> \<turnstile> {P'} c {Q'}"

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
  case (CondH P1 c1 Q P2 c2 b)
  then show ?case
    by (simp add: Valid_cond)
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

lemma wp_Cond: "wp (Cond b c1 c2) Q = (\<lambda>s. if b s then wp c1 Q s else wp c2 Q s)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: condE)
    using condB1 condB2 by auto
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
                   Q (p d) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})])))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (auto simp add: wp_def elim: contE)
    apply (auto simp add: ContB2)
    using ContB1[of b s] by fastforce
  done

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
  case (Wait d)
  show ?case
  proof (cases "d > 0")
    case True
    then show ?thesis
      unfolding wp_Wait1[OF True]
      by (rule WaitH1)
  next
    case False
    then show ?thesis
      unfolding wp_Wait2[OF False]
      by (rule WaitH2)
  qed
next
  case (IChoice c1 c2)
  then show ?case
    unfolding wp_IChoice by (rule IChoiceH)
next
  case (EChoice x)
  then show ?case sorry
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
  case (Cont x1a x2)
  then show ?case
    unfolding wp_ODE by (rule ContH)
next
  case (Interrupt x1a x2 x3)
  then show ?case sorry
qed


theorem hoare_complete:
  "Valid P c Q \<Longrightarrow> \<turnstile> {P} c {Q}"
  apply (rule ConseqH[where P="wp c Q" and Q=Q])
    apply (auto simp add: entails_def)
   apply (auto simp add: Valid_def wp_def)[1]
  by (rule wp_is_pre)

theorem hoare_sound_complete:
  "\<turnstile> {P} c {Q} \<longleftrightarrow> Valid P c Q"
  using hoare_sound hoare_complete by auto


end
