theory Complete
  imports BigStepContinuous
begin

subsection \<open>Proof system\<close>

inductive hoare :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50) 
  and echoice_hoare :: "assn \<Rightarrow> nat \<Rightarrow> (comm \<times> proc) list \<Rightarrow> assn \<Rightarrow> bool" where
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
    "echoice_hoare P 0 es R"
| EChoiceH2:
    "\<turnstile> {Q} p2 {R} \<Longrightarrow>
     es ! n = (ch[!]e, p2) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)])) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)])) \<Longrightarrow>
     echoice_hoare P n es R \<Longrightarrow>
     echoice_hoare P (Suc n) es R"
| EChoiceH3:
    "\<turnstile> {Q} p2 {R} \<Longrightarrow>
     es ! n = (ch[?]var, p2) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<Longrightarrow>
     P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v])) \<Longrightarrow>
     echoice_hoare P n es R \<Longrightarrow>
     echoice_hoare P (Suc n) es R"
| EChoiceH4:
    "echoice_hoare P (length es) es R \<Longrightarrow>
     \<turnstile> {P} EChoice es {R}"
| EChoiceH5:
    "P' \<Longrightarrow>\<^sub>A P \<Longrightarrow> echoice_hoare P n es R \<Longrightarrow> echoice_hoare P' n es R"
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

inductive big_step_echoice :: "nat \<Rightarrow> (comm \<times> proc) list \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  "i < n \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step_echoice n cs s1 (OutBlock ch (e s1) # tr2) s2"
| "d > 0 \<Longrightarrow> i < n \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step_echoice n cs s1 (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice cs) #
                              OutBlock ch (e s1) # tr2) s2"
| "i < n \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step_echoice n cs s1 (InBlock ch v # tr2) s2"
| "d > 0 \<Longrightarrow> i < n \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step_echoice n cs s1 (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"

inductive_cases big_step_echoiceE: "big_step_echoice n cs s1 tr s2"

lemma big_step_echoice_next:
  "big_step_echoice n es s1 tr2 s2 \<Longrightarrow> big_step_echoice (Suc n) es s1 tr2 s2"
  apply (auto elim!: big_step_echoiceE)
  by (rule big_step_echoice.intros, auto)+

lemma big_step_echoice_next_rev1:
  "big_step_echoice (Suc n) es s1 tr s2 \<Longrightarrow>
   es ! n = (Send ch e, p2) \<Longrightarrow>
   (big_step_echoice n es s1 tr s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>tr2. tr = OutBlock ch (e s1) # tr2 \<Longrightarrow> big_step p2 s1 tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   (\<And>d tr2. d > 0 \<Longrightarrow> tr = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es) #
                           OutBlock ch (e s1) # tr2 \<Longrightarrow> big_step p2 s1 tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (auto elim!: big_step_echoiceE)
  subgoal for i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(1))
    using less_antisym by fastforce
  subgoal for d i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(2))
    by (metis Pair_inject comm.inject(1) less_antisym)
  subgoal for i ch' var p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(3))
    using less_antisym by fastforce
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
   (\<And>d tr2 v. d > 0 \<Longrightarrow> tr = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es) #
                           InBlock ch v # tr2 \<Longrightarrow> big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (auto elim!: big_step_echoiceE)
  subgoal for i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(1))
    using less_antisym by fastforce
  subgoal for d i ch' e' p2' tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(2))
    by (metis Pair_inject comm.distinct(1) less_SucE)
  subgoal for i ch' var' p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(3))
    using less_antisym by fastforce
  subgoal for d i ch' var' p2' v tr2
    apply (cases "i < n")
     apply (simp add: big_step_echoice.intros(4))
    by (metis comm.inject(2) less_antisym old.prod.inject)
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
          (\<forall>d>0. wp p2 Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)]))
      | (ch[?]var, p2) \<Rightarrow>
          (\<forall>v. wp p2 Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
          (\<forall>d>0. \<forall>v. wp p2 Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v])))
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
   

theorem hoare_sound:
  "(\<turnstile> {P} c {Q} \<longrightarrow> Valid P c Q) \<and>
   (echoice_hoare P n cs Q \<longrightarrow> echoice_Valid P n cs Q)"
proof (induction rule: hoare_echoice_hoare.induct)
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
  case (EChoiceH1 P es R)
  then show ?case
    unfolding echoice_Valid_def
    by (auto elim: big_step_echoiceE)
next
  case (EChoiceH2 Q p2 R es n ch e P)
  have a: "R s2 (tr1 @ OutBlock ch (e s1) # tr2')"
    if "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))"
       "Valid Q p2 R" "P s1 tr1" "big_step p2 s1 tr2' s2" for s1 tr1 s2 tr2'
  proof -
    have "Q s1 (tr1 @ [OutBlock ch (e s1)])"
      using that(1,3) unfolding entails_def by auto
    then show ?thesis
      using that(2,4) unfolding Valid_def by fastforce
  qed
  have b: "R s2 (tr1 @ WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es) # OutBlock ch (e s1) # tr2')"
    if "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)]))"
       "Valid Q p2 R" "P s1 tr1" "big_step p2 s1 tr2' s2" "d > 0" for d s1 tr1 s2 tr2'
  proof -
    have "Q s1 (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es), OutBlock ch (e s1)])"
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
       "Valid Q p2 R" "P s1 tr1" "big_step p2 (s1(var := v)) tr2' s2" for s2 tr1 v tr2' s1
  proof -
    have "Q (s1(var := v)) (tr1 @ [InBlock ch v])"
      using that(1,3) unfolding entails_def by auto
    then show ?thesis
      using that(2,4) unfolding Valid_def by fastforce
  qed
  have b: "R s2 (tr1 @ WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es) # InBlock ch v # tr2')"
    if "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v]))"
       "Valid Q p2 R" "P s1 tr1" "big_step p2 (s1(var := v)) tr2' s2" "d > 0" for s2 tr1 d v tr2' s1
  proof -
    have "Q (s1(var := v)) (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es), InBlock ch v])"
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

lemma wp_echoice:
  "wp (EChoice es) R =
    (\<lambda>s tr. (\<forall>i<length es.
      case es ! i of
        (ch[!]e, p2) \<Rightarrow>
          wp p2 R s (tr @ [OutBlock ch (e s)]) \<and>
          (\<forall>d>0. wp p2 R s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)]))
      | (ch[?]var, p2) \<Rightarrow>
          (\<forall>v. wp p2 R (s(var := v)) (tr @ [InBlock ch v])) \<and>
          (\<forall>d>0. \<forall>v. wp p2 R (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v]))))"
proof -
  have a: "R s' (tr @ tr')" if assms_a:
    "\<forall>i<length es.
       case es ! i of
       (ch[!]e, p2) \<Rightarrow>
         wp p2 R s (tr @ [OutBlock ch (e s)]) \<and>
         (\<forall>d>0. wp p2 R s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)]))
       | (ch[?]var, p2) \<Rightarrow>
           (\<forall>v. wp p2 R (s(var := v)) (tr @ [InBlock ch v])) \<and>
           (\<forall>d>0. \<forall>v. wp p2 R (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v]))"
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
    have a2: "R s' (tr @ WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es) # OutBlock ch (e s) # tr2)"
      if "0 < d" "i < length es" "es ! i = (ch[!]e, p2)" "big_step p2 s tr2 s'" for d ch e tr2 i p2
    proof -
      have "wp p2 R s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)])"
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
    have a4: "R s' (tr @ WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es) # InBlock ch v # tr2)"
      if "0 < d" "i < length es" "es ! i = (ch[?]var, p2)" "big_step p2 (s(var := v)) tr2 s'" for d ch v tr2 i var p2
    proof -
      have "wp p2 R (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v])"
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


definition wp_echoice :: "nat \<Rightarrow> (comm \<times> proc) list \<Rightarrow> assn \<Rightarrow> assn" where
  "wp_echoice = undefined"

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
