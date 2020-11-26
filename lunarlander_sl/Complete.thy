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
| WaitH:
    "\<turnstile> {\<lambda>s tr. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})])}
         (Wait d)
       {Q}"
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


end
