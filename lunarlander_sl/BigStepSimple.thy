theory BigStepSimple
  imports Analysis_More
begin

subsection \<open>Syntax\<close>

text \<open>Channel names\<close>
type_synonym cname = string

text \<open>Ready information.
  First component is set of channels that are ready to output.
  Second component is set of channels that are ready to input.\<close>
type_synonym rdy_info = "cname set \<times> cname set"

text \<open>Communications\<close>
datatype comm =
  Send cname exp        ("_[!]_" [110,108] 100)
| Receive cname var     ("_[?]_" [110,108] 100)

text \<open>HCSP processes\<close>
datatype proc =
  Cm comm
| Skip
| Assign var exp             ("_ ::= _" [99,95] 94)
| Seq proc proc           ("_; _" [91,90] 90)
| Cond fform proc proc        ("IF _ THEN _ ELSE _ FI" [95,94] 93)
| Wait real  \<comment> \<open>Waiting for a specified amount of time\<close>
| IChoice proc proc  \<comment> \<open>Nondeterminism\<close>
| EChoice "(comm \<times> proc) list"  \<comment> \<open>External choice\<close>
| Rep proc   \<comment> \<open>Nondeterministic repetition\<close>
| Cont ODE fform  \<comment> \<open>ODE with boundary\<close>
| Interrupt ODE fform "(comm \<times> proc) list"  \<comment> \<open>Interrupt\<close>

text \<open>Parallel of several HCSP processes\<close>
datatype pproc =
  Single proc
| Parallel pproc "cname set" pproc

text \<open>Global states\<close>
datatype gstate =
  State state
| ParState gstate gstate

subsection \<open>Traces\<close>

datatype comm_type = In | Out | IO

datatype trace_block =
  CommBlock comm_type cname real
| WaitBlock real "real \<Rightarrow> gstate" rdy_info
| WaitBlockInf "real \<Rightarrow> gstate" rdy_info

abbreviation "InBlock ch v \<equiv> CommBlock In ch v"
abbreviation "OutBlock ch v \<equiv> CommBlock Out ch v"
abbreviation "IOBlock ch v \<equiv> CommBlock IO ch v"

type_synonym trace = "trace_block list"

type_synonym tassn = "trace \<Rightarrow> bool"


subsection \<open>Big-step semantics\<close>

text \<open>Compute list of ready communications for an external choice.\<close>
fun rdy_of_echoice :: "(comm \<times> proc) list \<Rightarrow> rdy_info" where
  "rdy_of_echoice [] = ({}, {})"
| "rdy_of_echoice ((ch[!]e, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_echoice ((ch[?]var, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (fst rdy, insert ch (snd rdy)))"

text \<open>big_step p s1 tr s2 means executing p starting from state s1 results
in a trace tr and final state s2.\<close>
inductive big_step :: "proc \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  skipB: "big_step Skip s [] s"
| assignB: "big_step (var ::= e) s [] (s(var := e s))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (p1; p2) s1 (tr1 @ tr2) s3"
| condB1: "b s1 \<Longrightarrow> big_step p1 s1 tr s2 \<Longrightarrow> big_step (IF b THEN p1 ELSE p2 FI) s1 tr s2"
| condB2: "\<not> b s1 \<Longrightarrow> big_step p2 s1 tr s2 \<Longrightarrow> big_step (IF b THEN p1 ELSE p2 FI) s1 tr s2"
| waitB1: "d > 0 \<Longrightarrow> big_step (Wait d) s [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})] s"
| waitB2: "\<not> d > 0 \<Longrightarrow> big_step (Wait d) s [] s"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "d > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}),
             OutBlock ch (e s)] s"
| sendB3: "big_step (Cm (ch[!]e)) s [WaitBlockInf (\<lambda>\<tau>\<in>{0..}. State s) ({ch}, {})] s"
| receiveB1: "big_step (Cm (ch[?]var)) s [InBlock ch v] (s(var := v))"
| receiveB2: "d > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}),
             InBlock ch v] (s(var := v))"
| IChoiceB1: "big_step p1 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| IChoiceB2: "big_step p2 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| EChoiceSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (OutBlock ch (e s1) # tr2) s2"
| EChoiceSendB2: "d > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice cs) #
                              OutBlock ch (e s1) # tr2) s2"
| EChoiceReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (InBlock ch v # tr2) s2"
| EChoiceReceiveB2: "d > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    big_step (Cont ode b) s1 [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) ({}, {})] (p d)"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (p d) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy #
                                      OutBlock ch (e (p d)) # tr2) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 ((p d)(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy #
                                      InBlock ch v # tr2) s2"
| InterruptB1: "\<not>b s \<Longrightarrow> big_step (Interrupt ode b cs) s [] s"
| InterruptB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow> p d = s2 \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy] s2"

lemma big_step_cong:
  "big_step c s1 tr s2 \<Longrightarrow> tr = tr' \<Longrightarrow> s2 = s2' \<Longrightarrow> big_step c s1 tr' s2'"
  by auto

inductive_cases skipE: "big_step Skip s1 tr s2"
inductive_cases assignE: "big_step (Assign var e) s1 tr s2"
inductive_cases sendE: "big_step (Cm (ch[!]e)) s1 tr s2"
inductive_cases receiveE: "big_step (Cm (ch[?]var)) s1 tr s2"
inductive_cases seqE: "big_step (Seq p1 p2) s1 tr s2"
inductive_cases condE: "big_step (Cond b p1 p2) s1 tr s2"
inductive_cases waitE: "big_step (Wait d) s1 tr s2"
inductive_cases echoiceE: "big_step (EChoice es) s1 tr s2"
inductive_cases ichoiceE: "big_step (IChoice p1 p2) s1 tr s2"
inductive_cases contE: "big_step (Cont ode b) s1 tr s2"
inductive_cases interruptE: "big_step (Interrupt ode b cs) s1 tr s2"


subsection \<open>Validity\<close>

text \<open>Assertion is a predicate on states and traces\<close>

type_synonym assn = "state \<Rightarrow> trace \<Rightarrow> bool"

definition Valid :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile> {P} c {Q} \<longleftrightarrow> (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step c s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

lemma entails_refl [simp]:
  "P \<Longrightarrow>\<^sub>A P"
  unfolding entails_def by auto

lemma entails_trans:
  "(P \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> (Q \<Longrightarrow>\<^sub>A R) \<Longrightarrow> (P \<Longrightarrow>\<^sub>A R)"
  unfolding entails_def by auto

lemma Valid_ex_pre:
  "(\<And>v. \<Turnstile> {P v} c {Q}) \<Longrightarrow> \<Turnstile> {\<lambda>s t. \<exists>v. P v s t} c {Q}"
  unfolding Valid_def by auto

lemma Valid_ex_post:
  "\<exists>v. \<Turnstile> {P} c {Q v} \<Longrightarrow> \<Turnstile> {P} c {\<lambda>s t. \<exists>v. Q v s t}"
  unfolding Valid_def by blast

lemma Valid_and_pre:
  "(P1 \<Longrightarrow> \<Turnstile> {P} c {Q}) \<Longrightarrow> \<Turnstile> {\<lambda>s t. P1 \<and> P s t} c {Q}"
  unfolding Valid_def by auto

theorem Valid_weaken_pre:
  "P \<Longrightarrow>\<^sub>A P' \<Longrightarrow> \<Turnstile> {P'} c {Q} \<Longrightarrow> \<Turnstile> {P} c {Q}"
  unfolding Valid_def entails_def by blast

theorem Valid_strengthen_post:
  "Q \<Longrightarrow>\<^sub>A Q' \<Longrightarrow> \<Turnstile> {P} c {Q} \<Longrightarrow> \<Turnstile> {P} c {Q'}"
  unfolding Valid_def entails_def by blast

theorem Valid_skip:
  "\<Turnstile> {P} Skip {P}"
  unfolding Valid_def
  by (auto elim: skipE)

theorem Valid_assign:
  "\<Turnstile> {\<lambda>s. Q (s(var := e s))} var ::= e {Q}"
  unfolding Valid_def
  by (auto elim: assignE)

theorem Valid_send:
  "\<Turnstile> {\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and>
               (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), OutBlock ch (e s)])) \<and>
              Q s (tr @ [WaitBlockInf (\<lambda>\<tau>\<in>{0..}. State s) ({ch}, {})])}
       Cm (ch[!]e) {Q}"
  unfolding Valid_def
  by (auto elim: sendE)

theorem Valid_receive:
  "\<Turnstile> {\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
               (\<forall>d>0. \<forall>v. Q (s(var := v))
                           (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), InBlock ch v]))}
       Cm (ch[?]var) {Q}"
  unfolding Valid_def
  by (auto elim: receiveE)

theorem Valid_seq:
  "\<Turnstile> {P} c1 {Q} \<Longrightarrow> \<Turnstile> {Q} c2 {R} \<Longrightarrow> \<Turnstile> {P} c1; c2 {R}"
  unfolding Valid_def
  apply (auto elim!: seqE) by fastforce

theorem Valid_cond:
  "\<Turnstile> {P1} c1 {Q} \<Longrightarrow> \<Turnstile> {P2} c2 {Q} \<Longrightarrow>
   \<Turnstile> {\<lambda>s. if b s then P1 s else P2 s} IF b THEN c1 ELSE c2 FI {Q}"
  unfolding Valid_def
  by (auto elim: condE)

theorem Valid_wait:
  "d > 0 \<Longrightarrow> \<Turnstile> {\<lambda>s tr. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})])} Wait d {Q}"
  unfolding Valid_def
  by (auto elim: waitE)

theorem Valid_wait2:
  "\<not> d > 0 \<Longrightarrow> \<Turnstile> {Q} Wait d {Q}"
  unfolding Valid_def
  by (auto elim: waitE)

theorem Valid_rep:
  assumes "\<Turnstile> {P} c {P}"
  shows "\<Turnstile> {P} Rep c {P}"
proof -
  have "big_step p s1 tr2 s2 \<Longrightarrow> p = Rep c \<Longrightarrow> \<forall>tr1. P s1 tr1 \<longrightarrow> P s2 (tr1 @ tr2)" for p s1 s2 tr2
    apply (induct rule: big_step.induct, auto)
    by (metis Valid_def append.assoc assms)
  then show ?thesis
    using assms unfolding Valid_def by auto
qed

theorem Valid_ichoice:
  assumes "\<Turnstile> {P1} c1 {Q}"
    and "\<Turnstile> {P2} c2 {Q}"
  shows "\<Turnstile> {\<lambda>s tr. P1 s tr \<and> P2 s tr} IChoice c1 c2 {Q}"
  using assms unfolding Valid_def by (auto elim: ichoiceE)

theorem Valid_echoice:
  assumes "\<And>i. i<length es \<Longrightarrow>
    case es ! i of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. \<Turnstile> {Q} p2 {R} \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)]))))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. \<Turnstile> {Q} p2 {R} \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v]))))"
  shows "\<Turnstile> {P} EChoice es {R}"
proof -
  have a: "R s2 (tr1 @ (OutBlock ch (e s1) # tr2))"
    if *: "P s1 tr1"
          "i < length es"
          "es ! i = (ch[!]e, p2)"
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
  have b: "R s2 (tr1 @ (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es) # OutBlock ch (e s1) # tr2))"
    if *: "P s1 tr1"
          "0 < d"
          "i < length es"
          "es ! i = (ch[!]e, p2)"
          "big_step p2 s1 tr2 s2" for s1 tr1 s2 d i ch e p2 tr2
  proof -
    obtain Q where 1:
      "\<Turnstile> {Q} p2 {R}"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)]))"
      using *(3,4) assms by fastforce
    have 2: "Q s1 (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es), OutBlock ch (e s1)])"
      using 1(2) *(1,2) unfolding entails_def by auto
    then show ?thesis
      using *(5) 1(1) unfolding Valid_def by fastforce
  qed
  have c: "R s2 (tr1 @ (InBlock ch v # tr2))"
    if *: "P s1 tr1"
          "i < length es"
          "es ! i = (ch[?]var, p2)"
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
  have d: "R s2 (tr1 @ (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es) # InBlock ch v # tr2))"
    if *: "P s1 tr1"
          "0 < d"
          "i < length es"
          "es ! i = (ch[?]var, p2)"
          "big_step p2 (s1(var := v)) tr2 s2" for s1 tr1 s2 d i ch var p2 v tr2
  proof -
    from assms obtain Q where 1:
      "\<Turnstile> {Q} p2 {R}"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v]))"
      using *(3,4) by fastforce
    have 2: "Q (s1(var := v)) (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es), InBlock ch v])"
      using 1(2) *(1,2) unfolding entails_def by auto
    then show ?thesis
      using *(5) 1(1) unfolding Valid_def by fastforce
  qed
  show ?thesis
    unfolding Valid_def apply auto
    apply (auto elim!: echoiceE) using a b c d by auto
qed


subsection \<open>Assertions on traces\<close>

definition entails_tassn :: "tassn \<Rightarrow> tassn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>t" 25) where
  "(P \<Longrightarrow>\<^sub>t Q) \<longleftrightarrow> (\<forall>tr. P tr \<longrightarrow> Q tr)"

lemma entails_tassn_refl [simp]:
  "P \<Longrightarrow>\<^sub>t P"
  unfolding entails_tassn_def by auto

lemma entails_tassn_trans:
  "(P \<Longrightarrow>\<^sub>t Q) \<Longrightarrow> (Q \<Longrightarrow>\<^sub>t R) \<Longrightarrow> (P \<Longrightarrow>\<^sub>t R)"
  unfolding entails_tassn_def by auto

lemma entails_tassn_ex_pre:
  "(\<And>x. P x \<Longrightarrow>\<^sub>t Q) \<Longrightarrow> (\<lambda>tr. (\<exists>x. P x tr)) \<Longrightarrow>\<^sub>t Q"
  by (auto simp add: entails_tassn_def)

lemma entails_tassn_ex_post:
  "(\<exists>x. P \<Longrightarrow>\<^sub>t Q x) \<Longrightarrow> P \<Longrightarrow>\<^sub>t (\<lambda>tr. (\<exists>x. Q x tr))"
  by (auto simp add: entails_tassn_def)

definition emp_assn :: "tassn" ("emp\<^sub>t") where
  "emp\<^sub>t = (\<lambda>tr. tr = [])"

definition join_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "@\<^sub>t" 65) where
  "P @\<^sub>t Q = (\<lambda>tr. \<exists>tr1 tr2. P tr1 \<and> Q tr2 \<and> tr = tr1 @ tr2)"

definition magic_wand_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "@-" 65) where
  "Q @- P = (\<lambda>tr. \<forall>tr1. Q tr1 \<longrightarrow> P (tr @ tr1))"

definition all_assn :: "(real \<Rightarrow> tassn) \<Rightarrow> tassn" (binder "\<forall>\<^sub>t" 10) where
  "(\<forall>\<^sub>tv. P v) = (\<lambda>tr. \<forall>v. P v tr)"

definition conj_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<and>\<^sub>t" 35) where
  "(P \<and>\<^sub>t Q) = (\<lambda>tr. P tr \<and> Q tr)"

definition disj_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<or>\<^sub>t" 25) where
  "(P \<or>\<^sub>t Q) = (\<lambda>tr. P tr \<or> Q tr)"

definition pure_assn :: "bool \<Rightarrow> tassn" ("\<up>") where
  "\<up>b = (\<lambda>_. b)"

inductive out_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> tassn" ("Out\<^sub>t") where
  "Out\<^sub>t s ch v [OutBlock ch v]"
| "d > 0 \<Longrightarrow> Out\<^sub>t s ch v [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), OutBlock ch v]"
| "Out\<^sub>t s ch v [WaitBlockInf (\<lambda>\<tau>\<in>{0..}. State s) ({ch}, {})]"

inductive in_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> tassn" ("In\<^sub>t") where
  "In\<^sub>t s ch v [InBlock ch v]"
| "d > 0 \<Longrightarrow> In\<^sub>t s ch v [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), InBlock ch v]"

inductive io_assn :: "cname \<Rightarrow> real \<Rightarrow> tassn" ("IO\<^sub>t") where
  "IO\<^sub>t ch v [IOBlock ch v]"

inductive wait_assn :: "real \<Rightarrow> (real \<Rightarrow> gstate) \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Wait\<^sub>t") where
  "Wait\<^sub>t d p rdy [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy]"

abbreviation "WaitS\<^sub>t d p \<equiv> Wait\<^sub>t d (\<lambda>t. State (p t))"

lemma emp_unit_left [simp]:
  "(emp\<^sub>t @\<^sub>t P) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma emp_unit_right [simp]:
  "(P @\<^sub>t emp\<^sub>t) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma join_assoc:
  "(P @\<^sub>t Q) @\<^sub>t R = P @\<^sub>t (Q @\<^sub>t R)"
  unfolding join_assn_def by fastforce

lemma entails_mp_emp:
  "emp\<^sub>t \<Longrightarrow>\<^sub>t P @- P"
  unfolding entails_tassn_def emp_assn_def magic_wand_assn_def by auto

lemma entails_mp:
  "Q \<Longrightarrow>\<^sub>t P @- (Q @\<^sub>t P)"
  unfolding entails_tassn_def magic_wand_assn_def join_assn_def by auto

lemma magic_wand_mono:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> (R @- P) \<Longrightarrow>\<^sub>t (R @- Q)"
  unfolding entails_tassn_def magic_wand_assn_def by auto

definition false_assn :: "tassn" ("false\<^sub>A") where
  "false_assn tr = False"

lemma false_assn_entails [simp]:
  "false\<^sub>A \<Longrightarrow>\<^sub>t P"
  by (simp add: entails_tassn_def false_assn_def)

lemma pure_assn_entails [simp]:
  "(\<up>b \<and>\<^sub>t P \<Longrightarrow>\<^sub>t Q) = (b \<longrightarrow> P \<Longrightarrow>\<^sub>t Q)"
  unfolding entails_tassn_def conj_assn_def pure_assn_def by auto

lemma entails_tassn_cancel_left:
  "Q \<Longrightarrow>\<^sub>t R \<Longrightarrow> P @\<^sub>t Q \<Longrightarrow>\<^sub>t P @\<^sub>t R"
  by (auto simp add: entails_tassn_def join_assn_def)

text \<open>Simpler forms of weakest precondition\<close>

theorem Valid_send':
  "\<Turnstile> {\<lambda>s. Out\<^sub>t s ch (e s) @- Q s}
       Cm (ch[!]e)
      {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send)
  unfolding entails_def magic_wand_assn_def
  by (auto intro: out_assn.intros)

theorem Valid_receive':
  "\<Turnstile> {\<lambda>s. \<forall>\<^sub>tv. In\<^sub>t s ch v @- Q (s(var := v))}
       Cm (ch[?]var)
      {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def magic_wand_assn_def all_assn_def
  by (auto intro: in_assn.intros)

theorem Valid_wait':
  "d > 0 \<Longrightarrow> \<Turnstile>
    {\<lambda>s. WaitS\<^sub>t d (\<lambda>_. s) ({}, {}) @- Q s}
      Wait d
    {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_wait)
  unfolding entails_def magic_wand_assn_def
  by (auto intro: wait_assn.intros)

text \<open>Strongest postcondition forms\<close>

theorem Valid_assign_sp:
  "\<Turnstile> {\<lambda>s t. s = st \<and> P s t}
        Assign x e
      {\<lambda>s t. s = st(x := e st) \<and> P st t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_assign)
  by (auto simp add: entails_def)

theorem Valid_send_sp:
  "\<Turnstile> {\<lambda>s t. s = st \<and> P s t}
       Cm (ch[!]e)
      {\<lambda>s t. s = st \<and> (P st @\<^sub>t Out\<^sub>t st ch (e st)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send')
  by (auto simp add: entails_def magic_wand_assn_def join_assn_def)

theorem Valid_receive_sp:
  "\<Turnstile> {\<lambda>s t. s = st \<and> P s t}
        Cm (ch[?]var)
      {\<lambda>s t. \<exists>v. s = st(var := v) \<and> (P st @\<^sub>t In\<^sub>t st ch v) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def
  apply (auto simp add: all_assn_def magic_wand_assn_def emp_assn_def join_assn_def)
  subgoal for tr v
    apply (rule exI[where x=v])
    apply auto apply (rule exI[where x=tr])
    by (simp add: in_assn.intros)
  subgoal for tr d v
    apply (rule exI[where x=v])
    apply auto apply (rule exI[where x=tr])
    by (simp add: in_assn.intros)
  done

theorem Valid_wait_sp:
  "d > 0 \<Longrightarrow> \<Turnstile>
    {\<lambda>s tr. s = st \<and> P s tr}
      Wait d
    {\<lambda>s tr. s = st \<and> (P s @\<^sub>t WaitS\<^sub>t d (\<lambda>_. st) ({}, {})) tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_wait')
  by (auto simp add: entails_def join_assn_def magic_wand_assn_def)

subsection \<open>Rules for internal and external choice\<close>

text \<open>Additional assertions\<close>

inductive inrdy_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Inrdy\<^sub>t") where
  "Inrdy\<^sub>t s ch v rdy [InBlock ch v]"
| "d > 0 \<Longrightarrow> Inrdy\<^sub>t s ch v rdy [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) rdy, InBlock ch v]"

inductive outrdy_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Outrdy\<^sub>t") where
  "Outrdy\<^sub>t s ch v rdy [OutBlock ch v]"
| "d > 0 \<Longrightarrow> Outrdy\<^sub>t s ch v rdy [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) rdy, OutBlock ch v]"

text \<open>Simpler form of weakest precondition\<close>

theorem Valid_echoice':
  assumes "\<And>i. i<length es \<Longrightarrow>
    case es ! i of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. \<Turnstile> {Q} p2 {R} \<and>
            (P \<Longrightarrow>\<^sub>A (\<lambda>s. Outrdy\<^sub>t s ch (e s) (rdy_of_echoice es) @- Q s)))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. \<Turnstile> {Q} p2 {R} \<and>
            (P \<Longrightarrow>\<^sub>A (\<lambda>s. \<forall>\<^sub>tv. Inrdy\<^sub>t s ch v (rdy_of_echoice es) @- Q (s(var := v)))))"
  shows "\<Turnstile> {P} EChoice es {R}"
proof -
  have 1: "\<exists>Q. \<Turnstile> {Q} p {R} \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)])))"
    if *: "i < length es" "es ! i = (ch[!]e, p)" for i ch e p
  proof -
    from assms obtain Q where
      Q: "\<Turnstile> {Q} p {R} \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s. Outrdy\<^sub>t s ch (e s) (rdy_of_echoice es) @- Q s))"
      using * by fastforce
    show ?thesis
      apply (rule exI[where x=Q])
      using Q by (auto simp add: entails_def magic_wand_assn_def
                       intro: outrdy_assn.intros)
  qed
  have 2: "\<exists>Q. \<Turnstile> {Q} p {R} \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v])))"
    if *: "i < length es" "es ! i = (ch[?]var, p)" for i ch var p
  proof -
    from assms obtain Q where
      Q: "\<Turnstile> {Q} p {R} \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s. \<forall>\<^sub>tv. Inrdy\<^sub>t s ch v (rdy_of_echoice es) @- Q (s(var := v))))"
      using * by fastforce
    show ?thesis
      apply (rule exI[where x=Q])
      using Q by (auto simp add: entails_def magic_wand_assn_def
                                 all_assn_def inrdy_assn.intros)
  qed
  show ?thesis
    apply (rule Valid_echoice)
    subgoal for i apply (cases "es ! i")
      subgoal for ch p apply (cases ch) apply auto
        using 1 2 by auto
      done
    done
qed

text \<open>Strongest postcondition form\<close>

theorem Valid_echoice_sp:
  assumes "\<And>i. i<length es \<Longrightarrow>
    case es ! i of
      (ch[!]e, p2) \<Rightarrow>
        \<Turnstile> {\<lambda>s tr. s = st \<and> (P s @\<^sub>t Outrdy\<^sub>t s ch (e s) (rdy_of_echoice es)) tr} p2 {Q}
    | (ch[?]var, p2) \<Rightarrow>
        \<Turnstile> {\<lambda>s tr. (\<exists>v. s = st(var := v) \<and> (P st @\<^sub>t Inrdy\<^sub>t st ch v (rdy_of_echoice es)) tr)} p2 {Q}"
  shows "\<Turnstile>
    {\<lambda>s tr. s = st \<and> P s tr}
      EChoice es
    {Q}"
  apply (rule Valid_echoice')
  subgoal for i
    apply (cases "es ! i") apply auto
    subgoal for comm p2
      apply (cases comm)
      subgoal for ch e
        apply auto
        apply (rule exI[where x="\<lambda>s tr. s = st \<and> (P s @\<^sub>t Outrdy\<^sub>t s ch (e s) (rdy_of_echoice es)) tr"])
        apply auto
        using assms apply fastforce
        by (auto simp add: entails_def join_assn_def magic_wand_assn_def)
      subgoal for ch var
        apply auto
        apply (rule exI[where x="\<lambda>s tr. (\<exists>v. s = st(var := v) \<and> (P st @\<^sub>t Inrdy\<^sub>t st ch v (rdy_of_echoice es)) tr)"])
        apply auto
        using assms apply fastforce
        by (auto simp add: entails_def magic_wand_assn_def join_assn_def all_assn_def)
      done
    done
  done

end
