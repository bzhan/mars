theory BigStepSimple
  imports "../Analysis_More"
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
| Wait exp  \<comment> \<open>Waiting for a specified amount of time\<close>
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

datatype comm_type = In | Out

datatype trace_block =
  CommBlock comm_type cname real
| WaitBlock real "real \<Rightarrow> gstate" rdy_info

abbreviation "InBlock ch v \<equiv> CommBlock In ch v"
abbreviation "OutBlock ch v \<equiv> CommBlock Out ch v"

definition WaitBlk :: "real \<Rightarrow> (real \<Rightarrow> gstate) \<Rightarrow> rdy_info \<Rightarrow> trace_block" where
  "WaitBlk d p rdy = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"

lemma WaitBlk_not_Comm [simp]:
  "WaitBlk d p rdy \<noteq> CommBlock ch_type ch v"
  "CommBlock ch_type ch v \<noteq> WaitBlk d p rdy"
  by (auto simp add: WaitBlk_def)

lemma restrict_cong_to_eq:
  fixes x :: real
  shows "restrict p1 {0..t} = restrict p2 {0..t} \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma WaitBlk_ext:
  fixes t1 t2 :: real
    and hist1 hist2 :: "real \<Rightarrow> gstate"
  shows "t1 = t2 \<Longrightarrow>
   (\<And>\<tau>::real. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
   WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
  by (auto simp add: restrict_def WaitBlk_def)

lemma WaitBlk_cong:
  "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2 \<Longrightarrow> t1 = t2 \<and> rdy1 = rdy2"
  by (auto simp add: WaitBlk_def)

lemma WaitBlk_cong2:
  assumes "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
    and "0 \<le> t" "t \<le> t1"
  shows "hist1 t = hist2 t"
proof -
  have a: "t1 = t2" "rdy1 = rdy2"
    using assms WaitBlk_cong by auto
  have b: "restrict hist1 {0..t1} = restrict hist2 {0..t1}"
    using assms(1) unfolding WaitBlk_def by auto
  show ?thesis
    using b restrict_cong_to_eq assms a by auto
qed

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
| waitB1: "e s > 0 \<Longrightarrow> big_step (Wait e) s [WaitBlk (e s) (\<lambda>_. State s) ({}, {})] s"
| waitB2: "\<not> e s > 0 \<Longrightarrow> big_step (Wait e) s [] s"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlk d (\<lambda>_. State s) ({ch}, {}),
             OutBlock ch (e s)] s"
| receiveB1: "big_step (Cm (ch[?]var)) s [InBlock ch v] (s(var := v))"
| receiveB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlk d (\<lambda>_. State s) ({}, {ch}),
             InBlock ch v] (s(var := v))"
| IChoiceB1: "big_step p1 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| IChoiceB2: "big_step p2 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| EChoiceSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (OutBlock ch (e s1) # tr2) s2"
| EChoiceSendB2: "(d::real) > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice cs) #
                              OutBlock ch (e s1) # tr2) s2"
| EChoiceReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (InBlock ch v # tr2) s2"
| EChoiceReceiveB2: "(d::real) > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    big_step (Cont ode b) s1 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p d)"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (p d) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                      OutBlock ch (e (p d)) # tr2) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 ((p d)(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                      InBlock ch v # tr2) s2"
| InterruptB1: "\<not>b s \<Longrightarrow> big_step (Interrupt ode b cs) s [] s"
| InterruptB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow> p d = s2 \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy] s2"

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
type_synonym assn2 = "state \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> bool"

definition emp :: assn where
  "emp = (\<lambda>s tr. tr = [])"

definition Valid :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile> {P} c {Q} \<longleftrightarrow> (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step c s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

theorem entails_triv:
  "P \<Longrightarrow>\<^sub>A P"
  unfolding entails_def by auto

definition subst_assn :: "assn \<Rightarrow> var \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> assn" ("_ {_ := _}" [90,90,90] 91) where 
  "P {var := e} = (\<lambda>s tr. P (s(var := e s)) tr)"

definition forall_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<forall>\<^sub>a" 10)where
  "(\<forall>\<^sub>a n. P n) = (\<lambda>s tr. \<forall>n. P n s tr)"

definition exists_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<exists>\<^sub>a" 10)where
  "(\<exists>\<^sub>a n. P n) = (\<lambda>s tr. \<exists>n. P n s tr)"

definition pure_assn :: "bool \<Rightarrow> tassn" ("\<up>") where
  "\<up>b = (\<lambda>_. b)"

definition conj_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<and>\<^sub>t" 35) where
  "(P \<and>\<^sub>t Q) = (\<lambda>tr. P tr \<and> Q tr)"

definition disj_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<or>\<^sub>t" 25) where
  "(P \<or>\<^sub>t Q) = (\<lambda>tr. P tr \<or> Q tr)"

theorem strengthen_pre:
  "\<Turnstile> {P2} c {Q} \<Longrightarrow> P1 \<Longrightarrow>\<^sub>A P2 \<Longrightarrow> \<Turnstile> {P1} c {Q}"
  unfolding Valid_def entails_def by metis

theorem weaken_post:
  "\<Turnstile> {P} c {Q1} \<Longrightarrow> Q1 \<Longrightarrow>\<^sub>A Q2 \<Longrightarrow> \<Turnstile> {P} c {Q2}"
  unfolding Valid_def entails_def by metis

theorem Valid_skip:
  "\<Turnstile> {P} Skip {P}"
  unfolding Valid_def
  by (auto elim: skipE)

theorem Valid_assign:
  "\<Turnstile> {Q {var := e}} var ::= e {Q}"
  unfolding Valid_def
  by (auto simp: subst_assn_def elim: assignE)

theorem Valid_seq:
  assumes "\<Turnstile> {Q} c2 {R}"
    and "\<Turnstile> {P} c1 {Q}"
  shows "\<Turnstile> {P} c1; c2 {R}"
  using assms unfolding Valid_def
  by (metis append.assoc seqE)

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

text \<open>State and trace satisfies P after receiving input\<close>
definition wait_in :: "cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> assn) \<Rightarrow> assn" where
  "wait_in ch P = (\<lambda>s tr. (\<forall>v. P 0 v s (tr @ [InBlock ch v])) \<and>
                          (\<forall>d>0. \<forall>v. P d v s (tr @ [WaitBlk d (\<lambda>_. State s) ({}, {ch}), InBlock ch v])))"

text \<open>Receive input, then state and trace satisfies P\<close>
inductive wait_in_c :: "cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> state \<Rightarrow> assn) \<Rightarrow> state \<Rightarrow> assn" where
  "P 0 v s0 s tr \<Longrightarrow> wait_in_c ch P s0 s (InBlock ch v # tr)"
| "0 < d \<Longrightarrow> P d v s0 s tr \<Longrightarrow> wait_in_c ch P s0 s (WaitBlk d (\<lambda>_. State s0) ({}, {ch}) # InBlock ch v # tr)"

definition init :: "state \<Rightarrow> assn" where
  "init s0 = (\<lambda>s tr. s = s0 \<and> tr = [])"

definition spec_of :: "proc \<Rightarrow> (state \<Rightarrow> assn) \<Rightarrow> bool" where
  "spec_of c Q \<longleftrightarrow> (\<forall>s0. \<Turnstile> {init s0} c {Q s0})"

lemma spec_of_assign:
  "spec_of (var ::= e) (\<lambda>s0 s tr. s = s0(var := e s0))"
  unfolding Valid_def spec_of_def init_def
  by (auto elim!: assignE)

lemma Valid_assign_sp:
  assumes "spec_of c Q"
  shows "spec_of (var ::= e; c) (\<lambda>s0. Q (s0(var := e s0)))"
  unfolding Valid_def spec_of_def
  apply (auto elim!: seqE assignE)
  using assms unfolding spec_of_def Valid_def init_def by auto

lemma spec_of_skip:
  "spec_of Skip init"
  unfolding Valid_def spec_of_def
  by (auto elim: skipE)

lemma spec_of_receive:
  "spec_of (Cm (ch[?]var)) (wait_in_c ch (\<lambda>d v s0. init (s0(var := v))))"
  unfolding Valid_def spec_of_def init_def
  apply (auto elim!: receiveE)
   apply (rule wait_in_c.intros(1)) apply auto[1]
  apply (rule wait_in_c.intros(2)) by auto

lemma Valid_receive_sp:
  assumes "spec_of c Q"
  shows "spec_of (Cm (ch[?]var); c)
                 (wait_in_c ch (\<lambda>d v s0. Q (s0(var := v))))"
  unfolding Valid_def spec_of_def init_def
  apply (auto elim!: seqE receiveE)
  apply (rule wait_in_c.intros(1))
  using Valid_def spec_of_def init_def assms apply auto[1]
  apply (rule wait_in_c.intros(2)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  done

theorem Valid_receive:
  "\<Turnstile> {wait_in ch (\<lambda>d v. P {var := (\<lambda>_. v)})}
        Cm (ch[?]var)
      {P}"
  unfolding Valid_def wait_in_def
  by (auto simp: subst_assn_def elim: receiveE)

definition wait_out :: "cname \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> assn) \<Rightarrow> assn" where
  "wait_out ch e P = (\<lambda>s tr. (P 0 s (tr @ [OutBlock ch (e s)])) \<and>
                             (\<forall>d>0. P d s (tr @ [WaitBlk d (\<lambda>_. State s) ({ch}, {}), OutBlock ch (e s)])))"

inductive wait_out_c :: "cname \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> state \<Rightarrow> assn) \<Rightarrow> state \<Rightarrow> assn" where
  "P 0 s0 s tr \<Longrightarrow> wait_out_c ch e P s0 s (OutBlock ch (e s0) # tr)"
| "0 < d \<Longrightarrow> P d s0 s tr \<Longrightarrow> wait_out_c ch e P s0 s (WaitBlk d (\<lambda>_. State s0) ({ch}, {}) # OutBlock ch (e s0) # tr)"

lemma spec_of_send:
  "spec_of (Cm (ch[!]e)) (wait_out_c ch e (\<lambda>d. init))"
  unfolding Valid_def spec_of_def init_def
  apply (auto elim!: sendE)
   apply (rule wait_out_c.intros(1)) apply auto[1]
  apply (rule wait_out_c.intros(2)) by auto

lemma Valid_send_sp:
  assumes "spec_of c Q"
  shows "spec_of (Cm (ch[!]e); c)
                 (wait_out_c ch e (\<lambda>d s0. Q s0))"
  unfolding Valid_def spec_of_def init_def
  apply (auto elim!: seqE sendE)
   apply (rule wait_out_c.intros(1))
  using Valid_def spec_of_def init_def assms apply auto[1]
  apply (rule wait_out_c.intros(2)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  done

lemma wait_in_forall:
  "wait_in ch (\<lambda>d v. \<forall>\<^sub>a n. P d v n) = (\<forall>\<^sub>a n. wait_in ch (\<lambda>d v. P d v n))"
  unfolding wait_in_def forall_assn_def
  apply (rule ext) apply (rule ext) by auto

lemma wait_out_forall:
  "wait_out ch e (\<lambda>d. \<forall>\<^sub>a n. P d n) = (\<forall>\<^sub>a n. wait_out ch e (\<lambda>d. P d n))"
  unfolding wait_out_def forall_assn_def
  apply (rule ext) apply (rule ext) by auto

lemma wait_in_c_exists:
  "wait_in_c ch (\<lambda>d v s0. \<exists>\<^sub>a n. P d v s0 n) s0 = (\<exists>\<^sub>a n. wait_in_c ch (\<lambda>d v s0. P d v s0 n) s0)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (rule iffI)
    subgoal unfolding exists_assn_def
      apply (induct rule: wait_in_c.cases) apply auto
      subgoal for v tr' n
        apply (rule exI[where x=n])
        apply (rule wait_in_c.intros(1)) by auto
      subgoal for d v tr' n
        apply (rule exI[where x=n])
        apply (rule wait_in_c.intros(2)) by auto
      done
    subgoal unfolding exists_assn_def
      apply auto subgoal for n
        apply (induction rule: wait_in_c.cases) apply auto
        subgoal for v tr'
          apply (rule wait_in_c.intros(1))
          apply (rule exI[where x=n]) by auto
        subgoal for d v tr'
          apply (rule wait_in_c.intros(2))
           apply simp apply (rule exI[where x=n]) by auto
        done
      done
    done
  done

lemma wait_out_c_exists:
  "wait_out_c ch e (\<lambda>d s0. \<exists>\<^sub>a n. P d s0 n) s0 = (\<exists>\<^sub>a n. wait_out_c ch e (\<lambda>d s0. P d s0 n) s0)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (rule iffI)
    subgoal unfolding exists_assn_def
      apply (induct rule: wait_out_c.cases) apply auto
      subgoal for tr' n
        apply (rule exI[where x=n])
        apply (rule wait_out_c.intros(1)) by auto
      subgoal for d tr' n
        apply (rule exI[where x=n])
        apply (rule wait_out_c.intros(2)) by auto
      done
    subgoal unfolding exists_assn_def
      apply auto subgoal for n
        apply (induction rule: wait_out_c.cases) apply auto
        subgoal for tr'
          apply (rule wait_out_c.intros(1))
          apply (rule exI[where x=n]) by auto
        subgoal for d tr'
          apply (rule wait_out_c.intros(2))
           apply simp apply (rule exI[where x=n]) by auto
        done
      done
    done
  done

lemma subst_forall:
  "(\<forall>\<^sub>a n. P n) {var := e} = (\<forall>\<^sub>a n. P n {var := e})"
  unfolding subst_assn_def forall_assn_def
  apply (rule ext) apply (rule ext) by auto

theorem Valid_send:
  "\<Turnstile> {wait_out ch e (\<lambda>d. P)}
        Cm (ch[!]e)
      {P}"
  unfolding Valid_def wait_out_def
  by (auto elim: sendE)

subsection \<open>Examples\<close>

definition A :: char where "A = CHR ''a''"
definition B :: char where "B = CHR ''b''"
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"

lemma ex1a:
  "\<Turnstile> {wait_in ch1 (\<lambda>d v. (wait_out ch2 (\<lambda>s. s X + 1) (\<lambda>d. P)) {X := (\<lambda>_. v)})}
        Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. s X + 1))
      {P}"
  apply (rule strengthen_pre)
   apply (rule Valid_seq)
    apply (rule Valid_send)
   apply (rule Valid_receive)
  by (rule entails_triv)

lemma ex1a_sp:
  "spec_of (Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. s X + 1)))
           (wait_in_c ch1 (\<lambda>d v s0. wait_out_c ch2 (\<lambda>s. s X + 1) (\<lambda>d. init) (s0(X := v))))"
  apply (rule Valid_receive_sp)
  apply (rule spec_of_send)
  done

lemma ex1b:
  "\<Turnstile> {wait_out ch1 (\<lambda>_. 3) (\<lambda>d. P)}
       Cm (ch1[!](\<lambda>_. 3))
      {P}"
  apply (rule strengthen_pre)
   apply (rule Valid_send)
  by (rule entails_triv)

lemma ex2a_sp:
  "spec_of (Cm (ch1[!](\<lambda>_. 3)))
           (wait_out_c ch1 (\<lambda>_. 3) (\<lambda>d. init))"
  apply (rule spec_of_send)
  done

fun rinv :: "nat \<Rightarrow> cname \<Rightarrow> assn \<Rightarrow> assn" where
  "rinv 0 ch Q = Q"
| "rinv (Suc n) ch Q = wait_out ch (\<lambda>s. s A) (\<lambda>d. (rinv n ch Q) {B := (\<lambda>s. s B + 1)})"
declare rinv.simps [simp del]

fun rinv_c :: "nat \<Rightarrow> cname \<Rightarrow> (state \<Rightarrow> assn) \<Rightarrow> (state \<Rightarrow> assn)" where
  "rinv_c 0 ch Q = Q"
| "rinv_c (Suc n) ch Q = wait_out_c ch (\<lambda>s. s A) (\<lambda>d s0. rinv_c n ch Q (s0(B := s0 B + 1)))"

lemma ex2':
  "\<Turnstile> {\<forall>\<^sub>a n. rinv n ch1 Q}
        Cm (ch1[!](\<lambda>s. s A)); B ::= (\<lambda>s. s B + 1)
      {\<forall>\<^sub>a n. rinv n ch1 Q}"
  apply (rule strengthen_pre)
  apply (rule Valid_seq)
    apply (rule Valid_assign)
   apply (rule Valid_send)
  unfolding entails_def apply auto
  subgoal premises pre for s tr
  proof -
    have "(\<forall>\<^sub>an. rinv (Suc n) ch1 Q) s tr"  
      using pre unfolding forall_assn_def by auto
    then show ?thesis
      unfolding rinv.simps subst_forall wait_out_forall
      by auto
  qed
  done

lemma ex2:
  "\<Turnstile> {\<forall>\<^sub>a n. rinv n ch1 P}
        Rep (Cm (ch1[!](\<lambda>s. s A)); B ::= (\<lambda>s. s B + 1))
      {P}"
  apply (rule weaken_post)
  apply (rule Valid_rep)
   apply (rule ex2')
  unfolding entails_def apply auto
  by (metis forall_assn_def rinv.simps(1))

lemma spec_of_post:
  "spec_of c Q1 \<Longrightarrow> \<forall>s0. Q1 s0 \<Longrightarrow>\<^sub>A Q2 s0 \<Longrightarrow> spec_of c Q2"
  unfolding spec_of_def using weaken_post by blast

lemma entails_exists:
  assumes "\<exists>n. P \<Longrightarrow>\<^sub>A Q n"
  shows "P \<Longrightarrow>\<^sub>A (\<exists>\<^sub>a n. Q n)"
  using assms unfolding exists_assn_def entails_def
  by auto

fun RepN :: "nat \<Rightarrow> proc \<Rightarrow> proc" where
  "RepN 0 c = Skip"
| "RepN (Suc n) c = c; RepN n c"

lemma big_step_rep:
  "big_step (Rep c) s1 tr1 s2 \<longleftrightarrow> (\<exists>n. big_step (RepN n c) s1 tr1 s2)"
proof -
  have "big_step p s1 tr1 s2 \<Longrightarrow> p = Rep c \<Longrightarrow> \<exists>n. big_step (RepN n c) s1 tr1 s2" for p s1 tr1 s2
    apply (induction rule: big_step.induct, auto)
     apply (rule exI[where x=0])
    apply simp apply (rule skipB)
    subgoal for s1 tr1 s2 tr2 s3 n
      apply (rule exI[where x="Suc n"])
      apply simp apply (rule seqB) by auto
    done
  moreover have "\<And>s1 tr1 s2. big_step (RepN n c) s1 tr1 s2 \<Longrightarrow> big_step (Rep c) s1 tr1 s2" for n
    apply (induction n)
     apply simp apply (elim skipE) apply (auto intro: RepetitionB1)[1]
    apply simp apply (elim seqE) apply (auto intro: RepetitionB2)
    done
  ultimately show ?thesis
    by auto
qed

lemma big_step_seq_assoc:
  "big_step ((p1; p2); p3) s1 tr s2 \<longleftrightarrow> big_step (p1; p2; p3) s1 tr s2"
  apply (rule iffI)
  subgoal apply (elim seqE)
    apply auto apply (rule seqB) apply auto
    apply (rule seqB) by auto
  subgoal apply (elim seqE)
    apply auto apply (subst append.assoc[symmetric])
    apply (rule seqB) apply (rule seqB) by auto
  done

lemma spec_of_seq_assoc:
  "spec_of ((p1; p2); p3) Q \<longleftrightarrow> spec_of (p1; p2; p3) Q"
  unfolding spec_of_def Valid_def
  using big_step_seq_assoc by auto

lemma spec_of_rep:
  assumes "\<And>n. spec_of (RepN n c) (Q n)"
  shows "spec_of (Rep c) (\<lambda>s0. \<exists>\<^sub>a n. Q n s0)"
  using assms unfolding spec_of_def Valid_def big_step_rep exists_assn_def
  by blast

lemma ex2_c':
  "spec_of (RepN n (Cm (ch1[!](\<lambda>s. s A)); B ::= (\<lambda>s. s B + 1)))
           (rinv_c n ch1 init)"
  apply (induction n)
  apply simp apply (rule spec_of_skip)
  subgoal premises pre for n
    apply simp apply (rule spec_of_post)
    apply (subst spec_of_seq_assoc)
   apply (rule Valid_send_sp)
   apply (rule Valid_assign_sp)
     apply (rule pre) apply clarify
    by (rule entails_triv)
  done

lemma ex2_c:
  "spec_of (Rep (Cm (ch1[!](\<lambda>s. s A)); B ::= (\<lambda>s. s B + 1)))
           (\<lambda>s0. \<exists>\<^sub>an. rinv_c n ch1 init s0)"
  apply (rule spec_of_rep)
  by (rule ex2_c')

fun linv :: "nat \<Rightarrow> cname \<Rightarrow> assn \<Rightarrow> assn" where
  "linv 0 ch Q = Q"
| "linv (Suc n) ch Q = wait_in ch (\<lambda>d v. (linv n ch Q) {Y := (\<lambda>s. s Y + s X)} {X := (\<lambda>_. v)})"
declare linv.simps [simp del]

lemma ex3':
  "\<Turnstile> {\<forall>\<^sub>a n. linv n ch1 Q}
        Cm (ch1[?]X); Y ::= (\<lambda>s. s Y + s X)
      {\<forall>\<^sub>a n. linv n ch1 Q}"
  apply (rule strengthen_pre)
  apply (rule Valid_seq)
  apply (rule Valid_assign)
   apply (rule Valid_receive)
  unfolding entails_def apply auto
  subgoal premises pre for s tr
  proof -
    have "(\<forall>\<^sub>an. linv (Suc n) ch1 Q) s tr"
      using pre unfolding forall_assn_def by auto
    then show ?thesis
      unfolding linv.simps subst_forall wait_in_forall
      by auto
  qed
  done

lemma ex3:
  "\<Turnstile> {\<forall>\<^sub>a n. linv n ch1 P}
        Rep (Cm (ch1[?]X); Y ::= (\<lambda>s. s Y + s X))
      {P}"
  apply (rule weaken_post)
   apply (rule Valid_rep)
  apply (rule ex3')
  unfolding entails_def apply auto
  by (metis forall_assn_def linv.simps(1))


subsection \<open>Combining two traces\<close>

text \<open>Whether two rdy_infos from different processes are compatible.\<close>
fun compat_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

text \<open>Merge two rdy infos\<close>
fun merge_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> rdy_info" where
  "merge_rdy (r11, r12) (r21, r22) = (r11 \<union> r21, r12 \<union> r22)"

text \<open>combine_blocks comms tr1 tr2 tr means tr1 and tr2 combines to tr, where
  comms is the list of internal communication channels.\<close>
inductive combine_blocks :: "cname set \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  \<comment> \<open>Empty case\<close>
  combine_blocks_empty:
  "combine_blocks comms [] [] []"

  \<comment> \<open>Paired communication\<close>
| combine_blocks_pair1:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (InBlock ch v # blks1) (OutBlock ch v # blks2) blks"
| combine_blocks_pair2:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (OutBlock ch v # blks1) (InBlock ch v # blks2) blks"

  \<comment> \<open>Unpaired communication\<close>
| combine_blocks_unpair1:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (CommBlock ch_type ch v # blks1) blks2 (CommBlock ch_type ch v # blks)"
| combine_blocks_unpair2:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (CommBlock ch_type ch v # blks2) (CommBlock ch_type ch v # blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_wait1:
  "combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t hist rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlk (t2 - t1) (\<lambda>\<tau>. (\<lambda>x::real. hist2 x) (\<tau> + t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow> t1 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t1 hist rdy # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlk (t1 - t2) (\<lambda>\<tau>. (\<lambda>x::real. hist1 x) (\<tau> + t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow> t2 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t2 hist rdy # blks)"

text \<open>Definition of big-step for two processes\<close>
definition par_big_step :: "proc \<Rightarrow> proc \<Rightarrow> cname set \<Rightarrow> state \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "par_big_step c1 c2 chs s11 s12 tr1 tr2 s21 s22 \<longleftrightarrow>
     big_step c1 s11 tr1 s12 \<and>
     big_step c2 s21 tr2 s22 \<and>
     (\<exists>tr. combine_blocks chs tr1 tr2 tr)"

text \<open>Definition of validity of Hoare triples for two processes\<close>
definition ParValid :: "(state \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> proc \<Rightarrow> proc \<Rightarrow> cname set \<Rightarrow> (state \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> bool"
      ("\<Turnstile>\<^sub>p ({(1_)}/ (_)/ (_)/ (_)/ {(1_)})" 50) where
  "\<Turnstile>\<^sub>p {P} c1 c2 chs {Q} \<longleftrightarrow> (\<forall>s11 s12 s21 s22 tr1 tr2. P s11 s21 \<longrightarrow>
      par_big_step c1 c2 chs s11 s12 tr1 tr2 s21 s22 \<longrightarrow> Q s12 s22)"

definition entails2 :: "(state \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> (state \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>S" 25) where
  "(P1 \<Longrightarrow>\<^sub>S P2) \<longleftrightarrow> (\<forall>s1 s2. P1 s1 s2 \<longrightarrow> P2 s1 s2)"

lemma entails2_triv:
  "P \<Longrightarrow>\<^sub>S P"
  unfolding entails2_def by auto

lemma ParValid_strengthen_pre:
  assumes "\<Turnstile>\<^sub>p {P2} c1 c2 chs {Q}"
    and "P1 \<Longrightarrow>\<^sub>S P2"
  shows "\<Turnstile>\<^sub>p {P1} c1 c2 chs {Q}"
  using assms unfolding ParValid_def entails2_def by metis

definition combine_assn :: "(assn \<Rightarrow> assn) \<Rightarrow> (assn \<Rightarrow> assn) \<Rightarrow> cname set \<Rightarrow> (state \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> (state \<Rightarrow> state \<Rightarrow> bool)" where
  "combine_assn f g chs Q =
    (\<lambda>s11 s21. g (\<lambda>s22 tr2. f (\<lambda>s12 tr1. (\<exists>tr. combine_blocks chs tr1 tr2 tr) \<longrightarrow> Q s12 s22) s11 []) s21 [])"

theorem ParValid_Parallel:
  fixes f g :: "assn \<Rightarrow> assn"
  assumes "\<And>P1. \<Turnstile> {f P1} c1 {P1}"
    and "\<And>P2. \<Turnstile> {g P2} c2 {P2}"
  shows "\<Turnstile>\<^sub>p {combine_assn f g chs Q} c1 c2 chs {Q}"
proof -
  have 1: "f P1 s11 [] \<Longrightarrow> big_step c1 s11 tr s12 \<Longrightarrow> P1 s12 tr" for P1 s11 tr s12
    using assms(1) unfolding Valid_def
    by (metis append_Nil)
  have 2: "g P2 s21 [] \<Longrightarrow> big_step c2 s21 tr s22 \<Longrightarrow> P2 s22 tr" for P2 s21 tr s22
    using assms(2) unfolding Valid_def
    by (metis append_Nil)
  have 3: "(\<exists>tr. combine_blocks chs tr1 tr2 tr) \<longrightarrow> Q s12 s22"
    if "combine_assn f g chs Q s11 s21" "big_step c1 s11 tr1 s12" "big_step c2 s21 tr2 s22" for s11 s12 s21 s22 tr1 tr2 
    apply (rule 1[OF _ that(2)])
    apply (rule 2[OF _ that(3)])
    using that(1) unfolding combine_assn_def by auto
  then show ?thesis
    unfolding ParValid_def par_big_step_def by metis
qed


subsection \<open>Examples of using ParValid_parallel\<close>

lemma ex1:
  "\<Turnstile>\<^sub>p {combine_assn
          (\<lambda>P1. wait_in ch1 (\<lambda>d v. wait_out ch2 (\<lambda>s. s X + 1) (\<lambda>d. P1) {X := (\<lambda>_. v)}))
          (\<lambda>P2. wait_out ch1 (\<lambda>_. 3) (\<lambda>d. P2))
          {ch1}
       P}
        (Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. s X + 1)))
        (Cm (ch1[!](\<lambda>_. 3)))
        {ch1}
      {P}"
  apply (rule ParValid_strengthen_pre)
  apply (rule ParValid_Parallel)
   apply (rule ex1a)
   apply (rule ex1b)
  by (rule entails2_triv)


subsection \<open>Basic elimination rules\<close>

named_theorems sync_elims

lemma combine_blocks_pairE [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. ch1 = ch2 \<Longrightarrow> v1 = v2 \<Longrightarrow> (ch_type1 = In \<and> ch_type2 = Out \<or> ch_type1 = Out \<and> ch_type2 = In) \<Longrightarrow>
   tr = tr' \<Longrightarrow> combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlock ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1' [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE2 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlock ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2' [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlk d2 p2 rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3' [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_waitE1 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   \<not>compat_rdy rdy1 rdy2 \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  then show ?case
    by (metis WaitBlk_cong list.inject)
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  then show ?case 
    by (metis WaitBlk_cong list.inject)
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  then show ?case 
    by (metis WaitBlk_cong list.inject)
qed (auto)
(*
lemma combine_blocks_waitE2 [sync_elims]:
  "combine_blocks comms (WaitBlk d p1 rdy1 # tr1) (WaitBlk d p2 rdy2 # tr2) tr \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms' blks1 blks2 blks rdy1' rdy2' hist hist1 hist2 rdy t)
  have a: "d = t" "rdy1 = rdy1'" "rdy2 = rdy2'" "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait1(2,3) by (auto simp add: WaitBlk_cong)
  have b: "WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk t (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine) using combine_blocks_wait1(2,3) by auto 
  show ?case
    apply (rule combine_blocks_wait1)
    unfolding b using combine_blocks_wait1(4) unfolding a combine_blocks_wait1(7,8)
    by (auto simp add: combine_blocks_wait1(1,5))
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have a: "d = ereal t1" "d = t2"
    using combine_blocks_wait2(2,3) by (auto simp add: WaitBlk_cong)
  show ?case
    using a combine_blocks_wait2(7) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have a: "d = ereal t2" "d = t1"
    using combine_blocks_wait3(2,3) by (auto simp add: WaitBlk_cong)
  show ?case
    using a combine_blocks_wait3(7) by auto
qed (auto)

lemma combine_blocks_waitE3 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   0 < d1 \<Longrightarrow> d1 < d2 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  have a: "t = ereal d1" "t = d2"
    using combine_blocks_wait1(2,3) WaitBlk_cong by blast+
  then show ?case
    using combine_blocks_wait1(10) by auto
next
  case (combine_blocks_wait2 comms' blks1 t2 t1 hist2 rdy2' blks2 blks rdy1' hist hist1 rdy)
  have a: "d1 = t1" "d2 = t2" "rdy1 = rdy1'" "rdy2 = rdy2'" "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait2(2,3) using WaitBlk_cong by blast+
  have a2: "WaitBlk d2 p2 rdy2 = WaitBlk d2 hist2 rdy2"
    using combine_blocks_wait2(3) unfolding a[symmetric] by auto
  have a3: "WaitBlk d1 p2 rdy2 = WaitBlk d1 hist2 rdy2"
           "WaitBlk (d2 - d1) (\<lambda>\<tau>. p2 (\<tau> + d1)) rdy2 = WaitBlk (d2 - d1) (\<lambda>\<tau>. hist2 (\<tau> + d1)) rdy2"
    using WaitBlk_split[OF a2] combine_blocks_wait2 by auto
  have b: "WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk t1 (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine)
    using combine_blocks_wait2.hyps(2) a(1,4) a3 by auto
  show ?case
    apply (rule combine_blocks_wait2) unfolding a3 b
    using combine_blocks_wait2(4) unfolding combine_blocks_wait2(9,10)
    by (auto simp add: a combine_blocks_wait2(1,5))
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have "ereal d1 = t1" "d2 = ereal t2"
    using combine_blocks_wait3(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait3(7,12) by auto
qed (auto)

lemma combine_blocks_waitE4 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   0 < d2 \<Longrightarrow> d2 < d1 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  have "d1 = t" "ereal d2 = t"
    using combine_blocks_wait1(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait1(10) by auto
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have "d1 = ereal t1" "ereal d2 = t2"
    using combine_blocks_wait2(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait2(7,12) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1' blks1 blks2 blks rdy2' hist hist2 rdy)
  have a: "d1 = t1" "d2 = t2" "rdy1 = rdy1'" "rdy2 = rdy2'"
          "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait3(2,3) using WaitBlk_cong by blast+
  have a2: "WaitBlk d1 p1 rdy1 = WaitBlk d1 hist1 rdy1"
    using combine_blocks_wait3(2) unfolding a[symmetric] by auto
  have a3: "WaitBlk d2 p1 rdy1 = WaitBlk d2 hist1 rdy1"
           "WaitBlk (d1 - d2) (\<lambda>\<tau>. p1 (\<tau> + d2)) rdy1 = WaitBlk (d1 - d2) (\<lambda>\<tau>. hist1 (\<tau> + d2)) rdy1"
    using WaitBlk_split[OF a2] combine_blocks_wait3 by auto
  have b: "WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk d2 (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine)
    using combine_blocks_wait3 a(2,3) a3 by auto
  show ?case
    apply (rule combine_blocks_wait3) unfolding a3 b
    using combine_blocks_wait3(4) unfolding combine_blocks_wait3(9,10)
    by (auto simp add: a combine_blocks_wait3)
qed (auto)
*)
lemma combine_blocks_emptyE1 [sync_elims]:
  "combine_blocks comms [] [] tr \<Longrightarrow> tr = []"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) [] tr \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2' [sync_elims]:
  "combine_blocks comms [] (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE3 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) [] tr \<Longrightarrow>
   (\<And>tr'. ch1 \<notin> comms \<Longrightarrow> tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 [] tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE3' [sync_elims]:
  "combine_blocks comms [] (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   (\<And>tr'. ch2 \<notin> comms \<Longrightarrow> tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms [] tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)


text \<open>Synchronization of two assertions\<close>

lemma combine_assn_emp:
  "Q \<Longrightarrow>\<^sub>S combine_assn (\<lambda>P1. P1) (\<lambda>P2. P2) chs Q"
  unfolding combine_assn_def entails2_def by auto

theorem combine_assn_in_out:
  fixes Q :: "state \<Rightarrow> state \<Rightarrow> bool"
    and e :: "state \<Rightarrow> real"
    and f :: "assn \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> assn)"
    and g :: "assn \<Rightarrow> (real \<Rightarrow> assn)"
  assumes "ch \<in> chs"
  shows "combine_assn (\<lambda>P1. f2 P1) (\<lambda>P2. g2 P2) chs Q \<Longrightarrow>\<^sub>S
         combine_assn (\<lambda>P1. wait_in ch (f P1)) (\<lambda>P2. wait_out ch e (g P2)) chs Q"
  unfolding entails2_def combine_assn_def wait_in_def wait_out_def apply auto
  sorry  

end
