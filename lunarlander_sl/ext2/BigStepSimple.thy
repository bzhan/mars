theory BigStepSimple
  imports "../Analysis_More"
begin


subsection \<open>Extended state\<close>

text \<open>Extended state is parameterized by a type 'a\<close>
datatype 'a estate = EState (rp: state) (ep: 'a)

text \<open>Expressions on an extended state\<close>
type_synonym 'a eexp = "'a estate \<Rightarrow> real"

text \<open>Predicates on an extended state\<close>
type_synonym 'a eform = "'a estate \<Rightarrow> bool"

text \<open>Updating some variable in the real part of the state\<close>
fun upd :: "'a estate \<Rightarrow> var \<Rightarrow> real \<Rightarrow> 'a estate" where
  "upd (EState r e) x v = EState (r(x := v)) e"

text \<open>Updating entirety of the real part of the state\<close>
fun updr :: "'a estate \<Rightarrow> state \<Rightarrow> 'a estate" where
  "updr (EState r e) r2 = EState r2 e"

text \<open>Updating the extra part of the state\<close>
fun upde :: "'a estate \<Rightarrow> 'a \<Rightarrow> 'a estate" where
  "upde (EState r e) e2 = EState r e2"

text \<open>Taking the real part and extra part of the state\<close>
fun rpart :: "'a estate \<Rightarrow> state" where
  "rpart (EState r e) = r"

fun epart :: "'a estate \<Rightarrow> 'a" where
  "epart (EState r e) = e"

fun val :: "'a estate \<Rightarrow> var \<Rightarrow> real" where
  "val (EState r e) v = r v"

declare upd.simps [simp del]
declare updr.simps [simp del]
declare rpart.simps [simp del]
declare epart.simps [simp del]
declare val.simps [simp del]

subsection \<open>Syntax\<close>

text \<open>Channel names\<close>
type_synonym cname = string

text \<open>Process names\<close>
type_synonym pname = string

text \<open>Ready information.
  First component is set of channels that are ready to output.
  Second component is set of channels that are ready to input.\<close>
type_synonym rdy_info = "cname set \<times> cname set"

text \<open>Communications\<close>
datatype 'a comm =
  Send cname "'a eexp"        ("_[!]_" [110,108] 100)
| Receive cname var           ("_[?]_" [110,108] 100)

text \<open>HCSP processes\<close>
datatype 'a proc =
  Cm "'a comm"
| Skip
| Assign var "'a eexp"                 ("_ ::= _" [99,95] 94)
| Basic "'a estate \<Rightarrow> 'a"
| Error
| Seq "'a proc" "'a proc"              ("_; _" [91,90] 90)
| Cond "'a eform" "'a proc" "'a proc"  ("IF _ THEN _ ELSE _ FI" [95,94] 93)
| Wait "'a eexp"  \<comment> \<open>Waiting for a specified amount of time\<close>
| IChoice "'a proc" "'a proc"  \<comment> \<open>Nondeterminism\<close>
| EChoice "('a comm \<times> 'a proc) list"  \<comment> \<open>External choice\<close>
| Rep "'a proc"   \<comment> \<open>Nondeterministic repetition\<close>
| Cont ODE "'a eform"  \<comment> \<open>ODE with boundary\<close>
| Interrupt ODE "'a eform" "('a comm \<times> 'a proc) list"  \<comment> \<open>Interrupt\<close>

text \<open>Parallel of several HCSP processes\<close>
datatype 'a pproc =
  Single pname "'a proc"
| Parallel "'a pproc" "cname set" "'a pproc"

text \<open>Set of process names of a parallel process\<close>
fun proc_of_pproc :: "'a pproc \<Rightarrow> pname set" where
  "proc_of_pproc (Single pn c) = {pn}"
| "proc_of_pproc (Parallel p1 chs p2) = proc_of_pproc p1 \<union> proc_of_pproc p2"

text \<open>Global state.
  This is represented as a partial mapping from process name to
  extended state.\<close>
type_synonym 'a gstate = "pname \<Rightarrow> 'a estate option"

text \<open>Global state for a single process\<close>
definition State :: "pname \<Rightarrow> 'a estate \<Rightarrow> 'a gstate" where
  "State p s = (\<lambda>p'. if p' = p then Some s else None)"

lemma State_eval [simp]:
  "State p s p = Some s"
  by (auto simp add: State_def)

subsection \<open>Traces\<close>

datatype comm_type = In | Out

text \<open>Each trace block is either:
  - Communication block, specified by communication type (In or Out),
    name of the channel, and the communicated value.
  - Wait block, specified by length of the wait, state as a function
    of time during the wait, and set of ready communications.
\<close>
datatype 'a trace_block =
  CommBlock comm_type cname real
| WaitBlock real "real \<Rightarrow> 'a estate" rdy_info

abbreviation "InBlock ch v \<equiv> CommBlock In ch v"
abbreviation "OutBlock ch v \<equiv> CommBlock Out ch v"

text \<open>Trace is defined as an ordered list of trace blocks.\<close>
type_synonym 'a trace = "'a trace_block list"


subsection \<open>Big-step semantics\<close>

text \<open>Compute list of ready communications for an external choice.\<close>
fun rdy_of_echoice :: "('a comm \<times> 'a proc) list \<Rightarrow> rdy_info" where
  "rdy_of_echoice [] = ({}, {})"
| "rdy_of_echoice ((ch[!]e, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_echoice ((ch[?]var, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (fst rdy, insert ch (snd rdy)))"

text \<open>big_step p s1 tr s2 means executing p starting from state s1 results
in a trace tr and final state s2.\<close>
inductive big_step :: "'a proc \<Rightarrow> 'a estate \<Rightarrow> 'a trace \<Rightarrow> 'a estate \<Rightarrow> bool" where
  skipB: "big_step Skip s [] s"
| assignB: "big_step (var ::= e) s [] (upd s var (e s))"
| basicB: "big_step (Basic f) s [] (upde s (f s))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (p1; p2) s1 (tr1 @ tr2) s3"
| condB1: "b s1 \<Longrightarrow> big_step p1 s1 tr s2 \<Longrightarrow> big_step (IF b THEN p1 ELSE p2 FI) s1 tr s2"
| condB2: "\<not> b s1 \<Longrightarrow> big_step p2 s1 tr s2 \<Longrightarrow> big_step (IF b THEN p1 ELSE p2 FI) s1 tr s2"
| waitB1: "e s > 0 \<Longrightarrow> big_step (Wait e) s [WaitBlock (e s) (\<lambda>_. s) ({}, {})] s"
| waitB2: "\<not> e s > 0 \<Longrightarrow> big_step (Wait e) s [] s"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlock d (\<lambda>_. s) ({ch}, {}),
             OutBlock ch (e s)] s"
| receiveB1: "big_step (Cm (ch[?]var)) s [InBlock ch v] (upd s var v)"
| receiveB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlock d (\<lambda>_. s) ({}, {ch}),
             InBlock ch v] (upd s var v)"
| IChoiceB1: "big_step p1 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| IChoiceB2: "big_step p2 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| EChoiceSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (OutBlock ch (e s1) # tr2) s2"
| EChoiceSendB2: "(d::real) > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlock d (\<lambda>_. s1) (rdy_of_echoice cs) #
                              OutBlock ch (e s1) # tr2) s2"
| EChoiceReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (upd s1 var v) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (InBlock ch v # tr2) s2"
| EChoiceReceiveB2: "(d::real) > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (upd s1 var v) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlock d (\<lambda>_. s1) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (updr s1 (p t))) \<Longrightarrow>
    \<not>b (updr s1 (p d)) \<Longrightarrow> p 0 = rpart s1 \<Longrightarrow>
    big_step (Cont ode b) s1 [WaitBlock d (\<lambda>\<tau>. updr s1 (p \<tau>)) ({}, {})] (updr s1 (p d))"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = rpart s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (updr s1 (p t))) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (updr s1 (p d)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlock d (\<lambda>\<tau>. updr s1 (p \<tau>)) rdy #
                                      OutBlock ch (e (updr s1 (p d))) # tr2) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (upd s var v) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = rpart s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (updr s1 (p t))) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (updr s1 ((p d)(var := v))) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlock d (\<lambda>\<tau>. updr s1 (p \<tau>)) rdy #
                                      InBlock ch v # tr2) s2"
| InterruptB1: "\<not>b s \<Longrightarrow> big_step (Interrupt ode b cs) s [] s"
| InterruptB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (updr s1 (p t))) \<Longrightarrow>
    \<not>b (updr s1 (p d)) \<Longrightarrow> p 0 = rpart s1 \<Longrightarrow> p d = rpart s2 \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 [WaitBlock d (\<lambda>\<tau>. updr s1 (p \<tau>)) rdy] s2"

lemma big_step_cong:
  "big_step c s1 tr s2 \<Longrightarrow> tr = tr' \<Longrightarrow> s2 = s2' \<Longrightarrow> big_step c s1 tr' s2'"
  by auto

inductive_cases skipE: "big_step Skip s1 tr s2"
inductive_cases assignE: "big_step (Assign var e) s1 tr s2"
inductive_cases basicE: "big_step (Basic f) s1 tr s2"
inductive_cases errorE: "big_step Error s1 tr s2"
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
type_synonym 'a assn = "'a estate \<Rightarrow> 'a trace \<Rightarrow> bool"

text \<open>We also define assertions parameterized by starting state.\<close>
type_synonym 'a assn2 = "'a estate \<Rightarrow> 'a assn"

text \<open>Assertion stating the trace is empty.\<close>
definition emp :: "'a assn" where
  "emp = (\<lambda>s tr. tr = [])"

definition false_assn2 :: "'a assn2" where
  "false_assn2 = (\<lambda>s0 s tr. False)"

text \<open>Quantifiers on assertions.\<close>
definition forall_assn :: "('b \<Rightarrow> 'a assn) \<Rightarrow> 'a assn" (binder "\<forall>\<^sub>a" 10)where
  "(\<forall>\<^sub>a n. P n) = (\<lambda>s tr. \<forall>n. P n s tr)"

definition exists_assn :: "('b \<Rightarrow> 'a assn) \<Rightarrow> 'a assn" (binder "\<exists>\<^sub>a" 10)where
  "(\<exists>\<^sub>a n. P n) = (\<lambda>s tr. \<exists>n. P n s tr)"

text \<open>Substitution on assertions: real part.
  Starting from a parameterized assertion P, let P act on the
  state after making an assignment.
\<close>
definition subst_assn2 :: "'a assn2 \<Rightarrow> var \<Rightarrow> ('a estate \<Rightarrow> real) \<Rightarrow> 'a assn2"
  ("_ {{_ := _}}" [90,90,90] 91) where 
  "P {{var := e}} = (\<lambda>s0. P (upd s0 var (e s0)))"

text \<open>Substitution on assertions: extra part.
  Starting from a parameterized assertion P, let P act on the
  state after updating the extra part using function f.  
\<close>
definition subste_assn2 :: "'a assn2 \<Rightarrow> ('a estate \<Rightarrow> 'a) \<Rightarrow> 'a assn2"
  ("_ {{_}}" [90,90] 91) where 
  "P {{f}} = (\<lambda>s0. P (upde s0 (f s0)))"

text \<open>Definition of Hoare triple\<close>
definition Valid :: "'a assn \<Rightarrow> 'a proc \<Rightarrow> 'a assn \<Rightarrow> bool" ("\<Turnstile> ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile> {P} c {Q} \<longleftrightarrow> (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step c s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"

text \<open>Entailment relation between assertions\<close>
definition entails :: "'a assn \<Rightarrow> 'a assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

theorem entails_triv:
  "P \<Longrightarrow>\<^sub>A P"
  unfolding entails_def by auto

lemma entails_trans:
  "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>A R \<Longrightarrow> P \<Longrightarrow>\<^sub>A R"
  unfolding entails_def by auto

theorem strengthen_pre:
  "\<Turnstile> {P2} c {Q} \<Longrightarrow> P1 \<Longrightarrow>\<^sub>A P2 \<Longrightarrow> \<Turnstile> {P1} c {Q}"
  unfolding Valid_def entails_def by metis

theorem weaken_post:
  "\<Turnstile> {P} c {Q1} \<Longrightarrow> Q1 \<Longrightarrow>\<^sub>A Q2 \<Longrightarrow> \<Turnstile> {P} c {Q2}"
  unfolding Valid_def entails_def by metis

text \<open>Parameterized assertion, specifying the initial state to be s0.\<close>
definition init :: "'a assn2" where
  "init s0 = (\<lambda>s tr. s = s0 \<and> tr = [])"

text \<open>Specification of a single process\<close>
definition spec_of :: "'a proc \<Rightarrow> 'a assn2 \<Rightarrow> bool" where
  "spec_of c Q \<longleftrightarrow> (\<forall>s0. \<Turnstile> {init s0} c {Q s0})"

text \<open>Hoare rule for skip statement\<close>
lemma spec_of_skip:
  "spec_of Skip init"
  unfolding Valid_def spec_of_def
  by (auto elim: skipE)

lemma Valid_skip_sp:
  assumes "spec_of c Q"
  shows "spec_of (Skip; c) Q"
  unfolding Valid_def spec_of_def
  apply (auto elim!: seqE skipE)
  using assms unfolding spec_of_def Valid_def init_def by auto

text \<open>Hoare rule for assign\<close>
lemma spec_of_assign:
  "spec_of (var ::= e) (\<lambda>s0 s tr. s = upd s0 var (e s0))"
  unfolding Valid_def spec_of_def init_def
  by (auto elim!: assignE)

lemma Valid_assign_sp:
  assumes "spec_of c Q"
  shows "spec_of (var ::= e; c) (Q {{ var := e }})"
  unfolding Valid_def spec_of_def
  apply (auto elim!: seqE assignE)
  using assms unfolding spec_of_def Valid_def init_def subst_assn2_def by auto

text \<open>Hoare rule for updating the extra state\<close>
lemma spec_of_basic:
  "spec_of (Basic f) (\<lambda>s0 s tr. s = upde s0 (f s0))"
  unfolding Valid_def spec_of_def init_def
  by (auto elim: basicE)

lemma Valid_basic_sp:
  assumes "spec_of c Q"
  shows "spec_of (Basic f; c) (Q {{ f }})"
  unfolding Valid_def spec_of_def
  apply (auto elim!: seqE basicE)
  using assms unfolding spec_of_def Valid_def init_def subste_assn2_def by auto

text \<open>Hoare rule for error\<close>
lemma spec_of_error:
  "spec_of Error P"
  unfolding Valid_def spec_of_def init_def
  by (auto elim: errorE)

lemma Valid_error_sp:
  "spec_of (Error; c) Q"
  unfolding Valid_def spec_of_def
  by (auto elim: seqE errorE)

text \<open>Hoare rule for conditional\<close>
definition cond_assn2 :: "'a eform \<Rightarrow> 'a assn2 \<Rightarrow> 'a assn2 \<Rightarrow> 'a assn2"
  ("IFA _ THEN _ ELSE _ FI" [95,94] 93) where
  "IFA b THEN Q1 ELSE Q2 FI = (\<lambda>s0 s tr. if b s0 then Q1 s0 s tr else Q2 s0 s tr)"

lemma spec_of_cond:
  assumes "spec_of c1 Q1"
    and "spec_of c2 Q2"
  shows "spec_of (IF b THEN c1 ELSE c2 FI) (IFA b THEN Q1 ELSE Q2 FI)"
  unfolding Valid_def spec_of_def init_def cond_assn2_def
  apply (auto elim!: condE)
  using assms unfolding Valid_def spec_of_def init_def by auto

text \<open>Hoare rule for input.
  The corresponding assertion is divided into two cases, either the input
  happens immediately, or after waiting for some time. The ensuing assertion
  is parameterized by waiting time and communicated value.
\<close>
inductive wait_in_c :: "cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "P 0 v s0 s tr \<Longrightarrow> wait_in_c ch P s0 s (InBlock ch v # tr)"
| "0 < d \<Longrightarrow> P d v s0 s tr \<Longrightarrow> wait_in_c ch P s0 s (WaitBlock d (\<lambda>_. s0) ({}, {ch}) # InBlock ch v # tr)"

lemma spec_of_receive:
  "spec_of (Cm (ch[?]var)) (wait_in_c ch (\<lambda>d v. init {{ var := (\<lambda>_. v) }}))"
  unfolding Valid_def spec_of_def init_def subst_assn2_def
  apply (auto elim!: receiveE)
   apply (rule wait_in_c.intros(1)) apply auto[1]
  apply (rule wait_in_c.intros(2)) by auto

lemma Valid_receive_sp:
  assumes "spec_of c Q"
  shows "spec_of (Cm (ch[?]var); c)
                 (wait_in_c ch (\<lambda>d v. Q {{ var := (\<lambda>_. v) }}))"
  using assms unfolding Valid_def spec_of_def init_def subst_assn2_def
  apply (auto elim!: seqE receiveE)
  apply (rule wait_in_c.intros(1)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  apply (rule wait_in_c.intros(2)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  done

text \<open>Hoare rule for output.
  In the corresponding assertion, the communicated value is computed by the
  function e. The ensuing assertion is parameterized by waiting time.
\<close>
inductive wait_out_c :: "cname \<Rightarrow> ('a estate \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "P 0 s0 s tr \<Longrightarrow> wait_out_c ch e P s0 s (OutBlock ch (e s0) # tr)"
| "0 < d \<Longrightarrow> P d s0 s tr \<Longrightarrow> wait_out_c ch e P s0 s (WaitBlock d (\<lambda>_. s0) ({ch}, {}) # OutBlock ch (e s0) # tr)"

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
  using assms unfolding Valid_def spec_of_def init_def
  apply (auto elim!: seqE sendE)
   apply (rule wait_out_c.intros(1))
  using Valid_def spec_of_def init_def assms apply auto[1]
  apply (rule wait_out_c.intros(2)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  done

text \<open>Commutativity between assertions and quantifiers.\<close>
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

text \<open>Monotonicity rules\<close>
lemma wait_in_c_mono:
  assumes "\<And>d v s. P1 d v s \<Longrightarrow>\<^sub>A P2 d v s"
  shows "wait_in_c ch P1 s0 \<Longrightarrow>\<^sub>A wait_in_c ch P2 s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (induct rule: wait_in_c.cases) apply auto
    subgoal for v tr'
      apply (rule wait_in_c.intros(1))
      using assms unfolding entails_def by auto
    subgoal for d v tr'
      apply (rule wait_in_c.intros(2))
      using assms unfolding entails_def by auto
    done
  done

lemma wait_out_c_mono:
  assumes "\<And>d s. P1 d s \<Longrightarrow>\<^sub>A P2 d s"
  shows "wait_out_c ch e P1 s0 \<Longrightarrow>\<^sub>A wait_out_c ch e P2 s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (induct rule: wait_out_c.cases) apply auto
    subgoal for tr'
      apply (rule wait_out_c.intros(1))
      using assms unfolding entails_def by auto
    subgoal for d tr'
      apply (rule wait_out_c.intros(2))
      using assms unfolding entails_def by auto
    done
  done


text \<open>Consequence rule\<close>
lemma spec_of_post:
  "spec_of c Q1 \<Longrightarrow> \<forall>s0. Q1 s0 \<Longrightarrow>\<^sub>A Q2 s0 \<Longrightarrow> spec_of c Q2"
  unfolding spec_of_def using weaken_post by blast

text \<open>Relation between quantifiers on assertions and usual quantifiers.\<close>
lemma entails_exists:
  assumes "\<exists>n. P \<Longrightarrow>\<^sub>A Q n"
  shows "P \<Longrightarrow>\<^sub>A (\<exists>\<^sub>a n. Q n)"
  using assms unfolding exists_assn_def entails_def
  by auto

text \<open>Repetition for n times.\<close>
fun RepN :: "nat \<Rightarrow> 'a proc \<Rightarrow> 'a proc" where
  "RepN 0 c = Skip"
| "RepN (Suc n) c = c; RepN n c"

text \<open>Some rules about big-step operational semantics\<close>
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
  using big_step_seq_assoc by blast

lemma big_step_cond_distrib:
  "big_step ((IF b THEN c1 ELSE c2 FI); c) s1 tr s2 \<longleftrightarrow>
   big_step ((IF b THEN (c1; c) ELSE (c2; c) FI)) s1 tr s2"
  apply (rule iffI)
  subgoal apply (elim seqE)
    subgoal for tr1 s3 tr2
      apply (cases "b s1")
      subgoal 
        apply (rule condB1) apply simp
        apply auto apply (rule seqB) by (auto elim: condE)
      subgoal
        apply (rule condB2) apply simp
        apply auto apply (rule seqB) by (auto elim: condE)
      done
    done
  subgoal apply (elim condE)
    subgoal
      apply (elim seqE) apply auto
      apply (rule seqB) by (auto intro: condB1)
    subgoal
      apply (elim seqE) apply auto
      apply (rule seqB) by (auto intro: condB2)
    done
  done

lemma spec_of_cond_distrib:
  "spec_of ((IF b THEN c1 ELSE c2 FI); c) Q \<longleftrightarrow>
   spec_of ((IF b THEN (c1; c) ELSE (c2; c) FI)) Q"
  unfolding spec_of_def Valid_def
  using big_step_cond_distrib by blast

lemma spec_of_rep:
  assumes "\<And>n. spec_of (RepN n c) (Q n)"
  shows "spec_of (Rep c) (\<lambda>s0. \<exists>\<^sub>a n. Q n s0)"
  using assms unfolding spec_of_def Valid_def big_step_rep exists_assn_def
  by blast

subsection \<open>Combining two traces\<close>

text \<open>Whether two rdy_infos from different processes are compatible.\<close>
fun compat_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

text \<open>Merge two rdy infos\<close>
fun merge_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> rdy_info" where
  "merge_rdy (r11, r12) (r21, r22) = (r11 \<union> r21, r12 \<union> r22)"

text \<open>Trace blocks for a parallel process.
  The only difference from trace blocks for a single process is that
  the waiting blocks record states for parallel processes.
\<close>
datatype 'a ptrace_block = 
  CommBlockP comm_type cname real
| WaitBlockP real "real \<Rightarrow> 'a gstate" rdy_info

abbreviation "InBlockP ch v \<equiv> CommBlockP In ch v"
abbreviation "OutBlockP ch v \<equiv> CommBlockP Out ch v"

text \<open>Trace for parallel process consists of a list of trace blocks.\<close>
type_synonym 'a ptrace = "'a ptrace_block list"

text \<open>Merge of two states.
  For each process name, first look up in the left state, if not
  found look up in the right state. This is ''well-behaved'' only
  if the states on the two sides have disjoint domains, an assumption
  we will need to use frequently.
\<close>
definition merge_state :: "'a gstate \<Rightarrow> 'a gstate \<Rightarrow> 'a gstate" where
  "merge_state ps1 ps2 = (\<lambda>p. case ps1 p of None \<Rightarrow> ps2 p | Some s \<Rightarrow> Some s)"

text \<open>combine_blocks comms tr1 tr2 tr means tr1 and tr2 combines to tr, where
  comms is the list of internal communication channels.\<close>
inductive combine_blocks :: "cname set \<Rightarrow> 'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> 'a ptrace \<Rightarrow> bool" where
  \<comment> \<open>Empty case\<close>
  combine_blocks_empty:
  "combine_blocks comms [] [] []"

  \<comment> \<open>Paired communication\<close>
| combine_blocks_pair1:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (InBlockP ch v # blks1) (OutBlockP ch v # blks2) blks"
| combine_blocks_pair2:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (OutBlockP ch v # blks1) (InBlockP ch v # blks2) blks"

  \<comment> \<open>Unpaired communication\<close>
| combine_blocks_unpair1:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (CommBlockP ch_type ch v # blks1) blks2 (CommBlockP ch_type ch v # blks)"
| combine_blocks_unpair2:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (CommBlockP ch_type ch v # blks2) (CommBlockP ch_type ch v # blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_wait1:
  "combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = (\<lambda>\<tau>. merge_state (hist1 \<tau>) (hist2 \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlockP t hist1 rdy1 # blks1)
                        (WaitBlockP t hist2 rdy2 # blks2)
                        (WaitBlockP t hist rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlockP (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow> t1 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. merge_state (hist1 \<tau>) (hist2 \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlockP t1 hist1 rdy1 # blks1)
                        (WaitBlockP t2 hist2 rdy2 # blks2)
                        (WaitBlockP t1 hist rdy # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlockP (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow> t2 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. merge_state (hist1 \<tau>) (hist2 \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlockP t1 hist1 rdy1 # blks1)
                        (WaitBlockP t2 hist2 rdy2 # blks2)
                        (WaitBlockP t2 hist rdy # blks)"

text \<open>Conversion from trace for a single process to trace for
  parallel processes.
\<close>
fun ptrace_of :: "pname \<Rightarrow> 'a trace \<Rightarrow> 'a ptrace" where
  "ptrace_of pn [] = []"
| "ptrace_of pn (CommBlock ch_type ch v # tr) = CommBlockP ch_type ch v # ptrace_of pn tr"
| "ptrace_of pn (WaitBlock d p rdy # tr) = WaitBlockP d (\<lambda>\<tau>. State pn (p \<tau>)) rdy # ptrace_of pn tr"

text \<open>Set of processes in a parallel state.\<close>
definition proc_set :: "'a gstate \<Rightarrow> pname set" where
  "proc_set gs = {pn. gs pn \<noteq> None}"

text \<open>Definition of big-step operational semantics for parallel processes.
  Note the restriction on disjoint condition for process names,
  as needed for good behavior of merge_state.
\<close>
inductive par_big_step :: "'a pproc \<Rightarrow> 'a gstate \<Rightarrow> 'a ptrace \<Rightarrow> 'a gstate \<Rightarrow> bool" where
  SingleB:
    "big_step p s1 tr s2 \<Longrightarrow>
     par_big_step (Single pn p) (State pn s1) (ptrace_of pn tr) (State pn s2)"
| ParallelB:
    "par_big_step p1 s11 tr1 s12 \<Longrightarrow>
     par_big_step p2 s21 tr2 s22 \<Longrightarrow>
     proc_of_pproc p1 \<inter> proc_of_pproc p2 = {} \<Longrightarrow>
     combine_blocks chs tr1 tr2 tr \<Longrightarrow>
     par_big_step (Parallel p1 chs p2) (merge_state s11 s21) tr (merge_state s12 s22)"

inductive_cases SingleE: "par_big_step (Single pn p) s1 tr s2"
inductive_cases ParallelE: "par_big_step (Parallel p1 ch p2) s1 tr s2"

lemma proc_set_State [simp]:
  "proc_set (State pn s) = {pn}"
  by (auto simp add: proc_set_def State_def)

lemma proc_set_merge [simp]:
  "proc_set (merge_state s1 s2) = proc_set s1 \<union> proc_set s2"
  apply (auto simp add: proc_set_def merge_state_def)
  subgoal for x y apply (cases "s1 x") by auto
  done

lemma proc_set_big_step:
  "par_big_step p s1 tr s2 \<Longrightarrow> proc_set s1 = proc_of_pproc p \<and> proc_set s2 = proc_of_pproc p"
  apply (induction rule: par_big_step.induct) by auto


text \<open>Assertion on global state\<close>
type_synonym 'a gs_assn = "'a gstate \<Rightarrow> bool"

text \<open>Assertion on global state and trace\<close>
type_synonym 'a gassn = "'a gstate \<Rightarrow> 'a ptrace \<Rightarrow> bool"

text \<open>Parameterized assertions on global state and trace\<close>
type_synonym 'a gassn2 = "'a gstate \<Rightarrow> 'a gassn"

definition entails_g :: "'a gassn \<Rightarrow> 'a gassn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>g" 25) where
  "(P \<Longrightarrow>\<^sub>g Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

lemma entails_g_triv:
  "P \<Longrightarrow>\<^sub>g P"
  unfolding entails_g_def by auto

lemma entails_g_trans:
  "P \<Longrightarrow>\<^sub>g Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>g R \<Longrightarrow> P \<Longrightarrow>\<^sub>g R"
  unfolding entails_g_def by auto

definition ParValid :: "'a gs_assn \<Rightarrow> 'a pproc \<Rightarrow> 'a gassn \<Rightarrow> bool" ("\<Turnstile>\<^sub>p ({(1_)}/ (_)/ {(1_)})" 50) where
  "(\<Turnstile>\<^sub>p {P} c {Q}) \<longleftrightarrow> (\<forall>s1 s2 tr2. P s1 \<longrightarrow> par_big_step c s1 tr2 s2 \<longrightarrow> Q s2 tr2)"

definition init_global :: "'a gstate \<Rightarrow> 'a gs_assn" where
  "init_global s0 = (\<lambda>s. s = s0)"

lemma init_global_parallel:
  "init_global s0 (merge_state s1 s2) \<Longrightarrow>
   (\<And>s01 s02. s0 = merge_state s01 s02 \<Longrightarrow> init_global s01 s1 \<Longrightarrow> init_global s02 s2 \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding init_global_def by auto

definition spec_of_global :: "'a pproc \<Rightarrow> 'a gassn2 \<Rightarrow> bool" where
  "spec_of_global c Q \<longleftrightarrow> (\<forall>s0. \<Turnstile>\<^sub>p {init_global s0} c {Q s0})"

lemma spec_of_globalE:
  "spec_of_global c Q \<Longrightarrow> \<Turnstile>\<^sub>p {init_global s0} c {Q s0}"
  unfolding spec_of_global_def by auto

inductive single_assn :: "pname \<Rightarrow> 'a assn2 \<Rightarrow> 'a gassn2" where
  "Q s s' tr \<Longrightarrow> single_assn pn Q (State pn s) (State pn s') (ptrace_of pn tr)"

inductive sync_gassn :: "cname set \<Rightarrow> pname set \<Rightarrow> pname set \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2" where
  "proc_set s11 = pns1 \<Longrightarrow> proc_set s12 = pns2 \<Longrightarrow>
   proc_set s21 = pns1 \<Longrightarrow> proc_set s22 = pns2 \<Longrightarrow>
   P s11 s21 tr1 \<Longrightarrow> Q s12 s22 tr2 \<Longrightarrow>
   combine_blocks chs tr1 tr2 tr \<Longrightarrow>
   sync_gassn chs pns1 pns2 P Q (merge_state s11 s12) (merge_state s21 s22) tr"

lemma spec_of_single:
  fixes Q :: "'a assn2"
  assumes "spec_of c Q"
  shows "spec_of_global (Single pn c) (single_assn pn Q)"
  unfolding spec_of_global_def ParValid_def init_global_def apply auto
  apply (elim SingleE) 
  using assms unfolding spec_of_def Valid_def init_def
  by (auto intro: single_assn.intros)

lemma spec_of_parallel:
  fixes P Q :: "'a gassn2"
  assumes "spec_of_global p1 P"
    and "spec_of_global p2 Q"
    and "proc_of_pproc p1 = pns1"
    and "proc_of_pproc p2 = pns2"
  shows "spec_of_global (Parallel p1 chs p2) (sync_gassn chs pns1 pns2 P Q)"
  unfolding spec_of_global_def ParValid_def apply auto
  apply (elim ParallelE) apply auto
  apply (elim init_global_parallel) apply (auto simp add: init_global_def)
  subgoal for tr' tr1 s12 tr2 s22 s01 s02
    apply (rule sync_gassn.intros)
    apply (auto simp add: assms(3,4) proc_set_big_step)
    using assms(1,2) unfolding spec_of_global_def ParValid_def init_global_def
    by (auto elim: proc_set_big_step)
  done

lemma weaken_post_global:
  "\<Turnstile>\<^sub>p {P} c {R} \<Longrightarrow> R \<Longrightarrow>\<^sub>g Q \<Longrightarrow> \<Turnstile>\<^sub>p {P} c {Q}"
  unfolding ParValid_def entails_g_def by auto

lemma spec_of_global_post:
  "spec_of_global p Q1 \<Longrightarrow> \<forall>s0. Q1 s0 \<Longrightarrow>\<^sub>g Q2 s0 \<Longrightarrow> spec_of_global p Q2"
  unfolding spec_of_global_def using weaken_post_global by blast

subsection \<open>More assertions for parallel\<close>

inductive wait_in_cg :: "cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" where
  "P 0 v s0 s tr \<Longrightarrow> wait_in_cg ch P s0 s (InBlockP ch v # tr)"
| "0 < d \<Longrightarrow> P d v s0 s tr \<Longrightarrow> wait_in_cg ch P s0 s (WaitBlockP d (\<lambda>_. s0) ({}, {ch}) # InBlockP ch v # tr)"

lemma single_assn_wait_in:
  "single_assn pn (wait_in_c ch1 P) = wait_in_cg ch1 (\<lambda>d v. single_assn pn (P d v))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0' s' tr'
        apply (elim wait_in_c.cases) apply auto
        by (auto intro: wait_in_cg.intros single_assn.intros)
      done
    subgoal apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr'
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (subst ptrace_of.simps[symmetric])
          apply (rule single_assn.intros)
          apply (rule wait_in_c.intros) by auto
        done
      subgoal for d v tr'
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (simp only: ptrace_of.simps[symmetric])
          apply (rule single_assn.intros)
          apply (rule wait_in_c.intros) by auto
        done
      done
    done
  done

inductive wait_out_cg :: "cname \<Rightarrow> pname \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" where
  "P 0 s0 s tr \<Longrightarrow> v = e (the (s0 pn)) \<Longrightarrow>  wait_out_cg ch pn e P s0 s (OutBlockP ch v # tr)"
| "0 < d \<Longrightarrow> P d s0 s tr \<Longrightarrow> v = e (the (s0 pn)) \<Longrightarrow>
   wait_out_cg ch pn e P s0 s (WaitBlockP d (\<lambda>_. s0) ({ch}, {}) # OutBlockP ch v # tr)"

lemma single_assn_wait_out:
  "single_assn pn (wait_out_c ch1 e P) = wait_out_cg ch1 pn e (\<lambda>d. single_assn pn (P d))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      apply (elim wait_out_c.cases) apply auto
      subgoal for s0' s' tr'
        apply (rule wait_out_cg.intros(1))
         apply (rule single_assn.intros)
        by (auto simp add: State_def)
      subgoal for d s0' s' tr'
        apply (rule wait_out_cg.intros(2)) apply simp
         apply (rule single_assn.intros)
        by (auto simp add: State_def)
      done
    subgoal apply (elim wait_out_cg.cases) apply auto
      subgoal for tr'
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (simp only: ptrace_of.simps[symmetric])
          apply (rule single_assn.intros) apply auto
          apply (simp add: State_def)
          apply (rule wait_out_c.intros) by auto
        done
      subgoal for d tr'
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (simp only: ptrace_of.simps[symmetric])
          apply (rule single_assn.intros) apply auto
          apply (simp add: State_def)
          apply (rule wait_out_c.intros) by auto
        done
      done
    done
  done

definition updg :: "'a gstate \<Rightarrow> pname \<Rightarrow> var \<Rightarrow> real \<Rightarrow> 'a gstate" where
  "updg gs pn x v = gs (pn \<mapsto> upd (the (gs pn)) x v)"

definition updeg :: "'a gstate \<Rightarrow> pname \<Rightarrow> 'a \<Rightarrow> 'a gstate" where
  "updeg gs pn e = gs (pn \<mapsto> upde (the (gs pn)) e)"

definition updg_assn2 :: "'a gassn2 \<Rightarrow> var \<Rightarrow> 'a eexp \<Rightarrow> pname \<Rightarrow> 'a gassn2"
  ("_ {{_ := _}}\<^sub>g at _" [90,90,90,90] 91) where
  "P {{var := e}}\<^sub>g at pn = (\<lambda>ps s tr. ps pn \<noteq> None \<and> P (updg ps pn var (e (the (ps pn)))) s tr)"

definition updeg_assn2 :: "'a gassn2 \<Rightarrow> ('a estate \<Rightarrow> 'a) \<Rightarrow> pname \<Rightarrow> 'a gassn2"
  ("_ {{_}}\<^sub>g at _" [90,90,90] 91) where
  "P {{f}}\<^sub>g at pn = (\<lambda>ps s tr. ps pn \<noteq> None \<and> P (updeg ps pn (f (the (ps pn)))) s tr)"

lemma subst_State:
  "State pn s(pn \<mapsto> s') = State pn s'"
  by (auto simp add: State_def)

lemma subst_State_elim:
  "s0 pn = Some s0' \<Longrightarrow> s0(pn \<mapsto> s1') = State pn s2' \<Longrightarrow> s0 = State pn s0'"
  apply (auto simp add: State_def fun_upd_def) by metis

lemma updg_proc_set:
  assumes "pn \<in> proc_set gs"
  shows "proc_set (updg gs pn var e) = proc_set gs"
  using assms by (auto simp add: updg_def proc_set_def)

lemma updeg_proc_set:
  assumes "pn \<in> proc_set gs"
  shows "proc_set (updeg gs pn f) = proc_set gs"
  using assms by (auto simp add: updeg_def proc_set_def)

lemma updg_subst2:
  "single_assn pn (P {{ var := e }}) = (single_assn pn P) {{ var := e }}\<^sub>g at pn"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases)
      apply (auto simp add: updg_assn2_def updg_def subst_assn2_def subst_State)
      apply (rule single_assn.intros) by simp
    subgoal
      apply (auto simp add: updg_assn2_def updg_def subst_assn2_def)
      apply (elim single_assn.cases) apply auto
      subgoal premises pre for s0' s0'' s' tr'
      proof -
        have s0: "s0 = State pn s0'"
          apply (rule subst_State_elim) using pre by auto
        show ?thesis
          unfolding s0 apply (rule single_assn.intros)
          using pre by (metis State_eval map_upd_Some_unfold)
      qed
      done
    done
  done

lemma updeg_subst2:
  "single_assn pn (P {{ f }}) = (single_assn pn P) {{ f }}\<^sub>g at pn"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases)
      apply (auto simp add: updeg_assn2_def updeg_def subste_assn2_def subst_State)
      apply (rule single_assn.intros) by simp
    subgoal
      apply (auto simp add: updeg_assn2_def updeg_def subst_assn2_def)
      apply (elim single_assn.cases) apply auto
      subgoal premises pre for s0' s0'' s' tr'
      proof -
        have s0: "s0 = State pn s0'"
          apply (rule subst_State_elim) using pre by auto
        show ?thesis
          unfolding s0 apply (rule single_assn.intros)
          using pre by (metis (full_types) map_upd_eqD1 subst_State subste_assn2_def)
      qed
      done
    done
  done

inductive init_single :: "pname set \<Rightarrow> 'a gassn2" where
  "proc_set gs = pns \<Longrightarrow> init_single pns gs gs []"

lemma proc_set_single_elim:
  assumes "proc_set gs = {pn}"
    and "(\<And>s. gs = State pn s \<Longrightarrow> P)"
  shows "P"
proof -
  have 1: "x \<in> proc_set gs \<longleftrightarrow> x = pn" for x
    using eqset_imp_iff[OF assms(1)] by auto
  show ?thesis
    apply (rule assms(2)[of "the (gs pn)"])
    apply (rule ext) subgoal for pn'
      apply (auto simp add: State_def)
      using 1 apply (auto simp add: proc_set_def)
      by fastforce
    done
qed

lemma single_assn_init:
  "single_assn pn init = init_single {pn}"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases)
      apply (auto simp add: init_def)
      apply (rule init_single.intros) by auto
    subgoal
      apply (elim init_single.cases) apply clarify
      apply (elim proc_set_single_elim) apply auto
      apply (subst ptrace_of.simps(1)[of pn, symmetric])
      apply (rule single_assn.intros)
      by (auto simp add: init_def)
    done
  done

definition cond_gassn2 :: "pname \<Rightarrow> ('a estate \<Rightarrow> bool) \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2"
  ("IFG [_] _ THEN _ ELSE _ FI" [95,95,94] 93) where
  "IFG [pn] b THEN Q1 ELSE Q2 FI = (\<lambda>s0 s tr. if b (the (s0 pn)) then Q1 s0 s tr else Q2 s0 s tr)"

lemma single_assn_cond:
  "single_assn pn (IFA b THEN a1 ELSE a2 FI) =
    (IFG [pn] b THEN single_assn pn a1 ELSE single_assn pn a2 FI)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal
      apply (auto simp add: cond_assn2_def cond_gassn2_def)
      by (auto elim!: single_assn.cases intro: single_assn.intros)
    subgoal
      apply (auto simp add: cond_assn2_def cond_gassn2_def)
      apply (cases "b (the (s0 pn))")
      by (auto elim!: single_assn.cases intro: single_assn.intros)
    done
  done

subsection \<open>Basic elimination rules\<close>

named_theorems sync_elims

lemma combine_blocks_pairE [sync_elims]:
  "combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) (CommBlockP ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. ch1 = ch2 \<Longrightarrow> v1 = v2 \<Longrightarrow> (ch_type1 = In \<and> ch_type2 = Out \<or> ch_type1 = Out \<and> ch_type2 = In) \<Longrightarrow>
   tr = tr' \<Longrightarrow> combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1 [sync_elims]:
  "combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) (CommBlockP ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlockP ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlockP ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1' [sync_elims]:
  "combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) (CommBlockP ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlockP ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE2 [sync_elims]:
  "combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) (CommBlockP ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlockP ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlockP ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow>
   (\<And>tr'. tr = CommBlockP ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2 [sync_elims]:
  "combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) (WaitBlockP d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2' [sync_elims]:
  "combine_blocks comms (WaitBlockP d1 p1 rdy1 # tr1) (CommBlockP ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3 [sync_elims]:
  "combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) (WaitBlockP d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlockP ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlockP d2 p2 rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3' [sync_elims]:
  "combine_blocks comms (WaitBlockP d1 p1 rdy1 # tr1) (CommBlockP ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlockP ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlockP d1 p1 rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_waitE1 [sync_elims]:
  "combine_blocks comms (WaitBlockP d1 p1 rdy1 # tr1) (WaitBlockP d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   \<not>compat_rdy rdy1 rdy2 \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

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
  "combine_blocks comms (WaitBlockP d1 p1 rdy1 # tr1) [] tr \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2' [sync_elims]:
  "combine_blocks comms [] (WaitBlockP d2 p2 rdy2 # tr2) tr \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE3 [sync_elims]:
  "combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) [] tr \<Longrightarrow>
   (\<And>tr'. ch1 \<notin> comms \<Longrightarrow> tr = CommBlockP ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 [] tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE3' [sync_elims]:
  "combine_blocks comms [] (CommBlockP ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   (\<And>tr'. ch2 \<notin> comms \<Longrightarrow> tr = CommBlockP ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms [] tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)


subsection \<open>Synchronization of two assertions\<close>

lemma merge_state_eval1:
  assumes "pn \<in> proc_set s11"
  shows "merge_state s11 s12 pn = s11 pn"
  using assms by (auto simp add: merge_state_def proc_set_def)

lemma merge_state_eval2:
  assumes "pn \<in> proc_set s12"
    and "proc_set s11 \<inter> proc_set s12 = {}"
  shows "merge_state s11 s12 pn = s12 pn"
  using assms apply (auto simp add: merge_state_def proc_set_def)
  apply (cases "s11 pn") by auto

lemma single_subst_merge_state1:
  assumes "pn \<in> proc_set s11"
  shows "updg (merge_state s11 s12) pn var e = merge_state (updg s11 pn var e) s12"
  apply (auto simp add: updg_def merge_state_def)
  apply (rule ext) apply auto
  apply (cases "s11 pn") apply auto
  using assms unfolding proc_set_def by auto

lemma single_subst_merge_state2:
  assumes "pn \<in> proc_set s12"
    and "proc_set s11 \<inter> proc_set s12 = {}"
  shows "updg (merge_state s11 s12) pn var e = merge_state s11 (updg s12 pn var e)"
  apply (auto simp add: updg_def merge_state_def)
  apply (rule ext) apply auto
  subgoal apply (cases "s11 pn") 
    using assms by (auto simp add: proc_set_def)
  subgoal for pn'
    apply (cases "s11 pn'") by auto
  done

lemma single_subste_merge_state1:
  assumes "pn \<in> proc_set s11"
  shows "updeg (merge_state s11 s12) pn f = merge_state (updeg s11 pn f) s12"
  apply (auto simp add: updeg_def merge_state_def)
  apply (rule ext) apply auto
  apply (cases "s11 pn") apply auto
  using assms unfolding proc_set_def by auto

lemma single_subste_merge_state2:
  assumes "pn \<in> proc_set s12"
    and "proc_set s11 \<inter> proc_set s12 = {}"
  shows "updeg (merge_state s11 s12) pn f = merge_state s11 (updeg s12 pn f)"
  apply (auto simp add: updeg_def merge_state_def)
  apply (rule ext) apply auto
  subgoal apply (cases "s11 pn") 
    using assms by (auto simp add: proc_set_def)
  subgoal for pn'
    apply (cases "s11 pn'") by auto
  done

lemma sync_gassn_in_out:
  "ch \<in> chs \<Longrightarrow>
   pn \<in> pns2 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_in_cg ch P) (wait_out_cg ch pn e Q) s0 \<Longrightarrow>\<^sub>g
   sync_gassn chs pns1 pns2 (P 0 (e (the (s0 pn)))) (Q 0) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr2'
          apply (elim combine_blocks_pairE)
            apply auto
          apply (rule sync_gassn.intros) apply auto
          apply (subst merge_state_eval2) by auto
        subgoal for d tr2'
          apply (elim sync_elims) by auto
        done
      subgoal for d v tr1'
        apply (elim wait_out_cg.cases) apply auto
        by (auto elim!: sync_elims)
      done
    done
  done

lemma sync_gassn_out_in:
  "ch \<in> chs \<Longrightarrow>
   pn \<in> pns1 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_out_cg ch pn e Q) (wait_in_cg ch P) s0 \<Longrightarrow>\<^sub>g
   sync_gassn chs pns1 pns2 (Q 0) (P 0 (e (the (s0 pn)))) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr2'
          apply (elim combine_blocks_pairE)
            apply auto
          apply (rule sync_gassn.intros) apply auto
          apply (subst merge_state_eval1) by auto
        subgoal for d tr2'
          apply (elim sync_elims) by auto
        done
      subgoal for d v tr1'
        apply (elim wait_out_cg.cases) apply auto
        by (auto elim!: sync_elims)
      done
    done
  done

lemma sync_gassn_out_emp:
  "ch \<notin> chs \<Longrightarrow>
   pn \<in> pns1 \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_out_cg ch pn e Q) (init_single pns2) s0 \<Longrightarrow>\<^sub>g
   wait_out_cg ch pn e (\<lambda>d. sync_gassn chs pns1 pns2 (Q d) (init_single pns2)) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_out_cg.cases) apply auto
      subgoal for tr1'
        apply (elim init_single.cases) apply auto
        apply (elim sync_elims) apply auto
        subgoal for tr'
          apply (rule wait_out_cg.intros)
           apply (rule sync_gassn.intros) apply auto
           apply (rule init_single.intros) apply auto
          apply (subst merge_state_eval1) by auto
        done
      subgoal for d tr'
        apply (elim init_single.cases) apply auto
        by (elim sync_elims)
      done
    done
  done

lemma sync_gassn_out_emp_unpair:
  "ch \<in> chs \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_out_cg ch pn e Q) (init_single pns2) s0 \<Longrightarrow>\<^sub>g P"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_out_cg.cases) apply auto
      subgoal for tr1'
        apply (elim init_single.cases) apply auto
        apply (elim sync_elims) by auto
      subgoal for d tr1'
        apply (elim init_single.cases) apply auto
        by (elim sync_elims)
      done
    done
  done

lemma sync_gassn_emp_in_unpair:
  "ch \<in> chs \<Longrightarrow>
   sync_gassn chs pns1 pns2 (init_single pns1) (wait_in_cg ch Q) s0 \<Longrightarrow>\<^sub>g P"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for tr1'
        apply (elim init_single.cases) apply auto
        apply (elim sync_elims) by auto
      subgoal for d tr1'
        apply (elim init_single.cases) apply auto
        by (elim sync_elims)
      done
    done
  done

lemma sync_gassn_subst_left:
  assumes "pn \<in> pns1"
  shows "sync_gassn chs pns1 pns2 (P {{ var := e }}\<^sub>g at pn) Q s0 \<Longrightarrow>\<^sub>g
         (sync_gassn chs pns1 pns2 P Q {{ var := e }}\<^sub>g at pn) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (auto simp add: updg_assn2_def)
      subgoal using assms by (auto simp add: merge_state_eval1)
      subgoal for s11'
        apply (subst single_subst_merge_state1)
        using assms apply simp
        apply (rule sync_gassn.intros)
        using assms by (auto simp add: merge_state_eval1 updg_proc_set)
      done
    done
  done

lemma sync_gassn_subst_right:
  assumes "pn \<in> pns2"
    and "pns1 \<inter> pns2 = {}"
  shows "sync_gassn chs pns1 pns2 Q (P {{ var := e }}\<^sub>g at pn) s0 \<Longrightarrow>\<^sub>g
         (sync_gassn chs pns1 pns2 Q P {{ var := e }}\<^sub>g at pn) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (auto simp add: updg_assn2_def)
      subgoal using assms by (auto simp add: merge_state_eval2)
      subgoal for s11'
        apply (subst single_subst_merge_state2)
        using assms apply auto
        apply (rule sync_gassn.intros)
        using assms by (auto simp add: merge_state_eval2 updg_proc_set)
      done
    done
  done

lemma sync_gassn_subste_left:
  assumes "pn \<in> pns1"
  shows "sync_gassn chs pns1 pns2 (P {{ f }}\<^sub>g at pn) Q s0 \<Longrightarrow>\<^sub>g
         (sync_gassn chs pns1 pns2 P Q {{ f }}\<^sub>g at pn) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (auto simp add: updeg_assn2_def)
      subgoal using assms by (auto simp add: merge_state_eval1)
      subgoal for s11'
        apply (subst single_subste_merge_state1)
        using assms apply simp
        apply (rule sync_gassn.intros)
        using assms by (auto simp add: merge_state_eval1 updeg_proc_set)
      done
    done
  done

lemma sync_gassn_subste_right:
  assumes "pn \<in> pns2"
    and "pns1 \<inter> pns2 = {}"
  shows "sync_gassn chs pns1 pns2 Q (P {{ f }}\<^sub>g at pn) s0 \<Longrightarrow>\<^sub>g
         (sync_gassn chs pns1 pns2 Q P {{ f }}\<^sub>g at pn) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (auto simp add: updeg_assn2_def)
      subgoal using assms by (auto simp add: merge_state_eval2)
      subgoal for s11'
        apply (subst single_subste_merge_state2)
        using assms apply auto
        apply (rule sync_gassn.intros)
        using assms by (auto simp add: merge_state_eval2 updeg_proc_set)
      done
    done
  done

lemma sync_gassn_emp:
  assumes "pns = pns1 \<union> pns2"
  shows "sync_gassn chs pns1 pns2 (init_single pns1) (init_single pns2) s0 \<Longrightarrow>\<^sub>g
         init_single pns s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim init_single.cases) apply auto
      apply (frule combine_blocks_emptyE1) apply auto
      apply (rule init_single.intros)
      by (auto simp add: assms)
    done
  done

lemma gassn_subst:
  "(P {{ var := e }}\<^sub>g at pn) s0 \<Longrightarrow>\<^sub>g P (updg s0 pn var (e (the (s0 pn))))"
  unfolding entails_g_def
  by (auto simp add: updg_assn2_def)

lemma gassn_subste:
  "(P {{ f }}\<^sub>g at pn) s0 \<Longrightarrow>\<^sub>g P (updeg s0 pn (f (the (s0 pn))))"
  unfolding entails_g_def
  by (auto simp add: updeg_assn2_def)

lemma wait_out_cg_entails:
  assumes "\<And>d s0. P d s0 \<Longrightarrow>\<^sub>g Q d s0"
  shows "wait_out_cg ch pn e P s0 \<Longrightarrow>\<^sub>g wait_out_cg ch pn e Q s0"
  apply (auto simp add: entails_g_def)
  subgoal for s tr
    apply (elim wait_out_cg.cases) apply auto
    subgoal apply (rule wait_out_cg.intros)
      using assms unfolding entails_g_def by auto
    subgoal apply (rule wait_out_cg.intros)
      using assms unfolding entails_g_def by auto
    done
  done

subsection \<open>More definitions and lemmas\<close>

definition valg :: "'a gstate \<Rightarrow> pname \<Rightarrow> var \<Rightarrow> real" where
  "valg gs pn v = val (the (gs pn)) v"

lemma val_upd_simp [simp]:
  "val (upd s var v) var = v"
  apply (cases s)
  by (auto simp add: upd.simps val.simps)

lemma val_upd_simp2 [simp]:
  "var \<noteq> var2 \<Longrightarrow> val (upd s var v) var2 = val s var2"
  apply (cases s)
  by (auto simp add: upd.simps val.simps)

lemma val_upde_simp [simp]:
  "val (upde s e) var = val s var"
  apply (cases s)
  by (auto simp add: val.simps)

lemma valg_updg_simp [simp]:
  "valg (updg s pn var v) pn var = v"
  unfolding valg_def updg_def by auto

lemma valg_updg_simp2 [simp]:
  "pn \<noteq> pn2 \<Longrightarrow> valg (updg s pn var v) pn2 var2 = valg s pn2 var2"
  unfolding valg_def updg_def by auto

lemma valg_updg_simp3 [simp]:
  "var \<noteq> var2 \<Longrightarrow> valg (updg s pn var v) pn var2 = valg s pn var2"
  unfolding valg_def updg_def by auto

lemma valg_updeg_simp [simp]:
  "valg (updeg s pn e) pn2 var = valg s pn2 var"
  unfolding valg_def updeg_def by auto

lemma sync_gassn_triv:
  assumes "s1 = s2"
  shows "sync_gassn chs pns1 pns2 P Q s1 \<Longrightarrow>\<^sub>g 
         sync_gassn chs pns1 pns2 P Q s2"
  apply (simp add: assms)
  by (rule entails_g_triv)

definition exists_gassn :: "('b \<Rightarrow> 'a gassn) \<Rightarrow> 'a gassn" (binder "\<exists>\<^sub>g" 10)where
  "(\<exists>\<^sub>g n. P n) = (\<lambda>s tr. \<exists>n. P n s tr)"

lemma exists_gassn_intro:
  assumes "\<exists>n. P \<Longrightarrow>\<^sub>g Q n"
  shows "P \<Longrightarrow>\<^sub>g (\<exists>\<^sub>g n. Q n)"
  using assms unfolding exists_gassn_def entails_g_def
  by auto

lemma single_assn_exists:
  "single_assn pn (\<lambda>s0. \<exists>\<^sub>an. P n s0) = (\<lambda>s0. (\<exists>\<^sub>g n. single_assn pn (P n) s0))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s tr s0
    apply (rule iffI)
    apply (auto simp add: exists_gassn_def exists_assn_def)
      by (auto elim: single_assn.cases intro: single_assn.intros)
    done

lemma sync_gassn_exists_left:
  "sync_gassn chs pns1 pns2 (\<lambda>s0. \<exists>\<^sub>gn. P n s0) Q = (\<lambda>s0. \<exists>\<^sub>g n. sync_gassn chs pns1 pns2 (P n) Q s0)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s tr s0
    apply (rule iffI)
     apply (auto simp add: exists_gassn_def)
    by (auto elim: sync_gassn.cases intro: sync_gassn.intros)
  done

lemma sync_gassn_exists_right:
  "sync_gassn chs pns1 pns2 P (\<lambda>s0. \<exists>\<^sub>gn. Q n s0) = (\<lambda>s0. \<exists>\<^sub>g n. sync_gassn chs pns1 pns2 P (Q n) s0)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s tr s0
    apply (rule iffI)
     apply (auto simp add: exists_gassn_def)
    by (auto elim: sync_gassn.cases intro: sync_gassn.intros)
  done

text \<open>General specification\<close>
definition spec_of_global_gen :: "('a gstate \<Rightarrow> bool) \<Rightarrow> 'a pproc \<Rightarrow> ('a gstate \<Rightarrow> 'a gassn) \<Rightarrow> bool" where
  "spec_of_global_gen P c Q \<longleftrightarrow> (\<forall>s0. P s0 \<longrightarrow> \<Turnstile>\<^sub>p {init_global s0} c {Q s0})"


end
