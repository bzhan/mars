theory BigStepSequential
  imports "../Analysis_More"
begin


subsection \<open>Extended state\<close>

text \<open>The state of each process consists of the real part, which
  is a mapping from variable names to real numbers, and an extra
  part, which can be of arbitrary type 'a.
\<close>
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

text \<open>Obtain the value of some variable in the real part of the state\<close>
fun val :: "'a estate \<Rightarrow> var \<Rightarrow> real" where
  "val (EState r e) v = r v"

text \<open>Taking the real part of the state\<close>
fun rpart :: "'a estate \<Rightarrow> state" where
  "rpart (EState r e) = r"

text \<open>Taking the extra part of the state\<close>
fun epart :: "'a estate \<Rightarrow> 'a" where
  "epart (EState r e) = e"

text \<open>The following rules allow to simplify expressions
  involving evaluation and updating the extended state.
\<close>
lemma val_upd_simp [simp]:
  "val (upd s var v) var = v"
  apply (cases s) by auto

lemma val_upd_simp2 [simp]:
  "var \<noteq> var2 \<Longrightarrow> val (upd s var v) var2 = val s var2"
  apply (cases s) by auto

lemma val_upde_simp [simp]:
  "val (upde s e) var = val s var"
  apply (cases s) by auto

lemma epart_upd_simp [simp]:
  "epart (upd s var v) = epart s"
  apply (cases s) by auto

lemma epart_upde_simp [simp]:
  "epart (upde s e) = e"
  apply (cases s) by auto

lemma updr_rpart_simp [simp]:
  "updr s (rpart s) = s"
  apply (cases s) by auto

lemma upd_val_simp [simp]:
  "upd s X (val s X) = s"
  apply (cases s) by auto

text \<open>The following lemmas need to be invoked by hand\<close>
lemma updr_rpart_simp1:
  "updr s ((rpart s)(X := v)) = upd s X v"
  apply (cases s) by auto

lemma updr_rpart_simp2:
  "updr s ((rpart s)(X := v, Y := w)) = upd (upd s X v) Y w"
  apply (cases s) by auto

declare upd.simps [simp del]
declare updr.simps [simp del]
declare rpart.simps [simp del]
declare epart.simps [simp del]
declare val.simps [simp del]

subsection \<open>Syntax of HCSP\<close>

text \<open>Channel names\<close>
type_synonym cname = string

text \<open>Process names\<close>
type_synonym pname = string

text \<open>Readiness information.
  First component is set of channels that are ready to output.
  Second component is set of channels that are ready to input.
\<close>
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
| Interrupt ODE "'a eform" "('a comm \<times> 'a proc) list" "'a proc" \<comment> \<open>Interrupt\<close>

text \<open>Parallel of several HCSP processes\<close>
datatype 'a pproc =
  Single pname "'a proc"
| Parallel "'a pproc" "cname set" "'a pproc"

text \<open>Set of process names of a parallel process\<close>
fun proc_of_pproc :: "'a pproc \<Rightarrow> pname set" where
  "proc_of_pproc (Single pn c) = {pn}"
| "proc_of_pproc (Parallel p1 chs p2) = proc_of_pproc p1 \<union> proc_of_pproc p2"

text \<open>Global state.

  The global state of a parallel process is represented as a
  partial mapping from process name to extended state.
\<close>
type_synonym 'a gstate = "pname \<Rightarrow> 'a estate option"

text \<open>Global state for a single process\<close>
definition State :: "pname \<Rightarrow> 'a estate \<Rightarrow> 'a gstate" where
  "State p s = (\<lambda>p'. if p' = p then Some s else None)"

lemma State_eval [simp]:
  "State p s p = Some s"
  by (auto simp add: State_def)

subsection \<open>Traces of sequential programs\<close>

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

definition WaitBlk :: "real \<Rightarrow> (real \<Rightarrow> 'a estate) \<Rightarrow> rdy_info \<Rightarrow> 'a trace_block" where
  "WaitBlk d p rdy = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"

lemma WaitBlk_eqE:
  "WaitBlk d p rdy = WaitBlk d2 p2 rdy2 \<Longrightarrow>
   (d = d2 \<Longrightarrow> rdy = rdy2 \<Longrightarrow> (\<And>t. t \<in> {0..d} \<Longrightarrow> p t = p2 t) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding WaitBlk_def restrict_def apply auto by meson

lemma WaitBlk_eqI:
  "d = d2 \<Longrightarrow> rdy = rdy2 \<Longrightarrow> (\<And>t. t \<in> {0..d} \<Longrightarrow> p t = p2 t) \<Longrightarrow> WaitBlk d p rdy = WaitBlk d2 p2 rdy2"
  unfolding WaitBlk_def by auto

text \<open>Trace is defined as an ordered list of trace blocks.\<close>
type_synonym 'a trace = "'a trace_block list"

text \<open>Compute list of ready communications for an external choice\<close>
fun rdy_info_of_list :: "('a \<Rightarrow> rdy_info) \<Rightarrow> 'a list \<Rightarrow> rdy_info" where
  "rdy_info_of_list f [] = ({}, {})"
| "rdy_info_of_list f (x # xs) = (
    let rdy = rdy_info_of_list f xs in
      (fst (f x) \<union> fst rdy, snd (f x) \<union> snd rdy))"

inductive rel_list :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool" for r where
  "rel_list r [] []"
| "r a b \<Longrightarrow> rel_list r as bs \<Longrightarrow> rel_list r (a # as) (b # bs)"

lemma rel_listD1:
  "rel_list r xs ys \<Longrightarrow> length xs = length ys"
  apply (induct rule: rel_list.induct) by auto

lemma rel_listD2:
  "rel_list r xs ys \<Longrightarrow> i < length xs \<Longrightarrow> r (xs ! i) (ys ! i)"
  apply (induct arbitrary: i rule: rel_list.induct) apply auto
  unfolding less_Suc_eq_0_disj by auto

lemma rel_list_mono:
  assumes "\<And>x y. r x y \<Longrightarrow> r2 x y"
  shows "rel_list r xs ys \<Longrightarrow> rel_list r2 xs ys"
  apply (induct rule: rel_list.induct)
  using assms by (auto intro!: rel_list.intros)

lemma rel_list_map:
  assumes "\<And>x. r x (f x)"
  shows "rel_list r xs (map f xs)"
  apply (induct xs)
  using assms by (auto intro: rel_list.intros)

lemma rdy_info_of_list_cong:
  "rel_list (\<lambda>x y. f x = g y) xs ys \<Longrightarrow> rdy_info_of_list f xs = rdy_info_of_list g ys"
  apply (induct xs ys rule: rel_list.induct)
  by (auto simp add: Let_def)

definition rdy_of_echoice :: "('a comm \<times> 'a proc) list \<Rightarrow> rdy_info" where
  "rdy_of_echoice = rdy_info_of_list (\<lambda>es.
    case es of (ch[!]e, _) \<Rightarrow> ({ch}, {})
             | (ch[?]var, _) \<Rightarrow> ({}, {ch}))"

subsection \<open>Big-step semantics\<close>

text \<open>big_step p s1 tr s2 means executing p starting from
  state s1 results in a trace tr and final state s2.
\<close>
inductive big_step :: "'a proc \<Rightarrow> 'a estate \<Rightarrow> 'a trace \<Rightarrow> 'a estate \<Rightarrow> bool" where
  skipB: "big_step Skip s [] s"
| assignB: "big_step (var ::= e) s [] (upd s var (e s))"
| basicB: "big_step (Basic f) s [] (upde s (f s))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (p1; p2) s1 (tr1 @ tr2) s3"
| condB1: "b s1 \<Longrightarrow> big_step p1 s1 tr s2 \<Longrightarrow> big_step (IF b THEN p1 ELSE p2 FI) s1 tr s2"
| condB2: "\<not> b s1 \<Longrightarrow> big_step p2 s1 tr s2 \<Longrightarrow> big_step (IF b THEN p1 ELSE p2 FI) s1 tr s2"
| waitB1: "e s > 0 \<Longrightarrow> big_step (Wait e) s [WaitBlk (e s) (\<lambda>_. s) ({}, {})] s"
| waitB2: "\<not> e s > 0 \<Longrightarrow> big_step (Wait e) s [] s"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlk d (\<lambda>_. s) ({ch}, {}), OutBlock ch (e s)] s"
| receiveB1: "big_step (Cm (ch[?]var)) s [InBlock ch v] (upd s var v)"
| receiveB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlk d (\<lambda>_. s) ({}, {ch}), InBlock ch v] (upd s var v)"
| IChoiceB1: "big_step p1 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| IChoiceB2: "big_step p2 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| EChoiceSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (OutBlock ch (e s1) # tr2) s2"
| EChoiceSendB2: "(d::real) > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlk d (\<lambda>_. s1) (rdy_of_echoice cs) #
                              OutBlock ch (e s1) # tr2) s2"
| EChoiceReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (upd s1 var v) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (InBlock ch v # tr2) s2"
| EChoiceReceiveB2: "(d::real) > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (upd s1 var v) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlk d (\<lambda>_. s1) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (updr s1 (p t))) \<Longrightarrow>
    \<not>b (updr s1 (p d)) \<Longrightarrow> p 0 = rpart s1 \<Longrightarrow>
    big_step (Cont ode b) s1 [WaitBlk d (\<lambda>\<tau>. updr s1 (p \<tau>)) ({}, {})] (updr s1 (p d))"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs pr) s (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = rpart s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (updr s1 (p t))) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (updr s1 (p d)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs pr) s1 (WaitBlk d (\<lambda>\<tau>. updr s1 (p \<tau>)) rdy #
                                         OutBlock ch (e (updr s1 (p d))) # tr2) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (upd s var v) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs pr) s (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = rpart s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (updr s1 (p t))) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (updr s1 ((p d)(var := v))) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs pr) s1 (WaitBlk d (\<lambda>\<tau>. updr s1 (p \<tau>)) rdy #
                                         InBlock ch v # tr2) s2"
| InterruptB1: "\<not>b s \<Longrightarrow> big_step pr s tr s2 \<Longrightarrow> big_step (Interrupt ode b cs pr) s tr s2"
| InterruptB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (updr s1 (p t))) \<Longrightarrow>
    \<not>b (updr s1 (p d)) \<Longrightarrow> p 0 = rpart s1 \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step pr (updr s1 (p d)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs pr) s1 (WaitBlk d (\<lambda>\<tau>. updr s1 (p \<tau>)) rdy # tr2) s2"

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
inductive_cases interruptE: "big_step (Interrupt ode b cs pr) s1 tr s2"

subsection \<open>Assertions on sequential processes\<close>

text \<open>Path invariant is a predicate on time and state\<close>
type_synonym 'a pinv = "real \<Rightarrow> 'a estate \<Rightarrow> bool"

text \<open>We also define path invariant parameterized by starting state\<close>
type_synonym 'a pinv2 = "'a estate \<Rightarrow> 'a pinv"

text \<open>Simplest parameterized path invariant: state always equal
  starting state
\<close>
fun single_id_inv :: "'a pinv2" where
  "single_id_inv s0 t s = (s = s0)"

text \<open>Assertion is a predicate on states and traces\<close>
type_synonym 'a assn = "'a estate \<Rightarrow> 'a trace \<Rightarrow> bool"

text \<open>We also define assertions parameterized by starting state\<close>
type_synonym 'a assn2 = "'a estate \<Rightarrow> 'a assn"

text \<open>True and false assertions\<close>
inductive true_assn2 :: "'a assn2" where
  "true_assn2 s0 s tr"

definition false_assn2 :: "'a assn2" where
  "false_assn2 = (\<lambda>s0 s tr. False)"

text \<open>Quantifiers on assertions.\<close>
definition forall_assn :: "('b \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" (binder "\<forall>\<^sub>a" 10)where
  "(\<forall>\<^sub>an. P n) = (\<lambda>s0 s tr. \<forall>n. P n s0 s tr)"

definition exists_assn :: "('b \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" (binder "\<exists>\<^sub>a" 10)where
  "(\<exists>\<^sub>an. P n) = (\<lambda>s0 s tr. \<exists>n. P n s0 s tr)"

text \<open>Substitution on assertions: real part.
  Starting from a parameterized assertion P, let P act on the
  state after making an assignment.
\<close>
definition subst_assn2 :: "'a assn2 \<Rightarrow> var \<Rightarrow> ('a estate \<Rightarrow> real) \<Rightarrow> 'a assn2"
  ("_ {{_ := _}}" [90,90,90] 91) where 
  "P {{var := e}} = (\<lambda>s0. P (upd s0 var (e s0)))"

definition substr_assn2 :: "'a assn2 \<Rightarrow> ('a estate \<Rightarrow> state) \<Rightarrow> 'a assn2"
  ("_ {{_}}\<^sub>r" [90,90] 91) where
  "P {{f}}\<^sub>r = (\<lambda>s0. P (updr s0 (f s0)))"

text \<open>Substitution on assertions: extra part.
  Starting from a parameterized assertion P, let P act on the
  state after updating the extra part using function f.  
\<close>
definition subste_assn2 :: "'a assn2 \<Rightarrow> ('a estate \<Rightarrow> 'a) \<Rightarrow> 'a assn2"
  ("_ {{_}}\<^sub>e" [90,90] 91) where 
  "P {{f}}\<^sub>e = (\<lambda>s0. P (upde s0 (f s0)))"

definition pure_assn :: "('a estate \<Rightarrow> bool) \<Rightarrow> 'a assn2" ("!\<^sub>a[_]" [71] 70) where
  "(!\<^sub>a[b]) = (\<lambda>s0 s tr. b s0)"

definition conj_assn :: "'a assn2 \<Rightarrow> 'a assn2 \<Rightarrow> 'a assn2" (infixr "\<and>\<^sub>a" 35) where
  "(P \<and>\<^sub>a Q) = (\<lambda>s0 s tr. P s0 s tr \<and> Q s0 s tr)"

definition disj_assn :: "'a assn2 \<Rightarrow> 'a assn2 \<Rightarrow> 'a assn2" (infixr "\<or>\<^sub>a" 35) where
  "(P \<or>\<^sub>a Q) = (\<lambda>s0 s tr. P s0 s tr \<or> Q s0 s tr)"

text \<open>Entailment relation between assertions\<close>
definition entails :: "'a assn \<Rightarrow> 'a assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

theorem entails_triv:
  "P \<Longrightarrow>\<^sub>A P"
  unfolding entails_def by auto

lemma entails_trans:
  "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>A R \<Longrightarrow> P \<Longrightarrow>\<^sub>A R"
  unfolding entails_def by auto

text \<open>Parameterized assertion specifying the initial condition
  with starting state s0 and empty trace.
\<close>
definition init :: "'a assn2" where
  "init s0 = (\<lambda>s tr. s = s0 \<and> tr = [])"

text \<open>Conditional assertion\<close>
definition cond_assn2 :: "'a eform \<Rightarrow> 'a assn2 \<Rightarrow> 'a assn2 \<Rightarrow> 'a assn2"
  ("IFA _ THEN _ ELSE _ FI" [95,94] 93) where
  "IFA b THEN Q1 ELSE Q2 FI = (\<lambda>s0 s tr. if b s0 then Q1 s0 s tr else Q2 s0 s tr)"

text \<open>Assertion for input.

  There are two cases, either the input happens immediately,
  or after waiting for some time. The ensuing assertion is
  parameterized by waiting time and communicated value.
\<close>
inductive wait_in_c :: "'a pinv2 \<Rightarrow> cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "P 0 v s0 s tr \<Longrightarrow> wait_in_c I ch P s0 s (InBlock ch v # tr)"
| "0 < d \<Longrightarrow> P d v s0 s tr \<Longrightarrow> \<forall>t\<in>{0..d}. I s0 t (p t) \<Longrightarrow>
   wait_in_c I ch P s0 s (WaitBlk d (\<lambda>\<tau>. p \<tau>) ({}, {ch}) # InBlock ch v # tr)"

text \<open>Assertion for output.

  There are two cases, either the output happens immediately,
  or after waiting for some time. The ensuing assertion is
  parameterized by waiting time and communicated value.
\<close>
inductive wait_out_c :: "'a pinv2 \<Rightarrow> cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "P 0 v s0 s tr \<Longrightarrow> wait_out_c I ch P s0 s (OutBlock ch v # tr)"
| "0 < d \<Longrightarrow> P d v s0 s tr \<Longrightarrow> \<forall>t\<in>{0..d}. I s0 t (p t) \<Longrightarrow>
   wait_out_c I ch P s0 s (WaitBlk d (\<lambda>\<tau>. p \<tau>) ({ch}, {}) # OutBlock ch v # tr)"

text \<open>A short form of wait_out_c, where the communicated value
  is specified by the function e.\<close> 
definition wait_out_cv :: "'a pinv2 \<Rightarrow> cname \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "wait_out_cv I ch e P = wait_out_c I ch (\<lambda>d v. !\<^sub>a[(\<lambda>s0. v = e s0)] \<and>\<^sub>a P d)"

text \<open>Waiting an amount of time, without state change\<close>
inductive wait_c :: "'a pinv2 \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "e s0 > 0 \<Longrightarrow> P (e s0) s0 s tr \<Longrightarrow> \<forall>t\<in>{0..e s0}. I s0 t (p t) \<Longrightarrow>
   wait_c I e P s0 s (WaitBlk (e s0) (\<lambda>\<tau>. p \<tau>) ({}, {}) # tr)"
| "\<not>e s0 > 0 \<Longrightarrow> P 0 s0 s tr \<Longrightarrow> wait_c I e P s0 s tr"

subsubsection \<open>Various rules about entailment\<close>

lemma entails_exists:
  assumes "\<exists>n. P s0 \<Longrightarrow>\<^sub>A Q n s0"
  shows "P s0 \<Longrightarrow>\<^sub>A (\<exists>\<^sub>an. Q n) s0"
  using assms unfolding exists_assn_def entails_def by auto

lemma entails_assumption:
  "P s \<Longrightarrow>\<^sub>A (IFA b THEN P ELSE true_assn2 FI) s"
  unfolding cond_assn2_def entails_def
  using true_assn2.intros by auto

subsubsection \<open>Commutativity rules\<close>

text \<open>The following rules state commutativity between
  assertions and quantifiers.
\<close>
lemma wait_in_c_exists:
  "wait_in_c I ch (\<lambda>d v. \<exists>\<^sub>an. P d v n) = (\<exists>\<^sub>an. wait_in_c I ch (\<lambda>d v. P d v n))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal unfolding exists_assn_def
      apply (induct rule: wait_in_c.cases) apply auto
      subgoal for v tr' n
        apply (rule exI[where x=n])
        apply (rule wait_in_c.intros(1)) by auto
      subgoal for d v tr' s' n
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
  "wait_out_c I ch (\<lambda>d v. \<exists>\<^sub>an. P d v n) = (\<exists>\<^sub>an. wait_out_c I ch (\<lambda>d v. P d v n))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal unfolding exists_assn_def
      apply (induct rule: wait_out_c.cases) apply auto
      subgoal for v tr' n
        apply (rule exI[where x=n])
        apply (rule wait_out_c.intros(1)) by auto
      subgoal for d v tr' s' n
        apply (rule exI[where x=n])
        apply (rule wait_out_c.intros(2)) by auto
      done
    subgoal unfolding exists_assn_def
      apply auto subgoal for n
        apply (induction rule: wait_out_c.cases) apply auto
        subgoal for v tr'
          apply (rule wait_out_c.intros(1))
          apply (rule exI[where x=n]) by auto
        subgoal for d v tr'
          apply (rule wait_out_c.intros(2))
           apply simp apply (rule exI[where x=n]) by auto
        done
      done
    done
  done

lemma conj_assn_exists:
  "(P \<and>\<^sub>a (\<exists>\<^sub>an. Q n)) = (\<exists>\<^sub>an. P \<and>\<^sub>a Q n)"
  unfolding conj_assn_def exists_assn_def by auto

lemma wait_out_cv_exists:
  "wait_out_cv I ch e (\<lambda>d. \<exists>\<^sub>an. P d n) = (\<exists>\<^sub>an. wait_out_cv I ch e (\<lambda>d. P d n))"
  unfolding wait_out_cv_def conj_assn_exists wait_out_c_exists by auto

subsubsection \<open>Monotonicity rules\<close>

text \<open>The following rules state monotonicity of assertions\<close>
lemma wait_in_c_mono:
  assumes "\<And>d v s. P1 d v s \<Longrightarrow>\<^sub>A P2 d v s"
  shows "wait_in_c I ch P1 s0 \<Longrightarrow>\<^sub>A wait_in_c I ch P2 s0"
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
  assumes "\<And>d v s. P1 d v s \<Longrightarrow>\<^sub>A P2 d v s"
  shows "wait_out_c I ch P1 s0 \<Longrightarrow>\<^sub>A wait_out_c I ch P2 s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (induct rule: wait_out_c.cases) apply auto
    subgoal for v tr'
      apply (rule wait_out_c.intros(1))
      using assms unfolding entails_def by auto
    subgoal for d v tr'
      apply (rule wait_out_c.intros(2))
      using assms unfolding entails_def by auto
    done
  done

lemma wait_c_mono:
  assumes "\<And>d. P1 d s0 \<Longrightarrow>\<^sub>A P2 d s0"
  shows "wait_c I e P1 s0 \<Longrightarrow>\<^sub>A wait_c I e P2 s0"
  unfolding entails_def apply auto
  subgoal for s tr
    apply (induct rule: wait_c.cases) apply auto
    subgoal for tr' p
      apply (rule wait_c.intros(1))
      using assms unfolding entails_def by auto
    subgoal
      apply (rule wait_c.intros(2))
      using assms unfolding entails_def by auto
    done
  done

lemma conj_pure_mono:
  assumes "b s0 \<Longrightarrow> (P1 s0 \<Longrightarrow>\<^sub>A P2 s0)"
  shows "(!\<^sub>a[b] \<and>\<^sub>a P1) s0 \<Longrightarrow>\<^sub>A (!\<^sub>a[b] \<and>\<^sub>a P2) s0"
  using assms unfolding entails_def conj_assn_def pure_assn_def by auto

lemma conj_assn_mono1:
  assumes "P1 s0 \<Longrightarrow>\<^sub>A P2 s0"
  shows "(P1 \<and>\<^sub>a Q) s0 \<Longrightarrow>\<^sub>A (P2 \<and>\<^sub>a Q) s0"
  using assms unfolding entails_def conj_assn_def by auto

lemma wait_out_cv_mono:
  assumes "\<And>d s. P1 d s \<Longrightarrow>\<^sub>A P2 d s"
  shows "wait_out_cv I ch e P1 s0 \<Longrightarrow>\<^sub>A wait_out_cv I ch e P2 s0"
  unfolding wait_out_cv_def
  apply (rule wait_out_c_mono)
  apply (rule conj_pure_mono)
  using assms by auto

subsection \<open>Hoare logic for sequential processes\<close>

text \<open>Definition of Hoare triple\<close>
definition Valid :: "'a assn \<Rightarrow> 'a proc \<Rightarrow> 'a assn \<Rightarrow> bool" ("\<Turnstile> ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile> {P} c {Q} \<longleftrightarrow> (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step c s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"

theorem strengthen_pre:
  "\<Turnstile> {P2} c {Q} \<Longrightarrow> P1 \<Longrightarrow>\<^sub>A P2 \<Longrightarrow> \<Turnstile> {P1} c {Q}"
  unfolding Valid_def entails_def by metis

theorem weaken_post:
  "\<Turnstile> {P} c {Q1} \<Longrightarrow> Q1 \<Longrightarrow>\<^sub>A Q2 \<Longrightarrow> \<Turnstile> {P} c {Q2}"
  unfolding Valid_def entails_def by metis

text \<open>Specification of a single process.

  Each HCSP process can be specified using a parameterized
  assertion, which for each starting state provides an assertion
  on the ending state and trace.
\<close>
definition spec_of :: "'a proc \<Rightarrow> 'a assn2 \<Rightarrow> bool" where
  "spec_of c Q \<longleftrightarrow> (\<forall>s0. \<Turnstile> {init s0} c {Q s0})"

text \<open>Consequence rule for spec_of\<close>
lemma spec_of_post:
  "spec_of c Q1 \<Longrightarrow> \<forall>s0. Q1 s0 \<Longrightarrow>\<^sub>A Q2 s0 \<Longrightarrow> spec_of c Q2"
  unfolding spec_of_def using weaken_post by blast

subsubsection \<open>Hoare rules for basic commands\<close>

text \<open>For each command, we state two versions of the rules,
  one for the command alone, and one for the command followed
  by an arbitrary process.
\<close>

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
  shows "spec_of (Basic f; c) (Q {{ f }}\<^sub>e)"
  unfolding Valid_def spec_of_def
  apply (auto elim!: seqE basicE)
  using assms unfolding spec_of_def Valid_def init_def subste_assn2_def by auto

lemma spec_of_ichoice:
  assumes "spec_of c1 Q1"
    and "spec_of c2 Q2"
  shows "spec_of (IChoice c1 c2) (Q1 \<or>\<^sub>a Q2)"
  unfolding Valid_def spec_of_def
  apply (auto elim!: ichoiceE)
  using assms unfolding spec_of_def Valid_def disj_assn_def by auto

text \<open>Hoare rule for error\<close>
lemma spec_of_error:
  "spec_of Error P"
  unfolding Valid_def spec_of_def init_def
  by (auto elim: errorE)

lemma Valid_error_sp:
  "spec_of (Error; c) Q"
  unfolding Valid_def spec_of_def
  by (auto elim: seqE errorE)

text \<open>Hoare rules for conditional\<close>
lemma spec_of_cond:
  assumes "spec_of c1 Q1"
    and "spec_of c2 Q2"
  shows "spec_of (IF b THEN c1 ELSE c2 FI) (IFA b THEN Q1 ELSE Q2 FI)"
  unfolding Valid_def spec_of_def init_def cond_assn2_def
  apply (auto elim!: condE)
  using assms unfolding Valid_def spec_of_def init_def by auto

text \<open>Hoare rule for input\<close>
lemma spec_of_receive:
  "spec_of (Cm (ch[?]var)) (wait_in_c single_id_inv ch (\<lambda>d v. init {{ var := (\<lambda>_. v) }}))"
  unfolding Valid_def spec_of_def init_def subst_assn2_def
  apply (auto elim!: receiveE)
   apply (rule wait_in_c.intros(1)) apply auto[1]
  apply (rule wait_in_c.intros(2)) by auto

lemma Valid_receive_sp:
  assumes "spec_of c Q"
  shows "spec_of (Cm (ch[?]var); c)
                 (wait_in_c single_id_inv ch (\<lambda>d v. Q {{ var := (\<lambda>_. v) }}))"
  using assms unfolding Valid_def spec_of_def init_def subst_assn2_def
  apply (auto elim!: seqE receiveE)
  apply (rule wait_in_c.intros(1)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  apply (rule wait_in_c.intros(2)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  by auto

text \<open>Hoare rule for output\<close>
lemma spec_of_send:
  "spec_of (Cm (ch[!]e)) (wait_out_cv single_id_inv ch e (\<lambda>d. init))"
  unfolding Valid_def spec_of_def init_def wait_out_cv_def pure_assn_def conj_assn_def
  apply (auto elim!: sendE)
   apply (rule wait_out_c.intros(1)) apply auto[1]
  apply (rule wait_out_c.intros(2)) by auto

lemma Valid_send_sp:
  assumes "spec_of c Q"
  shows "spec_of (Cm (ch[!]e); c)
                 (wait_out_cv single_id_inv ch e (\<lambda>d. Q))"
  using assms unfolding Valid_def spec_of_def init_def wait_out_cv_def pure_assn_def conj_assn_def
  apply (auto elim!: seqE sendE)
   apply (rule wait_out_c.intros(1))
  using Valid_def spec_of_def init_def assms apply auto[1]
  apply (rule wait_out_c.intros(2)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  by auto

text \<open>Hoare rules for wait\<close>
lemma spec_of_wait:
  "spec_of (Wait e) (wait_c single_id_inv e (\<lambda>_. init))"
  unfolding Valid_def spec_of_def init_def
  apply (auto elim!: waitE)
   apply (rule wait_c.intros(1)) apply auto
  apply (rule wait_c.intros(2)) by auto

lemma Valid_wait_sp:
  assumes "spec_of c Q"
  shows "spec_of (Wait e; c) (wait_c single_id_inv e (\<lambda>_. Q))"
  using assms unfolding Valid_def spec_of_def init_def
  apply (auto elim!: seqE waitE)
   apply (rule wait_c.intros(1)) apply auto
  apply (rule wait_c.intros(2)) by auto

subsection \<open>Update rules\<close>

text \<open>The following rules specify how various assertion changes upon
  update of a variable.
\<close>

lemma wait_out_c_upd:
  "(wait_out_c I ch P {{ var := e }}) s0 \<Longrightarrow>\<^sub>A
   wait_out_c (\<lambda>s0 t s. I (upd s0 var (e s0)) t s) ch (\<lambda>d v. P d v {{ var := e }}) s0"
  unfolding entails_def apply clarify
  subgoal for s tr unfolding subst_assn2_def
    apply (elim wait_out_c.cases) apply auto
    subgoal for v tr'
      apply (rule wait_out_c.intros(1)) by auto
    subgoal for d v tr' p
      apply (rule wait_out_c.intros(2)) by auto
    done
  done

lemma conj_assn_upd:
  "((P \<and>\<^sub>a Q) {{ var := e }}) s0 \<Longrightarrow>\<^sub>A
   (P {{ var := e }} \<and>\<^sub>a Q {{ var := e }}) s0"
  unfolding conj_assn_def subst_assn2_def
  by (rule entails_triv)

lemma pure_assn_upd:
  "((!\<^sub>a[b]) {{ var := e }}) s0 \<Longrightarrow>\<^sub>A
   (!\<^sub>a[(\<lambda>s0. b (upd s0 var (e s0)))]) s0"
  unfolding pure_assn_def subst_assn2_def
  by (rule entails_triv)

lemma wait_out_cv_upd:
  "(wait_out_cv I ch e' P {{ var := e }}) s0 \<Longrightarrow>\<^sub>A
   wait_out_cv (\<lambda>s0 t s. I (upd s0 var (e s0)) t s) ch (\<lambda>s0. e' (upd s0 var (e s0)))
               (\<lambda>d. P d {{ var := e }}) s0"
  unfolding wait_out_cv_def
  apply (rule entails_trans)
   apply (rule wait_out_c_upd)
  apply (rule wait_out_c_mono)
  apply (rule entails_trans)
   apply (rule conj_assn_upd)
  apply (rule conj_assn_mono1)
  by (rule pure_assn_upd)

lemma wait_in_c_upd:
  "(wait_in_c I ch P {{ var := e }}) s0 \<Longrightarrow>\<^sub>A
   wait_in_c (\<lambda>s0 t s. I (upd s0 var (e s0)) t s) ch
             (\<lambda>d v. P d v {{ var := e }}) s0"
  unfolding entails_def apply clarify
  subgoal for s tr unfolding subst_assn2_def
    apply (elim wait_in_c.cases) apply auto
    subgoal for v tr'
      apply (rule wait_in_c.intros(1)) by auto
    subgoal for d v tr' p
      apply (rule wait_in_c.intros(2)) by auto
    done
  done

lemma wait_c_upd:
  "(wait_c I e' P {{ var := e }}) s0 \<Longrightarrow>\<^sub>A
   wait_c (\<lambda>s0 t s. I (upd s0 var (e s0)) t s) (\<lambda>s0. e' (upd s0 var (e s0))) (\<lambda>d. P d {{ var := e }}) s0"
  unfolding entails_def apply clarify
  subgoal for s tr unfolding subst_assn2_def
    apply (elim wait_c.cases) apply auto
    subgoal for tr' p
      apply (rule wait_c.intros(1)) by auto
    subgoal
      apply (rule wait_c.intros(2)) by auto
    done
  done

subsection \<open>Rewrite rules for big-step semantics\<close>

text \<open>Repetition for n times\<close>
fun RepN :: "nat \<Rightarrow> 'a proc \<Rightarrow> 'a proc" where
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

lemma spec_of_rep:
  assumes "\<And>n. spec_of (RepN n c) (Q n)"
  shows "spec_of (Rep c) (\<exists>\<^sub>an. Q n)"
  using assms unfolding spec_of_def Valid_def big_step_rep exists_assn_def
  by blast

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

lemma big_step_ichoice_distrib:
  "big_step (IChoice c1 c2; c) s1 tr1 s2 \<longleftrightarrow>
   big_step (IChoice (c1; c) (c2; c)) s1 tr1 s2"
  apply (rule iffI)
  subgoal apply (elim seqE ichoiceE)
    by (auto intro: IChoiceB1 IChoiceB2 seqB)
  subgoal apply (elim seqE ichoiceE)
    by (auto intro: IChoiceB1 IChoiceB2 seqB)
  done

lemma spec_of_ichoice_distrib:
  "spec_of (IChoice c1 c2; c) Q \<longleftrightarrow> spec_of (IChoice (c1; c) (c2; c)) Q"
  unfolding spec_of_def Valid_def
  using big_step_ichoice_distrib by blast

fun cs_append :: "'a proc \<Rightarrow> 'a comm \<times> 'a proc \<Rightarrow> 'a comm \<times> 'a proc" where
  "cs_append c (ch[!]e, p) = (ch[!]e, p; c)"
| "cs_append c (ch[?]var, p) = (ch[?]var, p; c)"

lemma cs_appendE1:
  "cs_append c es = (ch[!]e, p2) \<Longrightarrow> (\<And>p. es = (ch[!]e, p) \<Longrightarrow> p2 = p; c \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases es) subgoal for comm proc
    apply (cases comm) by auto
  done

lemma cs_appendE2:
  "cs_append c es = (ch[?]var, p2) \<Longrightarrow> (\<And>p. es = (ch[?]var, p) \<Longrightarrow> p2 = p; c \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases es) subgoal for comm proc
    apply (cases comm) by auto
  done

lemma rdy_of_echoice_cs_append [simp]:
  "rdy_of_echoice (map (cs_append c) cs) = rdy_of_echoice cs"
  unfolding rdy_of_echoice_def apply (rule sym)
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_map)
  subgoal for es apply (cases es)
    subgoal for comm proc apply (cases comm) by auto
    done
  done

lemma cons_append:
  "x # ys @ zs = (x # ys) @ zs"
  by auto

lemma big_step_interrupt_distrib:
  "big_step (Interrupt ode b cs pr; c) s1 tr s2 \<longleftrightarrow>
   big_step (Interrupt ode b (map (cs_append c) cs) (pr; c)) s1 tr s2"
  apply (rule iffI)
  subgoal apply (elim seqE interruptE)
    by (auto intro: big_step.intros)
  subgoal apply (elim interruptE) apply auto
    subgoal for i ch e p2 tr2
      apply (elim cs_appendE1) subgoal for p
        apply auto apply (elim seqE)
        by (auto simp only: cons_append intro: seqB InterruptSendB1)
      done
    subgoal for d p i ch e p2 tr2
      apply (elim cs_appendE1) subgoal for p'
        apply auto apply (elim seqE)
        by (auto simp only: cons_append intro: seqB InterruptSendB2)
      done
    subgoal for i ch var p2 v tr2
      apply (elim cs_appendE2) subgoal for p'
        apply auto apply (elim seqE)
        by (auto simp only: cons_append intro: seqB InterruptReceiveB1)
      done
    subgoal for d p i ch var p2 v tr2
      apply (elim cs_appendE2) subgoal for p'
        apply auto apply (elim seqE)
        by (auto simp only: cons_append intro: seqB InterruptReceiveB2)
      done
    subgoal
      apply (elim seqE)
      by (auto simp only: cons_append intro: seqB InterruptB1)
    subgoal for d p tr2
      apply (elim seqE)
      by (auto simp only: cons_append intro: seqB InterruptB2)
    done
  done

lemma spec_of_interrupt_distrib:
  "spec_of (Interrupt ode b cs pr; c) Q \<longleftrightarrow>
   spec_of (Interrupt ode b (map (cs_append c) cs) (pr; c)) Q"
  unfolding spec_of_def Valid_def
  using big_step_interrupt_distrib by blast

lemma big_step_skip_left:
  "big_step (Skip; c) s1 tr s2 \<longleftrightarrow> big_step c s1 tr s2"
  apply (rule iffI)
  subgoal apply (elim seqE skipE) by (auto intro!: seqB)
  subgoal by (metis append_Nil seqB skipB)
  done

lemma spec_of_skip_left:
  "spec_of (Skip; c) Q \<longleftrightarrow> spec_of c Q"
  unfolding spec_of_def Valid_def
  using big_step_skip_left by blast

end
