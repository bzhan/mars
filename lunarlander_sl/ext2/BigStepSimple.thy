theory BigStepSimple
  imports "../Analysis_More"
begin


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
  Single pname proc
| Parallel pproc "cname set" pproc

text \<open>Global states\<close>
type_synonym gstate = "pname \<Rightarrow> state option"

definition State :: "pname \<Rightarrow> state \<Rightarrow> gstate" where
  "State p s = (\<lambda>p'. if p' = p then Some s else None)"

subsection \<open>Traces\<close>

datatype comm_type = In | Out

datatype trace_block =
  CommBlock comm_type cname real
| WaitBlock real "real \<Rightarrow> state" rdy_info

abbreviation "InBlock ch v \<equiv> CommBlock In ch v"
abbreviation "OutBlock ch v \<equiv> CommBlock Out ch v"

type_synonym trace = "trace_block list"


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
| waitB1: "e s > 0 \<Longrightarrow> big_step (Wait e) s [WaitBlock (e s) (\<lambda>_. s) ({}, {})] s"
| waitB2: "\<not> e s > 0 \<Longrightarrow> big_step (Wait e) s [] s"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlock d (\<lambda>_. s) ({ch}, {}),
             OutBlock ch (e s)] s"
| receiveB1: "big_step (Cm (ch[?]var)) s [InBlock ch v] (s(var := v))"
| receiveB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlock d (\<lambda>_. s) ({}, {ch}),
             InBlock ch v] (s(var := v))"
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
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (InBlock ch v # tr2) s2"
| EChoiceReceiveB2: "(d::real) > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlock d (\<lambda>_. s1) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    big_step (Cont ode b) s1 [WaitBlock d (\<lambda>\<tau>. p \<tau>) ({}, {})] (p d)"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (p d) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlock d (\<lambda>\<tau>. p \<tau>) rdy #
                                      OutBlock ch (e (p d)) # tr2) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 ((p d)(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlock d (\<lambda>\<tau>. p \<tau>) rdy #
                                      InBlock ch v # tr2) s2"
| InterruptB1: "\<not>b s \<Longrightarrow> big_step (Interrupt ode b cs) s [] s"
| InterruptB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow> p d = s2 \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 [WaitBlock d (\<lambda>\<tau>. p \<tau>) rdy] s2"

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
type_synonym assn2 = "state \<Rightarrow> assn"

definition emp :: assn where
  "emp = (\<lambda>s tr. tr = [])"

definition Valid :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile> {P} c {Q} \<longleftrightarrow> (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step c s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

theorem entails_triv:
  "P \<Longrightarrow>\<^sub>A P"
  unfolding entails_def by auto

definition forall_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<forall>\<^sub>a" 10)where
  "(\<forall>\<^sub>a n. P n) = (\<lambda>s tr. \<forall>n. P n s tr)"

definition exists_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<exists>\<^sub>a" 10)where
  "(\<exists>\<^sub>a n. P n) = (\<lambda>s tr. \<exists>n. P n s tr)"

theorem strengthen_pre:
  "\<Turnstile> {P2} c {Q} \<Longrightarrow> P1 \<Longrightarrow>\<^sub>A P2 \<Longrightarrow> \<Turnstile> {P1} c {Q}"
  unfolding Valid_def entails_def by metis

theorem weaken_post:
  "\<Turnstile> {P} c {Q1} \<Longrightarrow> Q1 \<Longrightarrow>\<^sub>A Q2 \<Longrightarrow> \<Turnstile> {P} c {Q2}"
  unfolding Valid_def entails_def by metis

text \<open>Receive input, then state and trace satisfies P\<close>
inductive wait_in_c :: "cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> assn2) \<Rightarrow> assn2" where
  "P 0 v s0 s tr \<Longrightarrow> wait_in_c ch P s0 s (InBlock ch v # tr)"
| "0 < d \<Longrightarrow> P d v s0 s tr \<Longrightarrow> wait_in_c ch P s0 s (WaitBlock d (\<lambda>_. s0) ({}, {ch}) # InBlock ch v # tr)"

definition subst_assn2 :: "assn2 \<Rightarrow> var \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> assn2" ("_ {{_ := _}}" [90,90,90] 91) where 
  "P {{var := e}} = (\<lambda>s0. P (s0(var := e s0)))"

definition init :: "state \<Rightarrow> assn" where
  "init s0 = (\<lambda>s tr. s = s0 \<and> tr = [])"

definition spec_of :: "proc \<Rightarrow> assn2 \<Rightarrow> bool" where
  "spec_of c Q \<longleftrightarrow> (\<forall>s0. \<Turnstile> {init s0} c {Q s0})"

lemma spec_of_assign:
  "spec_of (var ::= e) (\<lambda>s0 s tr. s = s0(var := e s0))"
  unfolding Valid_def spec_of_def init_def
  by (auto elim!: assignE)

lemma Valid_assign_sp:
  assumes "spec_of c Q"
  shows "spec_of (var ::= e; c) (Q {{ var := e }})"
  unfolding Valid_def spec_of_def
  apply (auto elim!: seqE assignE)
  using assms unfolding spec_of_def Valid_def init_def subst_assn2_def by auto

lemma spec_of_skip:
  "spec_of Skip init"
  unfolding Valid_def spec_of_def
  by (auto elim: skipE)

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
  unfolding Valid_def spec_of_def init_def subst_assn2_def
  apply (auto elim!: seqE receiveE)
  apply (rule wait_in_c.intros(1))
  using Valid_def spec_of_def init_def assms apply auto[1]
  apply (rule wait_in_c.intros(2)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  done

inductive wait_out_c :: "cname \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> assn2) \<Rightarrow> assn2" where
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
  unfolding Valid_def spec_of_def init_def
  apply (auto elim!: seqE sendE)
   apply (rule wait_out_c.intros(1))
  using Valid_def spec_of_def init_def assms apply auto[1]
  apply (rule wait_out_c.intros(2)) apply auto[1]
  using Valid_def spec_of_def init_def assms apply auto[1]
  done

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

subsection \<open>Examples\<close>

definition A :: char where "A = CHR ''a''"
definition B :: char where "B = CHR ''b''"
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"

lemma ex1a_sp:
  "spec_of (Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. s X + 1)))
           (wait_in_c ch1 (\<lambda>d v. wait_out_c ch2 (\<lambda>s. s X + 1) (\<lambda>d. init) {{ X := (\<lambda>_. v) }}))"
  apply (rule Valid_receive_sp)
  apply (rule spec_of_send)
  done

lemma ex1b_sp:
  "spec_of (Cm (ch1[!](\<lambda>_. 3)))
           (wait_out_c ch1 (\<lambda>_. 3) (\<lambda>d. init))"
  apply (rule spec_of_send)
  done

fun rinv_c :: "nat \<Rightarrow> cname \<Rightarrow> (state \<Rightarrow> assn) \<Rightarrow> (state \<Rightarrow> assn)" where
  "rinv_c 0 ch Q = Q"
| "rinv_c (Suc n) ch Q = wait_out_c ch (\<lambda>s. s A) (\<lambda>d. rinv_c n ch Q {{ B := (\<lambda>s0. s0 B + 1) }})"

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

fun linv_c :: "nat \<Rightarrow> cname \<Rightarrow> (state \<Rightarrow> assn) \<Rightarrow> (state \<Rightarrow> assn)" where
  "linv_c 0 ch Q = Q"
| "linv_c (Suc n) ch Q = wait_in_c ch (\<lambda>d v. linv_c n ch Q {{Y := (\<lambda>s. s Y + s X)}} {{X := (\<lambda>_. v)}} )"

lemma ex3_c':
  "spec_of (RepN n (Cm (ch1[?]X); Y ::= (\<lambda>s. s Y + s X)))
           (linv_c n ch1 init)"
  apply (induction n)
   apply simp apply (rule spec_of_skip)
  subgoal premises pre for n
    apply simp apply (rule spec_of_post)
     apply (subst spec_of_seq_assoc)
    apply (rule Valid_receive_sp)
     apply (rule Valid_assign_sp)
     apply (rule pre) apply clarify
    apply (rule entails_triv)
    done
  done

lemma ex3_c:
  "spec_of (Rep (Cm (ch1[?]X); Y ::= (\<lambda>s. s Y + s X)))
           (\<lambda>s0. \<exists>\<^sub>an. linv_c n ch1 init s0)"
  apply (rule spec_of_rep)
  by (rule ex3_c')


subsection \<open>Combining two traces\<close>

text \<open>Whether two rdy_infos from different processes are compatible.\<close>
fun compat_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

text \<open>Merge two rdy infos\<close>
fun merge_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> rdy_info" where
  "merge_rdy (r11, r12) (r21, r22) = (r11 \<union> r21, r12 \<union> r22)"

datatype ptrace_block = 
  CommBlockP comm_type cname real
| WaitBlockP real "real \<Rightarrow> gstate" rdy_info

abbreviation "InBlockP ch v \<equiv> CommBlockP In ch v"
abbreviation "OutBlockP ch v \<equiv> CommBlockP Out ch v"

type_synonym ptrace = "ptrace_block list"

definition merge_state :: "gstate \<Rightarrow> gstate \<Rightarrow> gstate" where
  "merge_state ps1 ps2 = (\<lambda>p. case ps1 p of None \<Rightarrow> ps2 p | Some s \<Rightarrow> Some s)"

text \<open>combine_blocks comms tr1 tr2 tr means tr1 and tr2 combines to tr, where
  comms is the list of internal communication channels.\<close>
inductive combine_blocks :: "cname set \<Rightarrow> ptrace \<Rightarrow> ptrace \<Rightarrow> ptrace \<Rightarrow> bool" where
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

fun ptrace_of :: "pname \<Rightarrow> trace \<Rightarrow> ptrace" where
  "ptrace_of pn [] = []"
| "ptrace_of pn (CommBlock ch_type ch v # tr) = CommBlockP ch_type ch v # ptrace_of pn tr"
| "ptrace_of pn (WaitBlock d p rdy # tr) = WaitBlockP d (\<lambda>\<tau>. State pn (p \<tau>)) rdy # ptrace_of pn tr"

inductive par_big_step :: "pproc \<Rightarrow> gstate \<Rightarrow> ptrace \<Rightarrow> gstate \<Rightarrow> bool" where
  SingleB: "big_step p s1 tr s2 \<Longrightarrow> par_big_step (Single pn p) (State pn s1) (ptrace_of pn tr) (State pn s2)"
| ParallelB:
    "par_big_step p1 s11 tr1 s12 \<Longrightarrow>
     par_big_step p2 s21 tr2 s22 \<Longrightarrow>
     combine_blocks chs tr1 tr2 tr \<Longrightarrow>
     par_big_step (Parallel p1 chs p2) (merge_state s11 s21) tr (merge_state s12 s22)"

inductive_cases SingleE: "par_big_step (Single pn p) s1 tr s2"
thm SingleE

inductive_cases ParallelE: "par_big_step (Parallel p1 ch p2) s1 tr s2"
thm ParallelE

text \<open>Assertion on global state\<close>
type_synonym gs_assn = "gstate \<Rightarrow> bool"

text \<open>Assertion on global state and trace\<close>
type_synonym gassn = "gstate \<Rightarrow> ptrace \<Rightarrow> bool"

definition entails_g :: "gassn \<Rightarrow> gassn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>g" 25) where
  "(P \<Longrightarrow>\<^sub>g Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

lemma entails_g_triv:
  "P \<Longrightarrow>\<^sub>g P"
  unfolding entails_g_def by auto

lemma entails_g_trans:
  "P \<Longrightarrow>\<^sub>g Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>g R \<Longrightarrow> P \<Longrightarrow>\<^sub>g R"
  unfolding entails_g_def by auto

definition ParValid :: "gs_assn \<Rightarrow> pproc \<Rightarrow> gassn \<Rightarrow> bool" ("\<Turnstile>\<^sub>p ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile>\<^sub>p {P} c {Q} \<longleftrightarrow> (\<forall>s1 s2 tr2. P s1 \<longrightarrow> par_big_step c s1 tr2 s2 \<longrightarrow> Q s2 tr2)"

definition init_global :: "gstate \<Rightarrow> gs_assn" where
  "init_global s0 = (\<lambda>s. s = s0)"

lemma init_global_parallel:
  "init_global s0 (merge_state s1 s2) \<Longrightarrow>
   (\<And>s01 s02. s0 = merge_state s01 s02 \<Longrightarrow> init_global s01 s1 \<Longrightarrow> init_global s02 s2 \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding init_global_def by auto

definition spec_of_global :: "pproc \<Rightarrow> (gstate \<Rightarrow> gassn) \<Rightarrow> bool" where
  "spec_of_global c Q \<longleftrightarrow> (\<forall>s0. \<Turnstile>\<^sub>p {init_global s0} c {Q s0})"

inductive single_assn :: "pname \<Rightarrow> (state \<Rightarrow> assn) \<Rightarrow> (gstate \<Rightarrow> gassn)" where
  "Q s s' tr \<Longrightarrow> single_assn pn Q (State pn s) (State pn s') (ptrace_of pn tr)"

inductive sync_gassn :: "cname set \<Rightarrow> (gstate \<Rightarrow> gassn) \<Rightarrow> (gstate \<Rightarrow> gassn) \<Rightarrow> (gstate \<Rightarrow> gassn)" where
  "P s01 s12 tr1 \<Longrightarrow> Q s02 s22 tr2 \<Longrightarrow>
   combine_blocks chs tr1 tr2 tr \<Longrightarrow>
   sync_gassn chs P Q (merge_state s01 s02) (merge_state s12 s22) tr"

lemma spec_of_single:
  fixes Q :: "state \<Rightarrow> assn"
  assumes "spec_of c Q"
  shows "spec_of_global (Single pn c) (single_assn pn Q)"
  unfolding spec_of_global_def ParValid_def init_global_def apply auto
  apply (elim SingleE) apply auto
  using assms unfolding spec_of_def Valid_def init_def
  by (auto intro: single_assn.intros)

lemma spec_of_parallel:
  fixes P Q :: "gstate \<Rightarrow> gassn"
  assumes "spec_of_global p1 P"
    and "spec_of_global p2 Q"
  shows "spec_of_global (Parallel p1 chs p2) (sync_gassn chs P Q)"
  unfolding spec_of_global_def ParValid_def apply auto
  apply (elim ParallelE) apply auto
  apply (elim init_global_parallel) apply (auto simp add: init_global_def)
  subgoal for tr tr1 s12 tr2 s22 s01 s02
    apply (rule sync_gassn.intros)
    using assms unfolding spec_of_global_def ParValid_def init_global_def by auto
  done

lemma weaken_post_global:
  "\<Turnstile>\<^sub>p {P} c {Q1} \<Longrightarrow> Q1 \<Longrightarrow>\<^sub>g Q2 \<Longrightarrow> \<Turnstile>\<^sub>p {P} c {Q2}"
  unfolding ParValid_def entails_g_def by auto

lemma spec_of_global_post:
  "spec_of_global p Q1 \<Longrightarrow> \<forall>s0. Q1 s0 \<Longrightarrow>\<^sub>g Q2 s0 \<Longrightarrow> spec_of_global p Q2"
  unfolding spec_of_global_def using weaken_post_global by blast


subsection \<open>Examples of using ParValid_parallel\<close>

lemma ex1:
  "spec_of_global
    (Parallel (Single ''a'' (Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. s X + 1)))) {ch1}
              (Single ''b'' (Cm (ch1[!](\<lambda>_. 3)))))
    (sync_gassn {ch1}
      (single_assn ''a'' (wait_in_c ch1 (\<lambda>d v. wait_out_c ch2 (\<lambda>s. s X + 1) (\<lambda>d. init) {{ X := (\<lambda>_. v) }} )))
      (single_assn ''b'' (wait_out_c ch1 (\<lambda>_. 3) (\<lambda>d. init))))"
  apply (rule spec_of_parallel)
   apply (rule spec_of_single)
   apply (rule ex1a_sp)
  apply (rule spec_of_single)
  apply (rule ex1b_sp)
  done

inductive wait_in_cg :: "cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> gstate \<Rightarrow> gassn) \<Rightarrow> gstate \<Rightarrow> gassn" where
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

inductive wait_out_cg :: "cname \<Rightarrow> (gstate \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> gstate \<Rightarrow> gassn) \<Rightarrow> gstate \<Rightarrow> gassn" where
  "P 0 s0 s tr \<Longrightarrow> wait_out_cg ch e P s0 s (OutBlockP ch (e s0) # tr)"
| "0 < d \<Longrightarrow> P d s0 s tr \<Longrightarrow> wait_out_cg ch e P s0 s (WaitBlockP d (\<lambda>_. s0) ({ch}, {}) # OutBlockP ch (e s0) # tr)"

fun single_expr :: "pname \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> (gstate \<Rightarrow> real)" where
  "single_expr pn e gs = e (the (gs pn))"

lemma single_expr_simp1:
  "single_expr pn e (State pn s) = e s"
  by (auto simp add: State_def)

lemma single_assn_wait_out:
  "single_assn pn (wait_out_c ch1 e P) = wait_out_cg ch1 (single_expr pn e) (\<lambda>d. single_assn pn (P d))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      apply (elim wait_out_c.cases) apply auto
      subgoal for s0' s' tr'
        apply (subst single_expr_simp1[of pn e s0',symmetric])
        apply (rule wait_out_cg.intros(1))
        apply (rule single_assn.intros) by auto
      subgoal for d s0' s' tr'
        apply (subst single_expr_simp1[of pn e s0',symmetric])
        apply (rule wait_out_cg.intros(2)) apply simp
        apply (rule single_assn.intros) by auto
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

fun single_subst :: "pname \<Rightarrow> gstate \<Rightarrow> var \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> gstate" where
  "single_subst pn gs var e = gs (pn \<mapsto> ((the (gs pn)) (var := e (the (gs pn)))))"

definition single_subst_assn2 :: "(gstate \<Rightarrow> gassn) \<Rightarrow> var \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> pname \<Rightarrow> (gstate \<Rightarrow> gassn)"
  ("_ {{_ := _}}\<^sub>g at _" [90,90,90,90] 91) where
  "P {{var := e}}\<^sub>g at pn = (\<lambda>ps s tr. ps pn \<noteq> None \<and> P (single_subst pn ps var e) s tr)"

lemma subst_State:
  "State pn s(pn \<mapsto> s') = State pn s'"
  by (auto simp add: State_def)

lemma eval_State:
  "State pn s pn = Some s"
  by (auto simp add: State_def)

lemma subst_State_elim:
  "s0 pn = Some s0' \<Longrightarrow> s0(pn \<mapsto> s1') = State pn s2' \<Longrightarrow> s0 = State pn s0'"
  apply (auto simp add: State_def fun_upd_def) by metis

lemma single_assn_subst2:
  "single_assn pn (P {{ var := e }}) = (single_assn pn P) {{ var := e }}\<^sub>g at pn"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases)
      apply (auto simp add: single_subst_assn2_def subst_assn2_def subst_State eval_State)
      apply (rule single_assn.intros) by simp
    subgoal
      apply (auto simp add: single_subst_assn2_def subst_assn2_def)
      apply (elim single_assn.cases) apply auto
      subgoal premises pre for s0' s0'' s' tr'
      proof -
        have s0: "s0 = State pn s0'"
          apply (rule subst_State_elim) using pre by auto
        show ?thesis
          unfolding s0 apply (rule single_assn.intros)
          using pre by (metis eval_State map_upd_Some_unfold)
      qed
      done
    done
  done

inductive init_single :: "pname \<Rightarrow> gstate \<Rightarrow> gassn" where
  "s0 = s1 \<Longrightarrow> init_single pn (State pn s0) (State pn s1) []"

lemma single_assn_init:
  "single_assn pn init = init_single pn"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases)
      by (auto simp add: init_def eval_State intro: init_single.intros)
    subgoal
      apply (elim init_single.cases) apply auto
      apply (subst ptrace_of.simps(1)[of pn, symmetric])
      apply (rule single_assn.intros)
      by (auto simp add: init_def)
    done
  done

lemma ex1':
  "spec_of_global
    (Parallel (Single ''a'' (Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. s X + 1)))) {ch1}
              (Single ''b'' (Cm (ch1[!](\<lambda>_. 3)))))
    (sync_gassn {ch1}
      (wait_in_cg ch1 (\<lambda>d v. wait_out_cg ch2 (single_expr ''a'' (\<lambda>s. s X + 1)) (\<lambda>d. single_assn ''a'' init) {{X := (\<lambda>_. v)}}\<^sub>g at ''a''))
      (wait_out_cg ch1 (single_expr ''b'' (\<lambda>_. 3)) (\<lambda>d. single_assn ''b'' init)))"
  apply (rule spec_of_global_post)
   apply (rule ex1) apply clarify subgoal for s0
    apply (auto simp: single_assn_wait_in single_assn_wait_out single_assn_subst2)
    by (rule entails_g_triv)
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

lemma sync_gassn_out_in:
  "ch \<in> chs \<Longrightarrow>
   sync_gassn chs (wait_in_cg ch P) (wait_out_cg ch e Q) s0 \<Longrightarrow>\<^sub>g
   sync_gassn chs (P 0 (e s0)) (Q 0) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s01 s12 tr1 s02 s22 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr2'
          apply (elim combine_blocks_pairE)
            apply auto
          apply (rule sync_gassn.intros) by auto
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
   sync_gassn chs (wait_out_cg ch e Q) init_single (ParState s1 s2) \<Longrightarrow>\<^sub>g
   wait_out_cg ch (\<lambda>s. e (left s)) (\<lambda>d. sync_gassn chs (Q d) init_single) (ParState s1 s2)"
proof -
  have 1: "(\<lambda>s. e (left s)) (ParState s1 s2') = e s1" for s2'
    by auto
  show ?thesis
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s12 tr1 s22 tr2
      apply (elim wait_out_cg.cases) apply auto
      subgoal for tr1'
        apply (cases s2) apply auto subgoal for s2'
          apply (elim sync_elims)
          subgoal for tr2' apply auto
            subgoal premises pre
              apply (subst 1[symmetric])
              apply (rule wait_out_cg.intros)
              apply (rule sync_gassn.intros)
              using pre by auto
            done
          done
        done
      subgoal for d tr1'
        apply (cases s2) apply auto subgoal for s2'
          by (elim sync_elims)
        done
      done
    done
  done
qed

fun left_subst :: "gstate \<Rightarrow> var \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> gstate" where
  "left_subst (State s) var e = State s"
| "left_subst (ParState s1 s2) var e = ParState (single_subst s1 var e) s2"

definition single_subst_assn_left :: "(gstate \<Rightarrow> gassn) \<Rightarrow> var \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> (gstate \<Rightarrow> gassn)"
  ("_ {{_ := _}}\<^sub>l" [90,90,90] 91) where
  "P {{var := e}}\<^sub>l = (\<lambda>s0. P (left_subst s0 var e))"

lemma sync_gassn_subst_left:
  "sync_gassn chs (P {{ var := e }}\<^sub>g) Q (ParState s1 s2) \<Longrightarrow>\<^sub>g
   (sync_gassn chs P Q {{ var := e }}\<^sub>l) (ParState s1 s2)"
  unfolding entails_g_def apply auto
  subgoal for s tr
    unfolding single_subst_assn_left_def single_subst_assn2_def
    apply (elim sync_gassn.cases) apply auto
    subgoal for s12 tr1 s22 tr2
      apply (rule sync_gassn.intros) by auto
    done
  done

lemma sync_gassn_par:
  assumes "(\<And>s1 s2. sync_gassn chs P Q (ParState s1 s2) \<Longrightarrow>\<^sub>g R (ParState s1 s2))"
  shows "sync_gassn chs P Q s0 \<Longrightarrow>\<^sub>g R s0"
  using assms unfolding entails_g_def
  apply auto apply (elim sync_gassn.cases)
  by (auto simp add: sync_gassn.intros)

lemma entails_g_subst_left:
  assumes "P (left_subst s0 var e) \<Longrightarrow>\<^sub>g Q (left_subst s0 var e)"
  shows "(P {{ var := e }}\<^sub>l) s0 \<Longrightarrow>\<^sub>g (Q {{ var := e }}\<^sub>l) s0"
  unfolding entails_g_def single_subst_assn_left_def
  apply auto using assms unfolding entails_g_def by auto

lemma ex1'':
  "spec_of_global
    (Parallel (Single (Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. s X + 1)))) {ch1}
              (Single (Cm (ch1[!](\<lambda>_. 3)))))
    (Q)"
  apply (rule spec_of_global_post)
   apply (rule ex1') apply auto subgoal for s0
  apply (rule sync_gassn_par) subgoal for s1 s2
    apply (rule entails_g_trans)
      apply (rule sync_gassn_out_in) apply simp
      apply (rule entails_g_trans)
       apply (rule sync_gassn_subst_left)
      apply (rule entails_g_trans)
       apply (rule entails_g_subst_left)
      apply (rule sync_gassn_out_emp)



end
