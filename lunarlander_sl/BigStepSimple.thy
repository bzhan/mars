theory BigStepSimple
  imports Analysis_More
begin

subsection \<open>Syntax\<close>

text \<open>State\<close>
type_synonym state = "char \<Rightarrow> real"

text \<open>Expressions\<close>
type_synonym exp = "state \<Rightarrow> real"

text \<open>Predicates\<close>
type_synonym fform = "state \<Rightarrow> bool"

text \<open>Channel names\<close>
type_synonym cname = string

text \<open>Time\<close>
type_synonym time = real

text \<open>Variable names\<close>
type_synonym var = char

text \<open>Some common variables\<close>
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"

lemma vars_distinct [simp]: "X \<noteq> Y" "X \<noteq> Z" "Y \<noteq> Z" "Y \<noteq> X" "Z \<noteq> X" "Z \<noteq> Y"
  unfolding X_def Y_def Z_def by auto

text \<open>Ready information.
  First component is set of channels that are ready to output.
  Second component is set of channels that are ready to input.\<close>
type_synonym rdy_info = "cname set \<times> cname set"

text \<open>History at a time interval\<close>
type_synonym history = "time \<Rightarrow> state"

text \<open>Communications\<close>
datatype comm =
  Send cname exp         ("_[!]_" [110,108] 100)
| Receive cname var     ("_[?]_" [110,108] 100)

text \<open>Definition of ODEs\<close>

type_synonym vec = "real^(var)"

text \<open>Conversion between state and vector\<close>
definition state2vec :: "state \<Rightarrow> vec" where
  "state2vec s = (\<chi> x. s x)"

definition vec2state :: "vec \<Rightarrow> state" where
  "(vec2state v) x = v $ x"

lemma vec_state_map1[simp]: "vec2state (state2vec s) = s"
  unfolding vec2state_def state2vec_def by auto

lemma vec_state_map2[simp]: "state2vec (vec2state s) = s"
  unfolding vec2state_def state2vec_def by auto

datatype ODE =
  ODE "var \<Rightarrow> exp"

text \<open>Given ODE and a state, find the derivative vector.\<close>
fun ODE2Vec :: "ODE \<Rightarrow> state \<Rightarrow> vec" where
  "ODE2Vec (ODE f) s = state2vec (\<lambda>a. f a s)"

text \<open>History p on time {0 .. d} is a solution to ode.\<close>
definition ODEsol :: "ODE \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> real \<Rightarrow> bool" where
  "ODEsol ode p d = (d \<ge> 0 \<and> (((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {0 .. d}))"

text \<open>History p on time {0 ..} is a solution to ode.\<close>
definition ODEsolInf :: "ODE \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> bool" where
  "ODEsolInf ode p = (((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {0 ..})"


text \<open>HCSP processes\<close>
datatype proc =
  Cm comm
| Skip
| Assign var exp             ("_ ::= _" [99,95] 94)
| Seq proc proc           ("_; _" [91,90] 90)
| Cond fform proc proc        ("IF _ _ _" [95,94] 93)
| Wait time  \<comment> \<open>Waiting for a specified amount of time\<close>
| IChoice proc proc  \<comment> \<open>Nondeterminism\<close>
| EChoice "(comm \<times> proc) list"  \<comment> \<open>External choice\<close>
| Rep proc   \<comment> \<open>Nondeterministic repetition\<close>
| Cont ODE fform  \<comment> \<open>ODE with boundary\<close>
| Interrupt ODE fform "(comm \<times> proc) list"  \<comment> \<open>Interrupt\<close>

text \<open>Parallel of several HCSP processes\<close>
datatype pproc =
  Single proc
| Parallel pproc "cname set" pproc

text \<open>Events\<close>
datatype event =
  In cname real
| Out cname real 
| IO cname real 

text \<open>Global states\<close>
datatype gstate =
  State state
| ParState gstate gstate

subsection \<open>Traces\<close>

text \<open>First, we define the concept of traces\<close>

datatype trace_block =
  InBlock cname real
  | OutBlock cname real
  | IOBlock cname real
  | WaitBlock time "real \<Rightarrow> gstate" rdy_info

type_synonym trace = "trace_block list"

type_synonym tassn = "trace \<Rightarrow> bool"


subsection \<open>Big-step semantics\<close>

text \<open>Compute list of ready communications for an external choice.\<close>
fun rdy_of_echoice :: "(comm \<times> proc) list \<Rightarrow> rdy_info" where
  "rdy_of_echoice [] = ({}, {})"
| "rdy_of_echoice ((Send ch e, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_echoice ((Receive ch var, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (fst rdy, insert ch (snd rdy)))"

text \<open>big_step p s1 tr s2 means executing p starting from state s1 results
in a trace tr and final state s2.\<close>
inductive big_step :: "proc \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  skipB: "big_step Skip s [] s"
| assignB: "big_step (var ::= e) s [] (s(var := e s))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (Seq p1 p2) s1 (tr1 @ tr2) s3"
| condB1: "b s1 \<Longrightarrow> big_step p1 s1 tr s2 \<Longrightarrow> big_step (Cond b p1 p2) s1 tr s2"
| condB2: "\<not> b s1 \<Longrightarrow> big_step p2 s1 tr s2 \<Longrightarrow> big_step (Cond b p1 p2) s1 tr s2"
| waitB1: "d > 0 \<Longrightarrow> big_step (Wait d) s [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})] s"
| waitB2: "\<not> d > 0 \<Longrightarrow> big_step (Wait d) s [] s"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "d > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}),
             OutBlock ch (e s)] s"
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


subsection \<open>More convenient version of rules\<close>

lemma assignB':
  assumes "s2 = s1(var := e s1)"
  shows "big_step (Assign var e) s1 [] s2"
  unfolding assms by (rule assignB)

lemma sendB1':
  assumes "blks = [OutBlock ch (e s)]"
  shows "big_step (Cm (Send ch e)) s blks s"
  unfolding assms by (rule sendB1)

lemma seqB':
  assumes "big_step p1 s1 tr1 s2"
    and "big_step p2 s2 tr2 s3"
    and "tr = tr1 @ tr2"
  shows "big_step (p1; p2) s1 tr s3"
  unfolding assms(3) using assms(1-2) by (rule seqB)

lemma receiveB2':
  assumes "d > 0"
    and "blks = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}),
                 InBlock ch v]"
    and "s' = s(var := v)"
  shows "big_step (Cm (ch[?]var)) s blks s'"
  unfolding assms(2-3) using assms(1) by (rule receiveB2)


subsection \<open>Validity\<close>

type_synonym assn = "state \<Rightarrow> trace \<Rightarrow> bool"

definition Valid :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" where
  "Valid P c Q \<longleftrightarrow> (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step c s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

lemma entails_refl [simp]:
  "P \<Longrightarrow>\<^sub>A P"
  unfolding entails_def by auto

lemma entails_trans:
  "(P \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> (Q \<Longrightarrow>\<^sub>A R) \<Longrightarrow> (P \<Longrightarrow>\<^sub>A R)"
  unfolding entails_def by auto

lemma Valid_ex_pre:
  "(\<And>v. Valid (P v) c Q) \<Longrightarrow> Valid (\<lambda>s t. \<exists>v. P v s t) c Q"
  unfolding Valid_def by auto

lemma Valid_ex_post:
  "\<exists>v. Valid P c (Q v) \<Longrightarrow> Valid P c (\<lambda>s t. \<exists>v. Q v s t)"
  unfolding Valid_def by blast

lemma Valid_and_pre:
  "(P1 \<Longrightarrow> Valid P c Q) \<Longrightarrow> Valid (\<lambda>s t. P1 \<and> P s t) c Q"
  unfolding Valid_def by auto

inductive_cases skipE: "big_step Skip s1 tr s2"
thm skipE

inductive_cases assignE: "big_step (Assign var e) s1 tr s2"
thm assignE

inductive_cases sendE: "big_step (Cm (ch[!]e)) s1 tr s2"
thm sendE

inductive_cases receiveE: "big_step (Cm (ch[?]var)) s1 tr s2"
thm receiveE

inductive_cases seqE: "big_step (Seq p1 p2) s1 tr s2"
thm seqE

inductive_cases condE: "big_step (Cond b p1 p2) s1 tr s2"
thm condE

inductive_cases waitE: "big_step (Wait d) s1 tr s2"
thm waitE

inductive_cases echoiceE: "big_step (EChoice es) s1 tr s2"
thm echoiceE

inductive_cases ichoiceE: "big_step (IChoice p1 p2) s1 tr s2"
thm ichoiceE

inductive_cases contE: "big_step (Cont ode b) s1 tr s2"
thm contE

inductive_cases interruptE: "big_step (Interrupt ode b cs) s1 tr s2"
thm interruptE

theorem Valid_weaken_pre:
  "P \<Longrightarrow>\<^sub>A P' \<Longrightarrow> Valid P' c Q \<Longrightarrow> Valid P c Q"
  unfolding Valid_def entails_def by blast

theorem Valid_strengthen_post:
  "Q \<Longrightarrow>\<^sub>A Q' \<Longrightarrow> Valid P c Q \<Longrightarrow> Valid P c Q'"
  unfolding Valid_def entails_def by blast

theorem Valid_skip:
  "Valid P Skip P"
  unfolding Valid_def
  by (auto elim: skipE)

theorem Valid_assign:
  "Valid
    (\<lambda>s tr. Q (s(var := e s)) tr)
    (var ::= e)
    Q"
  unfolding Valid_def
  by (auto elim: assignE)

theorem Valid_send:
  "Valid
    (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and>
        (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), OutBlock ch (e s)])))
    (Cm (ch[!]e))
    Q"
  unfolding Valid_def
  by (auto elim: sendE)

theorem Valid_receive:
  "Valid
    (\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
        (\<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), InBlock ch v])))
    (Cm (ch[?]var))
    Q"
  unfolding Valid_def
  by (auto elim: receiveE)

theorem Valid_seq:
  "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (c1; c2) R"
  unfolding Valid_def
  apply (auto elim!: seqE) by fastforce

theorem Valid_cond:
  "Valid P1 c1 Q \<Longrightarrow> Valid P2 c2 Q \<Longrightarrow>
   Valid (\<lambda>s. if b s then P1 s else P2 s) (Cond b c1 c2) Q"
  unfolding Valid_def
  by (auto elim: condE)

theorem Valid_wait:
  "d > 0 \<Longrightarrow> Valid
    (\<lambda>s tr. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})]))
    (Wait d)
    Q"
  unfolding Valid_def
  by (auto elim: waitE)

theorem Valid_wait2:
  "\<not> d > 0 \<Longrightarrow> Valid Q (Wait d) Q"
  unfolding Valid_def
  by (auto elim: waitE)

theorem Valid_rep:
  assumes "Valid P c P"
  shows "Valid P (Rep c) P"
proof -
  have "big_step p s1 tr2 s2 \<Longrightarrow> p = Rep c \<Longrightarrow> \<forall>tr1. P s1 tr1 \<longrightarrow> P s2 (tr1 @ tr2)" for p s1 s2 tr2
    apply (induct rule: big_step.induct, auto)
    by (metis Valid_def append.assoc assms)
  then show ?thesis
    using assms unfolding Valid_def by auto
qed

theorem Valid_ichoice:
  assumes "Valid P1 c1 Q"
    and "Valid P2 c2 Q"
  shows "Valid
    (\<lambda>s tr. P1 s tr \<and> P2 s tr)
    (IChoice c1 c2)
    Q"
  using assms unfolding Valid_def by (auto elim: ichoiceE)

theorem Valid_echoice:
  assumes "\<And>i. i<length es \<Longrightarrow>
    case es ! i of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)]))))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
             (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v]))))"
  shows "Valid P (EChoice es) R"
proof -
  have a: "R s2 (tr1 @ (OutBlock ch (e s1) # tr2))"
    if *: "P s1 tr1"
          "i < length es"
          "es ! i = (ch[!]e, p2)"
          "big_step p2 s1 tr2 s2" for s1 tr1 s2 i ch e p2 tr2
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
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
      "Valid Q p2 R"
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
      "Valid Q p2 R"
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
      "Valid Q p2 R"
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


text \<open>Some special cases of EChoice\<close>

lemma InIn_lemma:
  assumes "Q ch1 var1 p1"
    and "Q ch2 var2 p2"
    and "i < length [(ch1[?]var1, p1), (ch2[?]var2, p2)]"
  shows "case [(ch1[?]var1, p1), (ch2[?]var2, p2)] ! i of
            (ch[!]e, p1) \<Rightarrow> P ch e p1
          | (ch[?]var, p1) \<Rightarrow> Q ch var p1"
proof -
  have "case comm of ch[!]e \<Rightarrow> P ch e p | ch[?]var \<Rightarrow> Q ch var p"
    if "i < Suc (Suc 0)"
       "[(ch1[?]var1, p1), (ch2[?]var2, p2)] ! i = (comm, p)" for comm p i
  proof -
    have "i = 0 \<or> i = 1"
      using that(1) by auto
    then show ?thesis
      apply (rule disjE)
      using that(2) assms by auto
  qed
  then show ?thesis
    using assms(3) by auto
qed

theorem Valid_echoice_InIn:
  assumes "Valid Q1 p1 R"
    and "Valid Q2 p2 R"
  shows "Valid
    (\<lambda>s tr. (\<forall>v. Q1 (s(var1 := v)) (tr @ [InBlock ch1 v])) \<and>
            (\<forall>d>0. \<forall>v. Q1 (s(var1 := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch1, ch2}), InBlock ch1 v])) \<and>
            (\<forall>v. Q2 (s(var2 := v)) (tr @ [InBlock ch2 v])) \<and>
            (\<forall>d>0. \<forall>v. Q2 (s(var2 := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch1, ch2}), InBlock ch2 v])))
      (EChoice [(ch1[?]var1, p1), (ch2[?]var2, p2)])
    R"
  apply (rule Valid_echoice)
  apply (rule InIn_lemma)
  subgoal apply (rule exI[where x=Q1])
    by (auto simp add: assms entails_def)
  apply (rule exI[where x=Q2])
  by (auto simp add: assms entails_def)


subsection \<open>Standard assertions\<close>

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

definition and_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<and>\<^sub>A" 35) where
  "(P \<and>\<^sub>A Q) = (\<lambda>tr. P tr \<and> Q tr)"

definition emp_assn :: "tassn" ("emp\<^sub>A") where
  "emp\<^sub>A = (\<lambda>tr. tr = [])"

definition join_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "@\<^sub>t" 65) where
  "P @\<^sub>t Q = (\<lambda>tr. \<exists>tr1 tr2. P tr1 \<and> Q tr2 \<and> tr = tr1 @ tr2)"

definition magic_wand_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "@-" 65) where
  "Q @- P = (\<lambda>tr. \<forall>tr1. Q tr1 \<longrightarrow> P (tr @ tr1))"

definition all_assn :: "(real \<Rightarrow> tassn) \<Rightarrow> tassn" (binder "\<forall>\<^sub>A" 10) where
  "(\<forall>\<^sub>A v. P v) = (\<lambda>tr. \<forall>v. P v tr)"

definition conj_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<and>\<^sub>t" 35) where
  "(P \<and>\<^sub>t Q) = (\<lambda>tr. P tr \<and> Q tr)"

definition disj_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<or>\<^sub>t" 25) where
  "(P \<or>\<^sub>t Q) = (\<lambda>tr. P tr \<or> Q tr)"

definition pure_assn :: "bool \<Rightarrow> tassn" ("\<up>") where
  "\<up>b = (\<lambda>_. b)"

inductive out_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> tassn" ("Out\<^sub>A") where
  "Out\<^sub>A s ch v [OutBlock ch v]"
| "d > 0 \<Longrightarrow> Out\<^sub>A s ch v [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), OutBlock ch v]"

inductive in_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> tassn" ("In\<^sub>A") where
  "In\<^sub>A s ch v [InBlock ch v]"
| "d > 0 \<Longrightarrow> In\<^sub>A s ch v [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), InBlock ch v]"

inductive io_assn :: "cname \<Rightarrow> real \<Rightarrow> tassn" ("IO\<^sub>A") where
  "IO\<^sub>A ch v [IOBlock ch v]"

inductive wait_assn :: "real \<Rightarrow> (real \<Rightarrow> gstate) \<Rightarrow> tassn" ("Wait\<^sub>A") where
  "Wait\<^sub>A d p [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p \<tau>) ({}, {})]"

abbreviation "WaitS\<^sub>A d p \<equiv> Wait\<^sub>A d (\<lambda>t. State (p t))"

lemma emp_unit_left [simp]:
  "(emp\<^sub>A @\<^sub>t P) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma emp_unit_right [simp]:
  "(P @\<^sub>t emp\<^sub>A) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma join_assoc:
  "(P @\<^sub>t Q) @\<^sub>t R = P @\<^sub>t (Q @\<^sub>t R)"
  unfolding join_assn_def by fastforce

lemma entails_mp_emp:
  "emp\<^sub>A \<Longrightarrow>\<^sub>t P @- P"
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

theorem Valid_send':
  "Valid
    (\<lambda>s. Out\<^sub>A s ch (e s) @- Q s)
    (Cm (ch[!]e))
    Q"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send)
  unfolding entails_def magic_wand_assn_def
  by (auto intro: out_assn.intros)

theorem Valid_receive':
  "Valid
    (\<lambda>s. \<forall>\<^sub>A v. In\<^sub>A s ch v @- Q (s(var := v)))
    (Cm (ch[?]var))
    Q"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def magic_wand_assn_def all_assn_def
  by (auto intro: in_assn.intros)

theorem Valid_wait':
  "d > 0 \<Longrightarrow> Valid
    (\<lambda>s. WaitS\<^sub>A d (\<lambda>_. s) @- Q s)
    (Wait d)
    Q"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_wait)
  unfolding entails_def magic_wand_assn_def
  by (auto intro: wait_assn.intros)

theorem Valid_wait_sp:
  "d > 0 \<Longrightarrow> Valid
    (\<lambda>s tr. s = st \<and> P s tr)
    (Wait d)
    (\<lambda>s tr. s = st \<and> (P s @\<^sub>t WaitS\<^sub>A d (\<lambda>_. st)) tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_wait')
  by (auto simp add: entails_def join_assn_def magic_wand_assn_def)

theorem Valid_assign_sp:
  "Valid
    (\<lambda>s t. s = st \<and> P s t)
    (Assign x e)
    (\<lambda>s t. s = st(x := e st) \<and> P st t)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_assign)
  by (auto simp add: entails_def)

theorem Valid_assign_sp':
  "Valid
    (\<lambda>s t. \<exists>v. s = st v \<and> P v s t)
    (Assign x e)
    (\<lambda>s t. \<exists>v. s = (st v)(x := e (st v)) \<and> P v (st v) t)"
  apply (rule Valid_ex_pre)
  subgoal for v
    apply (rule Valid_ex_post)
    apply (rule exI[where x=v])
    by (rule Valid_assign_sp)
  done

theorem Valid_send_sp:
  "Valid
    (\<lambda>s t. s = st \<and> P s t)
    (Cm (ch[!]e))
    (\<lambda>s t. s = st \<and> (P st @\<^sub>t Out\<^sub>A st ch (e st)) t)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send')
  by (auto simp add: entails_def magic_wand_assn_def join_assn_def)

theorem Valid_receive_sp:
  "Valid
    (\<lambda>s t. s = st \<and> P s t)
    (Cm (ch[?]var))
    (\<lambda>s t. \<exists>v. s = st(var := v) \<and> (P st @\<^sub>t In\<^sub>A st ch v) t)"
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



subsection \<open>Rules for internal and external choice\<close>

inductive inrdy_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Inrdy\<^sub>A") where
  "Inrdy\<^sub>A s ch v rdy [InBlock ch v]"
| "d > 0 \<Longrightarrow> Inrdy\<^sub>A s ch v rdy [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) rdy, InBlock ch v]"

inductive outrdy_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Outrdy\<^sub>A") where
  "Outrdy\<^sub>A s ch v rdy [OutBlock ch v]"
| "d > 0 \<Longrightarrow> Outrdy\<^sub>A s ch v rdy [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) rdy, OutBlock ch v]"

text \<open>First, we restate the rule for Valid_echoice in simpler form\<close>

theorem Valid_echoice':
  assumes "\<And>i. i<length es \<Longrightarrow>
    case es ! i of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and>
            (P \<Longrightarrow>\<^sub>A (\<lambda>s. Outrdy\<^sub>A s ch (e s) (rdy_of_echoice es) @- Q s)))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and>
            (P \<Longrightarrow>\<^sub>A (\<lambda>s. \<forall>\<^sub>Av. Inrdy\<^sub>A s ch v (rdy_of_echoice es) @- Q (s(var := v)))))"
  shows "Valid P (EChoice es) R"
proof -
  have 1: "\<exists>Q. Valid Q p R \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]))) \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)])))"
    if *: "i < length es" "es ! i = (ch[!]e, p)" for i ch e p
  proof -
    from assms obtain Q where
      Q: "Valid Q p R \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s. Outrdy\<^sub>A s ch (e s) (rdy_of_echoice es) @- Q s))"
      using * by fastforce
    show ?thesis
      apply (rule exI[where x=Q])
      using Q by (auto simp add: entails_def magic_wand_assn_def
                       intro: outrdy_assn.intros)
  qed
  have 2: "\<exists>Q. Valid Q p R \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>v. Q (s(var := v)) (tr @ [InBlock ch v]))) \<and>
           (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. \<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v])))"
    if *: "i < length es" "es ! i = (ch[?]var, p)" for i ch var p
  proof -
    from assms obtain Q where
      Q: "Valid Q p R \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s. \<forall>\<^sub>Av. Inrdy\<^sub>A s ch v (rdy_of_echoice es) @- Q (s(var := v))))"
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

theorem Valid_echoice_InIn':
  assumes "Valid Q1 p1 R"
    and "Valid Q2 p2 R"
  shows "Valid
    (\<lambda>s. (\<forall>\<^sub>Av. ((Inrdy\<^sub>A s ch1 v ({}, {ch1, ch2})) @- Q1 (s(var1 := v)))) \<and>\<^sub>A
         (\<forall>\<^sub>Av. ((Inrdy\<^sub>A s ch2 v ({}, {ch1, ch2})) @- Q2 (s(var2 := v)))))
      (EChoice [(ch1[?]var1, p1), (ch2[?]var2, p2)])
    R"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_echoice_InIn[OF assms(1-2)])
  apply (auto simp add: entails_def magic_wand_assn_def and_assn_def all_assn_def)
  by (auto simp add: inrdy_assn.intros)

lemma echoice_test1:
  "Valid
    (\<lambda>s. (\<forall>\<^sub>Av. ((Inrdy\<^sub>A s ''ch1'' v ({}, {''ch1'', ''ch2''})) @- Q (s(X := v)))) \<and>\<^sub>A
         (\<forall>\<^sub>Av. ((Inrdy\<^sub>A s ''ch2'' v ({}, {''ch1'', ''ch2''})) @- Q (s(X := v)))))
    (EChoice [(''ch1''[?]X, Skip), (''ch2''[?]X, Skip)])
    Q"
  apply (rule Valid_echoice_InIn')
   apply (rule Valid_skip)
  by (rule Valid_skip)

text \<open>Contrast this with the case of internal choice\<close>
lemma ichoice_test1:
  "Valid
    (\<lambda>s. (\<forall>\<^sub>Av. In\<^sub>A s ''ch1'' v @- Q (s(X := v))) \<and>\<^sub>A
         (\<forall>\<^sub>Av. In\<^sub>A s ''ch2'' v @- Q (s(X := v))))
    (IChoice (Cm (''ch1''[?]X)) (Cm (''ch2''[?]X)))
    Q"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_ichoice)
    apply (rule Valid_receive') apply (rule Valid_receive')
  unfolding entails_def and_assn_def by auto

text \<open>Strongest postcondition form\<close>
lemma ichoice_test1':
  "Valid
    (\<lambda>s tr. s = st \<and> P tr)
    (IChoice (Cm (''ch1''[?]X)) (Cm (''ch2''[?]X)))
    (\<lambda>s tr. (\<exists>v. s = st(X := v) \<and> (P @\<^sub>t In\<^sub>A st ''ch1'' v) tr) \<or>
            (\<exists>v. s = st(X := v) \<and> (P @\<^sub>t In\<^sub>A st ''ch2'' v) tr))"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule ichoice_test1)
  apply (auto simp add: entails_def and_assn_def magic_wand_assn_def join_assn_def all_assn_def)
  subgoal for tr v tr'
    apply (rule exI[where x=v])
    apply auto
    apply (rule exI[where x=tr])
    by auto
  done

theorem Valid_echoice_sp:
  assumes "\<And>i. i<length es \<Longrightarrow>
    case es ! i of
      (ch[!]e, p2) \<Rightarrow>
        Valid (\<lambda>s tr. s = st \<and> (P s @\<^sub>t Outrdy\<^sub>A s ch (e s) (rdy_of_echoice es)) tr) p2 Q
    | (ch[?]var, p2) \<Rightarrow>
        Valid (\<lambda>s tr. (\<exists>v. s = st(var := v) \<and> (P st @\<^sub>t Inrdy\<^sub>A st ch v (rdy_of_echoice es)) tr)) p2 Q"
  shows "Valid
    (\<lambda>s tr. s = st \<and> P s tr)
    (EChoice es)
    Q"
  apply (rule Valid_echoice')
  subgoal for i
    apply (cases "es ! i") apply auto
    subgoal for comm p2
      apply (cases comm)
      subgoal for ch e
        apply auto
        apply (rule exI[where x="\<lambda>s tr. s = st \<and> (P s @\<^sub>t Outrdy\<^sub>A s ch (e s) (rdy_of_echoice es)) tr"])
        apply auto
        using assms apply fastforce
        by (auto simp add: entails_def join_assn_def magic_wand_assn_def)
      subgoal for ch var
        apply auto
        apply (rule exI[where x="\<lambda>s tr. (\<exists>v. s = st(var := v) \<and> (P st @\<^sub>t Inrdy\<^sub>A st ch v (rdy_of_echoice es)) tr)"])
        apply auto
        using assms apply fastforce
        by (auto simp add: entails_def magic_wand_assn_def join_assn_def all_assn_def)
      done
    done
  done

theorem Valid_echoice_InIn_sp:
  assumes "Valid (\<lambda>s tr. (\<exists>v. s = st(var1 := v) \<and> (P st @\<^sub>t Inrdy\<^sub>A st ch1 v ({}, {ch1, ch2})) tr)) p1 Q1"
    and "Valid (\<lambda>s tr. (\<exists>v. s = st(var2 := v) \<and> (P st @\<^sub>t Inrdy\<^sub>A st ch2 v ({}, {ch1, ch2})) tr)) p2 Q2"
  shows
   "Valid
    (\<lambda>s tr. s = st \<and> P s tr)
    (EChoice [(ch1[?]var1, p1), (ch2[?]var2, p2)])
    (\<lambda>s tr. Q1 s tr \<or> Q2 s tr)"
  apply (rule Valid_echoice_sp)
  apply (rule InIn_lemma)
  using assms by (auto simp add: Valid_def)


subsection \<open>Test for external choice\<close>

text \<open>Strongest postcondition form\<close>
lemma testEChoice1:
  "Valid
    (\<lambda>s tr. s = st \<and> P s tr)
    (EChoice [(''ch1''[?]X, Y ::= (\<lambda>s. s Y + s X)), (''ch2''[?]X, Y ::= (\<lambda>s. s Y - s X))])
    (\<lambda>s tr. (\<exists>v. s = st(X := v, Y := st Y + v) \<and> (P st @\<^sub>t Inrdy\<^sub>A st ''ch1'' v ({}, {''ch1'', ''ch2''})) tr) \<or>
            (\<exists>v. s = st(X := v, Y := st Y - v) \<and> (P st @\<^sub>t Inrdy\<^sub>A st ''ch2'' v ({}, {''ch1'', ''ch2''})) tr))"
  apply (rule Valid_strengthen_post)
  prefer 2
   apply (rule Valid_echoice_InIn_sp)
    apply (rule Valid_assign_sp')
   apply (rule Valid_assign_sp')
  by auto

datatype dir = CH1 | CH2

fun echoice_ex_inv :: "state \<Rightarrow> (dir \<times> real) list \<Rightarrow> tassn" where
  "echoice_ex_inv st [] = emp\<^sub>A"
| "echoice_ex_inv st ((CH1, v) # rest) =
    Inrdy\<^sub>A st ''ch1'' v ({}, {''ch1'', ''ch2''}) @\<^sub>t echoice_ex_inv (st(X := v, Y := st Y + v)) rest"
| "echoice_ex_inv st ((CH2, v) # rest) =
    Inrdy\<^sub>A st ''ch2'' v ({}, {''ch1'', ''ch2''}) @\<^sub>t echoice_ex_inv (st(X := v, Y := st Y - v)) rest"

fun last_echoice_ex :: "state \<Rightarrow> (dir \<times> real) list \<Rightarrow> state" where
  "last_echoice_ex st [] = st"
| "last_echoice_ex st ((CH1, v) # rest) = last_echoice_ex (st(X := v, Y := st Y + v)) rest"
| "last_echoice_ex st ((CH2, v) # rest) = last_echoice_ex (st(X := v, Y := st Y - v)) rest"

lemma echoice_ex_inv_snoc [simp]:
  "echoice_ex_inv st (ins @ [(CH1, v)]) =
    echoice_ex_inv st ins @\<^sub>t Inrdy\<^sub>A (last_echoice_ex st ins) ''ch1'' v ({}, {''ch1'', ''ch2''}) \<and>
   echoice_ex_inv st (ins @ [(CH2, v)]) =
    echoice_ex_inv st ins @\<^sub>t Inrdy\<^sub>A (last_echoice_ex st ins) ''ch2'' v ({}, {''ch1'', ''ch2''})"
  apply (induct ins arbitrary: st)
  subgoal by auto
  apply auto subgoal for dir v ins st
    apply (cases dir)
    by (auto simp add: join_assoc)
  subgoal for dir v ins st
    apply (cases dir)
    by (auto simp add: join_assoc)
  done

lemma last_echoice_ex_snoc [simp]:
  "last_echoice_ex st (ins @ [(CH1, v)]) = (last_echoice_ex st ins)(X := v, Y := last_echoice_ex st ins Y + v) \<and>
   last_echoice_ex st (ins @ [(CH2, v)]) = (last_echoice_ex st ins)(X := v, Y := last_echoice_ex st ins Y - v)"
  apply (induct ins arbitrary: st)
  apply auto
  by (metis (full_types) dir.exhaust last_echoice_ex.simps(2) last_echoice_ex.simps(3))+

lemma testEChoice:
  "Valid
    (\<lambda>s tr. s = st \<and> tr = [])
    (Rep (EChoice [(''ch1''[?]X, Y ::= (\<lambda>s. s Y + s X)), (''ch2''[?]X, Y ::= (\<lambda>s. s Y - s X))]))
    (\<lambda>s tr. \<exists>ins. s = last_echoice_ex st ins \<and> echoice_ex_inv st ins tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for ins
    apply (rule Valid_strengthen_post)
    prefer 2
     apply (rule Valid_echoice_InIn_sp)
    apply (rule Valid_assign_sp')
     apply (rule Valid_assign_sp')
    apply (auto simp add: entails_def)
    subgoal for tr v
      apply (rule exI[where x="ins@[(CH1,v)]"])
      by auto
    subgoal for tr v
      apply (rule exI[where x="ins@[(CH2,v)]"])
      by auto
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)


end
