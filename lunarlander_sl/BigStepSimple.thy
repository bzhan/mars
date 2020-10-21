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

lemma vars_distinct: "X \<noteq> Y" "X \<noteq> Z" "Y \<noteq> Z"
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
| Interrupt ODE "(comm \<times> proc) list"  \<comment> \<open>Interrupt\<close>

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
  State (single_st: state)
| ParState (left_st: gstate) (right_st: gstate)

subsection \<open>Traces\<close>

text \<open>First, we define the concept of traces\<close>

datatype trace_block =
  InBlock cname real
  | OutBlock cname real
  | IOBlock cname real
  | WaitBlock time "real \<Rightarrow> gstate" rdy_info

type_synonym trace = "trace_block list"

type_synonym tassn = "trace \<Rightarrow> bool"

text \<open>Combining two lists of blocks\<close>

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
   combine_blocks comms (InBlock ch v # blks1) (OutBlock ch v # blks2) (IOBlock ch v # blks)"
| combine_blocks_pair2:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (OutBlock ch v # blks1) (InBlock ch v # blks2) (IOBlock ch v # blks)"

  \<comment> \<open>Unpaired communication\<close>
| combine_blocks_unpair1:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (InBlock ch v # blks1) blks2 (InBlock ch v # blks)"
| combine_blocks_unpair2:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (OutBlock ch v # blks1) blks2 (OutBlock ch v # blks)"
| combine_blocks_unpair3:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (InBlock ch v # blks2) (InBlock ch v # blks)"
| combine_blocks_unpair4:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (OutBlock ch v # blks2) (OutBlock ch v # blks)"
| combine_blocks_unpair5:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (IOBlock ch v # blks1) blks2 (IOBlock ch v # blks)"
| combine_blocks_unpair6:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (IOBlock ch v # blks2) (IOBlock ch v # blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_wait1:
  "combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = restrict (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) {0..t} \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlock t hist1 rdy1 # blks1) (WaitBlock t hist2 rdy2 # blks2)
                  (WaitBlock t hist rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlock (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> - t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow>
   hist = restrict (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) {0..t1} \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlock t1 hist1 rdy1 # blks1) (WaitBlock t2 hist2 rdy2 # blks2)
                  (WaitBlock t1 hist rdy # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlock (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> - t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow>
   hist = restrict (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) {0..t2} \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlock t1 hist1 rdy1 # blks1) (WaitBlock t2 hist2 rdy2 # blks2)
                  (WaitBlock t2 hist rdy # blks)"

inductive_cases combine_blocksE1: "combine_blocks comms blks1 blks2 []"
thm combine_blocksE1

inductive_cases combine_blocksE2: "combine_blocks comms blks1 blks2 (IOBlock ch v # blks)"
thm combine_blocksE2

text \<open>Empty case\<close>
lemma combine_blocks_elim1:
  "combine_blocks comms [] [] blks \<Longrightarrow> blks = []"
  by (induct rule: combine_blocks.cases, auto)

text \<open>IO cases\<close>
lemma combine_blocks_elim2:
  "combine_blocks comms (InBlock ch v # blks1) (OutBlock ch w # blks2) blks \<Longrightarrow>
   ch \<in> comms \<Longrightarrow>
   (\<And>blks'. w = v \<Longrightarrow> blks = IOBlock ch v # blks' \<Longrightarrow> combine_blocks comms blks1 blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2a:
  "combine_blocks comms (OutBlock ch v # blks1) (InBlock ch w # blks2) blks \<Longrightarrow>
   ch \<in> comms \<Longrightarrow>
   (\<And>blks'. w = v \<Longrightarrow> blks = IOBlock ch v # blks' \<Longrightarrow> combine_blocks comms blks1 blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2b:
  "combine_blocks comms (OutBlock ch v # blks1) (WaitBlock d p rdy # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2c:
  "combine_blocks comms (InBlock ch v # blks1) (WaitBlock d p rdy # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2d:
  "combine_blocks comms (WaitBlock d p rdy # blks1) (OutBlock ch v # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2e:
  "combine_blocks comms (WaitBlock d p rdy # blks1) (InBlock ch v # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

text \<open>IO cases, unpaired\<close>
lemma combine_blocks_elim3:
  "combine_blocks comms (InBlock ch1 v # blks1) (OutBlock ch2 w # blks2) blks \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>blks'. blks = InBlock ch1 v # blks' \<Longrightarrow> combine_blocks comms blks1 (OutBlock ch2 w # blks2) blks' \<Longrightarrow> P) \<Longrightarrow>
   (\<And>blks'. blks = OutBlock ch2 w # blks' \<Longrightarrow> combine_blocks comms (InBlock ch1 v # blks1) blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim3a:
  "combine_blocks comms (InBlock ch1 v # blks1) [] blks \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   (\<And>blks'. blks = InBlock ch1 v # blks' \<Longrightarrow> combine_blocks comms blks1 [] blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim3b:
  "combine_blocks comms [] (OutBlock ch2 w # blks2) blks \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>blks'. blks = OutBlock ch2 w # blks' \<Longrightarrow> combine_blocks comms [] blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

text \<open>Wait cases\<close>
lemma combine_blocks_elim4a:
  "combine_blocks comms (WaitBlock d1 p1 rdy1 # blks1) (WaitBlock d2 p2 rdy2 # blks2) blks \<Longrightarrow>
   \<not>compat_rdy rdy1 rdy2 \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

subsection \<open>Tests for combine_blocks\<close>

lemma test_combine1:
  "combine_blocks {''ch''} [InBlock ''ch'' v] [OutBlock ''ch'' v] [IOBlock ''ch'' v]"
  by (intro combine_blocks.intros, auto)

lemma test_combine1_unique:
  "combine_blocks {''ch''} [InBlock ''ch'' v] [OutBlock ''ch'' v] blks \<Longrightarrow>
   blks = [IOBlock ''ch'' v]"
  by (auto elim: combine_blocks_elim1 combine_blocks_elim2)

lemma test_combine2:
  "combine_blocks {} [InBlock ''ch1'' v] [OutBlock ''ch2'' w] [InBlock ''ch1'' v, OutBlock ''ch2'' w]"
  by (intro combine_blocks.intros, auto)

lemma test_combine2_unique:
  "combine_blocks {} [InBlock ''ch1'' v] [OutBlock ''ch2'' w] blks \<Longrightarrow>
   blks = [InBlock ''ch1'' v, OutBlock ''ch2'' w] \<or>
   blks = [OutBlock ''ch2'' w, InBlock ''ch1'' v]"
  by (auto elim!: combine_blocks_elim3 combine_blocks_elim3a combine_blocks_elim3b
      combine_blocks_elim1)


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
| assignB: "big_step (Assign var e) s [] (s(var := e s))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (Seq p1 p2) s1 (tr1 @ tr2) s3"
| condB1: "b s1 \<Longrightarrow> big_step p1 s1 tr s2 \<Longrightarrow> big_step (Cond b p1 p2) s1 tr s2"
| condB2: "\<not> b s1 \<Longrightarrow> big_step p2 s1 tr s2 \<Longrightarrow> big_step (Cond b p1 p2) s1 tr s2"
| waitB: "big_step (Wait d) s [WaitBlock d (restrict (\<lambda>\<tau>. State s) {0..d}) ({}, {})] s"
| sendB1: "big_step (Cm (Send ch e)) s [OutBlock ch (e s)] s"
| sendB2: "d > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlock d (restrict (\<lambda>\<tau>. State s) {0..d}) ({ch}, {}),
             OutBlock ch (e s)] s"
| receiveB1: "big_step (Cm (Receive ch var)) s [InBlock ch v] (s(var := v))"
| receiveB2: "d > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlock d (restrict (\<lambda>\<tau>. State s) {0..d}) ({}, {ch}),
             InBlock ch v] (s(var := v))"
| IChoiceB1: "big_step p1 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| IChoiceB2: "big_step p2 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| EChoiceSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (OutBlock ch (e s1) # tr2) s2"
| EChoiceSendB2: "d > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlock d (restrict (\<lambda>\<tau>. State s1) {0..d}) (rdy_of_echoice cs) #
                              OutBlock ch (e s1) # tr2) s2"
| EChoiceReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (InBlock ch v # tr2) s2"
| EChoiceReceiveB2: "d > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlock d (restrict (\<lambda>\<tau>. State s1) {0..d}) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
     (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
     \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow>
     big_step (Cont ode b) s1 [WaitBlock d (restrict (\<lambda>\<tau>. State (p \<tau>)) {0..d}) ({}, {})] (p d)"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode cs) s1 (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 (p d) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode cs) s1 (WaitBlock d (restrict (\<lambda>\<tau>. State (p \<tau>)) {0..d}) (rdy_of_echoice cs) #
                                    OutBlock ch (e s) # tr) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode cs) s1 (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 ((p d)(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode cs) s1 (WaitBlock d (restrict (\<lambda>\<tau>. State (p \<tau>)) {0..d}) (rdy_of_echoice cs) #
                                    InBlock ch v # tr2) s2"

text \<open>Big-step semantics for parallel processes.\<close>

inductive par_big_step :: "pproc \<Rightarrow> gstate \<Rightarrow> trace \<Rightarrow> gstate \<Rightarrow> bool" where
  SingleB: "big_step p s1 tr s2 \<Longrightarrow> par_big_step (Single p) (State s1) tr (State s2)"
| ParallelB:
    "par_big_step p1 s11 tr1 s12 \<Longrightarrow>
     par_big_step p2 s12 tr2 s22 \<Longrightarrow>
     combine_blocks chs tr1 tr2 tr \<Longrightarrow>
     par_big_step (Parallel p1 chs p2) (ParState s11 s12) tr (ParState s12 s22)"

subsection \<open>More convenient version of rules\<close>

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

subsection \<open>Test of big-step semantics\<close>

text \<open>Send 1 immediately\<close>
lemma test1a: "big_step (Cm (''ch''[!](\<lambda>_. 1)))
  (\<lambda>_. 0) [OutBlock ''ch'' 1] (\<lambda>_. 0)"
  by (rule sendB1)

text \<open>Send x + 1 immediately\<close>
lemma test1b: "big_step (Cm (''ch''[!](\<lambda>s. s X + 1)))
  ((\<lambda>_. 0)(X := 1)) [OutBlock ''ch'' 2] ((\<lambda>_. 0)(X := 1))"
  by (rule sendB1', auto)

text \<open>Send 1 after delay 2\<close>
lemma test1c: "big_step (Cm (''ch''[!](\<lambda>_. 1)))
  (\<lambda>_. 0) [WaitBlock 2 (restrict (\<lambda>_. State (\<lambda>_. 0)) {0..2}) ({''ch''}, {}),
           OutBlock ''ch'' 1] (\<lambda>_. 0)"
  by (rule sendB2, auto)

text \<open>Receive 1 immediately\<close>
lemma test2a: "big_step (Cm (''ch''[?]X))
  (\<lambda>_. 0) [InBlock ''ch'' 1] ((\<lambda>_. 0)(X := 1))"
  by (rule receiveB1)

text \<open>Receive 1 after delay 2\<close>
lemma test2b: "big_step (Cm (''ch''[?]X))
  (\<lambda>_. 0) [WaitBlock 2 (restrict (\<lambda>_. State (\<lambda>_. 0)) {0..2}) ({}, {''ch''}),
           InBlock ''ch'' 1] ((\<lambda>_. 0)(X := 1))"
  by (rule receiveB2, auto)

text \<open>Communication\<close>
lemma test3: "par_big_step (
  Parallel (Single (Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
           (Single (Cm (''ch''[?]X))))
  (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [IOBlock ''ch'' 1]
  (ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test1a])
   apply (rule SingleB[OF test2a])
  by (auto intro: combine_blocks.intros)

text \<open>Wait\<close>
lemma test4: "big_step (Wait 2)
  (\<lambda>_. 0) [WaitBlock 2 (restrict (\<lambda>_. State (\<lambda>_. 0)) {0..2}) ({}, {})] (\<lambda>_. 0)"
  by (rule waitB)

text \<open>Seq\<close>
lemma test5: "big_step (Wait 2; Cm (''ch''[!](\<lambda>_. 1)))
  (\<lambda>_. 0) [WaitBlock 2 (restrict (\<lambda>_. State (\<lambda>_. 0)) {0..2}) ({}, {}), OutBlock ''ch'' 1] (\<lambda>_. 0)"
  by (rule seqB'[OF test4 test1a], auto)

text \<open>Communication after delay 2\<close>
lemma test6: "par_big_step (
  Parallel (Single (Wait 2; Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
           (Single (Cm (''ch''[?]X))))
  (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [WaitBlock 2 (restrict (\<lambda>_. ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0))) {0..2}) ({}, {''ch''}), IOBlock ''ch'' 1]
  (ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test5])
   apply (rule SingleB[OF test2b])
  by (auto intro!: combine_blocks.intros)

text \<open>Loop one time\<close>
lemma test7: "big_step (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X))))
  (\<lambda>_. 0) [OutBlock ''ch'' 1] ((\<lambda>_. 0)(X := 1))"
  apply (rule RepetitionB2)
    apply (rule seqB) apply (rule assignB) apply (rule sendB1)
  apply auto[1] apply (rule RepetitionB1)
  by auto

text \<open>Loop two times\<close>
lemma test8: "big_step (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X))))
  (\<lambda>_. 0) [OutBlock ''ch'' 1, OutBlock ''ch'' 2] ((\<lambda>_. 0)(X := 2))"
  apply (rule RepetitionB2)
    apply (rule seqB) apply (rule assignB) apply (rule sendB1)
   apply auto[1] apply (rule RepetitionB2)
     apply (rule seqB) apply (rule assignB) apply (rule sendB1)
    apply auto[1] apply (rule RepetitionB1)
  by auto

text \<open>External choice 1\<close>
lemma test9a: "big_step (EChoice [(''ch1''[!](\<lambda>_. 1), Wait 1),
                                  (''ch2''[!](\<lambda>_. 2), Wait 2)])
  (\<lambda>_. 0) [OutBlock ''ch1'' 1, WaitBlock 1 (restrict (\<lambda>_. State (\<lambda>_. 0)) {0..1}) ({}, {})] (\<lambda>_. 0)"
  apply (rule EChoiceSendB1[where i=0])
  apply auto by (rule waitB)

text \<open>External choice 2\<close>
lemma test9b: "big_step (EChoice [(''ch1''[!](\<lambda>_. 1), Wait 1),
                                  (''ch2''[!](\<lambda>_. 2), Wait 2)])
  (\<lambda>_. 0) [OutBlock ''ch2'' 2, WaitBlock 2 (restrict (\<lambda>_. State (\<lambda>_. 0)) {0..2}) ({}, {})] (\<lambda>_. 0)"
  apply (rule EChoiceSendB1[where i=1])
  apply auto by (rule waitB)

text \<open>Communication with external choice\<close>
lemma test10: "par_big_step (
  Parallel (Single (EChoice [(''ch1''[!](\<lambda>_. 1), Wait 1),
                             (''ch2''[!](\<lambda>_. 2), Wait 2)])) {''ch1'', ''ch2''}
           (Single (Cm (''ch1''[?]X); Wait 1)))
  (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [IOBlock ''ch1'' 1, WaitBlock 1 (restrict (\<lambda>_. ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1)))) {0..1}) ({}, {})]
  (ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test9a])
   apply (rule SingleB)
   apply (rule seqB) apply (rule receiveB1) apply (rule waitB)
  apply auto
  by (intro combine_blocks.intros, auto)

subsection \<open>Validity\<close>

type_synonym assn = "state \<Rightarrow> trace \<Rightarrow> bool"

definition Valid :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" where
  "Valid P c Q \<longleftrightarrow> (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step c s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

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

inductive_cases waitE: "big_step (Wait d) s1 tr s2"
thm waitE

inductive_cases echoiceE: "big_step (EChoice es) s1 tr s2"
thm echoiceE

inductive_cases ichoiceE: "big_step (IChoice p1 p2) s1 tr s2"
thm ichoiceE


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
    (Assign var e)
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
  "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (Seq c1 c2) R"
  unfolding Valid_def
  apply (auto elim!: seqE) by fastforce

theorem Valid_wait:
  "Valid
    (\<lambda>s tr. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {})]))
    (Wait d)
    Q"
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
  assumes "\<forall>i<length es.
    case (es ! i) of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. 
            Q s (tr @ [OutBlock ch (e s)]) \<and>
            (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)])))))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s tr.
            (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
            (\<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v])))))"
  shows "Valid P (EChoice es) R"
proof -
  have a: "R s2 (tr1 @ tr2)" if *: "P s1 tr1" "tr2 = OutBlock ch (e s1) # tr2a" "i < length es" "es ! i = (ch[!]e, p2)"
        "big_step p2 s1 tr2a s2"
      for s1 tr1 s2 tr2 i ch e p2 tr2a
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and> (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)])))"
      using *(3,4) by fastforce
    have 2: "Q s1 (tr1 @ [OutBlock ch (e s1)])"
      using 1(2) *(1) unfolding entails_def by auto
    have 3: "R s2 (tr1 @ [OutBlock ch (e s1)] @ tr2a)"
      using *(5) 1(1) 2 unfolding Valid_def by fastforce
    then show ?thesis
      using *(2) by auto
  qed
  have b: "R s2 (tr1 @ tr2)" if *: "P s1 tr1" "tr2 = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es) # OutBlock ch (e s1) # tr2a"
      "0 < d" "i < length es" "es ! i = (ch[!]e, p2)" "big_step p2 s1 tr2a s2"
    for s1 tr1 s2 tr2 d i ch e p2 tr2a
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and>
                     (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), OutBlock ch (e s)])))"
      using *(4,5) by fastforce
    have 2: "Q s1 (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es), OutBlock ch (e s1)])"
      using 1(2) *(1,3) unfolding entails_def by auto
    have 3: "R s2 (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es), OutBlock ch (e s1)] @ tr2a)"
      using *(6) 1(1) 2 unfolding Valid_def by fastforce
    then show ?thesis
      using *(2) by auto
  qed
  have c: "R s2 (tr1 @ tr2)" if *: "P s1 tr1" "tr2 = InBlock ch v # tr2a" "i < length es" "es ! i = (ch[?]var, p2)"
      "big_step p2 (s1(var := v)) tr2a s2"
    for s1 tr1 s2 tr2 i ch var p2 v tr2a
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
                      (\<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v])))"
      using *(3,4) by fastforce
    have 2: "Q (s1(var := v)) (tr1 @ [InBlock ch v])"
      using 1(2) *(1) unfolding entails_def by auto
    have 3: "R s2 (tr1 @ [InBlock ch v] @ tr2a)"
      using *(5) 1(1) 2 unfolding Valid_def by fastforce
    then show ?thesis
      using *(2) by auto
  qed
  have d: "R s2 (tr1 @ tr2)" if *: "P s1 tr1" "tr2 = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es) # InBlock ch v # tr2a"
      "0 < d" "i < length es" "es ! i = (ch[?]var, p2)" "big_step p2 (s1(var := v)) tr2a s2"
    for s1 tr1 s2 tr2 d i ch var p2 v tr2a
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
                      (\<forall>d>0. \<forall>v. Q (s(var := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) (rdy_of_echoice es), InBlock ch v])))"
      using *(4,5) by fastforce
    have 2: "Q (s1(var := v)) (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es), InBlock ch v])"
      using 1(2) *(1,3) unfolding entails_def by auto
    have 3: "R s2 (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s1) (rdy_of_echoice es), InBlock ch v] @ tr2a)"
      using *(6) 1(1) 2 unfolding Valid_def by fastforce
    then show ?thesis
      using *(2) by auto
  qed
  show ?thesis
    unfolding Valid_def apply auto
    apply (elim echoiceE) using a b c d by auto
qed


text \<open>Some special cases of EChoice\<close>
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
proof -
  have 0: "\<forall>i<length [(ch1[?]var1, p1), (ch2[?]var2, p2)].
       case [(ch1[?]var1, p1), (ch2[?]var2, p2)] ! i of
         (ch[!]e, p1) \<Rightarrow> P ch e p1
       | (ch[?]var, p1) \<Rightarrow> Q ch var p1" if assm0: "Q ch1 var1 p1" "Q ch2 var2 p2" for P Q
  proof -
    have "case comm of ch[!]e \<Rightarrow> P ch e p | ch[?]var \<Rightarrow> Q ch var p"
      if "i < Suc (Suc 0)" "[(ch1[?]var1, p1), (ch2[?]var2, p2)] ! i = (comm, p)" for comm p i
    proof -
      have "i = 0 \<or> i = 1"
        using that(1) by auto
      then show ?thesis
        apply (rule disjE)
        using that(2) assm0 by auto
    qed
    then show ?thesis
      by auto
  qed
  show ?thesis
    apply (rule Valid_echoice)
    apply (rule 0)
    subgoal apply (rule exI[where x=Q1])
      by (auto simp add: assms entails_def)
    apply (rule exI[where x=Q2])
    by (auto simp add: assms entails_def)
qed

subsection \<open>Validity for parallel programs\<close>

text \<open>Assertion on global state\<close>
type_synonym gs_assn = "gstate \<Rightarrow> bool"

text \<open>Assertion on global state and trace\<close>
type_synonym gassn = "gstate \<Rightarrow> trace \<Rightarrow> bool"

definition par_assn :: "gs_assn \<Rightarrow> gs_assn \<Rightarrow> gs_assn" where
  "par_assn P Q = (\<lambda>s. P (left_st s) \<and> Q (right_st s))"

definition sing_assn :: "fform \<Rightarrow> gs_assn" where
  "sing_assn P = (\<lambda>s. P (single_st s))"

definition pair_assn :: "fform \<Rightarrow> fform \<Rightarrow> gs_assn" where
  "pair_assn P Q = par_assn (sing_assn P) (sing_assn Q)"

definition ParValid :: "gs_assn \<Rightarrow> pproc \<Rightarrow> gassn \<Rightarrow> bool" where
  "ParValid P c Q \<longleftrightarrow> (\<forall>s1 s2 tr2. P s1 \<longrightarrow> par_big_step c s1 tr2 s2 \<longrightarrow> Q s2 tr2)"


inductive_cases SingleE: "par_big_step (Single p) s1 tr s2"
thm SingleE

inductive_cases ParallelE: "par_big_step (Parallel p1 ch p2) s1 tr s2"
thm ParallelE

lemma ParValid_Single:
  assumes "Valid P c Q"
  shows "ParValid (\<lambda>s. P (single_st s) []) (Single c) (\<lambda>s tr. Q (single_st s) tr)"
  using assms unfolding ParValid_def Valid_def
  by (metis SingleE append.monoid_axioms gstate.sel(1) monoid.left_neutral)

lemma ParValid_Parallel:
  assumes "ParValid P1 p1 Q1"
    and "ParValid P2 p2 Q2"
  shows "ParValid (\<lambda>s. P1 (left_st s) \<and> P2 (right_st s))
          (Parallel p1 chs p2)
         (\<lambda>s tr. \<exists>tr1 tr2. Q1 (left_st s) tr1 \<and> Q2 (right_st s) tr2 \<and> combine_blocks chs tr1 tr2 tr)"
proof -
  have *: "\<exists>tr1 tr2a. Q1 (left_st s2) tr1 \<and> Q2 (right_st s2) tr2a \<and> combine_blocks chs tr1 tr2a ([] @ tr2)"
    if "P1 (left_st s1)"
       "P2 (right_st s1)"
       "par_big_step p1 (left_st s1) tr1a (left_st s2)"
       "par_big_step p2 (right_st s1) tr2a (right_st s2)"
       "combine_blocks chs tr1a tr2a tr2" for s1 s2 tr2 tr1a tr2a
  proof -
    have 1: "Q1 (left_st s2) tr1a"
      using that(1,3) assms(1) unfolding ParValid_def by force
    have 2: "Q2 (right_st s2) tr2a"
      using that(2,4) assms(2) unfolding ParValid_def by force
    show ?thesis
      apply (rule exI[where x=tr1a])
      apply (rule exI[where x=tr2a])
      by (auto simp add: that(5) 1 2)
  qed
  show ?thesis
    unfolding ParValid_def apply clarify
    apply (elim ParallelE)
    using * by (metis ParValid_def assms(1) assms(2) gstate.sel(2) gstate.sel(3))
qed

lemma ParValid_Parallel':
  assumes "ParValid P1 p1 Q1"
    and "ParValid P2 p2 Q2"
    and "\<And>s. P s \<Longrightarrow> P1 (left_st s) \<and> P2 (right_st s)"
    and "\<And>s tr. (\<exists>tr1 tr2. Q1 (left_st s) tr1 \<and> Q2 (right_st s) tr2 \<and> combine_blocks chs tr1 tr2 tr) \<Longrightarrow> Q s tr"
  shows "ParValid P (Parallel p1 chs p2) Q"
  using ParValid_Parallel[OF assms(1,2)]
  unfolding ParValid_def using assms(3,4) by blast


subsection \<open>Simple examples\<close>

text \<open>Send 1\<close>
lemma testHL1:
  "Valid
    (\<lambda>s tr. Q s (tr @ [OutBlock ''ch'' 1]) \<and>
            (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({''ch''}, {}), OutBlock ''ch'' 1])))
    (Cm (''ch''[!](\<lambda>_. 1)))
    Q"
  by (rule Valid_send)

text \<open>This implies the strongest postcondition form\<close>
lemma testHL1':
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> tr = [])
    (Cm (''ch''[!](\<lambda>_. 1)))
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and>
            (tr = [OutBlock ''ch'' 1] \<or>
             (\<exists>d>0. tr = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (\<lambda>_. 0)) ({''ch''}, {}), OutBlock ''ch'' 1])))"
  apply (rule Valid_weaken_pre)
   prefer 2
   apply (rule Valid_send)
  unfolding entails_def by auto

text \<open>Send 1, then send 2\<close>
lemma testHL2:
  "Valid
    (\<lambda>s tr. (Q s ((tr @ [OutBlock ''ch'' 1]) @ [OutBlock ''ch'' 2]) \<and>
             (\<forall>d>0. Q s ((tr @ [OutBlock ''ch'' 1]) @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({''ch''}, {}), OutBlock ''ch'' 2]))) \<and>
            (\<forall>d>0. Q s ((tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({''ch''}, {}), OutBlock ''ch'' 1]) @ [OutBlock ''ch'' 2]) \<and>
             (\<forall>da>0. Q s ((tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({''ch''}, {}), OutBlock ''ch'' 1]) @
                           [WaitBlock da (\<lambda>\<tau>\<in>{0..da}. State s) ({''ch''}, {}), OutBlock ''ch'' 2]))))
    (Cm (''ch''[!](\<lambda>_. 1)); Cm (''ch''[!](\<lambda>_. 2)))
    Q"
  apply (rule Valid_seq)
    prefer 2 apply (rule Valid_send)
  by (rule Valid_send)

text \<open>Receive from ch\<close>
lemma testHL3:
  "Valid
    (\<lambda>s tr.
        (\<forall>v. Q (s(X := v)) (tr @ [InBlock ''ch'' v])) \<and>
        (\<forall>d>0. \<forall>v. Q (s(X := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {''ch''}), InBlock ''ch'' v])))
    (Cm (''ch''[?]X))
    Q"
  by (rule Valid_receive)

text \<open>Strongest postcondition form\<close>
lemma testHL3':
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> tr = [])
    (Cm (''ch''[?]X))
    (\<lambda>s tr. (\<exists>v. s = ((\<lambda>_. 0)(X := v)) \<and>
              (tr = [InBlock ''ch'' v]) \<or>
               (\<exists>d>0. tr = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (\<lambda>_. 0)) ({}, {''ch''}), InBlock ''ch'' v])))"
  apply (rule Valid_weaken_pre)
   prefer 2
   apply (rule testHL3)
  unfolding entails_def by auto

text \<open>Communication\<close>
lemma testHL4:
  "ParValid
    (pair_assn (\<lambda>s. s = (\<lambda>_. 0)) (\<lambda>s. s = (\<lambda>_. 0)))
    (Parallel (Single (Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
              (Single (Cm (''ch''[?]X))))
    (\<lambda>s tr. pair_assn (\<lambda>s. s = (\<lambda>_. 0)) (\<lambda>s. s = ((\<lambda>_. 0)(X := 1))) s \<and> tr = [IOBlock ''ch'' 1])"
  apply (rule ParValid_Parallel')
     apply (rule ParValid_Single[OF testHL1'])
    apply (rule ParValid_Single[OF testHL3'])
   apply (auto simp add: entails_def pair_assn_def par_assn_def sing_assn_def)
  by (auto elim!: combine_blocks_elim1 combine_blocks_elim2a combine_blocks_elim2b
                  combine_blocks_elim2e combine_blocks_elim4a)
  

subsection \<open>Standard assertions\<close>

definition entails_tassn :: "tassn \<Rightarrow> tassn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>t" 25) where
  "(P \<Longrightarrow>\<^sub>t Q) \<longleftrightarrow> (\<forall>tr. P tr \<longrightarrow> Q tr)"

lemma entails_tassn_trans:
  "(P \<Longrightarrow>\<^sub>t Q) \<Longrightarrow> (Q \<Longrightarrow>\<^sub>t R) \<Longrightarrow> (P \<Longrightarrow>\<^sub>t R)"
  unfolding entails_tassn_def by auto

definition and_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<and>\<^sub>A" 35) where
  "(P \<and>\<^sub>A Q) = (\<lambda>tr. P tr \<and> Q tr)"

definition emp_assn :: "tassn" ("emp\<^sub>A") where
  "emp\<^sub>A = (\<lambda>tr. tr = [])"

definition join_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixl "@\<^sub>t" 65) where
  "P @\<^sub>t Q = (\<lambda>tr. \<exists>tr1 tr2. P tr1 \<and> Q tr2 \<and> tr = tr1 @ tr2)"

definition magic_wand_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "@-" 65) where
  "Q @- P = (\<lambda>tr. \<forall>tr1. Q tr1 \<longrightarrow> P (tr @ tr1))"

definition all_assn :: "(real \<Rightarrow> tassn) \<Rightarrow> tassn" (binder "\<forall>\<^sub>A" 10) where
  "(\<forall>\<^sub>A v. P v) = (\<lambda>tr. \<forall>v. P v tr)"

inductive out_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> tassn" ("Out\<^sub>A") where
  "Out\<^sub>A s ch v [OutBlock ch v]"
| "d > 0 \<Longrightarrow> Out\<^sub>A s ch v [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({ch}, {}), OutBlock ch v]"

inductive in_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> tassn" ("In\<^sub>A") where
  "In\<^sub>A s ch v [InBlock ch v]"
| "d > 0 \<Longrightarrow> In\<^sub>A s ch v [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {ch}), InBlock ch v]"

lemma emp_unit_left [simp]:
  "(emp\<^sub>A @\<^sub>t P) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma emp_unit_right [simp]:
  "(P @\<^sub>t emp\<^sub>A) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma entails_mp_emp:
  "emp\<^sub>A \<Longrightarrow>\<^sub>t P @- P"
  unfolding entails_tassn_def emp_assn_def magic_wand_assn_def by auto

lemma entails_mp:
  "Q \<Longrightarrow>\<^sub>t P @- (Q @\<^sub>t P)"
  unfolding entails_tassn_def magic_wand_assn_def join_assn_def by auto

lemma magic_wand_mono:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> (R @- P) \<Longrightarrow>\<^sub>t (R @- Q)"
  unfolding entails_tassn_def magic_wand_assn_def by auto

theorem Valid_send':
  "Valid
    (\<lambda>s. ((Out\<^sub>A s ch (e s)) @- P s))
    (Cm (ch[!]e))
    P"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send)
  unfolding entails_def magic_wand_assn_def
  by (auto intro: out_assn.intros)

theorem Valid_receive':
  "Valid
    (\<lambda>s. \<forall>\<^sub>A v. ((In\<^sub>A s ch v) @- P (s(var := v))))
    (Cm (ch[?]var))
    P"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def magic_wand_assn_def all_assn_def
  by (auto intro: in_assn.intros)

lemma combine_assn_elim2:
  "combine_blocks comms tr1 tr2 tr \<Longrightarrow>
   Out\<^sub>A s1 ch v tr1 \<Longrightarrow>
   In\<^sub>A s2 ch w tr2 \<Longrightarrow>
   ch \<in> comms \<Longrightarrow>
   (\<And>blks'. w = v \<Longrightarrow> tr = [IOBlock ch v] \<Longrightarrow> P) \<Longrightarrow> P"
  apply (simp only: out_assn.simps in_assn.simps)
  apply (auto elim!: combine_blocks_elim1 combine_blocks_elim2a combine_blocks_elim2b
                     combine_blocks_elim2e combine_blocks_elim4a )
  by (simp add: combine_blocks_elim1)

subsection \<open>Simple examples redone\<close>

text \<open>Send 1\<close>
lemma testHL1s:
  "Valid
    (\<lambda>s. ((Out\<^sub>A s ''ch'' 1) @- P s))
    (Cm (''ch''[!](\<lambda>_. 1)))
    P"
  by (rule Valid_send')

text \<open>Strongest postcondition form\<close>
lemma testHL1s':
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> P tr)
    (Cm (''ch''[!](\<lambda>_. 1)))
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> (P @\<^sub>t Out\<^sub>A s ''ch'' 1) tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule testHL1s)
  unfolding entails_def apply simp
  unfolding entails_tassn_def[symmetric]
  by (auto simp add: entails_mp)

text \<open>Send 1, then send 2\<close>
lemma testHL2s:
  "Valid
    (\<lambda>s. Out\<^sub>A s ''ch'' 1 @- Out\<^sub>A s ''ch'' 2 @- P s)
    (Cm (''ch''[!](\<lambda>_. 1)); Cm (''ch''[!](\<lambda>_. 2)))
    P"
  apply (rule Valid_seq)
    prefer 2 apply (rule Valid_send')
  by (rule Valid_send')

text \<open>Strongest postcondition form\<close>
lemma testHL2s':
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> P tr)
    (Cm (''ch''[!](\<lambda>_. 1)); Cm (''ch''[!](\<lambda>_. 2)))
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> (P @\<^sub>t (Out\<^sub>A s ''ch'' 1) @\<^sub>t (Out\<^sub>A s ''ch'' 2)) tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule testHL2s)
  unfolding entails_def apply simp
  unfolding entails_tassn_def[symmetric]
  apply (rule entails_tassn_trans)
   prefer 2 
   apply (rule magic_wand_mono)
  apply (rule entails_mp) by (rule entails_mp)

text \<open>Receive from ch\<close>
lemma testHL3s:
  "Valid
    (\<lambda>s. \<forall>\<^sub>Av. In\<^sub>A s ''ch'' v @- P (s(X := v)))
    (Cm (''ch''[?]X))
    P"
  by (rule Valid_receive')

text \<open>Strongest postcondition form\<close>
lemma testHL3s':
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> P tr)
    (Cm (''ch''[?]X))
    (\<lambda>s tr. \<exists>v. s = ((\<lambda>_. 0)(X := v)) \<and> (P @\<^sub>t In\<^sub>A (\<lambda>_. 0) ''ch'' v) tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule testHL3s)
  unfolding entails_def
  by (auto simp add: all_assn_def magic_wand_assn_def emp_assn_def join_assn_def)

text \<open>Receive two values in a row\<close>
lemma testHL3a:
  "Valid
    ((\<lambda>s. \<forall>\<^sub>Av. In\<^sub>A s ''ch'' v @- (\<forall>\<^sub>Aw. In\<^sub>A (s(X := v)) ''ch'' w @- P (s(X := w)))))
    (Cm (''ch''[?]X); Cm (''ch''[?]X))
    P"
  apply (rule Valid_weaken_pre) prefer 2
  apply (rule Valid_seq)
    prefer 2 apply (rule Valid_receive')
  apply (rule Valid_receive')
  by (auto simp add: entails_def)

text \<open>Strongest postcondition form\<close>
lemma testHL3a':
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> P tr)
    (Cm (''ch''[?]X); Cm (''ch''[?]X))
    (\<lambda>s tr. \<exists>v w. s = ((\<lambda>_. 0)(X := w)) \<and> (P @\<^sub>t In\<^sub>A (\<lambda>_. 0) ''ch'' v @\<^sub>t In\<^sub>A ((\<lambda>_. 0)(X := v)) ''ch'' w) tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_seq)
    prefer 2 apply (rule Valid_receive')
  apply (rule Valid_receive')
  unfolding entails_def
  by (fastforce simp add: all_assn_def emp_assn_def magic_wand_assn_def join_assn_def)


text \<open>Communication\<close>
lemma testHL4s:
  "ParValid
    (pair_assn (\<lambda>s. s = (\<lambda>_. 0)) (\<lambda>s. s = (\<lambda>_. 0)))
    (Parallel (Single (Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
              (Single (Cm (''ch''[?]X))))
    (\<lambda>s tr. pair_assn (\<lambda>s. s = (\<lambda>_. 0)) (\<lambda>s. s = ((\<lambda>_. 0)(X := 1))) s \<and> tr = [IOBlock ''ch'' 1])"
  apply (rule ParValid_Parallel')
     apply (rule ParValid_Single[OF testHL1s'[where P="emp\<^sub>A"]])
    apply (rule ParValid_Single[OF testHL3s'[where P="emp\<^sub>A"]])
   apply (auto simp add: entails_def pair_assn_def par_assn_def sing_assn_def)
  by (auto simp add: emp_assn_def elim!: combine_assn_elim2)


subsection \<open>Examples for loops\<close>

text \<open>First example simply counts up variable X.\<close>
fun count_up_inv :: "nat \<Rightarrow> tassn" where
  "count_up_inv 0 = emp\<^sub>A"
| "count_up_inv (Suc n) = count_up_inv n @\<^sub>t Out\<^sub>A ((\<lambda>_. 0)(X := real n)) ''ch'' n"

lemma testLoop1:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> count_up_inv a tr)
    (Rep (Cm (''ch''[!](\<lambda>s. s X)); Assign X (\<lambda>s. s X + 1)))
    (\<lambda>s tr. \<exists>n. n \<ge> a \<and> s = ((\<lambda>_. 0)(X := n)) \<and> count_up_inv n tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_weaken_pre)
  prefer 2
   apply (rule Valid_seq)
    prefer 2 apply (rule Valid_assign)
  apply (rule Valid_send')
  unfolding entails_def apply (auto simp add: magic_wand_assn_def)
  subgoal for tr n tr'
    apply (rule exI[where x="Suc n"])
    by (auto simp add: join_assn_def)
  done

text \<open>In each iteration, increment by 1, output, then increment by 2.\<close>
fun count_up3_inv1 :: "nat \<Rightarrow> tassn" where
  "count_up3_inv1 0 = emp\<^sub>A"
| "count_up3_inv1 (Suc n) = count_up3_inv1 n @\<^sub>t Out\<^sub>A ((\<lambda>_. 0)(X := 3 * real n + 1)) ''ch'' (3 * real n + 1)"

lemma testLoop2:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := 3 * a)) \<and> count_up3_inv1 a tr)
    (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X)); Assign X (\<lambda>s. s X + 2)))
    (\<lambda>s tr. \<exists>n. n \<ge> a \<and> s = ((\<lambda>_. 0)(X := 3 * n)) \<and> count_up3_inv1 n tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_weaken_pre)
    prefer 2 apply (rule Valid_seq)
     prefer 2 apply (rule Valid_seq)
      prefer 2 apply (rule Valid_assign)
     apply (rule Valid_send') apply (rule Valid_assign)
   apply (auto simp add: entails_def magic_wand_assn_def)
  subgoal for tr n tr'
    apply (rule exI[where x="Suc n"])
    by (auto simp add: join_assn_def)
  done


subsection \<open>Test cases for external choice\<close>

inductive inrdy_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Inrdy\<^sub>A") where
  "Inrdy\<^sub>A s ch v rdy [InBlock ch v]"
| "d > 0 \<Longrightarrow> Inrdy\<^sub>A s ch v rdy [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) rdy, InBlock ch v]"

text \<open>First, we restate the rule for Valid_echoice in simpler form\<close>
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

text \<open>Strongest postcondition form\<close>
lemma echoice_test1':
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> P tr)
    (EChoice [(''ch1''[?]X, Skip), (''ch2''[?]X, Skip)])
    (\<lambda>s tr. (\<exists>v. s = ((\<lambda>_. 0)(X := v)) \<and> (P @\<^sub>t Inrdy\<^sub>A (\<lambda>_. 0) ''ch1'' v ({}, {''ch1'', ''ch2''})) tr) \<or>
            (\<exists>v. s = ((\<lambda>_. 0)(X := v)) \<and> (P @\<^sub>t Inrdy\<^sub>A (\<lambda>_. 0) ''ch2'' v ({}, {''ch1'', ''ch2''})) tr))"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule echoice_test1)
  apply (auto simp add: entails_def and_assn_def magic_wand_assn_def join_assn_def all_assn_def)
  subgoal for tr v tr'
    apply (rule exI[where x=v])
    apply auto
    apply (rule exI[where x=tr])
    by auto
  done

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
    (\<lambda>s tr. s = (\<lambda>_. 0) \<and> P tr)
    (IChoice (Cm (''ch1''[?]X)) (Cm (''ch2''[?]X)))
    (\<lambda>s tr. (\<exists>v. s = ((\<lambda>_. 0)(X := v)) \<and> (P @\<^sub>t In\<^sub>A (\<lambda>_. 0) ''ch1'' v) tr) \<or>
            (\<exists>v. s = ((\<lambda>_. 0)(X := v)) \<and> (P @\<^sub>t In\<^sub>A (\<lambda>_. 0) ''ch2'' v) tr))"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule ichoice_test1)
  apply (auto simp add: entails_def and_assn_def magic_wand_assn_def join_assn_def all_assn_def)
  subgoal for tr v tr'
    apply (rule exI[where x=v])
    apply auto
    apply (rule exI[where x=tr])
    by auto
  done



end
