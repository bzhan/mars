theory BigStepSimple
  imports Analysis_More
begin

subsection \<open>Syntax\<close>

text \<open>State\<close>
type_synonym state = "char \<Rightarrow> real option"

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

datatype ODE =
  ODE "var \<Rightarrow> exp"

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


subsection \<open>Traces\<close>

text \<open>First, we define the concept of traces\<close>

datatype trace_block =
  InBlock cname real
  | OutBlock cname real
  | IOBlock cname real
  | WaitBlock time "real \<Rightarrow> state" rdy_info

type_synonym trace = "trace_block list"

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
   hist = restrict (\<lambda>\<tau>. hist1 \<tau> ++ hist2 \<tau>) {0..t} \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlock t hist1 rdy1 # blks1) (WaitBlock t hist2 rdy2 # blks2)
                  (WaitBlock t hist rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlock (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> - t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow>
   combine_blocks comms (WaitBlock t1 hist1 rdy1 # blks1) (WaitBlock t2 hist2 rdy2 # blks2)
                  (WaitBlock t1 (\<lambda>\<tau>. hist1 \<tau> ++ hist2 \<tau>) (merge_rdy rdy1 rdy2) # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlock (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> - t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow>
   combine_blocks comms (WaitBlock t1 hist1 rdy1 # blks1) (WaitBlock t2 hist2 rdy2 # blks2)
                  (WaitBlock t2 (\<lambda>\<tau>. hist1 \<tau> ++ hist2 \<tau>) (merge_rdy rdy1 rdy2) # blks)"

inductive_cases combine_blocksE1: "combine_blocks comms blks1 blks2 []"
thm combine_blocksE1

inductive_cases combine_blocksE2: "combine_blocks comms blks1 blks2 (IOBlock ch v # blks)"
thm combine_blocksE2

lemma combine_blocks_elim1:
  "combine_blocks comms [] [] blks \<Longrightarrow> blks = []"
  apply (induct rule: combine_blocks.cases)
  by auto

lemma combine_blocks_elim2:
  "combine_blocks comms (InBlock ch v # blks1) (OutBlock ch v # blks2) blks \<Longrightarrow>
   ch \<in> comms \<Longrightarrow>
   (\<And>blks'. blks = IOBlock ch v # blks' \<Longrightarrow> combine_blocks comms blks1 blks2 blks' \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (induct rule: combine_blocks.cases)
  by auto

lemma combine_blocks_elim3:
  "combine_blocks comms (InBlock ch1 v # blks1) (OutBlock ch2 w # blks2) blks \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>blks'. blks = InBlock ch1 v # blks' \<Longrightarrow> combine_blocks comms blks1 (OutBlock ch2 w # blks2) blks' \<Longrightarrow> P) \<Longrightarrow>
   (\<And>blks'. blks = OutBlock ch2 w # blks' \<Longrightarrow> combine_blocks comms (InBlock ch1 v # blks1) blks2 blks' \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (induct rule: combine_blocks.cases)
  by auto

lemma combine_blocks_elim3a:
  "combine_blocks comms (InBlock ch1 v # blks1) [] blks \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   (\<And>blks'. blks = InBlock ch1 v # blks' \<Longrightarrow> combine_blocks comms blks1 [] blks' \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (induct rule: combine_blocks.cases)
  by auto

lemma combine_blocks_elim3b:
  "combine_blocks comms [] (OutBlock ch2 w # blks2) blks \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>blks'. blks = OutBlock ch2 w # blks' \<Longrightarrow> combine_blocks comms [] blks2 blks' \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (induct rule: combine_blocks.cases)
  by auto


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
| assignB: "big_step (Assign var e) s [] (s(var := Some (e s)))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (Seq p1 p2) s1 (tr1 @ tr2) s3"
| condB1: "b s1 \<Longrightarrow> big_step p1 s1 tr s2 \<Longrightarrow> big_step (Cond b p1 p2) s1 tr s2"
| condB2: "\<not> b s1 \<Longrightarrow> big_step p2 s1 tr s2 \<Longrightarrow> big_step (Cond b p1 p2) s1 tr s2"
| waitB: "big_step (Wait d) s [WaitBlock d (restrict (\<lambda>\<tau>. s) {0..d}) ({}, {})] s"
| sendB1: "big_step (Cm (Send ch e)) s [OutBlock ch (e s)] s"
| sendB2: "d > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlock d (restrict (\<lambda>\<tau>. s) {0..d}) ({ch}, {}),
             OutBlock ch (e s)] s"
| receiveB1: "big_step (Cm (Receive ch var)) s [InBlock ch v] (s(var := Some v))"
| receiveB2: "d > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlock d (restrict (\<lambda>\<tau>. s) {0..d}) ({}, {ch}),
             InBlock ch v] (s(var := Some v))"
| IChoiceB1: "big_step p1 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| IChoiceB2: "big_step p2 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| EChoiceSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (OutBlock ch (e s1) # tr2) s2"
| EChoiceSendB2: "d > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlock d (restrict (\<lambda>\<tau>. s1) {0..d}) (rdy_of_echoice cs) #
                              OutBlock ch (e s1) # tr2) s2"
| EChoiceReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := Some v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (InBlock ch v # tr2) s2"
| EChoiceReceiveB2: "d > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := Some v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlock d (restrict (\<lambda>\<tau>. s1) {0..d}) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
     (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
     \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow>
     big_step (Cont ode b) s1 [WaitBlock d (restrict p {0..d}) ({}, {})] (p d)"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode cs) s1 (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 (p d) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode cs) s1 (WaitBlock d (restrict p {0..d}) (rdy_of_echoice cs) #
                                    OutBlock ch (e s) # tr) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := Some v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode cs) s1 (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 ((p d)(var := Some v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode cs) s1 (WaitBlock d (restrict p {0..d}) (rdy_of_echoice cs) #
                                    InBlock ch v # tr2) s2"

text \<open>Big-step semantics for parallel processes.\<close>

inductive par_big_step :: "pproc \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  SingleB: "big_step p s1 tr s2 \<Longrightarrow> par_big_step (Single p) s1 tr s2"
| ParallelB: "par_big_step p1 s11 tr1 s12 \<Longrightarrow> par_big_step p2 s21 tr2 s22 \<Longrightarrow>
    combine_blocks chs tr1 tr2 tr \<Longrightarrow>
    par_big_step (Parallel p1 chs p2) (s11 ++ s21) tr (s12 ++ s22)"

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

lemma ParallelB':
  assumes "big_step p1 s11 tr1 s12"
    and "big_step p2 s21 tr2 s22"
    and "combine_blocks chs tr1 tr2 tr"
    and "s1 = s11 ++ s21"
    and "s2 = s12 ++ s22"
  shows "par_big_step (Parallel (Single p1) chs (Single p2)) s1 tr s2"
  unfolding assms(4,5)
  using assms(1-3) by (auto intro: ParallelB SingleB)

subsection \<open>Test of big-step semantics\<close>

text \<open>Send 1 immediately\<close>
lemma test1a: "big_step (Cm (''ch''[!](\<lambda>_. 1)))
  Map.empty [OutBlock ''ch'' 1] Map.empty"
  by (rule sendB1)

text \<open>Send x + 1 immediately\<close>
lemma test1b: "big_step (Cm (''ch''[!](\<lambda>s. the (s X) + 1)))
  ([X \<mapsto> 1]) [OutBlock ''ch'' 2] ([X \<mapsto> 1])"
  by (rule sendB1', auto)

text \<open>Send 1 after delay 2\<close>
lemma test1c: "big_step (Cm (''ch''[!](\<lambda>_. 1)))
  Map.empty [WaitBlock 2 (restrict (\<lambda>_. Map.empty) {0..2}) ({''ch''}, {}),
             OutBlock ''ch'' 1] Map.empty"
  by (rule sendB2, auto)

text \<open>Receive 1 immediately\<close>
lemma test2a: "big_step (Cm (''ch''[?]X))
  Map.empty [InBlock ''ch'' 1] ([X \<mapsto> 1])"
  by (rule receiveB1)

text \<open>Receive 1 after delay 2\<close>
lemma test2b: "big_step (Cm (''ch''[?]X))
  Map.empty [WaitBlock 2 (restrict (\<lambda>_. Map.empty) {0..2}) ({}, {''ch''}),
             InBlock ''ch'' 1] ([X \<mapsto> 1])"
  by (rule receiveB2, auto)

text \<open>Communication\<close>
lemma test3: "par_big_step (
  Parallel (Single (Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
           (Single (Cm (''ch''[?]X))))
  Map.empty [IOBlock ''ch'' 1] ([X \<mapsto> 1])"
  apply (rule ParallelB'[OF test1a test2a])
  by (intro combine_blocks.intros, auto)

text \<open>Wait\<close>
lemma test4: "big_step (Wait 2)
  Map.empty [WaitBlock 2 (restrict (\<lambda>_. Map.empty) {0..2}) ({}, {})] Map.empty"
  by (rule waitB)

text \<open>Seq\<close>
lemma test5: "big_step (Wait 2; Cm (''ch''[!](\<lambda>_. 1)))
  Map.empty [WaitBlock 2 (restrict (\<lambda>_. Map.empty) {0..2}) ({}, {}), OutBlock ''ch'' 1] Map.empty"
  by (rule seqB'[OF test4 test1a], auto)

text \<open>Communication after delay 2\<close>
lemma test6: "par_big_step (
  Parallel (Single (Wait 2; Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
           (Single (Cm (''ch''[?]X))))
  Map.empty [WaitBlock 2 (restrict (\<lambda>_. Map.empty) {0..2}) ({}, {''ch''}), IOBlock ''ch'' 1] ([X \<mapsto> 1])"
  apply (rule ParallelB'[OF test5 test2b])
  by (auto intro!: combine_blocks.intros)

text \<open>Loop one time\<close>

lemma test7: "big_step (Rep (Assign X (\<lambda>s. the (s X) + 1); Cm (''ch''[!](\<lambda>s. the (s X)))))
  ([X \<mapsto> 0]) [OutBlock ''ch'' 1] ([X \<mapsto> 1])"
  apply (rule RepetitionB2)
    apply (rule seqB) apply (rule assignB) apply (rule sendB1)
  apply auto[1] apply (rule RepetitionB1)
  by auto

text \<open>Loop two times\<close>
lemma test8: "big_step (Rep (Assign X (\<lambda>s. the (s X) + 1); Cm (''ch''[!](\<lambda>s. the (s X)))))
  ([X \<mapsto> 0]) [OutBlock ''ch'' 1, OutBlock ''ch'' 2] ([X \<mapsto> 2])"
  apply (rule RepetitionB2)
    apply (rule seqB) apply (rule assignB) apply (rule sendB1)
   apply auto[1] apply (rule RepetitionB2)
     apply (rule seqB) apply (rule assignB) apply (rule sendB1)
    apply auto[1] apply (rule RepetitionB1)
  by auto

text \<open>External choice 1\<close>
lemma test9a: "big_step (EChoice [(''ch1''[!](\<lambda>_. 1), Wait 1),
                                  (''ch2''[!](\<lambda>_. 2), Wait 2)])
  Map.empty [OutBlock ''ch1'' 1, WaitBlock 1 (restrict (\<lambda>_. Map.empty) {0..1}) ({}, {})] Map.empty"
  apply (rule EChoiceSendB1[where i=0])
  apply auto by (rule waitB)

text \<open>External choice 2\<close>
lemma test9b: "big_step (EChoice [(''ch1''[!](\<lambda>_. 1), Wait 1),
                                  (''ch2''[!](\<lambda>_. 2), Wait 2)])
  Map.empty [OutBlock ''ch2'' 2, WaitBlock 2 (restrict (\<lambda>_. Map.empty) {0..2}) ({}, {})] Map.empty"
  apply (rule EChoiceSendB1[where i=1])
  apply auto by (rule waitB)

text \<open>Communication with external choice\<close>
lemma test10: "par_big_step (
  Parallel (Single (EChoice [(''ch1''[!](\<lambda>_. 1), Wait 1),
                             (''ch2''[!](\<lambda>_. 2), Wait 2)])) {''ch1'', ''ch2''}
           (Single (Cm (''ch1''[?]X); Wait 1)))
  Map.empty [IOBlock ''ch1'' 1, WaitBlock 1 (restrict (\<lambda>_. [X \<mapsto> 1]) {0..1}) ({}, {})] [X \<mapsto> 1]"
  apply (rule ParallelB'[OF test9a])
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
    (\<lambda>s tr. Q (s(var \<mapsto> e s)) tr)
    (Assign var e)
    Q"
  unfolding Valid_def
  by (auto elim: assignE)

theorem Valid_send:
  "Valid
    (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and>
        (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) ({ch}, {}), OutBlock ch (e s)])))
    (Cm (ch[!]e))
    Q"
  unfolding Valid_def
  by (auto elim: sendE)

theorem Valid_receive:
  "Valid
    (\<lambda>s tr. (\<forall>v. Q (s(var := Some v)) (tr @ [InBlock ch v])) \<and>
        (\<forall>d>0. \<forall>v. Q (s(var := Some v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) ({}, {ch}), InBlock ch v])))
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
    (\<lambda>s tr. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) ({}, {})]))
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

theorem Valid_echoice:
  assumes "\<forall>i<length es.
    case (es ! i) of
      (ch[!]e, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s tr. 
            Q s (tr @ [OutBlock ch (e s)]) \<and>
            (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) (rdy_of_echoice es), OutBlock ch (e s)])))))
    | (ch[?]var, p2) \<Rightarrow>
        (\<exists>Q. Valid Q p2 R \<and> (P \<Longrightarrow>\<^sub>A (\<lambda>s tr.
            (\<forall>v. Q (s(var := Some v)) (tr @ [InBlock ch v])) \<and>
            (\<forall>d>0. \<forall>v. Q (s(var := Some v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) (rdy_of_echoice es), InBlock ch v])))))"
  shows "Valid P (EChoice es) R"
proof -
  have a: "R s2 (tr1 @ tr2)" if *: "P s1 tr1" "tr2 = OutBlock ch (e s1) # tr2a" "i < length es" "es ! i = (ch[!]e, p2)"
        "big_step p2 s1 tr2a s2"
      for s1 tr1 s2 tr2 i ch e p2 tr2a
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and> (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) (rdy_of_echoice es), OutBlock ch (e s)])))"
      using *(3,4) by fastforce
    have 2: "Q s1 (tr1 @ [OutBlock ch (e s1)])"
      using 1(2) *(1) unfolding entails_def by auto
    have 3: "R s2 (tr1 @ [OutBlock ch (e s1)] @ tr2a)"
      using *(5) 1(1) 2 unfolding Valid_def by fastforce
    then show ?thesis
      using *(2) by auto
  qed
  have b: "R s2 (tr1 @ tr2)" if *: "P s1 tr1" "tr2 = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s1) (rdy_of_echoice es) # OutBlock ch (e s1) # tr2a"
      "0 < d" "i < length es" "es ! i = (ch[!]e, p2)" "big_step p2 s1 tr2a s2"
    for s1 tr1 s2 tr2 d i ch e p2 tr2a
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and> (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) (rdy_of_echoice es), OutBlock ch (e s)])))"
      using *(4,5) by fastforce
    have 2: "Q s1 (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s1) (rdy_of_echoice es), OutBlock ch (e s1)])"
      using 1(2) *(1,3) unfolding entails_def by auto
    have 3: "R s2 (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s1) (rdy_of_echoice es), OutBlock ch (e s1)] @ tr2a)"
      using *(6) 1(1) 2 unfolding Valid_def by fastforce
    then show ?thesis
      using *(2) by auto
  qed
  have c: "R s2 (tr1 @ tr2)" if *: "P s1 tr1" "tr2 = InBlock ch v # tr2a" "i < length es" "es ! i = (ch[?]var, p2)"
      "big_step p2 (s1(var \<mapsto> v)) tr2a s2"
    for s1 tr1 s2 tr2 i ch var p2 v tr2a
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. (\<forall>v. Q (s(var := Some v)) (tr @ [InBlock ch v]) )\<and> (\<forall>d>0. \<forall>v. Q (s(var := Some v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) (rdy_of_echoice es), InBlock ch v])))"
      using *(3,4) by fastforce
    have 2: "Q (s1(var := Some v)) (tr1 @ [InBlock ch v])"
      using 1(2) *(1) unfolding entails_def by auto
    have 3: "R s2 (tr1 @ [InBlock ch v] @ tr2a)"
      using *(5) 1(1) 2 unfolding Valid_def by fastforce
    then show ?thesis
      using *(2) by auto
  qed
  have d: "R s2 (tr1 @ tr2)" if *: "P s1 tr1" "tr2 = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s1) (rdy_of_echoice es) # InBlock ch v # tr2a"
      "0 < d" "i < length es" "es ! i = (ch[?]var, p2)" "big_step p2 (s1(var \<mapsto> v)) tr2a s2"
    for s1 tr1 s2 tr2 d i ch var p2 v tr2a
  proof -
    from assms obtain Q where 1:
      "Valid Q p2 R"
      "P \<Longrightarrow>\<^sub>A (\<lambda>s tr. (\<forall>v. Q (s(var := Some v)) (tr @ [InBlock ch v]) )\<and> (\<forall>d>0. \<forall>v. Q (s(var := Some v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) (rdy_of_echoice es), InBlock ch v])))"
      using *(4,5) by fastforce
    have 2: "Q (s1(var \<mapsto> v)) (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s1) (rdy_of_echoice es), InBlock ch v])"
      using 1(2) *(1,3) unfolding entails_def by auto
    have 3: "R s2 (tr1 @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s1) (rdy_of_echoice es), InBlock ch v] @ tr2a)"
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
    (\<lambda>s tr. (\<forall>v. Q1 (s(var1 := Some v)) (tr @ [InBlock ch1 v])) \<and>
            (\<forall>d>0. \<forall>v. Q1 (s(var1 := Some v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) ({}, {ch1, ch2}), InBlock ch1 v])) \<and>
            (\<forall>v. Q2 (s(var2 := Some v)) (tr @ [InBlock ch2 v])) \<and>
            (\<forall>d>0. \<forall>v. Q2 (s(var2 := Some v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. s) ({}, {ch1, ch2}), InBlock ch2 v])))
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

end
