theory BigStep
  imports Complex_Main
    Ordinary_Differential_Equations.ODE_Analysis
begin

subsection \<open>Syntax\<close>

text \<open>State\<close>
type_synonym state = "string \<Rightarrow> real"

text \<open>Expressions\<close>
type_synonym exp = "state \<Rightarrow> real"

text \<open>Predicates\<close>
type_synonym fform = "state \<Rightarrow> bool"

text \<open>Channel names\<close>
type_synonym cname = string

text \<open>Time\<close>
type_synonym time = real

text \<open>Variable names\<close>
type_synonym var = string

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

text \<open>HCSP processes\<close>
datatype proc =
  Cm comm
| Skip
| Assign var exp             ("_ ::= _" [99,95] 94)
| Seq proc proc           ("_; _" [91,90] 90)
| Cond fform proc proc        ("IF _ _ _" [95,94] 93)
| Wait time  \<comment> \<open>Waiting for a specified amount of time\<close>
| IChoice "proc list"  \<comment> \<open>Nondeterminism\<close>
| EChoice "(comm \<times> proc) list"  \<comment> \<open>External choice\<close>

text \<open>Parallel of several HCSP processes\<close>
datatype pproc = PProc "proc list"

text \<open>Events\<close>
datatype event =
  Tau
| In cname real
| Out cname real 
| IO cname real 

text \<open>Two events are compatible if they are In-Out pairs.\<close>
fun compat :: "event \<Rightarrow> event \<Rightarrow> bool" where
  "compat Tau ev = False"
| "compat (In ch val) ev = (if ev = Out ch val then True else False)"
| "compat (Out ch val) ev = (if ev = In ch val then True else False)"
| "compat (IO ch val) ev = False"


(*
ch?1 to x at time 2, x := 2, ch!2 at 4

[Block 2 (\<lambda>t. if t = 2 then (\<lambda>_. 0)(x := 1) else (\<lambda>_. 0)) (In ''ch'' 1) ({}, {''ch''}),
 Block 0 _ Tau ({}, {}),
 Block 2 _ (Out ''ch'' 2) ({''ch''}, {})]

[Block 2 _ ... (Out ''ch'' 1) ({''ch''}, {}),
 ...]

*)
subsection \<open>Traces\<close>

text \<open>First, we define the concept of traces\<close>

text \<open>Time delay, ending state, and set of communications available at the interval\<close>
datatype trace_block = Block time history event rdy_info

text \<open>Starting state, blocks\<close>
datatype trace = Trace state "trace_block list"

fun delay_of_block :: "trace_block \<Rightarrow> time" where
  "delay_of_block (Block dly _ _ _) = dly"

fun history_of_block :: "trace_block \<Rightarrow> history" where
  "history_of_block (Block _ s _ _) = s"

fun end_of_block :: "trace_block \<Rightarrow> state" where
  "end_of_block (Block dly s _ _) = s dly"

fun event_of_block :: "trace_block \<Rightarrow> event" where
  "event_of_block (Block _ _ ev _) = ev"

fun rdy_of_block :: "trace_block \<Rightarrow> rdy_info" where
  "rdy_of_block (Block _ _ _ rdy) = rdy"

fun start_of_trace :: "trace \<Rightarrow> state" where
  "start_of_trace (Trace s _) = s"

fun blocks_of_trace :: "trace \<Rightarrow> trace_block list" where
  "blocks_of_trace (Trace _ blks) = blks"

fun end_of_trace :: "trace \<Rightarrow> state" where
  "end_of_trace (Trace s []) = s"
| "end_of_trace (Trace s blks) = end_of_block (last blks)"

fun extend_trace :: "trace \<Rightarrow> trace_block \<Rightarrow> trace" where
  "extend_trace (Trace s blks) blk = Trace s (blks @ [blk])"


text \<open>Now we define the ready set of a trace at any given time\<close>

fun rdy_of_blocks :: "trace_block list \<Rightarrow> time \<Rightarrow> rdy_info" where
  "rdy_of_blocks [] t = ({}, {})"
| "rdy_of_blocks ((Block dly _ _ rdy) # blks) t =
    (if 0 < t \<and> t < dly then rdy
     else if t \<le> dly then ({}, {})
     else rdy_of_blocks blks (t - dly))"

fun rdy_of_trace :: "trace \<Rightarrow> time \<Rightarrow> rdy_info" where
  "rdy_of_trace (Trace _ blks) t = rdy_of_blocks blks t"

text \<open>Whether two rdy_infos from different processes are compatible.\<close>
fun compat_rdy_pair :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy_pair (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

lemma compat_rdy_pair_sym:
  "compat_rdy_pair p1 p2 \<longleftrightarrow> compat_rdy_pair p2 p1"
  apply (cases p1) apply (cases p2) by auto

definition compat_rdy_block_pair :: "trace_block list \<Rightarrow> trace_block list \<Rightarrow> bool" where
  "compat_rdy_block_pair blks1 blks2 = (\<forall>t. compat_rdy_pair (rdy_of_blocks blks1 t) (rdy_of_blocks blks2 t))"

lemma compat_rdy_block_pair_sym:
  "compat_rdy_block_pair blks1 blks2 \<longleftrightarrow> compat_rdy_block_pair blks2 blks1"
  unfolding compat_rdy_block_pair_def 
  using compat_rdy_pair_sym by auto

fun compat_trace_pair :: "trace \<Rightarrow> trace \<Rightarrow> bool" where
  "compat_trace_pair (Trace _ blks1) (Trace _ blks2) = compat_rdy_block_pair blks1 blks2"

lemma compat_trace_pair_sym:
  "compat_trace_pair tr1 tr2 \<longleftrightarrow> compat_trace_pair tr2 tr1"
  by (metis compat_rdy_block_pair_sym compat_trace_pair.simps trace.exhaust)

definition compat_rdy_blocks :: "trace_block list list \<Rightarrow> bool" where
  "compat_rdy_blocks blkss = (\<forall>i<length blkss. \<forall>j<length blkss. i \<noteq> j \<longrightarrow> compat_rdy_block_pair (blkss ! i) (blkss ! j))"

lemma compat_rdy_blocks2:
  "compat_rdy_blocks [blks1, blks2] \<longleftrightarrow> compat_rdy_block_pair blks1 blks2"
  unfolding compat_rdy_blocks_def
  apply (auto simp add: less_Suc_eq)
  using compat_rdy_block_pair_sym by auto

text \<open>Main definition: compatibility between a list of traces.\<close>
definition compat_rdy :: "trace list \<Rightarrow> bool" where
  "compat_rdy trs = (\<forall>i<length trs. \<forall>j<length trs. i \<noteq> j \<longrightarrow> compat_trace_pair (trs ! i) (trs ! j))"


subsection \<open>Traces of parallel processes\<close>

datatype par_block = ParBlock time "history list" event

text \<open>ParTrace st pblks:
  st -- starting state for each process. Length is the number of processes.
  pblks -- list of parallel blocks.\<close>
datatype par_trace = ParTrace "state list" "par_block list"

text \<open>Now we define how to combine a list of traces for individual processes
  into a parallel trace.\<close>

text \<open>Given a delay time t and a block with time interval at least t,
  find the block starting at time t.

  Examples:
    wait_block 2 (In ''ch'' 1 after 5) = In ''ch'' 1 after 3.
\<close>
fun wait_block :: "time \<Rightarrow> trace_block \<Rightarrow> trace_block" where
  "wait_block t (Block dly s ev rdy) = Block (dly - t) (\<lambda>t'. s (t' + t)) ev rdy"

text \<open>Operate on a list of blocks. We assume that if the list is nonempty,
  then the first block has length at least t.\<close>
fun wait_blocks :: "time \<Rightarrow> trace_block list \<Rightarrow> trace_block list" where
  "wait_blocks t [] = []"
| "wait_blocks t (blk # blks) = wait_block t blk # blks"

text \<open>Given a delay time t and a block with time interval at least t,
  find the history at and before t.\<close>
fun start_block :: "time \<Rightarrow> trace_block \<Rightarrow> history" where
  "start_block t (Block dly s ev rdy) t' = (if t' \<le> t then s t' else s t)"

text \<open>Operate on a list of blocks. We assume that if the list is nonempty,
  then the first block has length at least t.\<close>
fun start_blocks :: "time \<Rightarrow> trace_block list \<Rightarrow> history" where
  "start_blocks t [] = (\<lambda>t'. undefined)"
| "start_blocks t (blk # blks) = start_block t blk"

text \<open>From a list of traces, delay every trace by t, and remove the first block
  from i'th trace. We assume that each trace is either empty or its first block
  has length at least t.\<close>
definition remove_one :: "nat \<Rightarrow> time \<Rightarrow> trace_block list list \<Rightarrow> trace_block list list" where
  "remove_one i t blkss = (
    let blkss' = map (wait_blocks t) blkss in
      blkss'[i := tl (blkss' ! i)])"

text \<open>From a list of traces, delay every trace by t, and remove the first block
  from i'th and j'th trace. We assume that each trace is either empty or its first
  block has length at least t.\<close>
definition remove_pair :: "nat \<Rightarrow> nat \<Rightarrow> time \<Rightarrow> trace_block list list \<Rightarrow> trace_block list list" where
  "remove_pair i j t blkss = (
    let blkss' = map (wait_blocks t) blkss in
      blkss'[i := tl (blkss' ! i), j := tl (blkss' ! j)])"

text \<open>Main definition: combining a list of block lists.
  combine_blocks blkss pblks means the list of block lists blkss can be combined
  together into pblks.\<close>
inductive combine_blocks :: "trace_block list list \<Rightarrow> par_block list \<Rightarrow> bool" where
  "\<forall>i<length blkss. blkss ! i = [] \<Longrightarrow> combine_blocks blkss []"  \<comment> \<open>empty case\<close>
  \<comment> \<open>Internal action at i'th process\<close>
| "i < length blkss \<Longrightarrow>
   \<comment> \<open>t \<ge> 0\<close>
   \<comment> \<open>\<forall>k<length blkss. blkss ! k \<noteq> [] \<longrightarrow> delay_of_block (hd (blkss ! k)) \<ge> t\<close>
   blkss ! i \<noteq> [] \<Longrightarrow>
   delay_of_block (hd (blkss ! i)) = t \<Longrightarrow>
   event_of_block (hd (blkss ! i)) = Tau \<Longrightarrow>
   combine_blocks (remove_one i t blkss) pblks \<Longrightarrow>
   block0 = map (start_blocks t) blkss \<Longrightarrow>
   combine_blocks blkss ((ParBlock t block0 Tau) # pblks)"
  \<comment> \<open>Communication between i'th and j'th process\<close>
| "i < length blkss \<Longrightarrow> j < length blkss \<Longrightarrow> i \<noteq> j \<Longrightarrow>
   \<comment> \<open>t \<ge> 0\<close>
   \<forall>k<length blkss. blkss ! k \<noteq> [] \<longrightarrow> delay_of_block (hd (blkss ! k)) \<ge> t \<Longrightarrow>
   blkss ! i \<noteq> [] \<Longrightarrow> blkss ! j \<noteq> [] \<Longrightarrow>
   delay_of_block (hd (blkss ! i)) = t \<Longrightarrow>
   delay_of_block (hd (blkss ! j)) = t \<Longrightarrow>
   event_of_block (hd (blkss ! i)) = In c v \<Longrightarrow>
   event_of_block (hd (blkss ! j)) = Out c v \<Longrightarrow>
   combine_blocks (remove_pair i j t blkss) pblks \<Longrightarrow>
   blockt = map (start_blocks t) blkss \<Longrightarrow>
   combine_blocks blkss ((ParBlock t blockt (IO c v)) # pblks)"

text \<open>Use the previous definition to combine a list of traces into a parallel trace.\<close>
inductive combine_par_trace :: "trace list \<Rightarrow> par_trace \<Rightarrow> bool" where
  "length trs = length sts \<Longrightarrow>
   \<forall>i<length trs. start_of_trace (trs ! i) = sts ! i \<Longrightarrow>
   combine_blocks (map blocks_of_trace trs) par_blks \<Longrightarrow>
   combine_par_trace trs (ParTrace sts par_blks)"


subsection \<open>External choice\<close>

text \<open>Compute list of ready communications for an external choice.\<close>
fun rdy_of_echoice :: "(comm \<times> proc) list \<Rightarrow> rdy_info" where
  "rdy_of_echoice [] = ({}, {})"
| "rdy_of_echoice ((Send ch e, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_echoice ((Receive ch var, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (fst rdy, insert ch (snd rdy)))"


subsection \<open>Big-step semantics\<close>

text \<open>Big-step semantics specifies for each command a mapping from trace to trace\<close>

text \<open>Extend by a send block\<close>
definition extend_send :: "cname \<Rightarrow> exp \<Rightarrow> time \<Rightarrow> rdy_info \<Rightarrow> trace \<Rightarrow> trace" where
  "extend_send ch e dly rdy tr =
    extend_trace tr (Block dly (\<lambda>t. end_of_trace tr) (Out ch (e (end_of_trace tr))) rdy)"

text \<open>Extend by a receive block\<close>
definition extend_receive :: "cname \<Rightarrow> var \<Rightarrow> time \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> trace \<Rightarrow> trace" where
  "extend_receive ch var dly v rdy tr =
    extend_trace tr (Block dly (\<lambda>t. if t \<ge> dly then (end_of_trace tr)(var := v) else end_of_trace tr)
                            (In ch v) ({}, {ch}))"

text \<open>Big-step semantics.
  big_step p tr tr2 means executing p starting at trace tr can end in trace tr2.
  This should imply that tr is a prefix of tr2.\<close>
inductive big_step :: "proc \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  \<comment> \<open>Send: dly \<ge> 0 is the amount of time waited at the current send.\<close>
  sendB: "big_step (Cm (Send ch e)) tr
    \<comment> \<open>dly \<ge> 0\<close>
    (extend_send ch e dly ({ch}, {}) tr)"
  \<comment> \<open>Receive: dly \<ge> 0 is the amount of time waited at the current receive.
      v is the value received.\<close>
| receiveB: "big_step (Cm (Receive ch var)) tr
    \<comment> \<open>dly \<ge> 0\<close>
    (extend_receive ch var dly v ({}, {ch}) tr)"
| skipB: "big_step Skip tr
    (extend_trace tr (Block 0 (\<lambda>t. end_of_trace tr) Tau ({}, {})))"
| assignB: "big_step (Assign var e) tr
    (extend_trace tr (Block 0 (\<lambda>t. (end_of_trace tr)(var := e (end_of_trace tr))) Tau ({}, {})))"
| seqB: "big_step p1 tr tr2 \<Longrightarrow>
   big_step p2 tr2 tr3 \<Longrightarrow> big_step (Seq p1 p2) tr tr3"
| condB1: "b (end_of_trace tr) \<Longrightarrow>
   big_step p1 tr tr2 \<Longrightarrow> big_step (Cond b p1 p2) tr tr2"
| condB2: "\<not> b (end_of_trace tr) \<Longrightarrow>
   big_step p2 tr tr2 \<Longrightarrow> big_step (Cond b p1 p2) tr tr2"
| waitB: "big_step (Wait d) tr
    (extend_trace tr (Block d (\<lambda>t. end_of_trace tr) Tau ({}, {})))"
| IChoiceB: "i < length ps \<Longrightarrow> big_step (ps ! i) tr tr2 \<Longrightarrow>
   big_step (IChoice ps) tr tr2"
  \<comment> \<open>cs is a list of comm \<times> proc elements.\<close>
(*
Trace 1: [Block 4 _ (In ch 1) ({ch2}, {ch})]
Trace 2: [Block 4 _ (Out ch 1) ({ch}, {})]     communicated with 1
Trace 3: [Delay 2, Block 2 _ (In ch2 2) ({}, {ch2})]    should communicate first
  then compat_rdy fails for time between 2 and 4.
*)
| EChoiceSendB: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
   big_step p2 (extend_send ch e dly (rdy_of_echoice cs) tr) tr3 \<Longrightarrow>
   big_step (EChoice cs) tr tr3"
| EChoiceReceiveB: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
   big_step p2 (extend_receive ch var dly v (rdy_of_echoice cs) tr) tr3 \<Longrightarrow>
   big_step (EChoice cs) tr tr3"

text \<open>Big-step semantics for parallel processes.\<close>
inductive par_big_step :: "pproc \<Rightarrow> par_trace \<Rightarrow> par_trace \<Rightarrow> bool" where
  parallelB: "length trs = length ps \<Longrightarrow> length trs2 = length ps \<Longrightarrow>
   \<forall>i<length ps. big_step (ps ! i) (trs ! i) (trs2 ! i) \<Longrightarrow>
   compat_rdy trs \<Longrightarrow> compat_rdy trs2 \<Longrightarrow>
   combine_par_trace trs par_tr \<Longrightarrow>
   combine_par_trace trs2 par_tr2 \<Longrightarrow>
   par_big_step (PProc ps) par_tr par_tr2"


subsection \<open>More convenient version of rules\<close>

lemma sendB2:
  assumes "blks' = blks @ [
      Block dly (\<lambda>t. end_of_trace (Trace s blks)) (Out ch (e (end_of_trace (Trace s blks)))) ({ch}, {})]"
  shows "big_step (Cm (Send ch e)) (Trace s blks) (Trace s blks')"
proof -
  have 1: "Trace s (blks @
        [Block dly (\<lambda>t. end_of_trace (Trace s blks))
          (Out ch (e (end_of_trace (Trace s blks)))) ({ch}, {})]) =
        extend_send ch e dly ({ch}, {}) (Trace s blks)"
    unfolding extend_send_def extend_trace.simps by auto
  show ?thesis
    apply (subst assms(1))
    apply (subst 1)
    by (rule sendB)
qed

lemma receiveB2:
  assumes "blks' = blks @ [
      Block dly (\<lambda>t. if t \<ge> dly then (end_of_trace (Trace s blks))(var := v) else end_of_trace (Trace s blks))
                            (In ch v) ({}, {ch})]"
  shows "big_step (Cm (Receive ch var)) (Trace s blks) (Trace s blks')"
proof -
  have 1: "Trace s (blks @
        [Block dly (\<lambda>t. if t \<ge> dly then (end_of_trace (Trace s blks))(var := v) else end_of_trace (Trace s blks))
          (In ch v) ({}, {ch})]) =
        extend_receive ch var dly v ({}, {ch}) (Trace s blks)"
    unfolding extend_receive_def extend_trace.simps by auto
  show ?thesis
    apply (subst assms(1))
    apply (subst 1)
    by (rule receiveB)
qed

lemma waitB2:
  assumes "blks' = blks @ [Block d (\<lambda>t. end_of_trace (Trace s blks)) Tau ({}, {})]"
  shows "big_step (Wait d) (Trace s blks) (Trace s blks')"
proof -
  have 1: "Trace s (blks @ [Block d (\<lambda>t. end_of_trace (Trace s blks)) Tau ({}, {})]) =
      (extend_trace (Trace s blks) (Block d (\<lambda>t. end_of_trace (Trace s blks)) Tau ({}, {})))"
    by auto
  show ?thesis
    apply (subst assms(1))
    apply (subst 1)
    by (rule waitB)
qed

lemma parallelB2:
  assumes "big_step ps1 tr11 tr12"
   "big_step ps2 tr21 tr22"
   "compat_trace_pair tr11 tr21"
   "compat_trace_pair tr12 tr22"
   "combine_par_trace [tr11, tr21] par_tr"
   "combine_par_trace [tr12, tr22] par_tr2"
  shows "par_big_step (PProc [ps1, ps2]) par_tr par_tr2"
  apply (rule parallelB[OF _ _ _ _ _ assms(5,6)])
  by (auto simp add: less_Suc_eq compat_rdy_def compat_trace_pair_sym assms)

subsection \<open>Test of big-step semantics\<close>

text \<open>Send 1 immediately\<close>
lemma test1a: "big_step (Cm (Send ''ch'' (\<lambda>_. 1)))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [Block 0 (\<lambda>_. \<lambda>_. 0) (Out ''ch'' 1) ({''ch''}, {})])"
  apply (rule sendB2)
  by simp

text \<open>Send x + 1 immediately\<close>
lemma test1b: "big_step (Cm (Send ''ch'' (\<lambda>s. s ''x'' + 1)))
        (Trace ((\<lambda>_. 0)(''x'' := 1)) [])
        (Trace ((\<lambda>_. 0)(''x'' := 1)) [Block 0 (\<lambda>_. ((\<lambda>_. 0)(''x'' := 1))) (Out ''ch'' 2) ({''ch''}, {})])"
  apply (rule sendB2)
  by simp

text \<open>Send 1 after delay 2\<close>
lemma test1c: "big_step (Cm (Send ''ch'' (\<lambda>_. 1)))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [Block 2 (\<lambda>_. \<lambda>_. 0) (Out ''ch'' 1) ({''ch''}, {})])"
  apply (rule sendB2)
  by simp

text \<open>Receive 1 immediately\<close>
lemma test2a: "big_step (Cm (Receive ''ch'' ''x''))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [Block 0 (\<lambda>t. if t \<ge> 0 then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0)) (In ''ch'' 1) ({}, {''ch''})])"
  apply (rule receiveB2)
  by auto

text \<open>Receive 1 after delay 2\<close>
lemma test2b: "big_step (Cm (Receive ''ch'' ''x''))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [Block 2 (\<lambda>t. if t \<ge> 2 then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0)) (In ''ch'' 1) ({}, {''ch''})])"
  apply (rule receiveB2)
  by auto

text \<open>Communication\<close>
lemma test3: "par_big_step (PProc [Cm (Send ''ch'' (\<lambda>_. 1)), Cm (Receive ''ch'' ''x'')])
        (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
        (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)]
          [ParBlock 0 [(\<lambda>_. \<lambda>_. 0), (\<lambda>t. if t \<ge> 0 then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0))] (IO ''ch'' 1)])"
proof -
  have 1: "combine_blocks [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)
  have 2: "combine_blocks
     [[Block 0 (\<lambda>_ _. 0) (Out ''ch'' 1) ({''ch''}, {})],
      [Block 0 (\<lambda>t. if 0 \<le> t then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0)) (In ''ch'' 1) ({}, {''ch''})]]
     ((ParBlock 0 [\<lambda>_ _. 0, \<lambda>t. if 0 \<le> t then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0)] (IO ''ch'' 1)) # [])"
    apply (rule combine_blocks.intros(3)[where i=1 and j=0])
    apply (auto simp add: less_Suc_eq)
    unfolding remove_pair_def Let_def apply auto
    by (rule 1)
  show ?thesis
    apply (rule parallelB2[OF test1a test2a])
    apply (auto simp add: compat_rdy_block_pair_def less_Suc_eq combine_par_trace.simps)
    using 1 2 by auto
qed

text \<open>Wait\<close>
lemma test4: "big_step (Wait 2)
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [Block 2 (\<lambda>_. \<lambda>_. 0) Tau ({}, {})])"
  apply (rule waitB2)
  by auto

text \<open>Seq\<close>
lemma test5: "big_step (Seq (Wait 2) (Cm (Send ''ch'' (\<lambda>_. 1))))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [Block 2 (\<lambda>_. \<lambda>_. 0) Tau ({}, {}),
                        Block 0 (\<lambda>_. \<lambda>_. 0) (Out ''ch'' 1) ({''ch''}, {})])"
  apply (rule seqB[OF test4])
  apply (rule sendB2)
  by auto

text \<open>Communication after delay 2\<close>
lemma test6: "par_big_step (PProc [
  Seq (Wait 2) (Cm (Send ''ch'' (\<lambda>_. 1))),
  Cm (Receive ''ch'' ''x'')])
    (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
    (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)]
      [ParBlock 2 [(\<lambda>_. \<lambda>_. 0), (\<lambda>t. if t \<ge> 2 then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0))] Tau,
       ParBlock 0 [(\<lambda>_. \<lambda>_. 0), (\<lambda>t. if t \<ge> 0 then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0))] (IO ''ch'' 1)])"
proof -
  have 1: "combine_blocks [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)
  have 2: "combine_blocks
     [[Block 2 (\<lambda>_ _. 0) Tau ({}, {}), Block 0 (\<lambda>_ _. 0) (Out ''ch'' 1) ({''ch''}, {})],
      [Block 2 (\<lambda>t. if 2 \<le> t then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0)) (In ''ch'' 1) ({}, {''ch''})]]
     [ParBlock 2 [\<lambda>_ _. 0, (\<lambda>t. if t \<ge> 2 then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0))] Tau,
      ParBlock 0 [\<lambda>_ _. 0, \<lambda>t. if 0 \<le> t then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0)] (IO ''ch'' 1)]"
    thm combine_blocks.intros(2)
    apply (rule combine_blocks.intros(2)[where i=0])
         apply (auto simp add: less_Suc_eq)
    unfolding remove_one_def Let_def apply auto
     apply (rule combine_blocks.intros(3)[where i=1 and j=0])
                apply (auto simp add: less_Suc_eq)
    unfolding remove_pair_def Let_def apply auto
    by (rule 1)
  show ?thesis
    apply (rule parallelB2[OF test5 test2b])
       apply (auto simp add: compat_rdy_block_pair_def less_Suc_eq combine_par_trace.simps)
    using 1 2 by auto
qed

subsection \<open>Validity\<close>

type_synonym assn = "trace \<Rightarrow> bool"

definition Valid :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" where
  "Valid P c Q \<longleftrightarrow> (\<forall>tr tr2. P tr \<longrightarrow> big_step c tr tr2 \<longrightarrow> Q tr2)"

theorem Valid_union:
  "\<forall>a\<in>S. Valid (P a) c (Q a) \<Longrightarrow> Valid (\<lambda>tr. \<exists>a\<in>S. P a tr) c (\<lambda>tr. \<exists>a\<in>S. Q a tr)"
  unfolding Valid_def by auto

theorem Valid_pre:
  "\<forall>tr. P tr \<longrightarrow> P' tr \<Longrightarrow> Valid P' c Q \<Longrightarrow> Valid P c Q"
  unfolding Valid_def by auto

theorem Valid_post:
  "\<forall>tr. Q tr \<longrightarrow> Q' tr \<Longrightarrow> Valid P c Q \<Longrightarrow> Valid P c Q'"
  unfolding Valid_def by auto

inductive_cases sendE: "big_step (Cm (Send ch e)) tr tr2"
thm sendE

inductive_cases receiveE: "big_step (Cm (Receive ch var)) tr tr2"
thm receiveE

inductive_cases seqE: "big_step (Seq p1 p2) tr tr3"
thm seqE

inductive_cases waitE: "big_step (Wait d) tr tr2"
thm waitE

theorem Valid_send:
  "Valid
    (\<lambda>t. t = tr)
    (Cm (Send ch e))
    (\<lambda>t. \<exists>dly. t = extend_send ch e dly ({ch}, {}) tr)"
  unfolding Valid_def by (auto elim: sendE)

theorem Valid_receive:
  "Valid
    (\<lambda>t. t = tr)
    (Cm (Receive ch var))
    (\<lambda>t. \<exists>dly v. t = extend_receive ch var dly v ({}, {ch}) tr)"
  unfolding Valid_def by (auto elim!: receiveE)

theorem Valid_seq:
  "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (Seq c1 c2) R"
  unfolding Valid_def by (auto elim!: seqE)

theorem Valid_wait:
  "Valid
    (\<lambda>t. t = tr)
    (Wait d)
    (\<lambda>t. t = extend_trace tr (Block d (\<lambda>t. end_of_trace tr) Tau ({}, {})))"
  unfolding Valid_def by (auto elim!: waitE)

subsection \<open>Validity for parallel processes\<close>

type_synonym par_assn = "par_trace \<Rightarrow> bool"

definition ParValid :: "par_assn \<Rightarrow> pproc \<Rightarrow> par_assn \<Rightarrow> bool" where
  "ParValid P pc Q \<longleftrightarrow> (\<forall>par_tr par_tr2. P par_tr \<longrightarrow> par_big_step pc par_tr par_tr2 \<longrightarrow> Q par_tr2)"

theorem ParValid_pre:
  "\<forall>tr. P tr \<longrightarrow> P' tr \<Longrightarrow> ParValid P' pc Q \<Longrightarrow> ParValid P pc Q"
  unfolding ParValid_def by auto

theorem ParValid_post:
  "\<forall>tr. Q tr \<longrightarrow> Q' tr \<Longrightarrow> ParValid P pc Q \<Longrightarrow> ParValid P pc Q'"
  unfolding ParValid_def by auto

inductive_cases parE: "par_big_step (PProc ps) par_tr par_tr2"
thm parE

inductive_cases combine_blocksE1: "combine_blocks blkss []"
thm combine_blocksE1

lemma combine_par_trace_trivial:
  "combine_par_trace tr (ParTrace par_st []) \<Longrightarrow> \<forall>i<length par_st. (tr ! i) = Trace (par_st ! i) []"
  apply (auto elim!: combine_par_trace.cases)
  apply (auto elim!: combine_blocksE1)
  by (metis blocks_of_trace.simps start_of_trace.simps trace.exhaust)

text \<open>Parallel rule\<close>

text \<open>Hoare triple for parallel processes.
  ps -- list of processes.
  P -- list of pre-conditions of processes.
  Q -- list of post-conditions of processes.
\<close>
theorem Valid_parallel:
  assumes "length P = length ps"
      "length Q = length ps"
      "length par_st = length ps"
      "\<forall>i<length ps. (P ! i) (Trace (par_st ! i) [])"
      "\<forall>i<length ps. Valid (P ! i) (ps ! i) (Q ! i)"
  shows "ParValid
    (\<lambda>par_t. par_t = ParTrace par_st [])
    (PProc ps)
    (\<lambda>par_t. \<exists>tr2. length tr2 = length ps \<and> (\<forall>i<length ps. (Q ! i) (tr2 ! i)) \<and> compat_rdy tr2 \<and> combine_par_trace tr2 par_t)"
proof -
  have 1: "\<forall>i<length ps. (Q ! i) (tr2 ! i)"
    if "\<forall>i<length ps. big_step (ps ! i) (tr ! i) (tr2 ! i)"
       "combine_par_trace tr (ParTrace par_st [])" for tr tr2
  proof -
    from that(2) have "\<forall>i<length ps. (tr ! i) = Trace (par_st ! i) []"
      using combine_par_trace_trivial assms(3) by auto
    then show ?thesis
      using assms(4-5) that(1) unfolding Valid_def by auto
  qed
  show ?thesis
    apply (auto simp add: ParValid_def)
    apply (auto elim!: parE)
    subgoal for par_tr2 tr tr2
      apply (rule exI[where x=tr2])
      by (auto simp add: assms 1)
  done
qed

subsection \<open>Other versions of Hoare triples\<close>

theorem Valid_send2:
  "\<forall>dly. Q (extend_send ch e dly ({ch}, {}) tr) \<Longrightarrow>
   Valid
    (\<lambda>t. t = tr)
    (Cm (Send ch e))
    Q"
  using Valid_def sendE by blast

theorem Valid_send3:
  "\<forall>tr dly. P tr \<longrightarrow> Q (extend_send ch e dly ({ch}, {}) tr) \<Longrightarrow>
    Valid P (Cm (Send ch e)) Q"
  using Valid_def sendE by blast

theorem Valid_receive2:
  "\<forall>dly v. Q (extend_receive ch var dly v ({}, {ch}) tr) \<Longrightarrow>
   Valid
    (\<lambda>t. t = tr)
    (Cm (Receive ch var))
    Q"
  using Valid_def receiveE by blast

text \<open>Version of Valid_parallel with arbitrary post-condition\<close>
theorem Valid_parallel':
  "length P = length ps \<Longrightarrow>
   length Q = length ps \<Longrightarrow>
   length par_st = length ps \<Longrightarrow>
   \<forall>i<length ps. (P ! i) (Trace (par_st ! i) []) \<Longrightarrow>
   \<forall>i<length ps. Valid (P ! i) (ps ! i) (Q ! i) \<Longrightarrow>
   (\<forall>par_t tr. length tr = length ps \<and> (\<forall>i<length ps. (Q ! i) (tr ! i)) \<and> compat_rdy tr \<and> combine_par_trace tr par_t \<longrightarrow> par_Q par_t) \<Longrightarrow>
   ParValid (\<lambda>t. t = ParTrace par_st [])
    (PProc ps)
    par_Q"
  using ParValid_post Valid_parallel by auto

text \<open>Version for two processes\<close>
theorem Valid_parallel2':
  assumes "P1 (Trace st1 [])"
    "P2 (Trace st2 [])"
    "Valid P1 p1 Q1" "Valid P2 p2 Q2"
    "(\<forall>par_t tr1 tr2. Q1 tr1 \<longrightarrow> Q2 tr2 \<longrightarrow> compat_trace_pair tr1 tr2 \<longrightarrow> combine_par_trace [tr1, tr2] par_t \<longrightarrow> par_Q par_t)"
  shows "ParValid (\<lambda>t. t = ParTrace [st1, st2] [])
    (PProc [p1, p2])
    par_Q"
proof -
  have 1: "par_Q par_t" if
    "length tr = length [p1, p2]" "(\<forall>i<length [p1, p2]. ([Q1, Q2] ! i) (tr ! i))" "compat_rdy tr" "combine_par_trace tr par_t"
  for par_t tr
  proof -
    have "tr = [tr ! 0, tr ! 1]"
      apply (rule nth_equalityI)
      using that(1) by (auto simp add: less_Suc_eq)
    then obtain tr1 tr2 where 2: "tr = [tr1, tr2]"
      by auto
    then have 3: "compat_trace_pair tr1 tr2"
      using \<open>compat_rdy tr\<close> unfolding compat_rdy_def by (auto simp add: less_Suc_eq)
    from assms show ?thesis
      using that 3 unfolding 2 by (auto simp add: less_Suc_eq)
  qed
  show ?thesis
    apply (rule Valid_parallel'[where P="[P1,P2]" and Q="[Q1,Q2]"])
    by (auto simp add: less_Suc_eq assms 1)
qed

subsection \<open>More on combine_blocks\<close>

lemma combine_blocks_IO2:
  "combine_blocks blkss par_tr \<Longrightarrow>
   compat_rdy_blocks blkss \<Longrightarrow>
   blkss = [Block d1 f1 (Out ch1 v1) ({''ch''}, {}) # blks1,
            Block d2 f2 (In ch2 v2) ({}, {''ch''}) # blks2] \<Longrightarrow>
   d1 = 0 \<and> d2 = 0"
proof (induct rule: combine_blocks.induct)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks block0)
  have "i = 0 \<or> i = 1"
    using 2(1) 2(9) by auto
  then show ?case using 2 by auto
next
  case (3 i blkss j t c v pblks blockt)
  have "length blkss = 2"
    using 3(15) by auto
  have "i = 0 \<or> i = 1" "j = 0 \<or> j = 1"
    using 3(1,2,15) by auto
  then have "i = 1" "j = 0"
    using 3(1,2,9,10,15) by auto
  then have "d1 = d2" "d1 = t" "d2 = t"
    using 3(7,8,15) by auto
  moreover have False if "t \<noteq> 0"
    using 3(14) unfolding 3(15) compat_rdy_blocks2
    unfolding compat_rdy_block_pair_def
    sorry
  ultimately show ?case
    using 3(4) by (auto simp add: less_Suc_eq)
qed


subsection \<open>Examples\<close>

text \<open>Send 1\<close>
lemma testHL1:
  "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) [])
    (Cm (Send ''ch'' (\<lambda>_. 1)))
    (\<lambda>t. \<exists>dly. t = Trace (\<lambda>_. 0) [Block dly (\<lambda>_. \<lambda>_. 0) (Out ''ch'' 1) ({''ch''}, {})])"
  apply (rule Valid_send2)
  by (auto simp add: extend_send_def)

text \<open>Send 1, then send 2\<close>
lemma testHL2:
  "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) [])
    (Seq (Cm (Send ''ch'' (\<lambda>_. 1))) (Cm (Send ''ch'' (\<lambda>_. 2))))
    (\<lambda>t. \<exists>dly dly2. t = Trace (\<lambda>_. 0) [Block dly (\<lambda>_. \<lambda>_. 0) (Out ''ch'' 1) ({''ch''}, {}),
                                       Block dly2 (\<lambda>_. \<lambda>_. 0) (Out ''ch'' 2) ({''ch''}, {})])"
  apply (rule Valid_seq[OF testHL1])
  apply (rule Valid_send3)
  by (auto simp add: extend_send_def)

text \<open>Receive from ch\<close>
lemma testHL3:
  "Valid
    (\<lambda>tr. tr = Trace (\<lambda>_. 0) [])
    (Cm (Receive ''ch'' ''x''))
    (\<lambda>tr. \<exists>dly v. tr = Trace (\<lambda>_. 0) [Block dly (\<lambda>t. if t \<ge> dly then (\<lambda>_. 0)(''x'' := v) else (\<lambda>_. 0))
                                            (In ''ch'' v) ({}, {''ch''})])"
  apply (rule Valid_receive2)
  by (auto simp add: extend_receive_def)

text \<open>Communication\<close>
lemma testHL4:
  "ParValid
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
    (PProc [Cm (Send ''ch'' (\<lambda>_. 1)), Cm (Receive ''ch'' ''x'')])
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)]
          [ParBlock 0 [(\<lambda>_. \<lambda>_. 0), (\<lambda>t. if t \<ge> 0 then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0))] (IO ''ch'' 1)])"
proof -
  have 1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] [ParBlock 0 [\<lambda>_ _. 0, \<lambda>t. if 0 \<le> t then (\<lambda>_. 0)(''x'' := 1) else (\<lambda>_. 0)] (IO ''ch'' 1)]"
    if ex1: "\<exists>dly. tr1 = Trace (\<lambda>_. 0) [Block dly (\<lambda>_ _. 0) (Out ''ch'' 1) ({''ch''}, {})]" and
       ex2: "(\<exists>dly v.
           tr2 = Trace (\<lambda>_. 0) [Block dly (\<lambda>t. if dly \<le> t then (\<lambda>_. 0)(''x'' := v) else (\<lambda>_. 0)) (In ''ch'' v) ({}, {''ch''})])" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t tr1 tr2
  proof -
    obtain dly1 where tr1: "tr1 = Trace (\<lambda>_. 0) [Block dly1 (\<lambda>_ _. 0) (Out ''ch'' 1) ({''ch''}, {})]"
      using ex1 by auto
    obtain dly2 v where tr2: "tr2 = Trace (\<lambda>_. 0) [Block dly2 (\<lambda>t. if dly2 \<le> t then (\<lambda>_. 0)(''x'' := v) else (\<lambda>_. 0)) (In ''ch'' v) ({}, {''ch''})]"
      using ex2 by auto
    have eq1: "dly1 = dly2 \<and> v = 1"
      sorry
    have eq2: "dly1 = 0"
      sorry
    show ?thesis
      sorry
  qed
  show ?thesis
    apply (rule Valid_parallel2'[OF _ _ testHL1 testHL3])
    using 1 by auto
qed

end
