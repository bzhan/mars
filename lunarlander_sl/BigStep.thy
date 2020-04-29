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

text \<open>Ready information\<close>
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

subsection \<open>Traces\<close>

text \<open>First, we define the concept of traces\<close>

text \<open>Time delay, ending state, and set of communications available at the interval\<close>
datatype trace_block = Block time history event "cname set \<times> cname set"

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
    (if t > 0 \<and> t < dly then rdy
     else if t \<le> dly then ({}, {})
     else rdy_of_blocks blks (t - dly))"

fun rdy_of_trace :: "trace \<Rightarrow> time \<Rightarrow> rdy_info" where
  "rdy_of_trace (Trace _ blks) t = rdy_of_blocks blks t"

fun compat_rdy_pair :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy_pair (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

definition compat_rdy :: "trace list \<Rightarrow> bool" where
  "compat_rdy trs = (\<forall>t. \<forall>i<length trs. \<forall>j<length trs. i \<noteq> j \<longrightarrow>
      compat_rdy_pair (rdy_of_trace (trs ! i) t) (rdy_of_trace (trs ! j) t))"


subsection \<open>Traces of parallel processes\<close>

datatype par_block = ParBlock time "history list" event

datatype par_trace = ParTrace "state list" "par_block list"

text \<open>Given a delay time t and a block with time interval at least t,
  find the block starting at time t.\<close>
fun wait_block :: "time \<Rightarrow> trace_block \<Rightarrow> trace_block" where
  "wait_block t (Block dly s ev rdy) = Block (dly - t) (\<lambda>t'. s (t' + t)) ev rdy"

fun wait_blocks :: "time \<Rightarrow> trace_block list \<Rightarrow> trace_block list" where
  "wait_blocks t [] = []"
| "wait_blocks t (blk # blks) = wait_block t blk # blks"

text \<open>Given a delay time t and a block with time interval at least t,
  find the history at and before t.\<close>
fun start_block :: "time \<Rightarrow> trace_block \<Rightarrow> history" where
  "start_block t (Block dly s ev rdy) t' = (if t' \<le> t then s t' else undefined)"

fun start_blocks :: "time \<Rightarrow> trace_block list \<Rightarrow> history" where
  "start_blocks t [] = (\<lambda>t'. undefined)"
| "start_blocks t (blk # blks) = start_block t blk"

definition remove_one :: "nat \<Rightarrow> trace_block list list \<Rightarrow> trace_block list list" where
  "remove_one i blkss = blkss[i := tl (blkss ! i)]"

definition remove_pair :: "nat \<Rightarrow> nat \<Rightarrow> time \<Rightarrow> trace_block list list \<Rightarrow> trace_block list list" where
  "remove_pair i j t blkss = (
    let blkss' = map (wait_blocks t) blkss in
      blkss'[i := tl (blkss' ! i), j := tl (blkss' ! j)])"

inductive combine_blocks :: "trace_block list list \<Rightarrow> par_block list \<Rightarrow> bool" where
  "\<forall>i<length blkss. blkss ! i = [] \<Longrightarrow> combine_blocks blkss []"
| "i < length blkss \<Longrightarrow>
   blkss ! i \<noteq> [] \<Longrightarrow>
   delay_of_block (hd (blkss ! i)) = 0 \<Longrightarrow>
   event_of_block (hd (blkss ! i)) = Tau \<Longrightarrow>
   combine_blocks (remove_one i blkss) pblks \<Longrightarrow>
   combine_blocks blkss ((ParBlock 0 (map (start_blocks 0) blkss) Tau) # pblks)"
| "i < length blkss \<Longrightarrow> j < length blkss \<Longrightarrow> i \<noteq> j \<Longrightarrow>
   \<forall>k<length blkss. blkss ! k \<noteq> [] \<longrightarrow> delay_of_block (hd (blkss ! k)) \<ge> t \<Longrightarrow>
   blkss ! i \<noteq> [] \<Longrightarrow> blkss ! j \<noteq> [] \<Longrightarrow>
   delay_of_block (hd (blkss ! i)) = t \<Longrightarrow>
   delay_of_block (hd (blkss ! j)) = t \<Longrightarrow>
   event_of_block (hd (blkss ! j)) = In c v \<Longrightarrow>
   event_of_block (hd (blkss ! j)) = Out c v \<Longrightarrow>
   combine_blocks (remove_pair i j t blkss) pblks \<Longrightarrow>
   combine_blocks blkss ((ParBlock t (map (start_blocks t) blkss) (IO c v)) # pblks)"

inductive combine_par_trace :: "trace list \<Rightarrow> par_trace \<Rightarrow> bool" where
  "length trs = length sts \<Longrightarrow>
   \<forall>i<length trs. start_of_trace (trs ! i) = sts ! i \<Longrightarrow>
   combine_blocks (map blocks_of_trace trs) par_blks \<Longrightarrow>
   combine_par_trace trs (ParTrace sts par_blks)"


subsection \<open>External choice\<close>

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

definition extend_send :: "cname \<Rightarrow> exp \<Rightarrow> time \<Rightarrow> rdy_info \<Rightarrow> trace \<Rightarrow> trace" where
  "extend_send ch e dly rdy tr =
    extend_trace tr (Block dly (\<lambda>t. end_of_trace tr) (Out ch (e (end_of_trace tr))) rdy)"

definition extend_receive :: "cname \<Rightarrow> var \<Rightarrow> time \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> trace \<Rightarrow> trace" where
  "extend_receive ch var dly v rdy tr =
    extend_trace tr (Block dly (\<lambda>t. if t = dly then (end_of_trace tr)(var := v) else end_of_trace tr)
                            (In ch v) ({}, {ch}))"

inductive big_step :: "proc \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "big_step (Cm (Send ch e)) tr
    (extend_send ch e dly ({ch}, {}) tr)"
| "big_step (Cm (Receive ch var)) tr
    (extend_receive ch var dly v ({}, {ch}) tr)"
| "big_step Skip tr
    (extend_trace tr (Block 0 (\<lambda>t. end_of_trace tr) Tau ({}, {})))"
| "big_step (Assign var e) tr
    (extend_trace tr (Block 0 (\<lambda>t. (end_of_trace tr)(var := e (end_of_trace tr))) Tau ({}, {})))"
| "big_step p1 tr tr2 \<Longrightarrow>
   big_step p2 tr2 tr3 \<Longrightarrow> big_step (Seq p1 p2) tr tr3"
| "b (end_of_trace tr) \<Longrightarrow>
   big_step p1 tr tr2 \<Longrightarrow> big_step (Cond b p1 p2) tr tr2"
| "\<not> b (end_of_trace tr) \<Longrightarrow>
   big_step p2 tr tr2 \<Longrightarrow> big_step (Cond b p1 p2) tr tr2"
| "big_step (Wait d) tr
    (extend_trace tr (Block d (\<lambda>t. end_of_trace tr) Tau ({}, {})))"
| "i < length ps \<Longrightarrow> big_step (ps ! i) tr tr2 \<Longrightarrow>
   big_step (IChoice ps) tr tr2"
| "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
   big_step p2 (extend_send ch e dly (rdy_of_echoice cs) tr) tr3 \<Longrightarrow>
   big_step (EChoice cs) tr tr3"
| "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
   big_step p2 (extend_receive ch var dly v (rdy_of_echoice cs) tr) tr3 \<Longrightarrow>
   big_step (EChoice cs) tr tr3"

inductive par_big_step :: "pproc \<Rightarrow> par_trace \<Rightarrow> par_trace \<Rightarrow> bool" where
  "\<forall>i<length ps. big_step (ps ! i) (tr ! i) (tr2 ! i) \<Longrightarrow>
   compat_rdy tr \<Longrightarrow> compat_rdy tr2 \<Longrightarrow>
   combine_par_trace tr par_tr \<Longrightarrow>
   combine_par_trace tr2 par_tr2 \<Longrightarrow>
   par_big_step (PProc ps) par_tr par_tr2"



end
