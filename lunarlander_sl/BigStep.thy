theory BigStep
  imports Complex_Main
    Ordinary_Differential_Equations.Flow
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
| IChoice "proc list"  \<comment> \<open>Nondeterminism\<close>
| EChoice "(comm \<times> proc) list"  \<comment> \<open>External choice\<close>
| Rep proc   \<comment> \<open>Nondeterministic repetition\<close>
| Cont ODE fform  \<comment> \<open>ODE with boundary\<close>
| Interrupt ODE "(comm \<times> proc) list"  \<comment> \<open>Interrupt\<close>

text \<open>Parallel of several HCSP processes\<close>
datatype pproc = PProc "proc list"

text \<open>Events\<close>
datatype event =
  Tau
| WaitE real \<comment> \<open>add Wait because ParTau and ParWait are distinct\<close>
| In cname real
| Out cname real 
| IO cname real 


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
datatype trace_block =
  InBlock time cname var real rdy_info  \<comment> \<open>Delay time, channel name, variable name, value sent\<close>
  | OutBlock time cname real rdy_info  \<comment> \<open>Delay time, channel name, value sent\<close>
  | TauBlock state   \<comment> \<open>Instantaneous update, keep new state\<close>
  | WaitBlock time   \<comment> \<open>Delay time\<close>
  | ODEBlock time "real \<Rightarrow> state"  \<comment> \<open>Length of time interval, history\<close>
  | ODEInBlock time "real \<Rightarrow> state" cname var real rdy_info
  | ODEOutBlock time "real \<Rightarrow> state" cname real rdy_info

text \<open>Starting state, blocks\<close>
datatype trace = Trace state "trace_block list"

fun delay_of_block :: "trace_block \<Rightarrow> time" where
  "delay_of_block (InBlock dly _ _ _ _) = dly"
| "delay_of_block (OutBlock dly _ _ _) = dly"
| "delay_of_block (TauBlock _) = 0"
| "delay_of_block (WaitBlock dly) = dly"
| "delay_of_block (ODEBlock d h) = d"
| "delay_of_block (ODEInBlock dly _ _ _ _ _) = dly"
| "delay_of_block (ODEOutBlock dly _ _ _ _) = dly"

fun event_of_block :: "trace_block \<Rightarrow> event" where
  "event_of_block (InBlock _ ch _ v _) = In ch v"
| "event_of_block (OutBlock _ ch v _) = Out ch v"
| "event_of_block (TauBlock _) = Tau"
| "event_of_block (WaitBlock v) = WaitE v"
| "event_of_block (ODEBlock v _) = WaitE v"
| "event_of_block (ODEInBlock _ _ ch _ v _) = In ch v"
| "event_of_block (ODEOutBlock _ _ ch v _) = Out ch v"


fun rdy_of_block :: "trace_block \<Rightarrow> rdy_info" where
  "rdy_of_block (InBlock _ _ _ _ rdy) = rdy"
| "rdy_of_block (OutBlock _ _ _ rdy) = rdy"
| "rdy_of_block (TauBlock _) = ({}, {})"
| "rdy_of_block (WaitBlock _) = ({}, {})"
| "rdy_of_block (ODEBlock _ _) = ({}, {})"
| "rdy_of_block (ODEInBlock _ _ _ _ _ rdy) = rdy"
| "rdy_of_block (ODEOutBlock _ _ _ _ rdy) = rdy"

fun var_of_block :: "trace_block \<Rightarrow> var set" where
  "var_of_block (InBlock dly _ v _ _) = {v}"
| "var_of_block (OutBlock dly _ _ _) = {}"
| "var_of_block (TauBlock _) = {}"
| "var_of_block (WaitBlock dly) = {}"
| "var_of_block (ODEBlock d h) = {}"
| "var_of_block (ODEInBlock dly _ _ v _ _) = {v}"
| "var_of_block (ODEOutBlock dly _ _ _ _) = {}"

fun start_of_trace :: "trace \<Rightarrow> state" where
  "start_of_trace (Trace s _) = s"

fun blocks_of_trace :: "trace \<Rightarrow> trace_block list" where
  "blocks_of_trace (Trace _ blks) = blks"

fun end_of_blocks :: "state \<Rightarrow> trace_block list \<Rightarrow> state" where
  "end_of_blocks s [] = s"
| "end_of_blocks s ((InBlock _ _ var v _) # rest) = end_of_blocks (s(var := v)) rest"
| "end_of_blocks s ((OutBlock _ _ _ _) # rest) = end_of_blocks s rest"
| "end_of_blocks s ((TauBlock st) # rest) = end_of_blocks st rest"
| "end_of_blocks s ((WaitBlock _) # rest) = end_of_blocks s rest"
| "end_of_blocks _ ((ODEBlock d h) # rest) = end_of_blocks (h d) rest"
| "end_of_blocks _ ((ODEInBlock d h _ var v _) # rest) = end_of_blocks ((h d)(var := v)) rest"
| "end_of_blocks _ ((ODEOutBlock d h _ _ _) # rest) = end_of_blocks (h d) rest"

theorem end_of_blocks_append:
  "end_of_blocks st (blks1 @ blks2) = end_of_blocks (end_of_blocks st blks1) blks2"
  apply (induction blks1 arbitrary: st rule: list.induct)
   apply auto
  subgoal for blk1 blk2 st
    by (cases blk1, auto)
  done

fun end_of_trace :: "trace \<Rightarrow> state" where
  "end_of_trace (Trace s blks) = end_of_blocks s blks"

fun extend_trace :: "trace \<Rightarrow> trace_block \<Rightarrow> trace" where
  "extend_trace (Trace s blks) blk = Trace s (blks @ [blk])"


text \<open>Now we define the ready set of a trace at any given time\<close>

fun rdy_of_blocks :: "trace_block list \<Rightarrow> time \<Rightarrow> rdy_info" where
  "rdy_of_blocks [] t = ({}, {})"
| "rdy_of_blocks ((InBlock dly _ _ _ rdy) # blks) t =
    (if 0 \<le> t \<and> t < dly then rdy
     else rdy_of_blocks blks (t - dly))"
| "rdy_of_blocks ((OutBlock dly _ _ rdy) # blks) t =
    (if 0 \<le> t \<and> t < dly then rdy
     else rdy_of_blocks blks (t - dly))"
| "rdy_of_blocks ((TauBlock _) # blks) t = rdy_of_blocks blks t"
| "rdy_of_blocks ((WaitBlock d) # blks) t =
    (if t \<le> d then ({}, {}) else rdy_of_blocks blks (t - d))"
| "rdy_of_blocks ((ODEBlock d _) # blks) t =
    (if t \<le> d then ({}, {}) else rdy_of_blocks blks (t - d))"
| "rdy_of_blocks ((ODEInBlock d _ _ _ _ rdy) # blks) t =
    (if 0 \<le> t \<and> t < d then rdy
     else rdy_of_blocks blks (t - d))"
| "rdy_of_blocks ((ODEOutBlock d _ _ _ rdy) # blks) t =
    (if 0 \<le> t \<and> t < d then rdy
     else rdy_of_blocks blks (t - d))"

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

datatype par_block =
    IOBlock nat nat cname var real  \<comment> \<open>Receive process, Send process, channel name, variable name, value sent\<close>
  | ParTauBlock nat state       \<comment> \<open>Instantaneous update on one process to new state\<close>
  | ParWaitBlock real "real \<Rightarrow> state list"  \<comment> \<open>Delay\<close>

text \<open>ParTrace st pblks:
  st -- starting state for each process. Length is the number of processes.
  pblks -- list of parallel blocks.\<close>
datatype par_trace = ParTrace "state list" "par_block list"

text \<open>Determine the end of state for a parallel trace\<close>
fun end_of_par_blocks :: "state list \<Rightarrow> par_block list \<Rightarrow> state list" where
  "end_of_par_blocks sts [] = sts"
| "end_of_par_blocks sts ((IOBlock pin pout ch v x) # rest) =
      end_of_par_blocks (sts[pin := (sts ! pin)(v := x)]) rest"
| "end_of_par_blocks sts ((ParTauBlock ptau st) # rest) =
      end_of_par_blocks (sts[ptau := st]) rest"
| "end_of_par_blocks sts ((ParWaitBlock d hist) # rest) =
      end_of_par_blocks (hist d) rest"


text \<open>Now we define how to combine a list of traces for individual processes
  into a parallel trace.\<close>

text \<open>Given a delay time t and a block with time interval at least t,
  find the block starting at time t.

  Examples:
    wait_block 2 (In ''ch'' 1 after 5) = In ''ch'' 1 after 3.
\<close>
fun wait_block :: "time \<Rightarrow> trace_block \<Rightarrow> trace_block" where
  "wait_block t (InBlock dly ch var v rdy) = InBlock (dly - t) ch var v rdy"
| "wait_block t (OutBlock dly ch v rdy) = OutBlock (dly - t) ch v rdy"
| "wait_block t (TauBlock st) = TauBlock st"
| "wait_block t (WaitBlock d) = WaitBlock (d - t)"
| "wait_block t (ODEBlock d h) = ODEBlock (d - t) (\<lambda>s. h (s + t))"
| "wait_block t (ODEInBlock d h ch var v rdy) = ODEInBlock (d - t) (\<lambda>s. h (s + t)) ch var v rdy"
| "wait_block t (ODEOutBlock d h ch v rdy) = ODEOutBlock (d - t) (\<lambda>s. h (s + t)) ch v rdy"

lemma wait_block_0[simp]:
  "wait_block 0 blk = blk" by (cases blk, auto)

text \<open>Operate on a list of blocks. We assume that if the list is nonempty,
  then the first block has length at least t.\<close>
fun wait_blocks :: "time \<Rightarrow> trace_block list \<Rightarrow> trace_block list" where
  "wait_blocks t [] = []"
| "wait_blocks t (blk # blks) = wait_block t blk # blks"

(*
text \<open>Given a delay time t and a block with time interval at least t,
  find the history at and before t.\<close>
fun start_block :: "time \<Rightarrow> trace_block \<Rightarrow> history" where
  "start_block t (Block dly s ev rdy) t' = (if t' \<le> t then s t' else s t)"

text \<open>Operate on a list of blocks. We assume that if the list is nonempty,
  then the first block has length at least t.\<close>
fun start_blocks :: "time \<Rightarrow> trace_block list \<Rightarrow> history" where
  "start_blocks t [] = (\<lambda>t'. undefined)"
| "start_blocks t (blk # blks) = start_block t blk"
*)

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
definition remove_pair :: "nat \<Rightarrow> nat \<Rightarrow> trace_block list list \<Rightarrow> trace_block list list" where
  "remove_pair i j blkss = (
      blkss[i := tl (blkss ! i), j := tl (blkss ! j)])"

text \<open>the state of a trace at any given time\<close>
fun state_of_blocks :: "state \<Rightarrow> trace_block list \<Rightarrow> time \<Rightarrow> state" where
  "state_of_blocks s [] t = s"
| "state_of_blocks s ((InBlock dly _ var v _) # blks) t =
    (if 0 \<le> t \<and> t \<le>dly then s
     else state_of_blocks (s(var := v)) blks (t - dly))"
| "state_of_blocks s ((OutBlock dly _ _ rdy) # blks) t =
    (if 0 \<le> t \<and> t \<le> dly then s
     else state_of_blocks s blks (t - dly))"
| "state_of_blocks s ((TauBlock _) # blks) t = state_of_blocks s blks t"
| "state_of_blocks s ((WaitBlock d) # blks) t =
    (if t \<le> d then s else state_of_blocks s blks (t - d))"
| "state_of_blocks s ((ODEBlock d h) # blks) t =
    (if t \<le> d then h t else state_of_blocks (h d) blks (t - d))"
| "state_of_blocks s ((ODEInBlock d h _ var v _) # blks) t = 
    (if t \<le> d then h t else state_of_blocks ((h d)(var := v)) blks (t - d))"
| "state_of_blocks s ((ODEOutBlock d h _ _ _) # blks) t = 
    (if t \<le> d then h t else state_of_blocks (h d) blks (t - d))"

fun wait_block_state_list :: "state list \<Rightarrow> time \<Rightarrow> trace_block list list \<Rightarrow> state list" where
  "wait_block_state_list [] t [] = []" 
| "wait_block_state_list [] t (b # trbl) = undefined"
| "wait_block_state_list (a # sts) t [] = (a # sts)"
| "wait_block_state_list (a # sts) t (b # trbl) = (state_of_blocks a b t) # (wait_block_state_list sts t trbl)"


text \<open>Main definition: combining a list of block lists.
  combine_blocks blkss pblks means the list of block lists blkss can be combined
  together into pblks.\<close>
inductive combine_blocks :: "state list \<Rightarrow> trace_block list list \<Rightarrow> par_block list \<Rightarrow> bool" where
  "\<forall>i<length blkss. blkss ! i = [] \<Longrightarrow> combine_blocks sts blkss []"  \<comment> \<open>empty case\<close>
| "i < length blkss \<Longrightarrow>
   blkss ! i \<noteq> [] \<Longrightarrow>
   delay_of_block (hd (blkss ! i)) = 0 \<Longrightarrow>
   event_of_block (hd (blkss ! i)) = Tau \<Longrightarrow>
  \<forall>k<length blkss. blkss ! k \<noteq> [] \<longrightarrow> delay_of_block (hd (blkss ! k)) \<ge> 0 \<Longrightarrow>
   combine_blocks (sts[i := (end_of_blocks (sts ! i) [hd (blkss ! i)])]) (remove_one i 0 blkss) pblks \<Longrightarrow>
   combine_blocks sts blkss ((ParTauBlock i (end_of_blocks (sts ! i) [hd (blkss ! i)])) # pblks)" 
  \<comment> \<open>Communication between i'th and j'th process\<close>
| "i < length blkss \<Longrightarrow> j < length blkss \<Longrightarrow> i \<noteq> j \<Longrightarrow>
   blkss ! i \<noteq> [] \<Longrightarrow> blkss ! j \<noteq> [] \<Longrightarrow>
   delay_of_block (hd (blkss ! i)) = 0 \<Longrightarrow>
   delay_of_block (hd (blkss ! j)) = 0 \<Longrightarrow>
   event_of_block (hd (blkss ! i)) = In c v \<Longrightarrow>
   event_of_block (hd (blkss ! j)) = Out c v \<Longrightarrow>
   var_of_block (hd (blkss !i)) = {x} \<Longrightarrow>
   combine_blocks (sts[i := (end_of_blocks (sts ! i) [hd (blkss ! i)])]) (remove_pair i j blkss) pblks \<Longrightarrow>
   combine_blocks sts blkss ((IOBlock i j c x v) # pblks)" 
 \<comment> \<open>Wait action at i'th process\<close>
| "i < length blkss \<Longrightarrow>
   t > 0 \<Longrightarrow>
   \<forall>k<length blkss. blkss ! k \<noteq> [] \<longrightarrow> delay_of_block (hd (blkss ! k)) \<ge> t \<Longrightarrow>
   blkss ! i \<noteq> [] \<Longrightarrow>
   delay_of_block (hd (blkss ! i)) = t \<Longrightarrow>
   event_of_block (hd (blkss ! i)) = WaitE t \<Longrightarrow>
   combine_blocks (wait_block_state_list sts t blkss) (remove_one i t blkss) pblks \<Longrightarrow>
   combine_blocks sts blkss (
     ParWaitBlock t (\<lambda>d. if 0\<le>d \<and> d\<le>t then wait_block_state_list sts d blkss else undefined)
     # pblks)"


text \<open>Use the previous definition to combine a list of traces into a parallel trace.\<close>
inductive combine_par_trace :: "trace list \<Rightarrow> par_trace \<Rightarrow> bool" where
  "length trs = length sts \<Longrightarrow>
   \<forall>i<length trs. start_of_trace (trs ! i) = sts ! i \<Longrightarrow>
   combine_blocks sts (map blocks_of_trace trs) par_blks \<Longrightarrow>
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

subsection \<open>Definitions of ODEs\<close>

definition Vagree :: "state \<Rightarrow> state \<Rightarrow> var set \<Rightarrow> bool"
  where "Vagree u v V = (\<forall>i. i \<in> V \<longrightarrow> u i = v i)"

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

text \<open>Given ODE and a state, find the derivative vector.\<close>
fun ODE2Vec :: "ODE \<Rightarrow> state \<Rightarrow> vec" where
  "ODE2Vec (ODE f) s = state2vec (\<lambda>a. f a s)"

text \<open>History p on time {0 .. d} is a solution to ode.\<close>
definition ODEsol :: "ODE \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> real \<Rightarrow> bool" where
  "ODEsol ode p d = (d \<ge> 0 \<and> (((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {0 .. d}))"

text \<open>Projection of has_vector_derivative onto components.\<close>
lemma has_vector_derivative_proj:
  assumes "(p has_vector_derivative q t) (at t within D)"
  shows "((\<lambda>t. p t $ i) has_vector_derivative q t $ i) (at t within D)"
  using assms unfolding has_vector_derivative_def has_derivative_def 
  apply (simp add: bounded_linear_scaleR_left)
  using tendsto_vec_nth by fastforce

lemma has_vector_derivative_projI:
  assumes "\<forall>i. ((\<lambda>t. p t $ i) has_vector_derivative q t $ i) (at t within D)"
  shows "(p has_vector_derivative q t) (at t within D)"
  using assms unfolding has_vector_derivative_def has_derivative_def
  apply (auto simp add: bounded_linear_scaleR_left)
  by (auto intro: vec_tendstoI)

lemma has_derivative_coords [simp,derivative_intros]:
  "((\<lambda>t. t$i) has_derivative (\<lambda>t. t$i)) (at x)"
  unfolding has_derivative_def by auto


text \<open>If the derivative is always 0, then the function is always 0.\<close>
lemma mvt_real_eq:
  fixes p :: "real \<Rightarrow> real"
  assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 .. d}. \<forall>s. q t s = 0"
    and "x \<in> {0 .. d}"
  shows "p 0 = p x" 
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by force
qed

text \<open>If the derivative is always non-negative, then the function is increasing.\<close>
lemma mvt_real_ge:
  fixes p :: "real \<Rightarrow>real"
 assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
  and "d \<ge> 0"
  and "\<forall>t\<in>{0 .. d}. \<forall>s\<ge>0. q t s \<ge> 0"
  and "x \<in> {0 .. d}"
  shows "p 0 \<le> p x"
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by (smt atLeastAtMost_iff greaterThanLessThan_iff)
qed

text \<open>If the derivative is always non-positive, then the function is decreasing.\<close>
lemma mvt_real_le:
  fixes p :: "real \<Rightarrow>real"
  assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 .. d}. \<forall>s\<ge>0 . q t s \<le> 0"
    and "x \<in> {0 .. d}"
  shows "p 0 \<ge> p x"
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by (smt atLeastAtMost_iff greaterThanLessThan_iff)
qed

text \<open>Mean value theorem (constant case) for vectors.\<close>
lemma mvt_vector:
  fixes p :: "real \<Rightarrow> state"
  assumes "\<forall>t\<in>{0 .. d}. (((\<lambda>t. state2vec (p t)) has_vector_derivative state2vec (q t)) (at t within {0 .. d}) \<and> q t v = 0)"
    and "d \<ge> 0"
  shows "\<forall>t\<in>{0 .. d}. p 0 v = p t v"
proof -
  have 1: "\<forall>t\<in>{0 .. d}. ((\<lambda>t. state2vec (p t) $ v) has_vector_derivative state2vec (q t) $ v) (at t within {0 .. d})" 
    using assms 
    using has_vector_derivative_proj[where p="\<lambda>t. state2vec (p t)" and q="\<lambda>t. state2vec (q t)"]
    by blast
  have 2: "\<forall>t\<in>{0 .. d}.  state2vec (q t) $ v = 0" 
    using assms  state2vec_def by auto
  have 3: "\<forall>t\<in>{0 .. d}. state2vec (p 0) $ v = state2vec (p t) $ v"
    using assms 1 2 unfolding has_vector_derivative_def 
    using mvt_real_eq[where p = "\<lambda>t. state2vec (p t) $ v" and q = "\<lambda>t. (\<lambda>x. x *\<^sub>R state2vec (q t) $ v)" and d="d"]
    by auto
  then show ?thesis
    using state2vec_def by auto
qed

lemma chainrule:
  assumes "\<forall>x. ((\<lambda>v. g (vec2state v)) has_derivative g' (vec2state x)) (at x within UNIV)"
    and "ODEsol ode p d"
    and "t \<in> {0 .. d}"
  shows "((\<lambda>t. g (p t)) has_derivative (\<lambda>s. g' (p t) (s *\<^sub>R ODE2Vec ode (p t)))) (at t within {0 .. d})"
proof -
  have 1: "(\<And>x. x \<in> UNIV \<Longrightarrow> ((\<lambda>v. g (vec2state v)) has_derivative g' (vec2state x)) (at x))"
    using assms(1) by auto
  have 2: "0 \<le> t \<and> t \<le> d"
    using assms(3) by auto
  have 3: "((\<lambda>t. state2vec(p t)) has_derivative (\<lambda>s. s *\<^sub>R ODE2Vec ode (p t))) (at t within {0..d})"
    using 2 assms(2) unfolding ODEsol_def has_vderiv_on_def has_vector_derivative_def by auto
  show ?thesis
  using 1 2 3 has_derivative_in_compose2[of UNIV "(\<lambda>v. g (vec2state v))" "(\<lambda>v. g' (vec2state v))" "(\<lambda>t. state2vec (p t))" "{0 .. d}" t "(\<lambda>s. s *\<^sub>R ODE2Vec ode (p t))"]
  by auto
qed


subsection \<open>Big-step semantics\<close>

text \<open>Big-step semantics specifies for each command a mapping from trace to trace\<close>

text \<open>Extend by a send block\<close>
definition extend_send :: "cname \<Rightarrow> exp \<Rightarrow> time \<Rightarrow> rdy_info \<Rightarrow> trace \<Rightarrow> trace" where
  "extend_send ch e dly rdy tr =
    extend_trace tr (OutBlock dly ch (e (end_of_trace tr)) rdy)"

text \<open>Extend by a receive block\<close>
definition extend_receive :: "cname \<Rightarrow> var \<Rightarrow> time \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> trace \<Rightarrow> trace" where
  "extend_receive ch var dly v rdy tr =
    extend_trace tr (InBlock dly ch var v ({}, {ch}))"

text \<open>Big-step semantics.
  big_step p tr tr2 means executing p starting at trace tr can end in trace tr2.
  This should imply that tr is a prefix of tr2.\<close>
inductive big_step :: "proc \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  \<comment> \<open>Send: dly \<ge> 0 is the amount of time waited at the current send.\<close>
  sendB: "dly \<ge> 0 \<Longrightarrow> big_step (Cm (Send ch e)) tr (extend_send ch e dly ({ch}, {}) tr)"
  \<comment> \<open>Receive: dly \<ge> 0 is the amount of time waited at the current receive.
      v is the value received.\<close>
| receiveB: "dly \<ge> 0 \<Longrightarrow> big_step (Cm (Receive ch var)) tr
    (extend_receive ch var dly v ({}, {ch}) tr)"
| skipB: "big_step Skip tr tr"
| assignB: "big_step (Assign var e) tr
    (extend_trace tr (TauBlock ((end_of_trace tr)(var := e (end_of_trace tr)))))"
| seqB: "big_step p1 tr tr2 \<Longrightarrow>
   big_step p2 tr2 tr3 \<Longrightarrow> big_step (Seq p1 p2) tr tr3"
| condB1: "b (end_of_trace tr) \<Longrightarrow>
   big_step p1 tr tr2 \<Longrightarrow> big_step (Cond b p1 p2) tr tr2"
| condB2: "\<not> b (end_of_trace tr) \<Longrightarrow>
   big_step p2 tr tr2 \<Longrightarrow> big_step (Cond b p1 p2) tr tr2"
| waitB: "big_step (Wait d) tr
    (extend_trace tr (WaitBlock d))"
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
| RepetitionB1: "big_step (Rep p) tr tr"
| RepetitionB2: "big_step p tr tr2 \<Longrightarrow> big_step (Rep p) tr2 tr3 \<Longrightarrow> 
   big_step (Rep p) tr tr3"
| ContB:
   "d \<ge> 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not> b (p d) \<Longrightarrow> p 0 = end_of_trace tr \<Longrightarrow>
    tr2 = extend_trace tr (ODEBlock d (restrict p {0..d})) \<Longrightarrow>
    big_step (Cont ode b) tr tr2"
| InterruptSendB:
   "d \<ge> 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    p 0 = end_of_trace tr \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 (extend_trace tr (ODEOutBlock d (restrict p {0..d}) ch (e (p d)) (rdy_of_echoice cs))) tr3 \<Longrightarrow>
    big_step (Interrupt ode cs) tr tr3"
| InterruptReceiveB:
   "d \<ge> 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    p 0 = end_of_trace tr \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (extend_trace tr (ODEInBlock d (restrict p {0..d}) ch var v (rdy_of_echoice cs))) tr3 \<Longrightarrow>
    big_step (Interrupt ode cs) tr tr3"


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
  assumes "blks' = blks @ [OutBlock dly ch (e (end_of_trace (Trace s blks))) ({ch}, {})]"
    and "dly \<ge> 0"
  shows "big_step (Cm (Send ch e)) (Trace s blks) (Trace s blks')"
proof -
  have 1: "Trace s (blks @ [OutBlock dly ch (e (end_of_trace (Trace s blks))) ({ch}, {})]) =
        extend_send ch e dly ({ch}, {}) (Trace s blks)"
    unfolding extend_send_def extend_trace.simps by auto
  show ?thesis
    apply (subst assms(1))
    apply (subst 1)
    using assms(2) by (rule sendB)
qed

lemma receiveB2:
  assumes "blks' = blks @ [InBlock dly ch var v ({}, {ch})]"
    and "dly \<ge> 0"
  shows "big_step (Cm (Receive ch var)) (Trace s blks) (Trace s blks')"
proof -
  have 1: "Trace s (blks @ [InBlock dly ch var v ({}, {ch})]) =
        extend_receive ch var dly v ({}, {ch}) (Trace s blks)"
    unfolding extend_receive_def extend_trace.simps by auto
  show ?thesis
    apply (subst assms(1))
    apply (subst 1)
    using assms(2) by (rule receiveB)
qed

lemma waitB2:
  assumes "blks' = blks @ [WaitBlock d]"
  shows "big_step (Wait d) (Trace s blks) (Trace s blks')"
proof -
  have 1: "Trace s (blks @ [WaitBlock d]) = extend_trace (Trace s blks) (WaitBlock d)"
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
        (Trace (\<lambda>_. 0) [OutBlock 0 ''ch'' 1 ({''ch''}, {})])"
  apply (rule sendB2)
  by auto

text \<open>Send x + 1 immediately\<close>
lemma test1b: "big_step (Cm (Send ''ch'' (\<lambda>s. s X + 1)))
        (Trace ((\<lambda>_. 0)(X := 1)) [])
        (Trace ((\<lambda>_. 0)(X := 1)) [OutBlock 0 ''ch'' 2 ({''ch''}, {})])"
  apply (rule sendB2)
  by auto

text \<open>Send 1 after delay 2\<close>
lemma test1c: "big_step (Cm (Send ''ch'' (\<lambda>_. 1)))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [OutBlock 2 ''ch'' 1 ({''ch''}, {})])"
  apply (rule sendB2)
  by auto

text \<open>Receive 1 immediately\<close>
lemma test2a: "big_step (Cm (Receive ''ch'' X))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [InBlock 0 ''ch'' X 1 ({}, {''ch''})])"
  apply (rule receiveB2)
  by auto

text \<open>Receive 1 after delay 2\<close>
lemma test2b: "big_step (Cm (Receive ''ch'' X))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [InBlock 2 ''ch'' X 1 ({}, {''ch''})])"
  apply (rule receiveB2)
  by auto

text \<open>Communication\<close>
lemma test3: "par_big_step (PProc [Cm (Send ''ch'' (\<lambda>_. 1)), Cm (Receive ''ch'' X)])
        (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
        (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [IOBlock 1 0 ''ch'' X 1])"
proof -
  have 1: "combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)
  have 2: "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)]
     [[OutBlock 0 ''ch'' 1 ({''ch''}, {})],
      [InBlock 0 ''ch'' X 1 ({}, {''ch''})]]
     [IOBlock 1 0 ''ch'' X 1]"
    apply (rule combine_blocks.intros(3)[where i=1 and j=0])
    apply (auto simp add: less_Suc_eq)
    unfolding remove_pair_def Let_def apply auto
    by (rule 1)
  have 3: " combine_blocks [\<lambda>_. 0, \<lambda>_. 0] [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)
  show ?thesis
    apply (rule parallelB2[OF test1a test2a])
    apply (auto simp add: compat_rdy_block_pair_def less_Suc_eq combine_par_trace.simps)
    using 1 2 3 by auto
qed

text \<open>Wait\<close>
lemma test4: "big_step (Wait 2)
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [WaitBlock 2])"
  apply (rule waitB2)
  by auto

text \<open>Seq\<close>
lemma test5: "big_step (Wait 2; Cm (Send ''ch'' (\<lambda>_. 1)))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [WaitBlock 2, OutBlock 0 ''ch'' 1 ({''ch''}, {})])"
  apply (rule seqB[OF test4])
  apply (rule sendB2)
  by auto

text \<open>Communication after delay 2\<close>
lemma test6: "par_big_step (PProc [
  Wait 2; Cm (Send ''ch'' (\<lambda>_. 1)),
  Cm (Receive ''ch'' X)])
    (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
    (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [ParWaitBlock 2 ((\<lambda>d. if 0 \<le> d \<and> d \<le> 2 then [\<lambda>_. 0, \<lambda>_. 0] else undefined)), 
                                  IOBlock 1 0 ''ch'' X 1])"
proof -
  have 1: "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)(X := 1)] [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)

  have 11: "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)] [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)

  have 2: "combine_blocks [\<lambda>_. 0, \<lambda>_. 0] [[OutBlock 0 ''ch'' 1 ({''ch''}, {})], [InBlock 0 ''ch'' X 1 ({}, {''ch''})]] [IOBlock 1 0 ''ch'' X 1]"
    apply (rule combine_blocks.intros(3))
     unfolding remove_pair_def Let_def apply auto
     by (rule 1)

   have 3: "(\<lambda>d. if 0 \<le> d \<and> d \<le> 2 then wait_block_state_list [\<lambda>_. 0, \<lambda>_. 0] d 
            [[WaitBlock 2, OutBlock 0 ''ch'' 1 ({''ch''}, {})], [InBlock 2 ''ch'' X 1 ({}, {''ch''})]] 
                                  else undefined)
           = (\<lambda>d. if 0 \<le> d \<and> d \<le> 2 then [\<lambda>_. 0, \<lambda>_. 0] else undefined)"
     by auto
    
  have 4: "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)]
     [[WaitBlock 2, OutBlock 0 ''ch'' 1 ({''ch''}, {})],
      [InBlock 2 ''ch'' X 1 ({}, {''ch''})]]
     [ParWaitBlock 2 (\<lambda>d. if 0 \<le> d \<and> d \<le> 2 then [(\<lambda>_. 0), (\<lambda>_. 0)] else undefined), IOBlock 1 0 ''ch'' X 1]"
   using combine_blocks.intros(4)[of 0 "[[WaitBlock 2, OutBlock 0 ''ch'' 1 ({''ch''}, {})],
      [InBlock 2 ''ch'' X 1 ({}, {''ch''})]]" 2
     "[(\<lambda>_. 0), (\<lambda>_. 0)]"] 
   apply (auto simp add: less_Suc_eq if_split)
   unfolding remove_one_def Let_def apply auto
   using 2 3 
   by auto
  show ?thesis
    apply (rule parallelB2[OF test5 test2b])
       apply (auto simp add: compat_rdy_block_pair_def less_Suc_eq combine_par_trace.simps)
    using 11 4 by auto
qed


text \<open>Loop one time\<close>
lemma test7: "big_step (Rep (Assign X (\<lambda>s. s X + 1); Cm (Send ''ch'' (\<lambda>s. s X))))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [TauBlock ((\<lambda>_. 0)(X := 1)), OutBlock 0 ''ch'' 1 ({''ch''}, {})])"
  apply (rule RepetitionB2)
   apply (rule seqB)
    apply (rule assignB)
  apply auto[1]
   apply (rule sendB2[where dly=0])
   apply auto
  apply (rule RepetitionB1)
  done

text \<open>Loop two times\<close>
lemma test8: "big_step (Rep (Assign X (\<lambda>s. s X + 1); Cm (Send ''ch'' (\<lambda>s. s X))))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [TauBlock ((\<lambda>_. 0)(X := 1)), OutBlock 0 ''ch'' 1 ({''ch''}, {}),
                        TauBlock ((\<lambda>_. 0)(X := 2)), OutBlock 0 ''ch'' 2 ({''ch''}, {})])"
  apply (rule RepetitionB2)
  apply (rule seqB)
  apply (rule assignB)
   apply auto[1]
  apply (rule sendB2[where dly=0])
   apply auto
  apply (rule RepetitionB2)
   apply (rule seqB)
  apply (rule assignB)
   apply auto[1]
   apply (rule sendB2[where dly=0])
   apply auto
  apply (rule RepetitionB1)
  done

text \<open>External choice 1\<close>
lemma test9a: "big_step (EChoice [(Send ''ch'' (\<lambda>_. 1), Wait 1), (Send ''ch2'' (\<lambda>_. 2), Wait 2)])
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [OutBlock 0 ''ch'' 1 ({''ch'', ''ch2''}, {}), WaitBlock 1])"
  apply (rule EChoiceSendB[where i=0])
    apply (auto simp add: extend_send_def)
  apply (rule waitB2)
  by auto

text \<open>External choice 2\<close>
lemma test9b: "big_step (EChoice [(Send ''ch'' (\<lambda>_. 1), Wait 1), (Send ''ch2'' (\<lambda>_. 2), Wait 2)])
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [OutBlock 0 ''ch2'' 2 ({''ch'', ''ch2''}, {}), WaitBlock 2])"
  apply (rule EChoiceSendB[where i=1])
    apply (auto simp add: extend_send_def)
  apply (rule waitB2)
  by auto

text \<open>Communication with external choice\<close>
lemma test10: "par_big_step (PProc [
  EChoice [(Send ''ch'' (\<lambda>_. 1), Wait 1), (Send ''ch2'' (\<lambda>_. 2), Wait 2)],
  Cm (Receive ''ch'' X)])
    (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
    (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [IOBlock 1 0 ''ch'' X 1, 
        ParWaitBlock 1 (\<lambda>d. if 0 \<le> d \<and> d \<le> 1 then [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] else undefined)])"
proof -
  have 1: "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)] [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)

  have 11: "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)(X := 1)] [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)

  have 2: "(\<lambda>d. if 0 \<le> d \<and> d \<le> 1 then wait_block_state_list [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] 
            d [[WaitBlock 1], []] else undefined)
         = (\<lambda>d. if 0 \<le> d \<and> d \<le> 1 then [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] else undefined)"
    by auto

  have 3: "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)]
     [[OutBlock 0 ''ch'' 1 ({''ch'', ''ch2''}, {}), WaitBlock 1],
      [InBlock 0 ''ch'' X 1 ({}, {''ch''})]]
     [IOBlock 1 0 ''ch'' X 1, ParWaitBlock 1 ((\<lambda>d. if 0 \<le> d \<and> d \<le> 1 then [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] else undefined))]"
    apply (rule combine_blocks.intros(3)[where i=1 and j=0])
    apply (auto simp add: remove_pair_def)
    using combine_blocks.intros(4)[where i=0 and t=1 and blkss="[[WaitBlock 1], []]" 
            and sts="[\<lambda>_. 0, (\<lambda>_. 0)(X := 1)]"]
    apply (auto simp add: remove_one_def less_Suc_eq)
    using 11 2 by auto
  show ?thesis
    apply (rule parallelB2[OF test9a test2a])
    apply (auto simp add: compat_rdy_block_pair_def less_Suc_eq combine_par_trace.simps)
    using 1 3 by auto
qed

text \<open>ODE Example 1\<close>
lemma test11: "big_step (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [ODEBlock 1 (restrict (\<lambda>t. (\<lambda>_. 0)(X := t)) {0..1})])"
  apply (rule ContB)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
  by (auto intro!: derivative_intros)

text \<open>ODE Example 2\<close>
lemma test11b: "big_step (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 2), Y := (\<lambda>s. s X)))) (\<lambda>s. s Y < 1))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [ODEBlock 1 (restrict (\<lambda>t. (\<lambda>_. 0)(X := 2 * t, Y := t ^ 2)) {0..1})])"
  apply (rule ContB)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
   apply (auto simp: vars_distinct)
  apply (rule has_vector_derivative_eq_rhs)
     apply (auto intro!: derivative_intros)[1] apply simp
   apply (rule has_vector_derivative_eq_rhs)
    unfolding power2_eq_square apply (auto intro!: derivative_intros)[1] apply simp
  by (metis (full_types) less_1_mult less_eq_real_def mult_le_one mult_less_cancel_left1)

text \<open>ODE Example 3\<close>
lemma test11c: "big_step (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>s. - s Y), Y := (\<lambda>s. s X)))) (\<lambda>s. s Y < 1))
        (Trace ((\<lambda>_. 0)(X := 1)) [])
        (Trace ((\<lambda>_. 0)(X := 1)) [ODEBlock (pi / 2) (restrict (\<lambda>t. (\<lambda>_. 0)(X := cos t, Y := sin t)) {0..pi / 2})])"
proof -
  have 1: "sin t < 1" if "0 \<le> t" "t * 2 < pi" for t
  proof (cases "t = 0")
    case True
    then show ?thesis by auto
  next
    case False
    have "0 < cos t"
      apply (rule cos_gt_zero) using that False by auto
    then show ?thesis
      using sin_cos_squared_add[of t, unfolded power2_eq_square]
      using less_eq_real_def by fastforce
  qed
  show ?thesis
    apply (rule ContB[where d="pi / 2"])
         apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def vars_distinct)
      apply (rule has_vector_derivative_projI)
      apply (auto simp: vars_distinct)
      apply (rule has_vector_derivative_eq_rhs)
    unfolding has_vector_derivative_def
       apply (auto intro!: derivative_intros)[1] apply simp
     apply (auto intro!: derivative_intros)[1]
    by (auto intro: 1)
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

theorem Valid_ex_pre:
  "Valid (\<lambda>tr. \<exists>x. P x tr) c Q \<longleftrightarrow> (\<forall>x. Valid (P x) c Q)"
  unfolding Valid_def by auto

theorem Valid_and_pre:
  "Valid (\<lambda>t. P t \<and> P2) c Q \<longleftrightarrow> (P2 \<longrightarrow> (Valid P c Q))"
  unfolding Valid_def by auto

theorem Valid_cond:
  assumes "b \<Longrightarrow> Valid P c Q1"
      and "\<not>b \<Longrightarrow> Valid P c Q2"
    shows "Valid P c (if b then Q1 else Q2)" 
  using assms Valid_def by auto

inductive_cases skipE :"big_step Skip tr tr2"
thm skipE

inductive_cases assignE: "big_step (Assign var e) tr tr2"
thm assignE

inductive_cases sendE: "big_step (Cm (Send ch e)) tr tr2"
thm sendE

inductive_cases receiveE: "big_step (Cm (Receive ch var)) tr tr2"
thm receiveE

inductive_cases seqE: "big_step (Seq p1 p2) tr tr3"
thm seqE

inductive_cases waitE: "big_step (Wait d) tr tr2"
thm waitE

inductive_cases repE: "big_step (Rep p) tr tr2"
thm repE

inductive_cases echoiceE: "big_step (EChoice cs) tr tr2"
thm echoiceE

inductive_cases contE: "big_step (Cont ode b) tr tr2"
thm contE

inductive_cases interruptE: "big_step (Interrupt ode cs) tr tr2"
thm interruptE

theorem Valid_skip:
  "Valid
    (\<lambda>t. t = tr)
    (Skip)
    (\<lambda>t. t = tr)"
  unfolding Valid_def by (auto elim: skipE)

theorem Valid_assign:
  "Valid
    (\<lambda>t. t = tr)
    (Assign var e)
    (\<lambda>t. t = extend_trace tr (TauBlock ((end_of_trace tr)(var := e (end_of_trace tr)))))"
  unfolding Valid_def by (auto elim: assignE)

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
    (\<lambda>t. t = extend_trace tr (WaitBlock d))"
  unfolding Valid_def by (auto elim!: waitE)

theorem Valid_rep:
  assumes "Valid P c P"
  shows "Valid P (Rep c) P"
proof -
  have 1: "big_step p tr tr2 \<Longrightarrow> p = Rep c \<Longrightarrow>
        \<forall>tr tr2. P tr \<longrightarrow> big_step c tr tr2 \<longrightarrow> P tr2 \<Longrightarrow> P tr \<Longrightarrow> P tr2" for p tr tr2
    by (induct rule: big_step.induct, auto)
  show ?thesis
    using assms 1 unfolding Valid_def by auto
qed

theorem Valid_echoice:
  assumes "\<forall>i<length es.
    case (es ! i) of
      (Send ch e, p2) \<Rightarrow> \<forall>dly. Valid (\<lambda>t. t = extend_send ch e dly (rdy_of_echoice es) tr) p2 R
    | (Receive ch var, p2) \<Rightarrow> \<forall>dly v. Valid (\<lambda>t. t = extend_receive ch var dly v (rdy_of_echoice es) tr) p2 R"
  shows
    "Valid (\<lambda>t. t = tr) (EChoice es) R"
proof -
  have 1: "R tr2" if "i < length es" "es ! i = (ch[!]e, p2)" "big_step p2 (extend_send ch e dly (rdy_of_echoice es) tr) tr2"
    for tr2 i ch e p2 dly
  proof -
    have "Valid (\<lambda>t. t = extend_send ch e dly (rdy_of_echoice es) tr) p2 R"
      using assms that by auto
    then show ?thesis
      unfolding Valid_def using that(3) by auto
  qed
  have 2: "R tr2" if "i < length es" "es ! i = (ch[?]var, p2)" "big_step p2 (extend_receive ch var dly v (rdy_of_echoice es) tr) tr2"
    for tr2 i ch var p2 dly v
  proof -
    have "Valid (\<lambda>t. t = extend_receive ch var dly v (rdy_of_echoice es) tr) p2 R"
      using assms that by auto
    then show ?thesis
      unfolding Valid_def using that(3) by auto
  qed
  show ?thesis
    unfolding Valid_def apply (auto elim!: echoiceE)
    using 1 2 by auto
qed

text \<open>Hoare triple for ODE with unique solution\<close>
theorem Valid_ode_solution:
  assumes "\<forall>d2 p2. d2 \<ge> 0 \<longrightarrow> ODEsol ode p2 d2 \<longrightarrow>
      (\<forall>t. t \<ge> 0 \<and> t < d2 \<longrightarrow> b (p2 t)) \<longrightarrow>
      \<not> b (p2 d2) \<longrightarrow> p2 0 = end_of_trace tr \<longrightarrow>d2 = d \<and> (restrict p {0..d} = restrict p2 {0..d2})"
  shows "Valid
     (\<lambda>t. t = tr)
     (Cont ode b)
     (\<lambda>t. t = extend_trace tr (ODEBlock d (restrict p {0..d})))"
  unfolding Valid_def using assms 
  by (metis contE)


text \<open>Hoare triple for ODE with non-unique solutions\<close>
theorem Valid_ode_all_solution:
  assumes "\<forall>d p. d \<ge> 0 \<longrightarrow> ODEsol ode p d \<longrightarrow>
      (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
      \<not> b (p d) \<longrightarrow> p 0 = end_of_trace tr \<longrightarrow> Q d p"
  shows "Valid
    (\<lambda>t. t = tr)
    (Cont ode b)
    (\<lambda>t. \<exists>d p. t = extend_trace tr (ODEBlock d (restrict p {0..d})) \<and> d \<ge> 0 \<and> p 0 = end_of_trace tr \<and> Q d p)"
  unfolding Valid_def using assms by (metis contE)

theorem Valid_interrupt:
  assumes "\<forall>i<length es.
    case (es ! i) of
      (Send ch e, p2) \<Rightarrow>
        \<forall>p d. d \<ge> 0 \<longrightarrow> ODEsol ode p d \<longrightarrow> p 0 = end_of_trace tr \<longrightarrow>
              Valid (\<lambda>t. t = extend_trace tr (ODEOutBlock d (restrict p {0..d}) ch (e (p d)) (rdy_of_echoice es))) p2 R
    | (Receive ch var, p2) \<Rightarrow>
        \<forall>p d v. d \<ge> 0 \<longrightarrow> ODEsol ode p d \<longrightarrow> p 0 = end_of_trace tr \<longrightarrow>
              Valid (\<lambda>t. t = extend_trace tr (ODEInBlock d (restrict p {0..d}) ch var v (rdy_of_echoice es))) p2 R"
  shows
    "Valid (\<lambda>t. t = tr) (Interrupt ode es) R"
proof -
  have 1: "R tr2" if "0 \<le> d" "ODEsol ode p d"
       "p 0 = end_of_trace tr"
       "i < length es"
       "es ! i = (ch[!]e, p2)" "big_step p2 (extend_trace tr (ODEOutBlock d (restrict p {0..d}) ch (e (p d)) (rdy_of_echoice es))) tr2"
     for tr2 d p i ch e p2
  proof -
    have "Valid (\<lambda>t. t = extend_trace tr (ODEOutBlock d (restrict p {0..d}) ch (e (p d)) (rdy_of_echoice es))) p2 R"
      using assms that(1-5) by auto
    then show ?thesis
      unfolding Valid_def using that(6) by auto
  qed
  have 2: "R tr2" if "0 \<le> d" "ODEsol ode p d"
       "p 0 = end_of_trace tr"
       "i < length es"
       "es ! i = (ch[?]var, p2)" "big_step p2 (extend_trace tr (ODEInBlock d (restrict p {0..d}) ch var v (rdy_of_echoice es))) tr2"
     for tr2 d p i ch var p2 v
  proof -
    have "Valid (\<lambda>t. t = extend_trace tr (ODEInBlock d (restrict p {0..d}) ch var v (rdy_of_echoice es))) p2 R"
      using assms that(1-5) by auto
    then show ?thesis
      unfolding Valid_def using that(6) by auto
  qed
  show ?thesis
    unfolding Valid_def apply (auto elim!: interruptE)
    using 1 2 by auto
qed


text \<open>Differential invariant rule\<close>

lemma Valid_ode_invariant:
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>S. g' (state2vec S) (ODE2Vec ode S) = 0"
  shows "Valid
    (\<lambda>t. t = tr)
    (Cont ode b)
    (\<lambda>t. \<exists>d p. t = extend_trace tr (ODEBlock d (restrict p {0..d})) \<and>
               d \<ge> 0 \<and> p 0 = end_of_trace tr \<and>
               (\<forall>t. 0\<le>t \<and> t\<le>d \<longrightarrow> inv (p t) = inv (p 0)))"
  apply(rule Valid_ode_all_solution)
  apply auto
  subgoal premises pre for d p t
  proof-
    have 1: "\<forall>t\<in>{0 .. d}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))) (at t within {0 .. d})"
      using pre assms
      using chainrule[of inv "\<lambda>x. g'(state2vec x)" ode p d] 
      by auto
    have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec ode (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec ode (p t))" if "t\<in>{0 .. d}" for t
      using 1 unfolding has_derivative_def bounded_linear_def 
      using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))"]
      by blast
    have 3: "\<forall>s. (s *\<^sub>R 1) = s" by simp
    have 4: "\<forall>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)) = s *\<^sub>R g' (state2vec(p t)) (ODE2Vec ode (p t))" if "t\<in>{0 .. d}" for t
      using 2 3 that by auto
    have 5: "\<forall>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t))= 0" if "t\<in>{0 .. d}" for t
      using 4 assms(2) that by simp 
    show ?thesis
      using mvt_real_eq[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec ode (p t)))" t]
      using 1 5 pre by auto
  qed
  done


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

inductive_cases combine_blocksE1: "combine_blocks sts blkss []"
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

theorem Valid_skip2:
  "Q tr \<Longrightarrow>
   Valid
    (\<lambda>t. t = tr)
    (Skip)
    Q"
  using Valid_def skipE by blast

theorem Valid_assign2:
  "Q (extend_trace tr (TauBlock ((end_of_trace tr)(var := e (end_of_trace tr))))) \<Longrightarrow>
   Valid
    (\<lambda>t. t = tr)
    (Assign var e)
    Q"
  using Valid_def assignE by blast

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

theorem Valid_wait2:
  "Q (extend_trace tr (WaitBlock d)) \<Longrightarrow>
   Valid
    (\<lambda>t. t = tr)
    (Wait d)
    Q"
  using Valid_def waitE by blast

theorem Valid_ode_solution2:
  assumes "\<forall>d2 p2. d2 \<ge> 0 \<longrightarrow> ODEsol ode p2 d2 \<longrightarrow>
      (\<forall>t. t \<ge> 0 \<and> t < d2 \<longrightarrow> b (p2 t)) \<longrightarrow>
      \<not> b (p2 d2) \<longrightarrow> p2 0 = end_of_trace tr \<longrightarrow> d2 = d \<and> (restrict p {0..d} = restrict p2 {0..d2})"
    and "Q (extend_trace tr (ODEBlock d (restrict p {0..d})))"
  shows "Valid
     (\<lambda>t. t = tr)
     (Cont ode b)
     Q"
  unfolding Valid_def using assms by (metis contE)

theorem Valid_ode_solution3:
  assumes "\<not> b (end_of_trace tr)"
      and "Q (extend_trace tr (ODEBlock 0 (restrict (\<lambda>t. end_of_trace tr) {0..0})))"
    shows "Valid
     (\<lambda>t. t = tr)
     (Cont ode b)
     Q"
proof-
  have main: "restrict p2 {0..d2} = restrict (\<lambda>t. end_of_trace tr) {0..0} \<and> d2 = 0"
    if cond: "0 \<le> d2"
       "ODEsol ode p2 d2"
       "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t)"
       "\<not> b (p2 d2)"
       "p2 0 = (end_of_trace tr)"
     for p2 d2
  proof-
    have "d2\<le>0" using cond(3) cond(5) assms(1) by auto
    then have "d2=0" using cond(1) by auto
    then show ?thesis using cond(5) by auto
  qed
  show ?thesis 
    apply(rule Valid_ode_solution2[where d=0 and p="(\<lambda>t. end_of_trace tr)"]) 
    using main assms by auto
qed

theorem Valid_ode_unique_solution:
  assumes "d \<ge> 0" "ODEsol ode p d" "\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)"
      "\<not> b (p d)" "p 0 = end_of_trace tr"
      "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec ode (vec2state v))"
      "Q (extend_trace tr (ODEBlock d (restrict p {0..d})))"
  shows "Valid
    (\<lambda>t. t = tr)
    (Cont ode b)
    Q"
proof -
  have main: "d2 = d \<and> restrict p {0..d} = restrict p2 {0..d2}"
    if cond: "0 \<le> d2"
       "ODEsol ode p2 d2"
       "(\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t))"
       "\<not> b (p2 d2)"
       "p2 0 = end_of_trace tr"
     for p2 d2
  proof -
    interpret loc:ll_on_open_it "{-1<..}"
      "\<lambda>t v. ODE2Vec ode (vec2state v)" UNIV 0
      apply standard
      using assms(6) by auto
    have s1: "((\<lambda>t. state2vec (p t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d} UNIV"
      using assms(2) unfolding ODEsol_def solves_ode_def by auto
    have s2: "(loc.flow 0 (state2vec (end_of_trace tr))) t = (\<lambda>t. state2vec (p t)) t" if "t \<in> {0..d}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s1])
      using that by (auto simp add: state2vec_def assms(1,5))
    have s3: "((\<lambda>t. state2vec(p2 t)) solves_ode ((\<lambda>t v. ODE2Vec ode (vec2state v)))) {0..d2} UNIV"
      using cond(2) unfolding ODEsol_def solves_ode_def by auto
    have s4: "loc.flow 0 (state2vec (end_of_trace tr)) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
      apply (rule loc.maximal_existence_flow(2)[OF s3])
      using cond(1,5) that by auto
    have s5: "d \<le> d2"
    proof (rule ccontr)
      assume 0: "\<not>(d \<le> d2)"
      from 0 have 1: "(\<lambda>t. state2vec (p t)) d2 = (\<lambda>t. state2vec (p2 t)) d2"
        using s2[of d2] s4[of d2] cond(1) by auto
      from 1 have "p d2 = p2 d2"
        by (auto simp add: state2vec_def)
      show False
        using "0" \<open>p d2 = p2 d2\<close> assms(3) that(1) that(4) by auto
    qed
    have s6: "d2 \<le> d"
    proof (rule ccontr)
      assume 0: "\<not>(d2 \<le> d)"
      from 0 have 1: "(\<lambda>t. state2vec (p t)) d = (\<lambda>t. state2vec (p2 t)) d"
        using s2[of d] s4[of d] assms(1) by auto
      from 1 have "p d = p2 d"
        by (auto simp add: state2vec_def)
      show False
        using "0" \<open>p d = p2 d\<close> assms(1) assms(4) that(3) by auto
    qed
    have s7: "d = d2" using s5 s6 by auto
    have s8: "t\<in>{0..d} \<Longrightarrow> p2 t = p t" for t
      using s2 s4 s7 by (metis vec_state_map1)
    have s9: "restrict p2 {0..d2} = restrict p {0..d}"
      using s7 s8 unfolding restrict_def by auto
    show ?thesis using s7 s9 by auto
  qed
  show ?thesis
    apply (rule Valid_ode_solution2[where d=d and p=p])
    using main assms(7) by auto
qed


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

lemma combine_blocks_triv2:
  "combine_blocks sts [[], []] par_blks \<Longrightarrow> par_blks = []"
proof (induct rule: combine_blocks.cases)
case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 0 \<or> i = 1"
    using 2  by auto
  then show ?case using 2 by auto
next
  case (3 i blkss j c v pblks)
  have "i = 0 \<or> i = 1"
    using 3  by auto
  then show ?case using 3 by auto
next
  case (4 i blkss t sts pblks)
 have "i = 0 \<or> i = 1"
    using 4  by auto
  then show ?case using 4 by auto
qed

lemma combine_blocks_IO2:
  "combine_blocks sts [OutBlock d1 ch1 v1 rdy1 # blks1,
                   InBlock d2 ch2 var v2 rdy2 # blks2] par_tr \<Longrightarrow>
   (\<exists>rest. d1 = 0 \<and> d2 = 0 \<and> ch1 = ch2 \<and> v1 = v2 \<and>
           combine_blocks (sts[1 := end_of_blocks (sts ! 1) [InBlock d2 ch2 var v2 rdy2]]) [blks1, blks2] rest \<and> par_tr = (IOBlock 1 0 ch1 var v1) # rest)"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 0 \<or> i = 1"
    using 2 by auto
  then show ?case using 2 by auto
next
  case (3 i blkss j c v x stsa pblks)
  have "length blkss = 2"
    using 3  by auto
  have "i = 0 \<or> i = 1" "j = 0 \<or> j = 1"
    using 3 by auto
  then have ij: "i = 1" "j = 0"
    using 3  by auto
  have "d1 = 0" "d2 = 0"
    using 3  ij by auto
  moreover have "v1 = v2" "ch1 = ch2" "v = v1" "c = ch1"
    using 3  ij by auto
  moreover have "\<exists>rest. combine_blocks (stsa[i := end_of_blocks (stsa ! i) [hd (blkss ! i)]]) [blks1, blks2] rest \<and> par_tr = (IOBlock 1 0 ch1 var v1) # rest"
    apply (rule exI[where x="pblks"])
    using 3 ij
    by (auto simp add: remove_pair_def)
  ultimately show ?case
    using 3 ij by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
   have "i = 0 \<or> i = 1"
    using 4 by auto
  then show ?case using 4 by auto 
qed

lemma combine_blocks_ODEIO2:
  "combine_blocks sts [ODEOutBlock d1 h ch1 v1 rdy1 # blks1,
                   InBlock d2 ch2 var v2 rdy2 # blks2] par_tr \<Longrightarrow>
   (\<exists>rest. d1 = 0 \<and> d2 = 0 \<and> ch1 = ch2 \<and> v1 = v2 \<and>
           combine_blocks (sts[1 := end_of_blocks (sts ! 1) [InBlock d2 ch2 var v2 rdy2]]) [blks1, blks2] rest \<and> par_tr = (IOBlock 1 0 ch1 var v1) # rest)"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 0 \<or> i = 1"
    using 2 by auto
  then show ?case using 2 by auto
next
  case (3 i blkss j c v x stsa pblks)
  have "length blkss = 2"
    using 3  by auto
  have "i = 0 \<or> i = 1" "j = 0 \<or> j = 1"
    using 3 by auto
  then have ij: "i = 1" "j = 0"
    using 3  by auto
  have "d1 = 0" "d2 = 0"
    using 3  ij by auto
  moreover have "v1 = v2" "ch1 = ch2" "v = v1" "c = ch1"
    using 3  ij by auto
  moreover have "\<exists>rest. combine_blocks (stsa[i := end_of_blocks (stsa ! i) [hd (blkss ! i)]]) [blks1, blks2] rest \<and> par_tr = (IOBlock 1 0 ch1 var v1) # rest"
    apply (rule exI[where x="pblks"])
    using 3 ij
    by (auto simp add: remove_pair_def)
  ultimately show ?case
    using 3 ij by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
   have "i = 0 \<or> i = 1"
    using 4 by auto
  then show ?case using 4 by auto 
qed

lemma combine_blocks_IO2':
  "combine_blocks sts [InBlock d2 ch2 var v2 rdy2 # blks2,
                       OutBlock d1 ch1 v1 rdy1 # blks1] par_tr \<Longrightarrow>
  (\<exists>rest. d1 = 0 \<and> d2 = 0 \<and> ch1 = ch2 \<and> v1 = v2 \<and>
           combine_blocks (sts[0 := end_of_blocks (sts ! 0) [InBlock d2 ch2 var v2 rdy2]]) [blks2, blks1] rest \<and> par_tr = (IOBlock 0 1 ch1 var v1) # rest)"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 0 \<or> i = 1"
    using 2  by auto
  then show ?case using 2 by auto
next
  case (3 i blkss j c v x stsa pblks)
  have "length blkss = 2"
    using 3  by auto
  have "i = 0 \<or> i = 1" "j = 0 \<or> j = 1"
    using 3  by auto
  then have ij: "i = 0" "j = 1"
    using 3  by auto
  have "d1 = 0" "d2 = 0"
    using 3  ij by auto
  moreover have "v1 = v2" "ch1 = ch2" "v = v1" "c = ch1"
    using 3 ij by auto
  moreover have "\<exists>rest. combine_blocks (sts[0 := end_of_blocks (sts ! 0) [InBlock d2 ch2 var v2 rdy2]]) [blks2, blks1] rest \<and> par_tr = (IOBlock 0 1 ch1 var v1) # rest"
    apply (rule exI[where x="pblks"])
    using 3  unfolding ij \<open>v = v1\<close> \<open>c = ch1\<close> 3(1)[symmetric] 3(12)
    by (auto simp add: remove_pair_def)
  ultimately show ?case
    using 3 by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
   have "i = 0 \<or> i = 1"
    using 4 by auto
  then show ?case using 4 by auto 
qed

definition sts_init :: "state list" where
  "sts_init == [(\<lambda>_. 0), (\<lambda>_. 0)]"
declare sts_init_def [simp]

lemma combine_blocks_OutW2:
  "combine_blocks sts_init [OutBlock d1 ch1 v ({ch1}, {}) # blks1,
                            WaitBlock d2 # blks2] par_tr \<Longrightarrow>
   \<exists>rest. d1 \<ge> d2 \<and>
          combine_blocks sts_init  [OutBlock (d1 - d2) ch1 v ({ch1}, {}) # blks1, blks2] rest \<and>
          par_tr = (ParWaitBlock d2 (\<lambda>d. if 0 \<le> d \<and> d \<le> d2 then sts_init else undefined)) # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss stsa pblks)
  then show ?case by (auto simp add: less_Suc_eq)
next
  case (3 i blkss j c v pblks)
  then show ?case by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
  have "i = 1"
    using 4  by (auto simp add: less_Suc_eq)
  then have 1: "t = d2"
    using 4 by auto
  then have 2: "d1 \<ge> d2"
    using 4 by auto
  show ?case
    apply (rule exI[where x=pblks])
    using 4  \<open>i = 1\<close> \<open>d1 \<ge> d2\<close> \<open>t = d2\<close>
    by (auto simp add: remove_one_def Let_def)
qed

lemma combine_blocks_ODEOutW2:
  "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)(X := 1)] [ODEOutBlock d1 h ch1 v ({ch1}, {}) # blks1,
                            WaitBlock d2 # blks2] par_tr \<Longrightarrow>
   \<exists>rest. d1 \<ge> d2 \<and>
          combine_blocks [h d2, (\<lambda>_. 0)(X := 1)] [ODEOutBlock (d1 - d2) (\<lambda>s. h (s + d2)) ch1 v ({ch1}, {}) # blks1, blks2] rest \<and>
          par_tr = (ParWaitBlock d2 (\<lambda>d. if 0 \<le> d \<and> d \<le> d2 then [h d, (\<lambda>_. 0)(X := 1)] else undefined)) # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss stsa pblks)
  then show ?case by (auto simp add: less_Suc_eq)
next
  case (3 i blkss j c v pblks)
  then show ?case by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
  have "i = 1"
    using 4  by (auto simp add: less_Suc_eq)
  then have 1: "t = d2"
    using 4 by auto
  then have 2: "d1 \<ge> d2"
    using 4 by auto
  show ?case
    apply (rule exI[where x=pblks])
    using 4  \<open>i = 1\<close> \<open>d1 \<ge> d2\<close> \<open>t = d2\<close>
    by (auto simp add: remove_one_def Let_def)
qed

lemma combine_blocks_WaitNil2:
  "combine_blocks [sl, sr] [WaitBlock d # blks1, []] par_tr \<Longrightarrow>
   \<exists>rest. combine_blocks [sl, sr] [blks1, []] rest \<and> par_tr 
         = (ParWaitBlock d (\<lambda>t. if 0 \<le> t \<and> t \<le> d then [sl, sr] else undefined)) # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss sts pblks)
  then show ?case by (auto simp add: less_Suc_eq)
next
  case (3 i blkss j c v pblks)
  then show ?case
    by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
  have "i = 0" "t = d"
    using 4 by (auto simp add: less_Suc_eq)
  then have 5: "wait_block_state_list sts t blkss = sts"
               "wait_block_state_list sts d blkss = sts"
               "remove_one i t blkss = [blks1, []]"
    using 4 remove_one_def by auto
  show ?case
    apply (rule exI[where x=pblks])
    using 4 \<open>i = 0\<close> \<open>t = d\<close> 5  by auto
qed

lemma combine_blocks_NilWait2:
  "combine_blocks [sl, sr] [[], WaitBlock d # blks1] par_tr \<Longrightarrow>
    \<exists>rest. combine_blocks [sl, sr] [[], blks1] rest \<and> par_tr 
         = (ParWaitBlock d (\<lambda>t. if 0 \<le> t \<and> t \<le> d then [sl, sr] else undefined)) # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss sts pblks)
  then show ?case by (auto simp add: less_Suc_eq)
next
  case (3 i blkss j c v pblks)
  then show ?case
    by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
  have "i = 1" "t = d"
    using 4 by (auto simp add: less_Suc_eq)
  then have 5: "wait_block_state_list sts t blkss = sts"
               "wait_block_state_list sts d blkss = sts"
               "remove_one i t blkss = [[],blks1]"
    using 4 remove_one_def by auto
  show ?case
    apply (rule exI[where x=pblks])
    using 4 \<open>i = 1\<close> \<open>t = d\<close> 5  by auto
qed

lemma combine_blocks_TauNil2:
  "combine_blocks sts [TauBlock st # blks1, []] par_tr \<Longrightarrow>
   \<exists>rest. combine_blocks (sts[0 := st]) [blks1, []] rest \<and> par_tr = ParTauBlock 0 st # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss sts pblks)
  have "i = 0"  
    using 2 by (auto simp add: less_Suc_eq)
  show ?case
    apply (rule exI[where x=pblks])
    using 2 \<open>i = 0\<close> by (auto simp add: remove_one_def)
next
  case (3 i blkss j c v x sts pblks)
  then show ?case
    by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
  then show ?case 
    by (auto simp add: less_Suc_eq)
qed

lemma combine_blocks_ODENil2:
  "combine_blocks [sl, sr] [ODEBlock d p # blks1, []] par_tr \<Longrightarrow>
   \<exists>rest. combine_blocks [p d, sr] [blks1, []] rest \<and> par_tr = (ParWaitBlock d (\<lambda>t. if 0 \<le> t \<and> t \<le> d then [p t, sr] else undefined)) # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss sts pblks)
  have "i = 0"  
    using 2 by (auto simp add: less_Suc_eq)
  show ?case
    apply (rule exI[where x=pblks])
    using 2 \<open>i = 0\<close>  by (auto simp add: remove_one_def)
next
  case (3 i blkss j c v pblks)
  then show ?case
    by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
   have "i = 0"
    using 4  by (auto simp add: less_Suc_eq)
  then have 1: "t = d"
    using 4 by auto
  show ?case
    apply (rule exI[where x=pblks])
    using 4  \<open>i = 0\<close> \<open>t = d\<close>
    by (auto simp add: remove_one_def Let_def)
qed

lemma combine_blocks_TauIn2:
  "combine_blocks sts [TauBlock st # blks1, blk2 # blks2] par_tr \<Longrightarrow>
   event_of_block blk2 \<noteq> Tau \<Longrightarrow>
   \<exists>rest. combine_blocks (sts[0 := st]) [blks1, blk2 # blks2] rest \<and> par_tr = ParTauBlock 0 st # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss sts)
  then show ?case by auto
next
  case (2 i blkss sts pblks)
  have "i = 0" 
    using 2 by (auto simp add: less_Suc_eq)
  show ?case
    apply (rule exI[where x=pblks])
    using 2 \<open>i = 0\<close> by (auto simp add: remove_one_def)
next
  case (3 i blkss j c v pblks)
  then show ?case by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
  then show ?case by (auto simp add: less_Suc_eq)
qed

lemma combine_blocks_ODEIn2:
  "combine_blocks [sl, sr] [ODEBlock d p # blks1, (InBlock dly ch x r rdy) # blks2] par_tr \<Longrightarrow>
    \<exists>rest. dly \<ge> d \<and>
     combine_blocks [p d, sr] [blks1, wait_block d (InBlock dly ch x r rdy) # blks2] rest \<and> par_tr = 
       (ParWaitBlock d (restrict (\<lambda>t. [p t, sr]) {0..d})) # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss sts)
  then show ?case by auto
next
  case (2 i blkss sts pblks)
  have "i = 0"  
    using 2 by (auto simp add: less_Suc_eq)
  show ?case
    apply (rule exI[where x=pblks])
    using 2 \<open>i = 0\<close> by (auto simp add: remove_one_def)
next
  case (3 i blkss j c v pblks)
  then show ?case by (auto simp add: less_Suc_eq)
next
  case (4 i blkss t sts pblks)
  have 40: "i = 0"
    using 4  by (auto simp add: less_Suc_eq)
  then have 41: "t = d"
    using 4 by auto
  then have 11: "dly \<ge> d"
    using 4 by auto
  have 42: "(wait_block_state_list sts t blkss) = [p d, sr]"
    using 4 41 by auto
  have 43: "remove_one i t blkss = [blks1, wait_block d (InBlock dly ch x r rdy) # blks2]"
    using 4(2) 41 40 unfolding remove_one_def Let_def by auto
  have 44: "(\<lambda>d. if 0 \<le> d \<and> d \<le> t then wait_block_state_list sts d blkss else undefined)
          = (\<lambda>t\<in>{0..d}. [p t, sr])" 
    using 41 4(1, 2) 11 by auto
  show ?case
    apply (rule exI[where x=pblks])
    using 44 4 \<open>i = 0\<close> \<open>t = d\<close> 42 43 11 by auto
 qed


lemma combine_blocks_OutNil:
  "combine_blocks sts [OutBlock d1 ch1 v ({ch1}, {}) # blks1, []] par_tr \<Longrightarrow> False"
  apply (induct rule: combine_blocks.cases)
  by (auto simp add: less_Suc_eq)

lemma combine_blocks_NilIn:
  "combine_blocks sts  [[], InBlock d2 ch2 var v2 ({}, {ch2}) # blks2] par_tr \<Longrightarrow> False"
  apply (induct rule: combine_blocks.cases)
  by (auto simp add: less_Suc_eq)

lemma combine_blocks_OOutNil:
  "combine_blocks sts [ODEOutBlock d1 p ch1 v ({ch1}, {}) # blks1, []] par_tr \<Longrightarrow> False"
  apply (induct rule: combine_blocks.cases)
  by (auto simp add: less_Suc_eq)



subsection \<open>More on combine_par_trace\<close>

inductive_cases combine_par_traceE: "combine_par_trace trs par_tr"
thm combine_par_traceE

lemma combine_par_traceE2:
  "combine_par_trace [Trace st1 blks1, Trace st2 blks2] par_tr \<Longrightarrow>
   \<exists>par_blks. par_tr = ParTrace [st1, st2] par_blks \<and> combine_blocks [st1, st2] [blks1, blks2] par_blks"
  apply (elim combine_par_traceE)
  apply auto
  apply (smt length_Cons less_Suc0 less_Suc_eq list.size(3) nth_Cons_0 nth_Cons_Suc nth_equalityI start_of_trace.simps)
  by (smt length_Cons less_Suc0 less_Suc_eq list.size(3) nth_Cons_0 nth_Cons_Suc nth_equalityI start_of_trace.simps)


subsection \<open>Examples\<close>

text \<open>Send 1\<close>
lemma testHL1:
  "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) [])
    (Cm (Send ''ch'' (\<lambda>_. 1)))
    (\<lambda>t. \<exists>dly. t = Trace (\<lambda>_. 0) [OutBlock dly ''ch'' 1 ({''ch''}, {})])"
  apply (rule Valid_send2)
  by (auto simp add: extend_send_def)

text \<open>Send 1, then send 2\<close>
lemma testHL2:
  "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) [])
    (Cm (Send ''ch'' (\<lambda>_. 1)); Cm (Send ''ch'' (\<lambda>_. 2)))
    (\<lambda>t. \<exists>dly dly2. t = Trace (\<lambda>_. 0) [OutBlock dly ''ch'' 1 ({''ch''}, {}),
                                       OutBlock dly2 ''ch'' 2 ({''ch''}, {})])"
  apply (rule Valid_seq[OF testHL1])
  apply (rule Valid_send3)
  by (auto simp add: extend_send_def)

text \<open>Receive from ch\<close>
lemma testHL3:
  "Valid
    (\<lambda>tr. tr = Trace (\<lambda>_. 0) [])
    (Cm (Receive ''ch'' X))
    (\<lambda>tr. \<exists>dly v. tr = Trace (\<lambda>_. 0) [InBlock dly ''ch'' X v ({}, {''ch''})])"
  apply (rule Valid_receive2)
  by (auto simp add: extend_receive_def)


text \<open>Communication\<close>
lemma testHL4:
  "ParValid
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
    (PProc [Cm (Send ''ch'' (\<lambda>_. 1)), Cm (Receive ''ch'' X)])
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [IOBlock 1 0 ''ch'' X 1])"
proof -
  have 1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] [IOBlock 1 0 ''ch'' X 1]"
    if tr1: "tr1 = Trace (\<lambda>_. 0) [OutBlock dly1 ''ch'' 1 ({''ch''}, {})]" and
       tr2: "tr2 = Trace (\<lambda>_. 0) [InBlock dly2 ''ch'' X v ({}, {''ch''})]" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t dly1 dly2 v tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] par_blks" and
      2: "combine_blocks [\<lambda>_. 0, \<lambda>_. 0] [
              [OutBlock dly1 ''ch'' 1 ({''ch''}, {})],
              [InBlock dly2 ''ch'' X v ({}, {''ch''})]] par_blks"
      using combine_par_traceE2 by blast
    from 2 obtain rest where
      3: "dly1 = 0" "dly2 = 0" "v = 1" "combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X:=1)] [[], []] rest"
         "par_blks = (IOBlock 1 0 ''ch'' X 1) # rest"
      using combine_blocks_IO2[of "[\<lambda>_. 0, \<lambda>_. 0]" dly1 "''ch''" 1 "({''ch''}, {})" "[]"
                                  dly2 "''ch''" X v "({}, {''ch''})" "[]" par_blks]
      by auto
    from 3(4) have 4: "rest = []"
      using combine_blocks_triv2 by auto
    show ?thesis
      using 1 unfolding 3(5) 4 by auto
  qed
  show ?thesis
    apply (rule Valid_parallel2'[OF _ _ testHL1 testHL3])
    using 1 by blast+
qed

text \<open>Delay followed by receive\<close>
lemma testHL5:
  "Valid
    (\<lambda>tr. tr = Trace (\<lambda>_. 0) [])
    (Wait 2; Cm (Receive ''ch'' X))
    (\<lambda>tr. \<exists>dly v. tr = Trace (\<lambda>_. 0) [WaitBlock 2, InBlock dly ''ch'' X v ({}, {''ch''})])"
  apply (rule Valid_seq)
   apply (rule Valid_wait)
  apply (rule Valid_receive2)
  by (auto simp add: extend_receive_def)

text \<open>Delay followed by communication\<close>
lemma testHL6:
  "ParValid
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
    (PProc [Cm (Send ''ch'' (\<lambda>_. 1)), Wait 2; Cm (Receive ''ch'' X)])
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] 
        [ParWaitBlock 2 (\<lambda>t. if 0 \<le> t \<and> t \<le> 2 then [(\<lambda>_. 0), (\<lambda>_. 0)] else undefined), IOBlock 1 0 ''ch'' X 1])"
proof -
  let ?HH = "(\<lambda>t. if 0 \<le> t \<and> t \<le> 2 then [(\<lambda>_. 0), (\<lambda>_. 0)] else undefined)"
  let ?sts = "[(\<lambda>_. 0), (\<lambda>_. 0)]"
  have 1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] [ParWaitBlock 2 ?HH, IOBlock 1 0 ''ch'' X 1]"
    if tr1: "tr1 = Trace (\<lambda>_. 0) [OutBlock dly1 ''ch'' 1 ({''ch''}, {})]" and
       tr2: "tr2 = Trace (\<lambda>_. 0) [WaitBlock 2, InBlock dly2 ''ch'' X v ({}, {''ch''})]" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t dly1 dly2 v tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] par_blks" and
      2: "combine_blocks ?sts [[OutBlock dly1 ''ch'' 1 ({''ch''}, {})],
                          [WaitBlock 2, InBlock dly2 ''ch'' X v ({}, {''ch''})]] par_blks"
      using combine_par_traceE2 by blast
    have 22: "(\<lambda>d. if 0 \<le> d \<and> d \<le> 2 then sts_init else undefined) = 
          (\<lambda>d. if 0 \<le> d \<and> d \<le> 2 then [(\<lambda>_. 0), (\<lambda>_. 0)] else undefined)"
      by auto
    from 2 22 obtain rest where
      3: "dly1 \<ge> 2"
      "combine_blocks ?sts [[OutBlock (dly1 - 2) ''ch'' 1 ({''ch''}, {})],
                       [InBlock dly2 ''ch'' X v ({}, {''ch''})]] rest"
      "par_blks = ParWaitBlock 2 ?HH # rest"
      using combine_blocks_OutW2[of dly1 "''ch''" 1 "[]" 2 "[InBlock dly2 ''ch'' X v ({}, {''ch''})]" par_blks]
      by auto 
    from 3 obtain rest2 where
      4: "dly1 - 2 = 0" "dly2 = 0" "v = 1" "combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X:=1)] [[], []] rest2"
         "rest = (IOBlock 1 0 ''ch'' X 1) # rest2"
      using combine_blocks_IO2[of ?sts "dly1-2" "''ch''" 1 "({''ch''}, {})" "[]" dly2 "''ch''" X v "({}, {''ch''})" "[]" rest] 
      by auto
    from 4(4) have 5: "rest2 = []"
      using combine_blocks_triv2 by auto
    show ?thesis
      using 1 unfolding 3(3) 4(5) 5 by auto
  qed
  show ?thesis
    apply (rule Valid_parallel2'[OF _ _ testHL1 testHL5])
    using 1 by blast+
qed


text \<open>Repetition: count up and send\<close>

text \<open>Auxiliary definition for invariant.
  n is the starting value of x (needed for induction to work)
  dlys is the list of delay times between send events.

  Intended invariant is: \<exists>dlys. tr = Trace (\<lambda>_. 0) (count_blocks 0 dlys).\<close>
fun count_blocks :: "real \<Rightarrow> real list \<Rightarrow> trace_block list" where
  "count_blocks n [] = []"
| "count_blocks n (dly # rest) =
     TauBlock ((\<lambda>_. 0)(X := n + 1)) # OutBlock dly ''ch'' (n + 1) ({''ch''}, {}) #
     count_blocks (n + 1) rest"

lemma end_count_blocks:
  "end_of_blocks ((\<lambda>_. 0)(X := n)) (count_blocks n dlys) = (\<lambda>_. 0)(X := n + length dlys)"
  apply (induct dlys arbitrary: n)
  by auto

lemma end_count_blocks_init:
  "end_of_blocks (\<lambda>_. 0) (count_blocks 0 dlys) = (\<lambda>_. 0)(X := length dlys)"
proof -
  have 1: "(\<lambda>_. 0) = (\<lambda>_. 0)(X := 0)"
    by auto
  show ?thesis
    apply (subst 1)
    apply (subst end_count_blocks)
    by auto
qed

lemma count_blocks_snoc:
  "count_blocks n (dlys @ [l]) = 
   count_blocks n dlys @ [
     TauBlock ((\<lambda>_. 0)(X := n + length dlys + 1)),
     OutBlock l ''ch'' (n + length dlys + 1) ({''ch''}, {})]"
  apply (induct dlys arbitrary: n)
  by auto

lemma testHL7:
  "Valid
    (\<lambda>tr. tr = Trace (\<lambda>_. 0) [])
    (Rep (Assign X (\<lambda>s. s X + 1); Cm (Send ''ch'' (\<lambda>s. s X))))
    (\<lambda>tr. \<exists>dlys. tr = Trace (\<lambda>_. 0) (count_blocks 0 dlys))"
proof -
  have 1: "Valid
             (\<lambda>tr. tr = Trace (\<lambda>_. 0) (count_blocks 0 dlys))
             (X ::= (\<lambda>s. s X + 1))
             (\<lambda>tr. \<exists>dlys. tr = Trace (\<lambda>_. 0) (count_blocks 0 dlys @ [TauBlock (\<lambda>x. real (((\<lambda>_. 0)(X := length dlys + 1)) x))]))" for dlys
    apply (rule Valid_assign2)
    apply (rule exI[where x=dlys])
    by (auto simp add: end_count_blocks_init count_blocks_snoc)
  have 2: "Valid
             (\<lambda>tr. tr = Trace (\<lambda>_. 0) (count_blocks 0 dlys @ [TauBlock (\<lambda>x. real (((\<lambda>_. 0)(X := length dlys + 1)) x))]))
             (Cm (''ch''[!](\<lambda>s. s X)))
             (\<lambda>tr. \<exists>dlys. tr = Trace (\<lambda>_. 0) (count_blocks 0 dlys))" for dlys
    apply (rule Valid_send2)
    apply auto
    subgoal for dly
      apply (rule exI[where x="dlys @ [dly]"])
      by (auto simp add: extend_send_def end_count_blocks_init count_blocks_snoc end_of_blocks_append)
    done
  have 3: "Valid
    (\<lambda>tr. \<exists>dlys. tr = Trace (\<lambda>_. 0) (count_blocks 0 dlys))
    (Rep (Assign X (\<lambda>s. s X + 1); Cm (Send ''ch'' (\<lambda>s. s X))))
    (\<lambda>tr. \<exists>dlys. tr = Trace (\<lambda>_. 0) (count_blocks 0 dlys))"
    apply (rule Valid_rep)
    apply (rule Valid_seq[where Q="\<lambda>tr. \<exists>dlys. tr = Trace (\<lambda>_. 0) (count_blocks 0 dlys @ [TauBlock ((\<lambda>_. 0)(X := length dlys + 1))])"])
    using 1 2 by (auto simp add: Valid_ex_pre)
  show ?thesis
    apply (rule Valid_pre[OF _ 3])
    apply auto
    apply (rule exI[where x="[]"])
    by auto
qed


text \<open>Repetition: receive\<close>

text \<open>Auxiliary definition for invariant.
  dly is the delay of each receive.
  v is the value of each receive.

  Intended invariant is: \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (receive_blocks dlyvs).\<close>
fun receive_blocks :: "(time \<times> real) list \<Rightarrow> trace_block list" where
  "receive_blocks [] = []"
| "receive_blocks ((dly, v) # rest) = InBlock dly ''ch'' X v ({}, {''ch''}) # receive_blocks rest"

lemma receive_blocks_snoc:
  "receive_blocks (dlyvs @ [(dly, v)]) = receive_blocks dlyvs @ [InBlock dly ''ch'' X v ({}, {''ch''})]"
  apply (induct dlyvs) by auto

lemma testHL8:
  "Valid
    (\<lambda>tr. tr = Trace (\<lambda>_. 0) [])
    (Rep (Cm (Receive ''ch'' X)))
    (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (receive_blocks dlyvs))"
proof -
  have 1: "Valid
             (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (receive_blocks dlyvs))
             (Rep (Cm (''ch''[?]X)))
             (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (receive_blocks dlyvs))"
    apply (rule Valid_rep)
    apply (subst Valid_ex_pre)
    apply auto
    subgoal for dlyvs
      apply (rule Valid_receive2)
      apply auto
      subgoal for dly v
        apply (rule exI[where x="dlyvs @ [(dly, v)]"])
        by (auto simp add: extend_receive_def receive_blocks_snoc)
      done
    done
  show ?thesis
    apply (rule Valid_pre[OF _ 1])
    apply auto
    apply (rule exI[where x="[]"])
    by auto
qed


text \<open>Repetition: communication\<close>

text \<open>The invariant\<close>
fun comm_blocks :: "real \<Rightarrow> nat \<Rightarrow> par_block list" where
  "comm_blocks x 0 = []"
| "comm_blocks x (Suc n) = (ParTauBlock 0 ((\<lambda>_. 0)(X := (x+1)))) # IOBlock 1 0 ''ch'' X (x + 1) # comm_blocks (x + 1) n"

lemma testHL9_blocks:
  "combine_blocks sts[count_blocks x dlys, receive_blocks dlyvs] par_blks \<Longrightarrow>
   \<exists>n. par_blks = comm_blocks x n"
proof (induct dlyvs arbitrary: dlys par_blks x sts)
  case Nil
  note Nil1 = Nil
  then show ?case
  proof (cases dlys)
    case Nil
    show ?thesis
      apply (rule exI[where x=0])
      using Nil1[unfolded Nil] combine_blocks_triv2 by auto 
  next
    case (Cons d restd)
    then show ?thesis
      using Nil1 apply auto
      using combine_blocks_TauNil2[of sts "((\<lambda>_. 0)(X := x + 1))" "OutBlock d ''ch'' (x + 1) ({''ch''}, {}) # count_blocks (x + 1) restd" "par_blks"] 
            combine_blocks_OutNil[of "(sts[0 := (\<lambda>_. 0)(X := x + 1)])" d "''ch''" "x+1" " count_blocks (x + 1) restd"]
      by metis
  qed
next
  case (Cons p dlyvs)
  note Cons1 = Cons
  then show ?case
  proof (cases dlys)
    case Nil
    then show ?thesis
      using Cons1 apply (cases p) apply auto
      using combine_blocks_NilIn
    by metis
  next
    case (Cons d restd)
    have 1: "combine_blocks sts
        [TauBlock ((\<lambda>_. 0)(X := x + 1)) # OutBlock d ''ch'' (x + 1) ({''ch''}, {}) # count_blocks (x + 1) restd,
         InBlock (fst p) ''ch'' X (snd p) ({}, {''ch''}) # receive_blocks dlyvs]
        par_blks"
      using Cons Cons1(2) apply (cases p) by auto 
    have 2: "event_of_block (InBlock (fst p) ''ch'' X (snd p) ({}, {''ch''})) \<noteq> Tau"
      by auto
    from 1 2 obtain rest where
      3: "combine_blocks (sts[0 := (\<lambda>_. 0)(X := x + 1)]) [OutBlock d ''ch'' (x + 1) ({''ch''}, {}) # count_blocks (x + 1) restd,
                          InBlock (fst p) ''ch'' X (snd p) ({}, {''ch''}) # receive_blocks dlyvs] rest"
         "par_blks = ParTauBlock 0 ((\<lambda>_. 0)(X := x + 1)) # rest"
      using combine_blocks_TauIn2 by blast
    let ?sts0 = "sts[0 := (\<lambda>_. 0)(X := x + 1)]" and
        ?sts1 = "(sts[0 := (\<lambda>_. 0)(X := x + 1)])[1 := (sts!1)(X := x + 1)]"
    from 3 have "snd p = x + 1"
      using combine_blocks_IO2[of ?sts0 d "''ch''" "x+1" "({''ch''}, {})" "count_blocks (x + 1) restd"
                   "fst p" "''ch''" X "snd p" "({}, {''ch''})" "receive_blocks dlyvs" rest]
      by auto
    then have 31:"(sts[0 := (\<lambda>_. 0)(X := x + 1), 1 := end_of_blocks (sts[0 := (\<lambda>_. 0)(X := x + 1)] ! 1) 
                 [InBlock (fst p) ''ch'' X (snd p) ({}, {''ch''})]])
          = ?sts1"
      by auto      
    from 3 31 obtain rest2 where
      4: "d = 0" "fst p = 0" "x + 1 = snd p" "combine_blocks ?sts1 [count_blocks (x + 1) restd, receive_blocks dlyvs] rest2"
         "rest = (IOBlock 1 0 ''ch'' X (x + 1)) # rest2"
         "(sts[0 := (\<lambda>_. 0)(X := x + 1), 1 := end_of_blocks (sts[0 := (\<lambda>_. 0)(X := x + 1)] ! 1) [InBlock (fst p) ''ch'' X (snd p) ({}, {''ch''})]])
          = ?sts1"
      using combine_blocks_IO2[of ?sts0 d "''ch''" "x+1" "({''ch''}, {})" "count_blocks (x + 1) restd"
                   "fst p" "''ch''" X "snd p" "({}, {''ch''})" "receive_blocks dlyvs" rest] 
      by auto
    obtain n where 5: "rest2 = comm_blocks (x + 1) n"
      using 4  Cons1  by blast
    then have 6: "par_blks = ParTauBlock 0 ((\<lambda>_. 0)(X := x + 1)) # IOBlock 1 0 ''ch'' X (x + 1) # comm_blocks (x + 1) n"
      using 3(2) unfolding 4(5) 4(3)[symmetric] by auto
    show ?thesis
      apply (rule exI[where x="Suc n"])
      using 6 by auto
  qed
qed

lemma testHL9:
  "ParValid
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
    (PProc [Rep (Assign X (\<lambda>s. s X + 1); Cm (Send ''ch'' (\<lambda>s. s X))),
            Rep (Cm (Receive ''ch'' X))])
    (\<lambda>t. \<exists>n. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] (comm_blocks 0 n))"
proof -
  have 1: "\<exists>n. par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] (comm_blocks 0 n)"
    if tr1: "tr1 = Trace (\<lambda>_. 0) (count_blocks 0 dlys)" and
       tr2: "tr2 = Trace (\<lambda>_. 0) (receive_blocks dlyvs)" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t dlys dlyvs tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] par_blks" and
      2: "combine_blocks sts_init [count_blocks 0 dlys, receive_blocks dlyvs] par_blks"
      using combine_par_traceE2 sts_init_def 
      by metis
    then obtain n where 3: "par_blks = comm_blocks 0 n"
      using testHL9_blocks by blast
    show ?thesis
      apply (rule exI[where x=n])
      using 1 unfolding 3 by auto
  qed
  show ?thesis
    apply (rule Valid_parallel2'[OF _ _ testHL7 testHL8])
    using 1 by blast+
qed


text \<open>External choice\<close>

lemma testHL10:
  "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) [])
    (EChoice [(Send ''ch'' (\<lambda>_. 1), Wait 1), (Send ''ch2'' (\<lambda>_. 2), Wait 2)])
    (\<lambda>t. (\<exists>dly. t = Trace (\<lambda>_. 0) [OutBlock dly ''ch'' 1 ({''ch'', ''ch2''}, {}), WaitBlock 1]) \<or>
         (\<exists>dly. t = Trace (\<lambda>_. 0) [OutBlock dly ''ch2'' 2 ({''ch'', ''ch2''}, {}), WaitBlock 2]))"
  apply (rule Valid_echoice)
  apply (auto simp add: less_Suc_eq)
  by (auto simp add: Valid_wait2 extend_send_def)

text \<open>External choice with communication\<close>

lemma testHL11:
  "ParValid
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
    (PProc [EChoice [(Send ''ch'' (\<lambda>_. 1), Wait 1), (Send ''ch2'' (\<lambda>_. 2), Wait 2)],
            Cm (Receive ''ch'' X)])
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [IOBlock 1 0 ''ch'' X 1, ParWaitBlock 1 (\<lambda>d. if 0 \<le> d \<and> d \<le> 1 then [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] else undefined)])"
proof -
  let ?sts = "[(\<lambda>_. 0), (\<lambda>_. 0)]"
  let ?HH = "(\<lambda>d. if 0 \<le> d \<and> d \<le> 1 then [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] else undefined)"
  have 1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] [IOBlock 1 0 ''ch'' X 1, ParWaitBlock 1 ?HH]"
    if tr1: "tr1 = Trace (\<lambda>_. 0) [OutBlock dly1 ''ch'' 1 ({''ch'', ''ch2''}, {}), WaitBlock 1]" and
       tr2: "tr2 = Trace (\<lambda>_. 0) [InBlock dly2 ''ch'' X v ({}, {''ch''})]" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t dly1 dly2 v tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] par_blks" and
      2: "combine_blocks [\<lambda>_. 0, \<lambda>_. 0] [[OutBlock dly1 ''ch'' 1 ({''ch'', ''ch2''}, {}), WaitBlock 1],
                          [InBlock dly2 ''ch'' X v ({}, {''ch''})]] par_blks"
      using combine_par_traceE2 by blast
    from 2 obtain rest where
      3: "dly1 = 0" "dly2 = 0" "v = 1" "combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] [[WaitBlock 1], []] rest"
         "par_blks = (IOBlock 1 0 ''ch'' X 1) # rest"
      using combine_blocks_IO2[of "?sts" dly1 "''ch''" 1 " ({''ch'', ''ch2''}, {})" "[WaitBlock 1]" dly2 "''ch''" X v "({}, {''ch''})" "[]" par_blks]  
      by auto
    from 3(4) obtain rest2 where
      4: "combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] [[], []] rest2" "rest = ParWaitBlock 1 ?HH # rest2"
      using combine_blocks_WaitNil2 by blast
    from 4(1) have 5: "rest2 = []"
      using combine_blocks_triv2 by auto
    show ?thesis
      using 1 unfolding 3(5) 4(2) 5 by auto
  qed
  have 2: "False"
    if tr1: "tr1 = Trace (\<lambda>_. 0) [OutBlock dly1 ''ch2'' 2 ({''ch'', ''ch2''}, {}), WaitBlock 2]" and
       tr2: "tr2 = Trace (\<lambda>_. 0) [InBlock dly2 ''ch'' X v ({}, {''ch''})]" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t dly1 dly2 v tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] par_blks" and
      2: "combine_blocks ?sts [[OutBlock dly1 ''ch2'' 2 ({''ch'', ''ch2''}, {}), WaitBlock 2],
                          [InBlock dly2 ''ch'' X v ({}, {''ch''})]] par_blks"
      using combine_par_traceE2 by blast
    from 2 show ?thesis
      using combine_blocks_IO2 by blast
  qed
  show ?thesis
    apply (rule Valid_parallel2'[OF _ _ testHL10 testHL3])
    using 1 2 by fastforce+
qed


text \<open>ODE with solution\<close>

lemma testHL12:
  "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) [])
    (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
    (\<lambda>t. t = Trace (\<lambda>_. 0) [ODEBlock 1 (restrict (\<lambda>t. (\<lambda>_. 0)(X := t)) {0..1})])"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (fun_upd (\<lambda>_. 0) X) 1"
     unfolding ODEsol_def solves_ode_def has_vderiv_on_def
     apply auto
     apply (rule has_vector_derivative_projI)
     by (auto simp add: state2vec_def)
  have 2: "local_lipschitz {- 1<..} UNIV (\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (vec2state v))"
  proof -
    have eq: "(\<chi> a. (if a = X then \<lambda>_. 1 else (\<lambda>_. 0)) (($) v)) = (\<chi> a. if a = X then 1 else 0)" for v::vec
      by auto
    show ?thesis
      unfolding fun_upd_def vec2state_def
      apply (auto simp add: state2vec_def eq)
      by (rule local_lipschitz_constI)
  qed
  show ?thesis
    apply (rule Valid_ode_unique_solution[of 1 _ "\<lambda>t. (\<lambda>_. 0)(X := t)"])
    using 1 2 by auto
qed


lemma testHL12':
  fixes v :: real
  assumes d1: "v < 1"
      and d2: "end_of_trace (Trace (\<lambda>_. 0) list) = (\<lambda>_. 0)(X := v)"
    shows "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) list)
    (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
    (\<lambda>t. t = Trace (\<lambda>_. 0) (list@[ODEBlock (1-v) (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..1-v})]))"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + v)) (1 - v)"
    unfolding ODEsol_def has_vderiv_on_def
    apply auto using d1 apply simp
    apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def)
    apply (rule has_vector_derivative_eq_rhs)
    apply (auto intro!: derivative_intros)[1]
    by auto
  have 2: "local_lipschitz {- 1<..} UNIV (\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (vec2state v))"
  proof -
    have 1: "(\<chi> a. (if a = X then \<lambda>_. 1 else (\<lambda>_. 0)) (($) v)) = (\<chi> a. if a = X then 1 else 0)"
      for v::vec
      by auto
    show ?thesis
      unfolding fun_upd_def vec2state_def
      apply (auto simp add: state2vec_def 1)
      by (rule local_lipschitz_constI)
  qed
  show ?thesis
    apply (rule Valid_ode_unique_solution[of "1-v" _ "\<lambda>t. (\<lambda>_. 0)(X := t+v)"])
    using d1 d2 1 2 by auto
qed

lemma testHL12b:
  "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) [])
    (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 2), Y := (\<lambda>s. s X)))) (\<lambda>s. s Y < 1))
    (\<lambda>t. t = Trace (\<lambda>_. 0) [ODEBlock 1 (restrict (\<lambda>t. ((\<lambda>_. 0)(X := 2 * t, Y := t * t))) {0..1})])"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 2, Y := \<lambda>s. s X))) (\<lambda>t. (\<lambda>_. 0)(X := 2 * t, Y := t * t)) 1"
    unfolding ODEsol_def has_vderiv_on_def
    apply auto
    apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def vars_distinct)
    apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
    apply auto
    apply (rule has_vector_derivative_eq_rhs)
    apply (auto intro!: derivative_intros)[1]
    by auto
  have 2: "local_lipschitz {- (1::real)<..} UNIV (\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 2, Y := \<lambda>s. s X))) (vec2state v))"
  proof -
    have bounded: "bounded_linear ((\<lambda>(y::vec). \<chi> a. if a = Y then y $ X else 0))"
      apply (rule bounded_linearI')
      using vec_lambda_unique by fastforce+
    show ?thesis
      unfolding state2vec_def vec2state_def fun_upd_def ODE2Vec.simps
      apply (rule c1_implies_local_lipschitz[where f'="(\<lambda>(t,y). Blinfun(\<lambda>y. \<chi> a. if a = Y then y $ X else 0))"])
         apply (auto simp add: bounded_linear_Blinfun_apply[OF bounded])
      subgoal premises pre for t x
        unfolding has_derivative_def apply (auto simp add: bounded)
        apply (rule vec_tendstoI)
        by (auto simp add: vars_distinct)
      done
  qed
  have 3: "\<And>t. 0 \<le> (t::real) \<Longrightarrow> t < 1 \<Longrightarrow> t * t < 1"
    using mult_left_le_one_le by fastforce
  show ?thesis
    apply (rule Valid_ode_unique_solution[of 1 _ "\<lambda>t. ((\<lambda>_. 0)(X := 2 * t, Y := t * t))"])
    using 1 2 3 by auto
qed

lemma testHL12inv:
  "Valid
    (\<lambda>t. t = Trace ((\<lambda>_. 0)(X := 1)) [])
    (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>s. - s Y), Y := (\<lambda>s. s X)))) (\<lambda>s. s Y < 1))
    (\<lambda>t. \<exists>d p. t = extend_trace (Trace ((\<lambda>_. 0)(X := 1)) []) (ODEBlock d (restrict p {0..d})) \<and>
               d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(X := 1)) []) \<and>
               (\<forall>t. 0\<le>t \<and> t\<le>d \<longrightarrow> p t X * p t X + p t Y * p t Y = p 0 X * p 0 X + p 0 Y * p 0 Y))"
  apply (rule Valid_ode_invariant)
   apply (auto simp add: vec2state_def)[1]
   apply (auto intro!: derivative_intros)[1]
  by (auto simp add: state2vec_def vars_distinct)


text \<open>Example with parallel, loop, and ODE\<close>

fun right_blocks :: "(time \<times> real \<times> time) list \<Rightarrow> trace_block list" where
  "right_blocks [] = []"
| "right_blocks ((dly1, v, dly2) # rest) =
      InBlock dly1 ''ch'' X v ({}, {''ch''}) #
      OutBlock dly2 ''ch'' (v - 1) ({''ch''}, {}) # right_blocks rest"

lemma right_blocks_snoc:
  "right_blocks (dlys @ [(dly1, v, dly2)]) =
   right_blocks dlys @ [
      InBlock dly1 ''ch'' X v ({}, {''ch''}),
      OutBlock dly2 ''ch'' (v - 1) ({''ch''}, {})]"
  by (induct dlys, auto)

lemma end_of_right_blocks:
  "end_of_blocks ((\<lambda>_. 0)(X := a)) (right_blocks dlyvs @ [InBlock dly1 ''ch'' X v ({}, {''ch''})]) X = v"
  by (induction dlyvs arbitrary: a, auto)

lemma end_of_right_blocks_zero:
  "end_of_blocks (\<lambda>_. 0) (right_blocks dlyvs @ [InBlock dly1 ''ch'' X v ({}, {''ch''})]) X = v"
proof -
  have 1: "(\<lambda>_. 0) = ((\<lambda>_. 0)(X := 0))"
    by auto
  show ?thesis
    apply (subst 1)
    by (auto simp add: end_of_right_blocks)
qed

lemma testHL13b:
  "Valid
    (\<lambda>tr. tr = Trace ((\<lambda>_. 0)(X := 1)) [])
    (Rep (Cm (Receive ''ch'' X); Cm (Send ''ch'' (\<lambda>s. s X - 1))))
    (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (right_blocks dlyvs))"
proof -
  have 1: "Valid
     (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (right_blocks dlyvs))
     (Cm (''ch''[?]X))
     (\<lambda>tr. \<exists>dlyvs dly1 v. tr = Trace ((\<lambda>_. 0)(X := 1)) (right_blocks dlyvs @ [InBlock dly1 ''ch'' X v ({}, {''ch''})]))"
    apply (subst Valid_ex_pre)
    apply auto
    apply (rule Valid_receive2)
    by (auto simp add: extend_receive_def)
  have 2: "Valid
     (\<lambda>tr. \<exists>dlyvs dly1 v. tr = Trace ((\<lambda>_. 0)(X := 1)) (right_blocks dlyvs @ [InBlock dly1 ''ch'' X v ({}, {''ch''})]))
     (Cm (''ch''[!](\<lambda>s. s X - 1)))
     (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (right_blocks dlyvs))"
    apply (simp only: Valid_ex_pre)
    apply auto
    apply (rule Valid_send2)
    apply (auto simp add: extend_send_def end_of_right_blocks_zero)
    subgoal for dlyvs dly1 v dly2
      apply (rule exI[where x="dlyvs @ [(dly1, v, dly2)]"])
      by (simp add: end_of_right_blocks right_blocks_snoc)
      done
  have 3: "Valid
    (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (right_blocks dlyvs))
    (Rep (Cm (Receive ''ch'' X); Cm (Send ''ch'' (\<lambda>s. s X - 1))))
    (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (right_blocks dlyvs))"
    apply (rule Valid_rep)
    apply (rule Valid_seq[where Q="\<lambda>tr. \<exists>dlyvs dly1 v. tr = Trace ((\<lambda>_. 0)(X := 1)) (right_blocks dlyvs @ [InBlock dly1 ''ch'' X v ({}, {''ch''})])"])
    using 1 2 by auto
  show ?thesis
    apply (rule Valid_pre[OF _ 3])
    apply auto
    apply (rule exI[where x="[]"])
    by auto
qed

fun left_blocks :: "real \<Rightarrow> (time \<times> real \<times> time) list \<Rightarrow> trace_block list" where
  "left_blocks x [] = []"
| "left_blocks x ((dly1, v, dly2) # rest) =
    (if x < 1 then
       ODEBlock (1-x) (restrict (\<lambda>t. (\<lambda>_. 0)(X := t+x)){0..1-x}) #
       OutBlock dly1 ''ch'' 1 ({''ch''}, {}) # 
       InBlock dly2 ''ch'' X v ({}, {''ch''}) # left_blocks v rest 
     else
       ODEBlock 0 (restrict(\<lambda>t. (\<lambda>_. 0)(X := x)){0..0}) #
       OutBlock dly1 ''ch'' x ({''ch''}, {}) # 
       InBlock dly2 ''ch'' X v ({}, {''ch''}) # left_blocks v rest)"

lemma left_blocks_snoc: 
  assumes "length dlys > 0"
      and "x = fst(snd(last dlys))"
    shows "left_blocks n (dlys @ [(dly1, v, dly2)]) =
           left_blocks n dlys @ (
             if x < 1 then
               [ODEBlock (1-x) (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+x)){0..1-x}),
                OutBlock dly1 ''ch'' 1 ({''ch''}, {}), 
                InBlock dly2 ''ch'' X v ({}, {''ch''})]
             else
               [ODEBlock 0 (restrict(\<lambda>t. (\<lambda>_. 0)(X := x)){0..0}),
                OutBlock dly1 ''ch'' x ({''ch''}, {}), 
                InBlock dly2 ''ch'' X v ({}, {''ch''})])"
  using assms apply (induct dlys arbitrary: n)
  by auto

lemma end_left_blocks:
  "end_of_blocks ((\<lambda>_. 0)(X := v)) (left_blocks v dlys) =
    (if length dlys = 0 then (\<lambda>_. 0)(X := v) else (\<lambda>_. 0)(X := fst (snd (last dlys))))" 
  apply (induct dlys arbitrary: v) by auto

lemma end_left_blocks_init:
  "end_of_blocks (\<lambda>_. 0) (left_blocks 0 dlys) =
    (if length dlys = 0 then (\<lambda>_. 0)(X := 0) else (\<lambda>_. 0)(X := fst (snd (last dlys))))"
proof -
  have 1: "(\<lambda>_. 0) = (\<lambda>_. 0)(X := 0)"
    by auto
  show ?thesis
    apply (subst 1)
    apply (subst end_left_blocks)
    by auto
qed

lemma end_left_blocks_1:
  "end_of_blocks ((\<lambda>_. 0)(X := v)) ((left_blocks v dlys) @ [ODEBlock d (restrict p {0..d})]) =
     restrict p {0..d} d" 
  apply (induct dlys arbitrary: v)
  by auto

lemma end_left_blocks_1_init:
  "end_of_blocks ((\<lambda>_. 0)) ((left_blocks 0 dlys) @ [ODEBlock d (restrict p {0..d})]) =
     restrict p {0..d} d" 
proof-  
  have 1: "(\<lambda>_. 0) = (\<lambda>_. 0)(X := 0)"
    by auto
  show ?thesis
    apply (subst 1)
    apply (subst end_left_blocks_1)
    by auto
qed

lemma testHL13a:
  "Valid
    (\<lambda>tr. tr = Trace (\<lambda>_. 0) [])
    (Rep ((Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1); Cm (Send ''ch'' (\<lambda>s. s X )));Cm (Receive ''ch'' X)))
    (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (left_blocks  0 dlyvs))"
proof -
  have main: "Valid
    (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))
    (Rep ((Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1); Cm (Send ''ch'' (\<lambda>s. s X )));Cm (Receive ''ch'' X)))
    (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))"
    apply (rule Valid_rep)
    apply (subst Valid_ex_pre)
    apply auto
    subgoal for dlyvs
    proof cases
      assume c1: "length dlyvs = 0"
      have 1: "left_blocks 0 dlyvs = []"
        using end_left_blocks_init c1 by auto
      have 2: "Valid
                (\<lambda>t. t = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))
                (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
                (\<lambda>t. t = Trace (\<lambda>_. 0) [ODEBlock 1 (restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..1})])"
        using testHL12 1 by auto
      have 3: "Valid
                (\<lambda>t. t = Trace (\<lambda>_. 0) [ODEBlock 1 (restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..1})])
                (Cm (Send ''ch'' (\<lambda>s. s X )))
                (\<lambda>t. \<exists>dly1. t = Trace (\<lambda>_. 0) [ODEBlock 1 (restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..1}),
                                               OutBlock dly1 ''ch'' 1 ({''ch''}, {})])"
        apply (rule Valid_send2)
        unfolding extend_send_def by auto
      have 4: "Valid
                 (\<lambda>t. \<exists>dly1. t = Trace (\<lambda>_. 0) [ODEBlock 1 (restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..1}),
                                                OutBlock dly1 ''ch'' 1 ({''ch''}, {})])
                 (Cm (Receive ''ch'' X))
                 (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))"
        apply(simp only: Valid_ex_pre)
        apply auto
        subgoal for dly1
          apply(rule Valid_receive2)
          apply auto
          subgoal for dly v
            apply(rule exI[where x="[(dly1,v,dly)]"])
            unfolding extend_receive_def 
            by auto
          done
        done
      show ?thesis 
        using 2 3 4 by (auto intro: Valid_seq)
    next
      assume c2: "length dlyvs \<noteq> 0"
      obtain v where ini: "v=fst (snd (last dlyvs))" by auto
      have 1: "end_of_trace (Trace (\<lambda>_. 0) (left_blocks 0 dlyvs)) = (\<lambda>_. 0)(X := v)"
        using end_left_blocks_init c2 ini by auto
      have 2: "Valid
                (\<lambda>t. t = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))
                (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
                (\<lambda>t. t = Trace (\<lambda>_. 0) ((left_blocks 0 dlyvs)@[ODEBlock  (1-v) (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..1-v})]))" 
        if cond1:"v<1"
        using testHL12' cond1 ini end_left_blocks_init c2 by auto
      have 3: "Valid
                (\<lambda>t. t = Trace (\<lambda>_. 0) ((left_blocks 0 dlyvs)@[ODEBlock  (1-v) (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..1-v})]))
                (Cm (Send ''ch'' (\<lambda>s. s X )))
                (\<lambda>t. \<exists>dly1. t = Trace (\<lambda>_. 0) ((left_blocks 0 dlyvs)@[ODEBlock (1-v) (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..1-v}),
                                                                      OutBlock dly1 ''ch'' 1 ({''ch''}, {})]))"
        if cond1:"v<1"
        apply(rule Valid_send2)
        apply auto
        subgoal for dly
          apply(rule exI[where x="dly"])
          unfolding extend_send_def apply auto
          using cond1 end_left_blocks_1_init by auto
        done
      have 4: "Valid
              (\<lambda>t. \<exists>dly1. t = Trace (\<lambda>_. 0) ((left_blocks 0 dlyvs)@[ODEBlock  (1-v) (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..1-v}),OutBlock dly1 ''ch'' 1 ({''ch''}, {})]))
              (Cm (Receive ''ch'' X))
              (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))" 
        if cond1:"v<1"
        apply(simp only:Valid_ex_pre)
        apply auto
        subgoal for dly1
          apply(rule Valid_receive2)
          apply auto
          subgoal for dly va 
            apply(rule exI[where x= "dlyvs @ [(dly1,va,dly)]"])
            using c2 ini cond1 left_blocks_snoc[of dlyvs v 0 dly1 va dly]
            unfolding extend_receive_def by auto
          done
        done
      have 5: "Valid (\<lambda>tr. tr = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))
                ((Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1)))
                (\<lambda>s. s X < 1); Cm (''ch''[!](\<lambda>s. s X))); Cm (''ch''[?]X))
                (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))" 
        if cond1:"v<1"
        using 2 3 4 cond1 by (auto intro: Valid_seq)
     have 6: "Valid
               (\<lambda>t. t = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))
               (Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
               (\<lambda>t. t = Trace (\<lambda>_. 0) ((left_blocks 0 dlyvs)@[ODEBlock 0 (restrict(\<lambda>t. (\<lambda>_. 0)(X := v)){0..0})]))" 
       if cond2:"v\<ge>1"
       apply(rule Valid_ode_solution3) 
       using cond2 ini end_left_blocks_init c2 by auto
     have 7: "Valid
               (\<lambda>t. t = Trace (\<lambda>_. 0) ((left_blocks 0 dlyvs)@[ODEBlock  0 (restrict(\<lambda>t. (\<lambda>_. 0)(X := v)){0..0})]))
               (Cm (Send ''ch'' (\<lambda>s. s X )))
               (\<lambda>t. \<exists>dly1. t = Trace (\<lambda>_. 0) ((left_blocks 0 dlyvs)@[ODEBlock 0 (restrict(\<lambda>t. (\<lambda>_. 0)(X := v)){0..0}),
                                                                     OutBlock dly1 ''ch'' v ({''ch''}, {})]))"
       if cond2:"v\<ge>1"
       apply(rule Valid_send2)
       apply auto
       subgoal for dly
         apply(rule exI[where x="dly"])
         unfolding extend_send_def apply auto
         using cond2 end_left_blocks_1_init[of dlyvs 0 "(\<lambda>t\<in>{0}. (\<lambda>_. 0)(X := v))"] by auto
       done
     have 8: "Valid
               (\<lambda>t. \<exists>dly1. t = Trace (\<lambda>_. 0) ((left_blocks 0 dlyvs)@[ODEBlock 0 (restrict(\<lambda>t. (\<lambda>_. 0)(X := v)){0..0}),
                                                                 OutBlock dly1 ''ch'' v ({''ch''}, {})]))
               (Cm (Receive ''ch'' X))
               (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))" 
        if cond2:"v\<ge>1"
        apply(simp only:Valid_ex_pre)
        apply auto
        subgoal for dly1
          apply(rule Valid_receive2)
          apply auto
          subgoal for dly va 
            apply(rule exI[where x="dlyvs @ [(dly1,va,dly)]"])
            using c2 ini cond2 left_blocks_snoc[of dlyvs v 0 dly1 va dly]
            unfolding extend_receive_def by auto
          done
        done
     have 9: "Valid (\<lambda>tr. tr = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))
               ((Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1)))
               (\<lambda>s. s X < 1); Cm (''ch''[!](\<lambda>s. s X))); Cm (''ch''[?]X))
               (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (left_blocks 0 dlyvs))" 
       if cond2:"v\<ge>1"
       using 6 7 8 cond2 by (auto intro: Valid_seq)
      show ?thesis
        using 5 9 by linarith
    qed
    done
  show ?thesis
    apply (rule Valid_pre[OF _ main])
    apply auto
    apply (rule exI[where x="[]"])
    by auto
qed       


fun tot_blocks :: "nat \<Rightarrow> par_block list" where
  "tot_blocks 0 = []"
| "tot_blocks (Suc n) = ParWaitBlock 1 (restrict (\<lambda>t. [(\<lambda>_. 0)(X := t), (\<lambda>_. 0)(X := 1)]) {0..1::real}) 
                        # IOBlock 1 0 ''ch'' X 1 # IOBlock 0 1 ''ch'' X 0 # tot_blocks  n"

lemma testHL13_blocks:
  "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)(X := 1)] [left_blocks 0 dlys, right_blocks dlyvs] par_blks \<Longrightarrow>
   \<exists>n. par_blks = tot_blocks n"
proof (induct dlyvs arbitrary: dlys par_blks)
  case Nil
  note Nil1 = Nil
  then show ?case
  proof (cases dlys)
    case Nil
    show ?thesis 
      apply (rule exI[where x=0])
      using Nil1[unfolded Nil]  combine_blocks_triv2 by auto
  next
    case (Cons a list)
    then show ?thesis 
      using Nil1 apply auto
      apply(cases a) apply auto
      subgoal for aa b c
        using combine_blocks_ODENil2 combine_blocks_OutNil by blast
      done
    qed
next
  case (Cons a dlyvs)
  note Cons1 = Cons
  then show ?case
  proof (cases dlys)
    case Nil
    then show ?thesis 
      using Cons1(2) apply (cases a) apply auto
      using combine_blocks_NilIn by blast
  next
    case (Cons b list)
    have 1: "combine_blocks [(\<lambda>_. 0), (\<lambda>_. 0)(X := 1)]
        [ODEBlock 1 (restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..1}) #
        OutBlock (fst b) ''ch'' 1 ({''ch''}, {}) # 
        InBlock (snd(snd b)) ''ch'' X (fst(snd b)) ({}, {''ch''}) # 
        left_blocks (fst(snd b)) list,
        InBlock (fst a) ''ch'' X (fst(snd a)) ({}, {''ch''}) #
        OutBlock (snd(snd a)) ''ch'' ((fst(snd a)) - 1) ({''ch''}, {}) # 
        right_blocks dlyvs]
        par_blks"
      using Cons Cons1(2) 
      apply auto 
      by (smt Cons.prems fst_conv left_blocks.elims list.distinct(1) list.inject restrict_ext right_blocks.elims snd_conv)      
    have 2: "event_of_block (InBlock (fst a) ''ch'' X (fst(snd a)) ({}, {''ch''})) \<noteq> Tau"
      by auto
    have 21: "restrict (fun_upd (\<lambda>_. 0) X) {0..1::real} 1 = (\<lambda>_. 0)(X := 1)"
      by auto
    have 22: "(\<lambda>t\<in>{0..1}. [restrict (fun_upd (\<lambda>_. 0) X) {0..1::real} t, (\<lambda>_. 0)(X := 1)]) =
              (\<lambda>t\<in>{0..1}. [(\<lambda>_. 0)(X := t), (\<lambda>_. 0)(X := 1)])"
      by auto 
    from 1 2 obtain rest where
      3: "combine_blocks [(\<lambda>_. 0)(X := 1), (\<lambda>_. 0)(X := 1)] [OutBlock (fst b) ''ch'' 1 ({''ch''}, {}) # 
        InBlock (snd(snd b)) ''ch'' X (fst(snd b)) ({}, {''ch''}) # 
        left_blocks (fst(snd b)) list,
        wait_block 1 (InBlock (fst a) ''ch'' X (fst(snd a)) ({}, {''ch''})) #
        OutBlock (snd(snd a)) ''ch'' ((fst(snd a)) - 1) ({''ch''}, {}) # 
        right_blocks dlyvs] rest"
         "par_blks = ParWaitBlock 1 (restrict (\<lambda>t. [(\<lambda>_. 0)(X := t), (\<lambda>_. 0)(X := 1)]) {0..1::real})  # rest"
      using combine_blocks_ODEIn2[of "(\<lambda>_. 0)" "(\<lambda>_. 0)(X := 1)" 1 "(restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..1::real})"
              "OutBlock (fst b) ''ch'' 1 ({''ch''}, {}) # InBlock (snd (snd b)) ''ch'' X (fst (snd b)) ({}, {''ch''}) # left_blocks (fst (snd b)) list"
              "fst a" "''ch''" X "(fst (snd a))" "({}, {''ch''})" "OutBlock (snd (snd a)) ''ch'' (fst (snd a) - 1) ({''ch''}, {}) # right_blocks dlyvs"
              "par_blks"] 21 22 by auto

    from 3(1) obtain rest1 where
      4: "(fst b) = 0" "fst a = 1" "(fst(snd a)) = 1" 
         "combine_blocks [(\<lambda>_. 0)(X := 1), (\<lambda>_. 0)(X := 1)] [InBlock (snd(snd b)) ''ch'' X (fst(snd b)) ({}, {''ch''}) # left_blocks (fst(snd b)) list, 
               OutBlock (snd(snd a)) ''ch'' ((fst(snd a)) - 1) ({''ch''}, {}) #right_blocks dlyvs] rest1"
         "rest =  IOBlock 1 0 ''ch'' X 1 # rest1"
        apply simp
        using combine_blocks_IO2 by(force)

    from 4(3,4) obtain rest2 where
      5: "(snd (snd b)) = 0" "(snd (snd a)) = 0" "(fst (snd b)) = 0" "combine_blocks [(\<lambda>_. 0)(X := 0), (\<lambda>_. 0)(X := 1)] [left_blocks (fst(snd b)) list,right_blocks dlyvs] rest2"
         "rest1 =  IOBlock 0 1 ''ch'' X 0 # rest2"
        using combine_blocks_IO2' by force

    obtain n where 6: "rest2 = tot_blocks n"
      using 5(3,4) Cons1(1)[of list rest2] 
      by (metis fun_upd_triv)

    then have 7: "par_blks = ParWaitBlock 1 (restrict (\<lambda>t. [(\<lambda>_. 0)(X := t), (\<lambda>_. 0)(X := 1)]) {0..1::real})
                   # IOBlock 1 0 ''ch'' X 1 # IOBlock 0 1 ''ch'' X 0 # tot_blocks  n"
      using 3(2) unfolding 4(5) 4(3)[symmetric] 5(5) by auto
    show ?thesis
      apply (rule exI[where x="Suc n"])
      using 7 by auto
    qed
qed

lemma testHL13:
  "ParValid
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)(X := 1)] [])
    (PProc [Rep(((Cont (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
             Cm (Send ''ch'' (\<lambda>s. s X)));
             Cm (Receive ''ch'' X))),
            Rep((Cm (Receive ''ch'' X);
             Cm (Send ''ch'' (\<lambda>s. s X - 1))))] )
    (\<lambda>t. \<exists>n. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)(X := 1)] (tot_blocks n))"
proof-
  have 1: "\<exists>n. par_t = ParTrace [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] (tot_blocks n)"
    if tr1: "tr1 = Trace (\<lambda>_. 0) (left_blocks 0 dlys)" and
       tr2: "tr2 = Trace ((\<lambda>_. 0)(X := 1)) (right_blocks dlyvs)" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t dlys dlyvs tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] par_blks" and
      2: "combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] [left_blocks 0 dlys, right_blocks dlyvs] par_blks"
      using combine_par_traceE2 by blast
    then obtain n where 3: "par_blks = tot_blocks n"
      using testHL13_blocks by blast
    show ?thesis
      apply (rule exI[where x=n])
      using 1 unfolding 3 by auto
  qed
  show ?thesis
    apply (rule Valid_parallel2'[OF _ _ testHL13a testHL13b]) 
    using 1 by auto
qed


text \<open>Example with interrupt, loop, and parallel\<close>

inductive ileft_blocks :: "real \<Rightarrow> trace_block list \<Rightarrow> bool" where
  "ileft_blocks x []"
| "ileft_blocks v rest \<Longrightarrow> dly1 \<ge> 0 \<Longrightarrow>
   ileft_blocks x (ODEOutBlock dly1 (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+x)){0..dly1}) ''ch'' (dly1+x) ({''ch''}, {}) #
                   InBlock dly2 ''ch'' X v ({}, {''ch''}) # rest)"

lemma end_ileft_blocks:
  "ileft_blocks x blks \<Longrightarrow>
   \<exists>v. end_of_blocks ((\<lambda>_. 0)(X := x)) blks = ((\<lambda>_. 0)(X := v))"
proof (induction rule: ileft_blocks.induct)
  case (1 x)
  then show ?case by auto
next
  case (2 v rest dly1 x dly2)
  from 2(3) obtain v2 where 3:
    "end_of_blocks ((\<lambda>_. 0)(X := v)) rest = (\<lambda>_. 0)(X := v2)"
    by blast
  show ?case
    apply (rule exI[where x=v2])
    by (auto simp add: 3 2(2))
qed

lemma end_ileft_blocks_init:
  assumes "ileft_blocks 0 blks"
  shows "\<exists>v. end_of_blocks (\<lambda>_. 0) blks = ((\<lambda>_. 0)(X := v))"
proof -
  have 1: "(\<lambda>_. 0) = (\<lambda>_. 0)(X := 0)"
    by auto
  show ?thesis
    apply (subst 1) apply (rule end_ileft_blocks)
    using assms by auto
qed

lemma ileft_blocks_snoc:
  "ileft_blocks x blks \<Longrightarrow>
   end_of_blocks ((\<lambda>_. 0)(X := x)) blks = ((\<lambda>_. 0)(X := v)) \<Longrightarrow> dly1 \<ge> 0 \<Longrightarrow>
   ileft_blocks x (blks @ [ODEOutBlock dly1 (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..dly1}) ''ch'' (dly1+v) ({''ch''}, {}),
      InBlock dly2 ''ch'' X v2 ({}, {''ch''})])"
proof (induction rule: ileft_blocks.induct)
  case (1 x)
  have "v = x"
    using 1 apply simp by metis
  show ?case
    apply (simp only: append_Nil \<open>v = x\<close>)
    by (auto intro!: ileft_blocks.intros 1(2))
next
  case (2 v1 rest dly11 x1 dly21)
  show ?case
    thm 2
    apply (simp only: append_Cons)
    apply (rule ileft_blocks.intros(2)[of v1 _ dly11 x1 dly21])
     apply (rule 2(3))
    using 2(2,4,5) apply auto
    by (auto simp add: fun_upd_def)
qed

lemma testHL14o:
  assumes "end_of_trace (Trace (\<lambda>_. 0) list) = (\<lambda>_. 0)(X := v)"
    shows "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) list)
    (Interrupt (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) [
             ((Send ''ch'' (\<lambda>s. s X)), Skip)])
    (\<lambda>t. \<exists>d. t = Trace (\<lambda>_. 0) (list@[ODEOutBlock d (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..d}) ''ch'' (d+v) ({''ch''}, {})])
              \<and> d \<ge> 0)"
proof -
  have main: "ODEOutBlock d (restrict p {0..d}) ''ch'' (p d X) ({''ch''}, {}) =
              ODEOutBlock d (\<lambda>t\<in>{0..d}. (\<lambda>_. 0)(X := t + v)) ''ch'' (d + v) ({''ch''}, {})"
    if pre: "0 \<le> d" "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) p d"
       "p 0 = end_of_blocks (\<lambda>_. 0) list"
     for p d
  proof-
    have 1: "restrict p {0..d} = restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..d}"
    proof -
      interpret loc:ll_on_open_it "{-1<..}" "(\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (vec2state v))" "UNIV" "0"
        apply standard
        apply auto
        subgoal proof -
        have 1: "(\<chi> a. (if a = X then \<lambda>_. 1 else (\<lambda>_. 0)) (($) v)) = (\<chi> a. if a = X then 1 else 0)"
          for v::vec
          by auto
        show ?thesis
          unfolding state2vec_def vec2state_def fun_upd_def 1
          by (rule local_lipschitz_constI)
        qed
        done
      have step2: "((\<lambda>t. state2vec ((\<lambda>_. 0)(X := t+v))) solves_ode ((\<lambda>t. \<lambda>v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1)))(vec2state v)))) {0..} UNIV"
        unfolding solves_ode_def has_vderiv_on_def
        apply auto
        apply (rule has_vector_derivative_projI)
        apply (auto simp add: state2vec_def)
        apply (rule has_vector_derivative_eq_rhs)
         apply (auto intro!: derivative_intros)[1]
        by auto
      have step4: "(loc.flow 0 (state2vec ((\<lambda>_. 0)(X := v)))) t = (\<lambda>t. state2vec((\<lambda>_. 0)(X := t+v))) t" if "t \<in> {0..}" for t
        apply (rule loc.maximal_existence_flow(2)[OF step2])
        using that by (auto simp add: state2vec_def)
      have step5: "((\<lambda>t. state2vec(p t)) solves_ode ((\<lambda>t. \<lambda>v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1)))(vec2state v)))) {0..d} UNIV"
        using pre unfolding ODEsol_def solves_ode_def by auto
      have step6: "loc.flow 0 (state2vec ((\<lambda>_. 0)(X := v))) t = state2vec (p t)" if "t\<in>{0..d}" for t
        apply (rule loc.maximal_existence_flow(2)[OF step5])
        using assms that pre by auto
      have step7:"(\<lambda>t. state2vec((\<lambda>_. 0)(X := t+v))) t =  state2vec (p t)" if "t\<in>{0..d}" for t
        using step4 step6 that by auto
      then show ?thesis 
        unfolding restrict_def state2vec_def by auto
    qed
    show ?thesis
      using 1 apply (auto simp add: restrict_def)
      by (metis fun_upd_same order_refl pre(1))
  qed
  show ?thesis
    apply (rule Valid_interrupt)
    apply auto
    apply (rule Valid_skip2)
    using main by auto
qed

lemma testHL14a:
  "Valid
    (\<lambda>tr. tr = Trace (\<lambda>_. 0) [])
    (Rep (Interrupt (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) [
             ((Send ''ch'' (\<lambda>s. s X)),Skip)];
             Cm (Receive ''ch'' X)))
    (\<lambda>tr. \<exists>blks. tr = Trace (\<lambda>_. 0) blks \<and> ileft_blocks 0 blks)"
proof -
  have 1: "Valid
     (\<lambda>tr. tr = Trace (\<lambda>_. 0) blks)
     (Interrupt (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1)))
      [(''ch''[!](\<lambda>s. s X), Skip)];
      Cm (''ch''[?]X))
     (\<lambda>tr. \<exists>blks. tr = Trace (\<lambda>_. 0) blks \<and> ileft_blocks 0 blks)"
    if ileft_blks: "ileft_blocks 0 blks" for blks
  proof -
    obtain v where v: "end_of_blocks (\<lambda>_. 0) blks = ((\<lambda>_. 0)(X := v))"
      using end_ileft_blocks_init[OF ileft_blks] by blast
    have eq: "(\<lambda>_. 0) = ((\<lambda>_. 0)(X := 0))"
      by auto
    have 2: "Valid
              (\<lambda>t. t = Trace (\<lambda>_. 0) blks)
              (Interrupt (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1)))[(''ch''[!](\<lambda>s. s X), Skip)])
              (\<lambda>tr. \<exists>d. tr = Trace (\<lambda>_. 0) (blks @ [
                ODEOutBlock d (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..d}) ''ch'' (d+v) ({''ch''}, {})]) \<and> d \<ge> 0)"
      apply (rule testHL14o[of blks "v"])
      using v by auto
    have 3: "Valid
              (\<lambda>tr. \<exists>d. tr = Trace (\<lambda>_. 0) (blks @ [
                ODEOutBlock d (restrict(\<lambda>t. (\<lambda>_. 0)(X := t+v)){0..d}) ''ch'' (d+v) ({''ch''}, {})]) \<and> d \<ge> 0)
              (Cm (Receive ''ch'' X))
              (\<lambda>tr. \<exists>blks. tr = Trace (\<lambda>_. 0) blks \<and> (ileft_blocks 0 blks))"
      apply (simp only: Valid_ex_pre Valid_and_pre)
      apply auto
      subgoal premises pre for d
        apply(rule Valid_receive2)
        apply auto
        subgoal for dly v2
          unfolding extend_receive_def
          apply (auto simp add: ileft_blocks_snoc)
          apply (rule ileft_blocks_snoc[OF ileft_blks _ pre])
            apply (subst eq[symmetric]) by (rule v)
        done
      done
    show ?thesis
      using 2 3 by (auto intro: Valid_seq)
  qed
  have main: "Valid
    (\<lambda>tr. \<exists>blks. tr = Trace (\<lambda>_. 0) blks \<and> ileft_blocks 0 blks)
    (Rep (Interrupt (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) [
             ((Send ''ch'' (\<lambda>s. s X)),Skip)];
             Cm (Receive ''ch'' X)))
    (\<lambda>tr. \<exists>blks. tr = Trace (\<lambda>_. 0) blks \<and> ileft_blocks 0 blks)"
    apply (rule Valid_rep)
    apply (simp only: Valid_ex_pre Valid_and_pre)
    using 1 by auto
  show ?thesis
    apply(rule Valid_pre[OF _ main])
    apply auto
    by (rule ileft_blocks.intros(1))
qed

fun iright_blocks :: "(time \<times> real \<times> time) list \<Rightarrow> trace_block list" where
  "iright_blocks [] = []"
| "iright_blocks ((dly1, v, dly2) # rest) = WaitBlock 1 #
      InBlock dly1 ''ch'' X v ({}, {''ch''}) #
      OutBlock dly2 ''ch'' (v - 1) ({''ch''}, {}) # iright_blocks rest"

lemma iright_blocks_snoc:
  "iright_blocks (dlys @ [(dly1, v, dly2)]) =
   iright_blocks dlys @ [ WaitBlock 1,
      InBlock dly1 ''ch'' X v ({}, {''ch''}),
      OutBlock dly2 ''ch'' (v - 1) ({''ch''}, {})]"
  by (induct dlys, auto)

lemma end_of_iright_blocks:
  "end_of_blocks ((\<lambda>_. 0)(X := a)) (iright_blocks dlyvs @ [WaitBlock 1,InBlock dly1 ''ch'' X v ({}, {''ch''})]) X = v"
  by (induction dlyvs arbitrary: a, auto)

lemma end_of_iright_blocks_zero:
  "end_of_blocks (\<lambda>_. 0) (iright_blocks dlyvs @ [WaitBlock 1,InBlock dly1 ''ch'' X v ({}, {''ch''})]) X = v"
proof -
  have 1: "(\<lambda>_. 0) = ((\<lambda>_. 0)(X := 0))"
    by auto
  show ?thesis
    apply (subst 1)
    by (auto simp add: end_of_iright_blocks)
qed


lemma testHL14b:
  "Valid
    (\<lambda>tr. tr = Trace ((\<lambda>_. 0)(X := 1)) [])
    (Rep (Wait 1; Cm (Receive ''ch'' X); Cm (Send ''ch'' (\<lambda>s. s X - 1))))
    (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs))"
proof-
  have 1:"Valid (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs)) (Wait 1)
     (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs @ [WaitBlock 1]))"
    apply(simp only: Valid_ex_pre)
    apply auto
    subgoal for dlyvs
      apply(rule Valid_wait2)
      apply(rule exI[where x="dlyvs"])
      by auto
    done
  have 2:"Valid 
     (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs @ [WaitBlock 1])) 
     (Cm (''ch''[?]X))
     (\<lambda>tr. \<exists>dlyvs dly1 v. tr = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs @ [WaitBlock 1, InBlock dly1 ''ch'' X v ({}, {''ch''})]))"
    apply(simp only:Valid_ex_pre)
    apply auto
    subgoal for dlyvs
      apply(rule Valid_receive2)
      apply auto
      subgoal for dly v
        apply(rule exI[where x="dlyvs"])
        apply(rule exI[where x="dly"])
        apply(rule exI[where x="v"])
        unfolding extend_receive_def
        by auto
      done
    done
  have 3:"Valid
     (\<lambda>tr. \<exists>dlyvs dly1 v. tr = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs @ [WaitBlock 1, InBlock dly1 ''ch'' X v ({}, {''ch''})]))
     (Cm (''ch''[!](\<lambda>s. s X - 1))) 
     (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs))"
    apply(simp only:Valid_ex_pre)
    apply auto
    subgoal for dlyvs dly1 v
      apply(rule Valid_send2)
      apply auto
      subgoal for dly
        apply (rule exI[where x="dlyvs @ [(dly1, v, dly)]"])
        unfolding extend_send_def
        using end_of_iright_blocks iright_blocks_snoc by auto
      done
    done
  have 4:"Valid
    (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs))
    (Rep (Wait 1;Cm (Receive ''ch'' X); Cm (Send ''ch'' (\<lambda>s. s X - 1))))
    (\<lambda>tr. \<exists>dlyvs. tr = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs))"
    apply(rule Valid_rep)
    using 1 2 3 by (auto intro: Valid_seq)
  show ?thesis
    apply (rule Valid_pre[OF _ 4])
    apply auto
    apply (rule exI[where x="[]"])
    by auto
qed


lemma testHL14_blocks:
  "ileft_blocks 0 blks \<Longrightarrow>
   combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] [blks, iright_blocks dlyvs] par_blks \<Longrightarrow>
   \<exists>n. par_blks = tot_blocks n"
proof(induct dlyvs arbitrary: blks par_blks)
  case Nil
  from Nil(1) show ?case
  proof (induct rule: ileft_blocks.cases)
    case (1 x)
    show ?case
      apply (rule exI[where x=0])
      using Nil(2)[unfolded 1(2)] combine_blocks_triv2 by auto
  next
    case (2 v rest dly1 x dly2)
    show ?case 
      using Nil(2)[unfolded 2(2)] apply auto 
      using combine_blocks_OOutNil by blast
  qed
next
  case (Cons a dlyvs)
  from Cons(2) show ?case
  proof (induct rule: ileft_blocks.cases)
    case (1 x)
    show ?case
      using Cons(3)[unfolded 1(2)] apply (cases a) apply auto
      using combine_blocks_NilWait2 combine_blocks_NilIn by blast
  next
    case (2 v rest dly1 x dly2)
    have 1: "combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)]
      [ODEOutBlock dly1 (restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..dly1}) ''ch'' dly1 ({''ch''}, {}) # 
       InBlock dly2 ''ch'' X v ({}, {''ch''}) # rest,
       WaitBlock 1 #
       InBlock (fst a) ''ch'' X (fst(snd a)) ({}, {''ch''}) #
       OutBlock (snd(snd a)) ''ch'' ((fst(snd a)) - 1) ({''ch''}, {}) # 
       iright_blocks dlyvs]
       par_blks"
      using Cons(3)[unfolded 2(2) 2(1)[symmetric]]
      apply (cases a) by (auto simp add: fun_upd_def)

    obtain rest2 where s2:
      "dly1 \<ge> 1"
      "combine_blocks [(restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..dly1}) 1, (\<lambda>_. 0)(X := 1)]
      [ODEOutBlock (dly1 - 1) ((\<lambda>s. restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..dly1} (s + 1))) ''ch'' dly1 ({''ch''}, {}) # 
       InBlock dly2 ''ch'' X v ({}, {''ch''}) # rest,
       InBlock (fst a) ''ch'' X (fst(snd a)) ({}, {''ch''}) #
       OutBlock (snd(snd a)) ''ch'' ((fst(snd a)) - 1) ({''ch''}, {}) # 
       iright_blocks dlyvs]
       rest2"
      "par_blks = (ParWaitBlock 1 (\<lambda>d. if 0\<le>d \<and> d\<le>1 then [(restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..dly1}) d, (\<lambda>_. 0)(X := 1)] else undefined)) # rest2"
      using combine_blocks_ODEOutW2[OF 1] by blast

    from s2 have 21:
      "combine_blocks [(\<lambda>_. 0)(X := 1), (\<lambda>_. 0)(X := 1)]
      [ODEOutBlock (dly1 - 1) ((\<lambda>s. restrict(\<lambda>t. (\<lambda>_. 0)(X := t)){0..dly1} (s + 1))) ''ch'' dly1 ({''ch''}, {}) # 
       InBlock dly2 ''ch'' X v ({}, {''ch''}) # rest,
       InBlock (fst a) ''ch'' X (fst(snd a)) ({}, {''ch''}) #
       OutBlock (snd(snd a)) ''ch'' ((fst(snd a)) - 1) ({''ch''}, {}) # 
       iright_blocks dlyvs]
       rest2"
      "par_blks = (ParWaitBlock 1 (\<lambda>d. if 0\<le>d \<and> d\<le>1 then [(\<lambda>_. 0)(X := d), (\<lambda>_. 0)(X := 1)] else undefined)) # rest2"
      by auto

    let ?sts = "[(\<lambda>_. 0)(X := 1), (\<lambda>_. 0)(X := 1)]"
    obtain rest3 where 3:
      "dly1 - 1 = 0" "fst a = 0" "dly1 = fst (snd a)"
      "combine_blocks (?sts[1 := end_of_blocks (?sts ! 1)
          [InBlock (fst a) ''ch'' X (fst(snd a)) ({}, {''ch''})]])
       [InBlock dly2 ''ch'' X v ({}, {''ch''}) # rest,
        OutBlock (snd(snd a)) ''ch'' ((fst(snd a)) - 1) ({''ch''}, {}) # 
        iright_blocks dlyvs] rest3"
      "rest2 = IOBlock 1 0 ''ch'' X dly1 # rest3"
      using combine_blocks_ODEIO2[OF 21(1)] by blast

    from 3(4) have 31:
      "combine_blocks ([(\<lambda>_. 0)(X := 1), (\<lambda>_. 0)(X := fst (snd a))])
       [InBlock dly2 ''ch'' X v ({}, {''ch''}) # rest,
        OutBlock (snd(snd a)) ''ch'' ((fst(snd a)) - 1) ({''ch''}, {}) # 
        iright_blocks dlyvs] rest3"
      by auto

    let ?sts2 = "[(\<lambda>_. 0)(X := 1), (\<lambda>_. 0)(X := fst (snd a))]"
    from 31 obtain rest4 where 4:
      "dly2 = 0" "snd (snd a) = 0" "fst (snd a) - 1 = v"
      "combine_blocks (?sts2[0 := end_of_blocks (?sts2 ! 0) [InBlock dly2 ''ch'' X v ({}, {''ch''})]])
       [rest, iright_blocks dlyvs] rest4"
      "rest3 = IOBlock 0 1 ''ch'' X (fst (snd a) - 1) # rest4"
      using combine_blocks_IO2' by blast

    from 3(1) have 5: "dly1 = 1" "(\<lambda>_. 0)(X := 0) = (\<lambda>_. 0)" "v = 0"
      by (auto simp add: 4(3)[symmetric] 3(3)[symmetric])

    from 4(4) have 41:
      "combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)]
       [rest, iright_blocks dlyvs] rest4"
      by (auto simp add: 4(3)[symmetric] 3(3)[symmetric] 5)

    obtain n where 6: "rest4 = tot_blocks n"
      using Cons(1) 41 2(3) 5(3) by blast

    show ?thesis
      apply (rule exI[where x="Suc n"])
      by (auto simp add: 21(2) 3(5) 4(5) 5 6 3(3)[symmetric])
  qed
qed


lemma testHL14:
  "ParValid
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), ((\<lambda>_. 0)(X := 1))] [])
    (PProc [Rep (Interrupt (ODE ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) [
             ((Send ''ch'' (\<lambda>s. s X)),Skip)];
             Cm (Receive ''ch'' X)),
            Rep(Wait 1;(Cm (Receive ''ch'' X);
             Cm (Send ''ch'' (\<lambda>s. s X - 1))))] )
    (\<lambda>t. \<exists>n. t = ParTrace [(\<lambda>_. 0), ((\<lambda>_. 0)(X := 1))] (tot_blocks n))"
proof -
  have 1: "(\<exists>n. par_t = ParTrace [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] (tot_blocks n))"
    if tr1: "tr1 = Trace (\<lambda>_. 0) blks1" "ileft_blocks 0 blks1" and
       tr2: "tr2 = Trace ((\<lambda>_. 0)(X := 1)) (iright_blocks dlyvs2)" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t blks1 dlyvs2 tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] par_blks" and
      2: "combine_blocks [\<lambda>_. 0, (\<lambda>_. 0)(X := 1)] [blks1, iright_blocks dlyvs2] par_blks"
      using combine_par_traceE2 by blast
    then obtain n where 3: "par_blks = tot_blocks n"
      using testHL14_blocks tr1(2) by blast
    show ?thesis
      apply (rule exI[where x=n])
      using 1 unfolding 3 by auto
  qed
  show ?thesis
    apply (rule Valid_parallel2'[OF _ _ testHL14a testHL14b])
    using 1 by auto
qed


end
