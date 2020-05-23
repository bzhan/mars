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
  ODE "var set" "var \<Rightarrow> exp"

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
| "event_of_block (WaitBlock _) = Tau"
| "event_of_block (ODEBlock _ _) = Tau"
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
    IOBlock nat nat cname real  \<comment> \<open>Receive process, Send process, channel name, value sent\<close>
  | ParTauBlock int state       \<comment> \<open>Instantaneous update on one process to new state\<close>
  | ParWaitBlock real   \<comment> \<open>Delay\<close>

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

text \<open>Main definition: combining a list of block lists.
  combine_blocks blkss pblks means the list of block lists blkss can be combined
  together into pblks.\<close>
inductive combine_blocks :: "trace_block list list \<Rightarrow> par_block list \<Rightarrow> bool" where
  "\<forall>i<length blkss. blkss ! i = [] \<Longrightarrow> combine_blocks blkss []"  \<comment> \<open>empty case\<close>
  \<comment> \<open>Wait action at i'th process\<close>
| "i < length blkss \<Longrightarrow>
   t \<ge> 0 \<Longrightarrow>
   \<forall>k<length blkss. blkss ! k \<noteq> [] \<longrightarrow> delay_of_block (hd (blkss ! k)) \<ge> t \<Longrightarrow>
   blkss ! i \<noteq> [] \<Longrightarrow>
   delay_of_block (hd (blkss ! i)) = t \<Longrightarrow>
   event_of_block (hd (blkss ! i)) = Tau \<Longrightarrow>
   combine_blocks (remove_one i t blkss) pblks \<Longrightarrow>
   combine_blocks blkss ((ParWaitBlock t) # pblks)"
  \<comment> \<open>Communication between i'th and j'th process\<close>
| "i < length blkss \<Longrightarrow> j < length blkss \<Longrightarrow> i \<noteq> j \<Longrightarrow>
   blkss ! i \<noteq> [] \<Longrightarrow> blkss ! j \<noteq> [] \<Longrightarrow>
   delay_of_block (hd (blkss ! i)) = 0 \<Longrightarrow>
   delay_of_block (hd (blkss ! j)) = 0 \<Longrightarrow>
   event_of_block (hd (blkss ! i)) = In c v \<Longrightarrow>
   event_of_block (hd (blkss ! j)) = Out c v \<Longrightarrow>
   combine_blocks (remove_pair i j blkss) pblks \<Longrightarrow>
   combine_blocks blkss ((IOBlock i j c v) # pblks)"

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

subsection \<open>Definitions of ODEs\<close>

text \<open>the value of vector field\<close>

definition Vagree :: "state \<Rightarrow> state \<Rightarrow> var set \<Rightarrow> bool"
  where "Vagree u v V = (\<forall>i. i \<in> V \<longrightarrow> u i = v i)"

type_synonym vec = "real^(var)"

definition state2vec :: "state \<Rightarrow> vec" where
  "state2vec s = (\<chi> x. s x)"

definition vec2state :: "vec \<Rightarrow> state" where
  "(vec2state v) x = v $ x"

lemma vec_state_map1[simp]: "vec2state (state2vec s) = s"
  unfolding vec2state_def state2vec_def
  by auto

lemma vec_state_map2[simp]: "state2vec (vec2state s) = s"
  unfolding vec2state_def state2vec_def
  by auto

text \<open>Given ODE and a state, find the derivative vector.\<close>
fun ODE2Vec :: "ODE \<Rightarrow> state \<Rightarrow> vec" where
  "ODE2Vec (ODE S f) s = state2vec (\<lambda>a. if a \<in> S then f a s else 0)"

text \<open>History p on time {0 .. d} is a solution to ode.\<close>
definition ODEsol :: "ODE \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> real \<Rightarrow> bool" where
  "ODEsol ode p d = (d \<ge> 0 \<and> (((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {0 .. d}))"

text \<open>Exists solution f to the ODE on time {0 .. d}, starting at u and ending at v.\<close>
definition ODEstate :: "ODE \<Rightarrow> real \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "ODEstate ode d u v = (d \<ge> 0 \<and> (\<exists>f. ODEsol ode f d \<and> u = f 0 \<and> v = f d))"

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
  sorry

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


definition INV :: "fform \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> real \<Rightarrow> bool" where
  "INV Inv p d = (d \<ge> 0 \<and> (\<forall>t. 0\<le>t\<and>t\<le>d \<longrightarrow> Inv (p t)))"


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
  sendB: "big_step (Cm (Send ch e)) tr
    \<comment> \<open>dly \<ge> 0\<close>
    (extend_send ch e dly ({ch}, {}) tr)"
  \<comment> \<open>Receive: dly \<ge> 0 is the amount of time waited at the current receive.
      v is the value received.\<close>
| receiveB: "big_step (Cm (Receive ch var)) tr
    \<comment> \<open>dly \<ge> 0\<close>
    (extend_receive ch var dly v ({}, {ch}) tr)"
| skipB: "big_step Skip tr
    (extend_trace tr (TauBlock (end_of_trace tr)))"
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
    big_step p2 (extend_trace tr (ODEOutBlock d p ch (e (p d)) (rdy_of_echoice cs))) tr3 \<Longrightarrow>
    big_step (Interrupt ode cs) tr tr3"
| InterruptReceiveB:
   "d \<ge> 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    p 0 = end_of_trace tr \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (extend_trace tr (ODEInBlock d p ch var v (rdy_of_echoice cs))) tr3 \<Longrightarrow>
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
  shows "big_step (Cm (Send ch e)) (Trace s blks) (Trace s blks')"
proof -
  have 1: "Trace s (blks @ [OutBlock dly ch (e (end_of_trace (Trace s blks))) ({ch}, {})]) =
        extend_send ch e dly ({ch}, {}) (Trace s blks)"
    unfolding extend_send_def extend_trace.simps by auto
  show ?thesis
    apply (subst assms(1))
    apply (subst 1)
    by (rule sendB)
qed

lemma receiveB2:
  assumes "blks' = blks @ [InBlock dly ch var v ({}, {ch})]"
  shows "big_step (Cm (Receive ch var)) (Trace s blks) (Trace s blks')"
proof -
  have 1: "Trace s (blks @ [InBlock dly ch var v ({}, {ch})]) =
        extend_receive ch var dly v ({}, {ch}) (Trace s blks)"
    unfolding extend_receive_def extend_trace.simps by auto
  show ?thesis
    apply (subst assms(1))
    apply (subst 1)
    by (rule receiveB)
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
  by simp

text \<open>Send x + 1 immediately\<close>
lemma test1b: "big_step (Cm (Send ''ch'' (\<lambda>s. s X + 1)))
        (Trace ((\<lambda>_. 0)(X := 1)) [])
        (Trace ((\<lambda>_. 0)(X := 1)) [OutBlock 0 ''ch'' 2 ({''ch''}, {})])"
  apply (rule sendB2)
  by simp

text \<open>Send 1 after delay 2\<close>
lemma test1c: "big_step (Cm (Send ''ch'' (\<lambda>_. 1)))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [OutBlock 2 ''ch'' 1 ({''ch''}, {})])"
  apply (rule sendB2)
  by simp

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
        (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [IOBlock 1 0 ''ch'' 1])"
proof -
  have 1: "combine_blocks [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)
  have 2: "combine_blocks
     [[OutBlock 0 ''ch'' 1 ({''ch''}, {})],
      [InBlock 0 ''ch'' X 1 ({}, {''ch''})]]
     [IOBlock 1 0 ''ch'' 1]"
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
    (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [ParWaitBlock 2, IOBlock 1 0 ''ch'' 1])"
proof -
  have 1: "combine_blocks [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)
  have 2: "combine_blocks
     [[WaitBlock 2, OutBlock 0 ''ch'' 1 ({''ch''}, {})],
      [InBlock 2 ''ch'' X 1 ({}, {''ch''})]]
     [ParWaitBlock 2, IOBlock 1 0 ''ch'' 1]"
    apply (rule combine_blocks.intros(2)[where i=0])
         apply (auto simp add: less_Suc_eq)
    unfolding remove_one_def Let_def apply auto
     apply (rule combine_blocks.intros(3))
                apply (auto simp add: less_Suc_eq)
    unfolding remove_pair_def Let_def apply auto
    by (rule 1)
  show ?thesis
    apply (rule parallelB2[OF test5 test2b])
       apply (auto simp add: compat_rdy_block_pair_def less_Suc_eq combine_par_trace.simps)
    using 1 2 by auto
qed


text \<open>Loop one time\<close>
lemma test7: "big_step (Rep (Assign X (\<lambda>s. s X + 1); Cm (Send ''ch'' (\<lambda>s. s X))))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [TauBlock ((\<lambda>_. 0)(X := 1)), OutBlock 0 ''ch'' 1 ({''ch''}, {})])"
  apply (rule RepetitionB2)
   apply (rule seqB)
    apply (rule assignB)
  apply auto[1]
   apply (rule sendB2)
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
  apply (rule sendB2)
   apply auto
  apply (rule RepetitionB2)
   apply (rule seqB)
  apply (rule assignB)
   apply auto[1]
   apply (rule sendB2)
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
    (ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [IOBlock 1 0 ''ch'' 1, ParWaitBlock 1])"
proof -
  have 1: "combine_blocks [[], []] []"
    apply (rule combine_blocks.intros(1))
    by (auto simp add: less_Suc_eq)
  have 2: "combine_blocks
     [[OutBlock 0 ''ch'' 1 ({''ch'', ''ch2''}, {}), WaitBlock 1],
      [InBlock 0 ''ch'' X 1 ({}, {''ch''})]]
     [IOBlock 1 0 ''ch'' 1, ParWaitBlock 1]"
    apply (rule combine_blocks.intros(3)[where i=1 and j=0])
             apply (auto simp add: remove_pair_def)
    apply (rule combine_blocks.intros(2)[where i=0])
          apply (auto simp add: remove_one_def less_Suc_eq)
    by (rule 1)
  show ?thesis
    apply (rule parallelB2[OF test9a test2a])
    apply (auto simp add: compat_rdy_block_pair_def less_Suc_eq combine_par_trace.simps)
    using 1 2 by auto
qed

text \<open>ODE Example 1\<close>
lemma test11: "big_step (Cont (ODE {X} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
        (Trace (\<lambda>_. 0) [])
        (Trace (\<lambda>_. 0) [ODEBlock 1 (restrict (\<lambda>t. (\<lambda>_. 0)(X := t)) {0..1})])"
  apply (rule ContB)
  apply auto
  apply (simp add: ODEsol_def state2vec_def fun_upd_def)
  unfolding has_vderiv_on_def
  unfolding has_vector_derivative_def
  unfolding has_derivative_iff_norm
  apply auto
  subgoal premises pre for x
    unfolding bounded_linear_def 
    apply simp
    unfolding bounded_linear_axioms_def
    apply auto
    done
  subgoal premises pre for x
  proof-
    have 1:"\<forall>i.((\<chi> x. if x = X then y else 0) - (\<chi> xa. if xa = X then x else 0) -
            (y - x) *\<^sub>R
            (\<chi> xa. if xa = X
                   then (if xa = X then \<lambda>_. 1 else (\<lambda>_. 0)) (\<lambda>xa. if xa = X then x else 0)
                   else 0) ) $ i= 0 " for y 
      by auto
    have 2:"(\<forall>i. (v:: vec)$i = 0) \<Longrightarrow> norm v = 0" for v
      apply simp 
      by (simp add: vec_eq_iff)
    have 3:"norm
           ((\<chi> x. if x = X then y else 0) - (\<chi> xa. if xa = X then x else 0) -
            (y - x) *\<^sub>R
            (\<chi> xa. if xa = X
                   then (if xa = X then \<lambda>_. 1 else (\<lambda>_. 0)) (\<lambda>xa. if xa = X then x else 0)
                   else 0)) = 0" for y
      using 1[of y]  2[of "((\<chi> x. if x = X then y else 0) - (\<chi> xa. if xa = X then x else 0) -
         (y - x) *\<^sub>R
         (\<chi> xa. if xa = X
                then (if xa = X then \<lambda>_. 1 else (\<lambda>_. 0)) (\<lambda>xa. if xa = X then x else 0)
                else 0))"]
      by auto
    then show ?thesis using pre by auto
  qed
  done



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

theorem Valid_ode_unique_solution:
  assumes "d \<ge> 0" "ODEsol ode p d" "\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)"
      "\<not> b (p d)" "p 0 = end_of_trace tr"
      \<comment> \<open>Some other constraints on ode\<close>
    shows "Valid
      (\<lambda>t. t = tr)
      (Cont ode b)
      (\<lambda>t. t = extend_trace tr (ODEBlock d (restrict p {0..d})))"
  sorry

thm continuous_on_TimesI

text \<open>Hoare triple for ODE with non-unique solutions\<close>
theorem Valid_ode_all_solution:
  assumes "\<forall>d p. d \<ge> 0 \<longrightarrow> ODEsol ode p d \<longrightarrow>
      (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<longrightarrow>
      \<not> b (p d) \<longrightarrow> p 0 = end_of_trace tr \<longrightarrow> Q d p"
  shows "Valid
    (\<lambda>t. t = tr)
    (Cont ode b)
    (\<lambda>t. \<exists>d p. Q d p \<and> t = extend_trace tr (ODEBlock d (restrict p {0..d})))"
  unfolding Valid_def using assms by (metis contE)

theorem Valid_interrupt:
  assumes "\<forall>i<length es.
    case (es ! i) of
      (Send ch e, p2) \<Rightarrow>
        \<forall>p d. d \<ge> 0 \<longrightarrow> ODEsol ode p d \<longrightarrow> p 0 = end_of_trace tr \<longrightarrow>
              Valid (\<lambda>t. t = extend_trace tr (ODEOutBlock d p ch (e (p d)) (rdy_of_echoice es))) p2 R
    | (Receive ch var, p2) \<Rightarrow>
        \<forall>p d v. d \<ge> 0 \<longrightarrow> ODEsol ode p d \<longrightarrow> p 0 = end_of_trace tr \<longrightarrow>
              Valid (\<lambda>t. t = extend_trace tr (ODEInBlock d p ch var v (rdy_of_echoice es))) p2 R"
  shows
    "Valid (\<lambda>t. t = tr) (Interrupt ode es) R"
proof -
  have 1: "R tr2" if "0 \<le> d" "ODEsol ode p d"
       "p 0 = end_of_trace tr"
       "i < length es"
       "es ! i = (ch[!]e, p2)" "big_step p2 (extend_trace tr (ODEOutBlock d p ch (e (p d)) (rdy_of_echoice es))) tr2"
     for tr2 d p i ch e p2
  proof -
    have "Valid (\<lambda>t. t = extend_trace tr (ODEOutBlock d p ch (e (p d)) (rdy_of_echoice es))) p2 R"
      using assms that(1-5) by auto
    then show ?thesis
      unfolding Valid_def using that(6) by auto
  qed
  have 2: "R tr2" if "0 \<le> d" "ODEsol ode p d"
       "p 0 = end_of_trace tr"
       "i < length es"
       "es ! i = (ch[?]var, p2)" "big_step p2 (extend_trace tr (ODEInBlock d p ch var v (rdy_of_echoice es))) tr2"
     for tr2 d p i ch var p2 v
  proof -
    have "Valid (\<lambda>t. t = extend_trace tr (ODEInBlock d p ch var v (rdy_of_echoice es))) p2 R"
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
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (vec2state x)) (at x within UNIV)"
      and "\<forall>S. g' (S) (ODE2Vec ode (S)) = 0"
  shows "Valid
    (\<lambda>t. t = tr)
    (Cont ode b)
    (\<lambda>t. \<exists>d p. (\<forall>t. 0\<le>t \<and> t\<le>d \<longrightarrow> inv (p t) = inv (p 0)) \<and> t = extend_trace tr (ODEBlock d (restrict p {0..d})))"
  apply(rule Valid_ode_all_solution)
  apply auto
  subgoal premises pre for d p t
  proof-
    have 1:"\<forall>t\<in>{0 .. d}. ((\<lambda>t. inv(p t)) has_derivative  (\<lambda>s. g' (p t) (s *\<^sub>RODE2Vec ode (p t)))) (at t within {0 .. d})"
      using pre assms
      using chainrule[of inv g' ode p d] 
      by auto
    have 2:"\<forall>s. g' (p t) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec ode (p t)) = s *\<^sub>R g' (p t) (1 *\<^sub>RODE2Vec ode (p t))" if ran:"t\<in>{0 .. d}" for t
      using 1 unfolding has_derivative_def bounded_linear_def 
      using ran
      using linear_iff[of "(\<lambda>s. g' (p t) (s *\<^sub>R ODE2Vec ode (p t)))"]
      by blast
    have 3:"\<forall>s. (s *\<^sub>R 1) = s" by simp
    have 4:"\<forall>s. g' (p t) (s *\<^sub>R ODE2Vec ode (p t)) = s *\<^sub>R g' (p t) (ODE2Vec ode (p t))" if ran:"t\<in>{0 .. d}" for t
      using 2 3 ran by auto
    have 5:"\<forall>s. g' (p t) (s *\<^sub>R ODE2Vec ode (p t))= 0"  if ran:"t\<in>{0 .. d}" for t
      using 4 assms(2) ran by simp 
    show ?thesis
      using mvt_real_eq[of d "(\<lambda>t. inv(p t))""\<lambda>t. (\<lambda>s. g' (p t) (s *\<^sub>RODE2Vec ode (p t)))" t]
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
  "combine_blocks [[], []] par_blks \<Longrightarrow> par_blks = []"
proof (induct rule: combine_blocks.cases)
case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 0 \<or> i = 1"
    using 2(1,3,7) by auto
  then show ?case using 2 by auto
next
  case (3 i blkss j c v pblks)
  have "i = 0 \<or> i = 1"
    using 3(1,3,8) by auto
  then show ?case using 3 by auto
qed

lemma combine_blocks_IO2:
  "combine_blocks [OutBlock d1 ch1 v1 rdy1 # blks1,
                   InBlock d2 ch2 var v2 rdy2 # blks2] par_tr \<Longrightarrow>
   (\<exists>rest. d1 = 0 \<and> d2 = 0 \<and> ch1 = ch2 \<and> v1 = v2 \<and>
           combine_blocks [blks1, blks2] rest \<and> par_tr = (IOBlock 1 0 ch1 v1) # rest)"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 0 \<or> i = 1"
    using 2(1,3,7) by auto
  then show ?case using 2 by auto
next
  case (3 i blkss j c v pblks)
  have "length blkss = 2"
    using 3(1,12) by auto
  have "i = 0 \<or> i = 1" "j = 0 \<or> j = 1"
    using 3(1,3,4,12) by auto
  then have ij: "i = 1" "j = 0"
    using 3(1,9,10,11) by auto
  have "d1 = 0" "d2 = 0"
    using 3(1,8,9,12) ij by auto
  moreover have "v1 = v2" "ch1 = ch2" "v = v1" "c = ch1"
    using 3(1,10,11,12) ij by auto
  moreover have "\<exists>rest. combine_blocks [blks1, blks2] rest \<and> par_tr = (IOBlock 1 0 ch1 v1) # rest"
    apply (rule exI[where x="pblks"])
    using 3(2,12) unfolding ij \<open>v = v1\<close> \<open>c = ch1\<close> 3(1)[symmetric] 3(12)
    by (auto simp add: remove_pair_def)
  ultimately show ?case
    using 3(4) by (auto simp add: less_Suc_eq)
qed

lemma combine_blocks_OutW2:
  "combine_blocks [OutBlock d1 ch1 v ({ch1}, {}) # blks1,
                   WaitBlock d2 # blks2] par_tr \<Longrightarrow>
   \<exists>rest. d1 \<ge> d2 \<and>
          combine_blocks [OutBlock (d1 - d2) ch1 v ({ch1}, {}) # blks1, blks2] rest \<and>
          par_tr = ParWaitBlock d2 # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 1"
    using 2(1,3,8) by (auto simp add: less_Suc_eq)
  then have "t = d2"
    using 2(1,7) by auto
  then have "d1 \<ge> d2"
    using 2(1,5) by auto
  show ?case
    apply (rule exI[where x=pblks])
    using 2(1,2,9) \<open>i = 1\<close> \<open>d1 \<ge> d2\<close> \<open>t = d2\<close>
    by (auto simp add: remove_one_def Let_def)
next
  case (3 i blkss j c v pblks)
  then show ?case by (auto simp add: less_Suc_eq)
qed

lemma combine_blocks_WaitNil2:
  "combine_blocks [WaitBlock d # blks1, []] par_tr \<Longrightarrow>
   \<exists>rest. combine_blocks [blks1, []] rest \<and> par_tr = ParWaitBlock d # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 0" "t = d"
    using 2(1,3,6,7) by (auto simp add: less_Suc_eq)
  show ?case
    apply (rule exI[where x=pblks])
    using 2 \<open>i = 0\<close> \<open>t = d\<close> by (auto simp add: remove_one_def)
next
  case (3 i blkss j c v pblks)
  then show ?case
    by (auto simp add: less_Suc_eq)
qed

lemma combine_blocks_TauNil2:
  "combine_blocks [TauBlock st # blks1, []] par_tr \<Longrightarrow>
   \<exists>rest. combine_blocks [blks1, []] rest \<and> par_tr = ParWaitBlock 0 # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 0" "t = 0"
    using 2(1,3,6,7) by (auto simp add: less_Suc_eq)
  show ?case
    apply (rule exI[where x=pblks])
    using 2 \<open>i = 0\<close> \<open>t = 0\<close> by (auto simp add: remove_one_def)
next
  case (3 i blkss j c v pblks)
  then show ?case
    by (auto simp add: less_Suc_eq)
qed

lemma combine_blocks_TauIn2:
  "combine_blocks [TauBlock st # blks1, blk2 # blks2] par_tr \<Longrightarrow>
   event_of_block blk2 \<noteq> Tau \<Longrightarrow>
   \<exists>rest. combine_blocks [blks1, blk2 # blks2] rest \<and> par_tr = ParWaitBlock 0 # rest"
proof (induct rule: combine_blocks.cases)
  case (1 blkss)
  then show ?case by auto
next
  case (2 i blkss t pblks)
  have "i = 0" "t = 0"
    using 2 by (auto simp add: less_Suc_eq)
  show ?case
    apply (rule exI[where x=pblks])
    using 2 \<open>i = 0\<close> \<open>t = 0\<close> by (auto simp add: remove_one_def)
next
  case (3 i blkss j c v pblks)
  then show ?case by (auto simp add: less_Suc_eq)
qed


lemma combine_blocks_OutNil:
  "combine_blocks [OutBlock d1 ch1 v ({ch1}, {}) # blks1, []] par_tr \<Longrightarrow> False"
  apply (induct rule: combine_blocks.cases)
  by (auto simp add: less_Suc_eq)

lemma combine_blocks_NilIn:
  "combine_blocks [[], InBlock d2 ch2 var v2 ({}, {ch2}) # blks2] par_tr \<Longrightarrow> False"
  apply (induct rule: combine_blocks.cases)
  by (auto simp add: less_Suc_eq)

subsection \<open>More on combine_par_trace\<close>

inductive_cases combine_par_traceE: "combine_par_trace trs par_tr"
thm combine_par_traceE

lemma combine_par_traceE2:
  "combine_par_trace [Trace st1 blks1, Trace st2 blks2] par_tr \<Longrightarrow>
   \<exists>par_blks. par_tr = ParTrace [st1, st2] par_blks \<and> combine_blocks [blks1, blks2] par_blks"
  apply (elim combine_par_traceE)
  apply auto
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
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [IOBlock 1 0 ''ch'' 1])"
proof -
  have 1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] [IOBlock 1 0 ''ch'' 1]"
    if tr1: "tr1 = Trace (\<lambda>_. 0) [OutBlock dly1 ''ch'' 1 ({''ch''}, {})]" and
       tr2: "tr2 = Trace (\<lambda>_. 0) [InBlock dly2 ''ch'' X v ({}, {''ch''})]" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t dly1 dly2 v tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] par_blks" and
      2: "combine_blocks [
              [OutBlock dly1 ''ch'' 1 ({''ch''}, {})],
              [InBlock dly2 ''ch'' X v ({}, {''ch''})]] par_blks"
      using combine_par_traceE2 by blast
    from 2 obtain rest where
      3: "dly1 = 0" "dly2 = 0" "v = 1" "combine_blocks [[], []] rest"
         "par_blks = (IOBlock 1 0 ''ch'' 1) # rest"
      using combine_blocks_IO2 by blast
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
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [ParWaitBlock 2, IOBlock 1 0 ''ch'' 1])"
proof -
  have 1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] [ParWaitBlock 2, IOBlock 1 0 ''ch'' 1]"
    if tr1: "tr1 = Trace (\<lambda>_. 0) [OutBlock dly1 ''ch'' 1 ({''ch''}, {})]" and
       tr2: "tr2 = Trace (\<lambda>_. 0) [WaitBlock 2, InBlock dly2 ''ch'' X v ({}, {''ch''})]" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t dly1 dly2 v tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] par_blks" and
      2: "combine_blocks [[OutBlock dly1 ''ch'' 1 ({''ch''}, {})],
                          [WaitBlock 2, InBlock dly2 ''ch'' X v ({}, {''ch''})]] par_blks"
      using combine_par_traceE2 by blast
    from 2 obtain rest where
      3: "dly1 \<ge> 2"
      "combine_blocks [[OutBlock (dly1 - 2) ''ch'' 1 ({''ch''}, {})],
                       [InBlock dly2 ''ch'' X v ({}, {''ch''})]] rest"
      "par_blks = ParWaitBlock 2 # rest"
      using combine_blocks_OutW2 by blast
    from 3(2) obtain rest2 where
      4: "dly1 - 2 = 0" "dly2 = 0" "v = 1" "combine_blocks [[], []] rest2"
         "rest = (IOBlock 1 0 ''ch'' 1) # rest2"
      using combine_blocks_IO2 by blast
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
| "comm_blocks x (Suc n) = ParWaitBlock 0 # IOBlock 1 0 ''ch'' (x + 1) # comm_blocks (x + 1) n"

lemma testHL9_blocks:
  "combine_blocks [count_blocks x dlys, receive_blocks dlyvs] par_blks \<Longrightarrow>
   \<exists>n. par_blks = comm_blocks x n"
proof (induct dlyvs arbitrary: dlys par_blks x)
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
      using combine_blocks_TauNil2 combine_blocks_OutNil by blast
  qed
next
  case (Cons p dlyvs)
  note Cons1 = Cons
  then show ?case
  proof (cases dlys)
    case Nil
    then show ?thesis
      using Cons1(2) apply (cases p) apply auto
      using combine_blocks_NilIn by blast
  next
    case (Cons d restd)
    have 1: "combine_blocks
        [TauBlock ((\<lambda>_. 0)(X := x + 1)) # OutBlock d ''ch'' (x + 1) ({''ch''}, {}) # count_blocks (x + 1) restd,
         InBlock (fst p) ''ch'' X (snd p) ({}, {''ch''}) # receive_blocks dlyvs]
        par_blks"
      using Cons Cons1(2) apply (cases p) by auto
    have 2: "event_of_block (InBlock (fst p) ''ch'' X (snd p) ({}, {''ch''})) \<noteq> Tau"
      by auto
    from 1 2 obtain rest where
      3: "combine_blocks [OutBlock d ''ch'' (x + 1) ({''ch''}, {}) # count_blocks (x + 1) restd,
                          InBlock (fst p) ''ch'' X (snd p) ({}, {''ch''}) # receive_blocks dlyvs] rest"
         "par_blks = ParWaitBlock 0 # rest"
      using combine_blocks_TauIn2 by blast
    from 3 obtain rest2 where
      4: "d = 0" "fst p = 0" "x + 1 = snd p" "combine_blocks [count_blocks (x + 1) restd, receive_blocks dlyvs] rest2"
         "rest = (IOBlock 1 0 ''ch'' (x + 1)) # rest2"
      using combine_blocks_IO2 by blast
    obtain n where 5: "rest2 = comm_blocks (x + 1) n"
      using 4(4) Cons1(1) by blast
    then have 6: "par_blks = ParWaitBlock 0 # IOBlock 1 0 ''ch'' (x + 1) # comm_blocks (x + 1) n"
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
      2: "combine_blocks [count_blocks 0 dlys, receive_blocks dlyvs] par_blks"
      using combine_par_traceE2 by blast
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
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [IOBlock 1 0 ''ch'' 1, ParWaitBlock 1])"
proof -
  have 1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] [IOBlock 1 0 ''ch'' 1, ParWaitBlock 1]"
    if tr1: "tr1 = Trace (\<lambda>_. 0) [OutBlock dly1 ''ch'' 1 ({''ch'', ''ch2''}, {}), WaitBlock 1]" and
       tr2: "tr2 = Trace (\<lambda>_. 0) [InBlock dly2 ''ch'' X v ({}, {''ch''})]" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t dly1 dly2 v tr1 tr2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [\<lambda>_. 0, \<lambda>_. 0] par_blks" and
      2: "combine_blocks [[OutBlock dly1 ''ch'' 1 ({''ch'', ''ch2''}, {}), WaitBlock 1],
                          [InBlock dly2 ''ch'' X v ({}, {''ch''})]] par_blks"
      using combine_par_traceE2 by blast
    from 2 obtain rest where
      3: "dly1 = 0" "dly2 = 0" "v = 1" "combine_blocks [[WaitBlock 1], []] rest"
         "par_blks = (IOBlock 1 0 ''ch'' 1) # rest"
      using combine_blocks_IO2 by blast
    from 3(4) obtain rest2 where
      4: "combine_blocks [[], []] rest2" "rest = ParWaitBlock 1 # rest2"
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
      2: "combine_blocks [[OutBlock dly1 ''ch2'' 2 ({''ch'', ''ch2''}, {}), WaitBlock 2],
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
    (Cont (ODE {X} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
    (\<lambda>t. t = Trace (\<lambda>_. 0) [ODEBlock 1 (restrict (\<lambda>t. (\<lambda>_. 0)(X := t)){0..1})])"
proof-
  have main: "restrict p2 {0..d2} = restrict (\<lambda>t. ((\<lambda>_. 0)(X := t))) {0..1} \<and> d2 = 1"
    if cond: "0 \<le> d2"
       "ODEsol (ODE {X} ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) p2 d2"
       "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> p2 t X < 1"
       "\<not> p2 d2 X < 1"
       "p2 0 = (\<lambda>_. 0)"
     for p2 d2
  proof-
    interpret loc:ll_on_open_it "{-1<..}" "(\<lambda>t. \<lambda>v. ODE2Vec (ODE {X} ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (vec2state v))" "UNIV" "0"
      apply standard
      apply auto
      subgoal proof -
        have 1: "(\<chi> a. if a = X then (if a = X then \<lambda>_. 1 else (\<lambda>_. 0)) (($) v) else 0) = (\<chi> a. if a = X then 1 else 0)"
          for v::vec
          by auto
        show ?thesis
          unfolding state2vec_def vec2state_def fun_upd_def 1
          by (rule local_lipschitz_constI)
      qed
      done
   have step2: "((\<lambda>t. state2vec ((\<lambda>_. 0)(X := t))) solves_ode ((\<lambda>t. \<lambda>v. ODE2Vec (ODE {X} ((\<lambda>_ _. 0)(X := \<lambda>_. 1)))(vec2state v)))) {0..1} UNIV"
     unfolding solves_ode_def has_vderiv_on_def
     apply auto
     apply (rule has_vector_derivative_projI)
     by (auto simp add: state2vec_def)
   have step4: "(loc.flow 0 (state2vec (\<lambda>_. 0))) t = (\<lambda>t. state2vec((\<lambda>_. 0)(X := t))) t" if "t \<in> {0..1}" for t
     apply (rule loc.maximal_existence_flow(2)[OF step2])
     using that by (auto simp add: state2vec_def)
   have step5: "((\<lambda>t. state2vec(p2 t)) solves_ode ((\<lambda>t. \<lambda>v. ODE2Vec (ODE {X} ((\<lambda>_ _. 0)(X := \<lambda>_. 1)))(vec2state v)))) {0..d2} UNIV"
     using cond(2) unfolding ODEsol_def solves_ode_def by auto
   have step7: "loc.flow 0 (state2vec (\<lambda>_. 0)) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
     apply (rule loc.maximal_existence_flow(2)[OF step5])
     using cond(1,5) that by auto
   have step8: "1 \<le> d2"
   proof (rule ccontr)
     assume 0:" \<not> (1 \<le> d2)"
     from 0 have 1:"(\<lambda>t. state2vec((\<lambda>_. 0)(X := t))) d2 = (\<lambda>t. state2vec(p2 t)) d2"
       using step4[of d2] step7[of d2] cond(1) by auto
     from 1 have 2:"((\<lambda>_. 0)(X := d2)) = p2 d2"
       unfolding state2vec_def by auto
     from 2 have 3:"p2 d2 X < 1" using 0 
       by (metis fun_upd_same less_eq_real_def linorder_neqE_linordered_idom)
     have 4:"\<not> p2 d2 X < 1" using cond(4) by auto
     then show "False" using 3 by auto
   qed
   have step9: "1 \<ge> d2"
   proof (rule ccontr)
     assume 0:"\<not> d2 \<le> 1" 
     from 0 have 1:"(\<lambda>t. state2vec((\<lambda>_. 0)(X := t))) 1 = (\<lambda>t. state2vec(p2 t)) 1"
       using step4[of "1"] step7[of "1"] cond(1) by auto
     from 1 have 2:"((\<lambda>_. 0)(X := 1)) = p2 1"
       unfolding state2vec_def by auto
     have 3:"p2 1 X < 1" using cond 0 by auto
     have 4:"p2 1 X = 1" using 2 unfolding fun_upd_def
       by (metis "2" fun_upd_same)
     show "False" using 3 and 4 by auto
   qed
   have step10: "d2 = 1" using step8 step9 by auto
   have step11: "t\<in>{0..1} \<Longrightarrow> (p2 t) = ((\<lambda>_. 0)(X := t))" for t
     using step4 step7 step10 by (metis vec_state_map1)
   have step12: "restrict p2 {0..d2} = restrict (\<lambda>t. ((\<lambda>_. 0)(X := t))) {0..1}"
     using step10 step11 unfolding restrict_def by auto
    show ?thesis using step10 step12 by auto
  qed
  show ?thesis
    apply(rule Valid_ode_solution2[where d=1 and p="\<lambda>t. (\<lambda>_. 0)(X := t)"])
    using main by auto
qed

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
    (\<lambda>tr. tr = Trace (\<lambda>_. 0) [])
    (Rep (Cm (Receive ''ch'' X); Cm (Send ''ch'' (\<lambda>s. s X - 1))))
    (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (right_blocks dlyvs))"
proof -
  have 1: "Valid
     (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (right_blocks dlyvs))
     (Cm (''ch''[?]X))
     (\<lambda>tr. \<exists>dlyvs dly1 v. tr = Trace (\<lambda>_. 0) (right_blocks dlyvs @ [InBlock dly1 ''ch'' X v ({}, {''ch''})]))"
    apply (subst Valid_ex_pre)
    apply auto
    apply (rule Valid_receive2)
    by (auto simp add: extend_receive_def)
  have 2: "Valid
     (\<lambda>tr. \<exists>dlyvs dly1 v. tr = Trace (\<lambda>_. 0) (right_blocks dlyvs @ [InBlock dly1 ''ch'' X v ({}, {''ch''})]))
     (Cm (''ch''[!](\<lambda>s. s X - 1)))
     (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (right_blocks dlyvs))"
    apply (simp only: Valid_ex_pre)
    apply auto
    apply (rule Valid_send2)
    apply (auto simp add: extend_send_def end_of_right_blocks_zero)
    subgoal for dlyvs dly1 v dly2
      apply (rule exI[where x="dlyvs @ [(dly1, v, dly2)]"])
      by (auto simp add: right_blocks_snoc)
    done
  have 3: "Valid
    (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (right_blocks dlyvs))
    (Rep (Cm (Receive ''ch'' X); Cm (Send ''ch'' (\<lambda>s. s X - 1))))
    (\<lambda>tr. \<exists>dlyvs. tr = Trace (\<lambda>_. 0) (right_blocks dlyvs))"
    apply (rule Valid_rep)
    apply (rule Valid_seq[where Q="\<lambda>tr. \<exists>dlyvs dly1 v. tr = Trace (\<lambda>_. 0) (right_blocks dlyvs @ [InBlock dly1 ''ch'' X v ({}, {''ch''})])"])
    using 1 2 by auto
  show ?thesis
    apply (rule Valid_pre[OF _ 3])
    apply auto
    apply (rule exI[where x="[]"])
    by auto
qed

lemma testHL13:
  "ParValid
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [])
    (PProc [(Cont (ODE {X} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
             Cm (Send ''ch'' (\<lambda>s. s X));
             Cm (Receive ''ch'' X)),
            (Cm (Receive ''ch'' X);
             Cm (Send ''ch'' (\<lambda>s. s X - 1)))] )
    (\<lambda>t. t = ParTrace [(\<lambda>_. 0), (\<lambda>_. 0)] [ParWaitBlock 1, IOBlock 1 0 ''ch'' 1 , IOBlock 0 1 ''ch'' 0])"
proof-
  have 1: "Valid (\<lambda>t. t = Trace (\<lambda>_. 0) [])
             (Cm (Receive ''ch'' X);
              Cm (Send ''ch'' (\<lambda>s. s X - 1)))
           (\<lambda>t. \<exists>dly1 v dly2. t = Trace (\<lambda>_. 0) [InBlock dly1 ''ch'' X v ({}, {''ch''}),
                                                 OutBlock dly2 ''ch'' (v - 1) ({''ch''}, {})])"
    apply (rule Valid_seq)
     apply (rule Valid_receive)
    apply (simp only: Valid_ex_pre)
    apply auto
    subgoal for dly v
      apply (rule Valid_send2)
      by (auto simp add: extend_send_def extend_receive_def)


end
