theory BigStepParallel
  imports BigStepSequential
begin

subsection \<open>States for parallel programs\<close>

text \<open>Merge of two states.
  For each process name, first look up in the left state, if not
  found look up in the right state. This is ''well-behaved'' only
  if the states on the two sides have disjoint domains, an assumption
  we will need to use frequently.
\<close>
definition merge_state :: "'a gstate \<Rightarrow> 'a gstate \<Rightarrow> 'a gstate" where
  "merge_state ps1 ps2 = (\<lambda>p. case ps1 p of None \<Rightarrow> ps2 p | Some s \<Rightarrow> Some s)"

definition restrict_state :: "pname set \<Rightarrow> 'a gstate \<Rightarrow> 'a gstate" where
  "restrict_state pns gs = (\<lambda>pn. if pn \<in> pns then gs pn else None)"

text \<open>Set of processes in a parallel state.\<close>
definition proc_set :: "'a gstate \<Rightarrow> pname set" where
  "proc_set gs = {pn. gs pn \<noteq> None}"

lemma proc_set_State [simp]:
  "proc_set (State pn s) = {pn}"
  by (auto simp add: proc_set_def State_def)

lemma proc_set_merge [simp]:
  "proc_set (merge_state s1 s2) = proc_set s1 \<union> proc_set s2"
  apply (auto simp add: proc_set_def merge_state_def)
  subgoal for x y apply (cases "s1 x") by auto
  done

lemma proc_set_restrict_state:
  assumes "pns1 \<subseteq> proc_set s"
  shows "proc_set (restrict_state pns1 s) = pns1"
  using assms unfolding restrict_state_def proc_set_def by auto

text \<open>Updating the global state: real part\<close>
definition updg :: "'a gstate \<Rightarrow> pname \<Rightarrow> var \<Rightarrow> real \<Rightarrow> 'a gstate" where
  "updg gs pn x v = gs (pn \<mapsto> upd (the (gs pn)) x v)"

text \<open>Updating the global state: extra part\<close>
definition updeg :: "'a gstate \<Rightarrow> pname \<Rightarrow> 'a \<Rightarrow> 'a gstate" where
  "updeg gs pn e = gs (pn \<mapsto> upde (the (gs pn)) e)"

lemma updg_proc_set [simp]:
  assumes "pn \<in> proc_set gs"
  shows "proc_set (updg gs pn var e) = proc_set gs"
  using assms by (auto simp add: updg_def proc_set_def)

lemma updeg_proc_set [simp]:
  assumes "pn \<in> proc_set gs"
  shows "proc_set (updeg gs pn f) = proc_set gs"
  using assms by (auto simp add: updeg_def proc_set_def)

text \<open>Access functions on global state\<close>

definition valg :: "'a gstate \<Rightarrow> pname \<Rightarrow> var \<Rightarrow> real" where
  "valg gs pn v = val (the (gs pn)) v"

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

definition epartg :: "'a gstate \<Rightarrow> pname \<Rightarrow> 'a" where
  "epartg gs pn = epart (the (gs pn))"

lemma epartg_upd_simp [simp]:
  "epartg (updg s pn var v) pn2 = epartg s pn2"
  unfolding epartg_def updg_def by auto

lemma epartg_updeg_simp [simp]:
  "epartg (updeg s pn e) pn = e"
  unfolding epartg_def updeg_def by auto

lemma epartg_updeg_simp2 [simp]:
  "pn \<noteq> pn2 \<Longrightarrow> epartg (updeg s pn e) pn2 = epartg s pn2"
  unfolding epartg_def updeg_def by auto

text \<open>Some lemmas about updating a single state\<close>
lemma subst_State:
  "State pn s(pn \<mapsto> s') = State pn s'"
  by (auto simp add: State_def)

lemma subst_State_elim:
  "s0 pn = Some s0' \<Longrightarrow> s0(pn \<mapsto> s1') = State pn s2' \<Longrightarrow> s0 = State pn s0'"
  apply (auto simp add: State_def fun_upd_def) by metis

text \<open>A state whose proc_set is singleton\<close>
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

text \<open>Some lemmas about merge of two states\<close>

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

lemma restrict_state_merge1:
  assumes "proc_set gs1 = pns1"
  shows "restrict_state pns1 (merge_state gs1 gs2) = gs1"
  apply (rule ext) subgoal for pn
    unfolding restrict_state_def apply auto
     apply (subst merge_state_eval1) using assms apply auto
    unfolding proc_set_def by auto
  done

lemma restrict_state_merge2:
  assumes "proc_set gs1 = pns1"
    and "proc_set gs2 = pns2"
    and "pns1 \<inter> pns2 = {}"
  shows "restrict_state pns2 (merge_state gs1 gs2) = gs2"
  apply (rule ext) subgoal for pn
    unfolding restrict_state_def apply auto
     apply (subst merge_state_eval2) using assms apply auto
    unfolding proc_set_def by auto
  done

lemma merge_restrict:
  assumes "proc_set s = pns1 \<union> pns2"
    and "pns1 \<inter> pns2 = {}"
  shows "merge_state (restrict_state pns1 s) (restrict_state pns2 s) = s"
  unfolding merge_state_def restrict_state_def
  apply (rule ext) apply auto
  using assms(1,2) unfolding proc_set_def apply auto
  subgoal for p apply (cases "s p") by auto
  subgoal for p apply (cases "s p") by auto
  done

lemma merge_state_elim:
  assumes "proc_set s = pns1 \<union> pns2"
    and "pns1 \<inter> pns2 = {}"
    and "\<And>s1 s2. s = merge_state s1 s2 \<Longrightarrow> proc_set s1 = pns1 \<Longrightarrow> proc_set s2 = pns2 \<Longrightarrow> P"
  shows P
  apply (rule assms(3)[of "restrict_state pns1 s" "restrict_state pns2 s"])
  by (auto simp add: merge_restrict proc_set_restrict_state assms)  

lemma valg_merge_state_left:
  assumes "pn \<in> proc_set s1"
  shows "valg (merge_state s1 s2) pn v = valg s1 pn v"
  using assms by (auto simp add: proc_set_def merge_state_def valg_def)

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

subsection \<open>Semantics of parallel processes\<close>

text \<open>Whether two ready info from different processes are compatible\<close>
fun compat_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

lemma compat_rdy_empty [simp]:
  "compat_rdy rdy ({}, {})"
  apply (cases rdy) by auto

text \<open>Merge two ready info, common channels are removed\<close>
fun merge_rdy :: "cname set \<Rightarrow> rdy_info \<Rightarrow> rdy_info \<Rightarrow> rdy_info" where
  "merge_rdy chs (r11, r12) (r21, r22) = (r11 \<union> r21 - chs, r12 \<union> r22 - chs)"

text \<open>Trace blocks for a parallel process.
  The only difference from trace blocks for a single process is that
  the waiting blocks record states for parallel processes.
\<close>
datatype 'a ptrace_block = 
  CommBlockP comm_type cname real
| WaitBlockP real "real \<Rightarrow> 'a gstate" rdy_info

abbreviation "InBlockP ch v \<equiv> CommBlockP In ch v"
abbreviation "OutBlockP ch v \<equiv> CommBlockP Out ch v"

definition WaitBlkP :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> 'a ptrace_block" where
  "WaitBlkP d p rdy = WaitBlockP d (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"

lemma WaitBlkP_eqE:
  "WaitBlkP d p rdy = WaitBlkP d2 p2 rdy2 \<Longrightarrow>
   (d = d2 \<Longrightarrow> rdy = rdy2 \<Longrightarrow> (\<And>t. t \<in> {0..d} \<Longrightarrow> p t = p2 t) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding WaitBlkP_def restrict_def apply auto by meson

lemma WaitBlkP_eqI:
  "d = d2 \<Longrightarrow> rdy = rdy2 \<Longrightarrow> (\<And>t. t \<in> {0..d} \<Longrightarrow> p t = p2 t) \<Longrightarrow>
   WaitBlkP d p rdy = WaitBlkP d2 p2 rdy2"
  unfolding WaitBlkP_def by auto

lemma WaitBlk_distinct [simp]:
  "WaitBlkP d p rdy \<noteq> CommBlockP ctype ch v"
  "CommBlockP ctype ch v \<noteq> WaitBlkP d p rdy"
  unfolding WaitBlkP_def by auto

text \<open>Trace for parallel process consists of a list of trace blocks.\<close>
type_synonym 'a ptrace = "'a ptrace_block list"

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
   rdy = merge_rdy comms rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlkP t (\<lambda>\<tau>. hist1 \<tau>) rdy1 # blks1)
                        (WaitBlkP t (\<lambda>\<tau>. hist2 \<tau>) rdy2 # blks2)
                        (WaitBlkP t (\<lambda>\<tau>. hist \<tau>) rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlkP (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow> t1 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. merge_state (hist1 \<tau>) (hist2 \<tau>)) \<Longrightarrow>
   rdy = merge_rdy comms rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlkP t1 (\<lambda>\<tau>. hist1 \<tau>) rdy1 # blks1)
                        (WaitBlkP t2 (\<lambda>\<tau>. hist2 \<tau>) rdy2 # blks2)
                        (WaitBlkP t1 (\<lambda>\<tau>. hist \<tau>) rdy # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlkP (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow> t2 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. merge_state (hist1 \<tau>) (hist2 \<tau>)) \<Longrightarrow>
   rdy = merge_rdy comms rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlkP t1 (\<lambda>\<tau>. hist1 \<tau>) rdy1 # blks1)
                        (WaitBlkP t2 (\<lambda>\<tau>. hist2 \<tau>) rdy2 # blks2)
                        (WaitBlkP t2 (\<lambda>\<tau>. hist \<tau>) rdy # blks)"

text \<open>Conversion from trace for a single process to trace for
  parallel processes.
\<close>
inductive ptrace_of :: "pname \<Rightarrow> 'a trace \<Rightarrow> 'a ptrace \<Rightarrow> bool" where
  "ptrace_of pn [] []"
| "ptrace_of pn tr tr' \<Longrightarrow> ptrace_of pn (CommBlock ch_type ch v # tr) (CommBlockP ch_type ch v # tr')"
| "ptrace_of pn tr tr' \<Longrightarrow> WaitBlkP d p' rdy = WaitBlkP d (\<lambda>\<tau>. State pn (p \<tau>)) rdy \<Longrightarrow>
   ptrace_of pn (WaitBlk d p rdy # tr) (WaitBlkP d p' rdy # tr')"

inductive_cases ptrace_of_emptyE: "ptrace_of pn [] tr"
inductive_cases ptrace_of_emptyE2: "ptrace_of pn tr []"
inductive_cases ptrace_of_commE2: "ptrace_of pn tr (CommBlockP ch_type ch v # tr')"
inductive_cases ptrace_of_waitE2: "ptrace_of pn tr (WaitBlkP d p' rdy # tr')"

lemma ptrace_of_commE:
  "ptrace_of pn (CommBlock ch_type ch v # tr') tr \<Longrightarrow>
   (\<And>tr''. tr = CommBlockP ch_type ch v # tr'' \<Longrightarrow> ptrace_of pn tr' tr'' \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases rule: ptrace_of.cases)
  by (auto simp add: WaitBlk_def)

lemma ptrace_of_waitE:
  "ptrace_of pn (WaitBlk d p rdy # tr') tr \<Longrightarrow>
  (\<And>tr''. tr = WaitBlkP d (\<lambda>\<tau>. State pn (p \<tau>)) rdy # tr'' \<Longrightarrow> ptrace_of pn tr' tr'' \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases rule: ptrace_of.cases)
     apply (auto simp add: WaitBlk_def)
  by (smt (verit, best) WaitBlkP_def WaitBlk_def WaitBlk_eqE restrict_ext)

text \<open>Definition of big-step operational semantics for parallel processes.
  Note the restriction on disjoint condition for process names,
  as needed for good behavior of merge_state.
\<close>
inductive par_big_step :: "'a pproc \<Rightarrow> 'a gstate \<Rightarrow> 'a ptrace \<Rightarrow> 'a gstate \<Rightarrow> bool" where
  SingleB:
    "big_step p s1 tr s2 \<Longrightarrow>
     ptrace_of pn tr tr' \<Longrightarrow>
     par_big_step (Single pn p) (State pn s1) tr' (State pn s2)"
| ParallelB:
    "par_big_step p1 s11 tr1 s12 \<Longrightarrow>
     par_big_step p2 s21 tr2 s22 \<Longrightarrow>
     proc_of_pproc p1 \<inter> proc_of_pproc p2 = {} \<Longrightarrow>
     combine_blocks chs tr1 tr2 tr \<Longrightarrow>
     par_big_step (Parallel p1 chs p2) (merge_state s11 s21) tr (merge_state s12 s22)"

inductive_cases SingleE: "par_big_step (Single pn p) s1 tr s2"
inductive_cases ParallelE: "par_big_step (Parallel p1 ch p2) s1 tr s2"

lemma proc_set_big_step:
  "par_big_step p s1 tr s2 \<Longrightarrow> proc_set s1 = proc_of_pproc p \<and> proc_set s2 = proc_of_pproc p"
  apply (induction rule: par_big_step.induct) by auto

text \<open>Trace is compatible with a given set of procedure names\<close>
inductive proc_set_trace :: "pname set \<Rightarrow> 'a ptrace \<Rightarrow> bool" where
  "proc_set_trace pns []"
| "proc_set_trace pns tr \<Longrightarrow> proc_set_trace pns (CommBlockP ctype ch v # tr)"
| "proc_set_trace pns tr \<Longrightarrow> \<forall>t\<in>{0..d}. proc_set (p t) = pns \<Longrightarrow>
   proc_set_trace pns (WaitBlkP d (\<lambda>\<tau>. p \<tau>) rdy # tr)"

lemma proc_set_trace_tl:
  "proc_set_trace pns (blk # tr) \<Longrightarrow> proc_set_trace pns tr"
  by (induct rule: proc_set_trace.cases, auto)

lemma proc_set_trace_wait:
  "proc_set_trace pns (WaitBlkP d (\<lambda>\<tau>. p \<tau>) rdy # tr) \<Longrightarrow> t \<in> {0..d} \<Longrightarrow> proc_set (p t) = pns"
  apply (induct rule: proc_set_trace.cases, auto)
  by (elim WaitBlkP_eqE, auto)+

text \<open>Action of proc_set on synchronization of traces\<close>
lemma proc_set_trace_combine:
  "combine_blocks chs tr1 tr2 tr \<Longrightarrow>
   proc_set_trace pns1 tr1 \<Longrightarrow> proc_set_trace pns2 tr2 \<Longrightarrow> pns1 \<union> pns2 = pns \<Longrightarrow>
   proc_set_trace pns tr"
proof (induction rule: combine_blocks.induct)
  case (combine_blocks_empty comms)
  then show ?case
    by (auto intro: proc_set_trace.intros)
next
  case (combine_blocks_pair1 ch comms blks1 blks2 blks v)
  then show ?case
    using proc_set_trace_tl by auto
next
  case (combine_blocks_pair2 ch comms blks1 blks2 blks v)
  then show ?case
    using proc_set_trace_tl by auto
next
  case (combine_blocks_unpair1 ch comms blks1 blks2 blks ch_type v)
  show ?case
    apply (rule proc_set_trace.intros(2))
    using combine_blocks_unpair1 proc_set_trace_tl by auto
next
  case (combine_blocks_unpair2 ch comms blks1 blks2 blks ch_type v)
  show ?case
    apply (rule proc_set_trace.intros(2))
    using combine_blocks_unpair2 proc_set_trace_tl by auto
next
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  show ?case
    apply (rule proc_set_trace.intros(3))
    subgoal using combine_blocks_wait1 proc_set_trace_tl by auto
    using combine_blocks_wait1 proc_set_merge proc_set_trace_wait by blast
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  show ?case
    apply (rule proc_set_trace.intros(3))
    subgoal apply (rule combine_blocks_wait2(7))
      subgoal using combine_blocks_wait2 proc_set_trace_tl by auto
      apply (rule proc_set_trace.intros(3))
      using combine_blocks_wait2 proc_set_trace_tl apply auto[1]
      using proc_set_trace_wait[OF combine_blocks_wait2(9)]
      using combine_blocks_wait2 by auto
    using combine_blocks_wait2(3,4,5) proc_set_merge proc_set_trace_wait[OF combine_blocks_wait2(8)]
      proc_set_trace_wait[OF combine_blocks_wait2(9)] combine_blocks_wait2 by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  show ?case
    apply (rule proc_set_trace.intros(3))
    subgoal apply (rule combine_blocks_wait3(7))
        apply (rule proc_set_trace.intros(3))
      using combine_blocks_wait3 proc_set_trace_tl apply auto[1]
      using proc_set_trace_wait[OF combine_blocks_wait3(8)]
      using combine_blocks_wait3 apply auto[1]
      subgoal using combine_blocks_wait3 proc_set_trace_tl by auto
      using combine_blocks_wait3 by auto
    using combine_blocks_wait3(3,4,5) proc_set_merge proc_set_trace_wait[OF combine_blocks_wait3(8)]
      proc_set_trace_wait[OF combine_blocks_wait3(9)] combine_blocks_wait3 by auto
qed

text \<open>The following two lemmas show that a parallel trace is compatible
  with a single procedure name if and only if it satisfies ptrace_of
  for some sequential trace..
\<close>
lemma proc_set_trace_single:
  "ptrace_of pn tr tr' \<Longrightarrow> proc_set_trace {pn} tr'"
  by (induction rule: ptrace_of.induct, auto intro: proc_set_trace.intros)

lemma proc_set_trace_is_single:
  "proc_set_trace {pn} tr \<Longrightarrow> \<exists>tr'. ptrace_of pn tr' tr"
proof (induction "{pn}" tr rule: proc_set_trace.induct)
  case 1
  show ?case
    apply (rule exI[where x="[]"])
    by (auto intro: ptrace_of.intros)
next
  case (2 tr ctype ch v)
  obtain tr' where tr': "ptrace_of pn tr' tr"
    using 2(2) by auto
  show ?case
    apply (rule exI[where x="CommBlock ctype ch v # tr'"])
    using tr' by (auto intro: ptrace_of.intros)
next
  case (3 tr d p rdy)
  obtain tr' where tr': "ptrace_of pn tr' tr"
    using 3(2) by auto
  have "proc_set (p t) = {pn}" if "t \<in> {0..d}" for t
    using 3(3) that by auto
  then have p': "\<exists>p'. p t = State pn p'" if "t \<in> {0..d}" for t
    by (meson proc_set_single_elim that)
  show ?case
    apply (rule exI[where x="WaitBlk d (\<lambda>\<tau>. SOME p'. p \<tau> = State pn p') rdy # tr'"])
    apply (rule ptrace_of.intros) apply (rule tr') apply (rule WaitBlkP_eqI) apply auto
    subgoal premises pre for t
    proof -
      obtain p' where "p t = State pn p'"
        using p' pre by auto
      then show ?thesis
        apply auto apply (rule someI)
        by auto
    qed
    done
qed

lemma proc_set_trace_single_elim:
  "proc_set_trace {pn} tr \<Longrightarrow> (\<And>tr'. ptrace_of pn tr' tr \<Longrightarrow> P) \<Longrightarrow> P"
  using proc_set_trace_is_single by blast

subsection \<open>Assertions on parallel processes\<close>

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

inductive true_gassn :: "pname set \<Rightarrow> 'a gassn2" where
  "proc_set gs0 = pns \<Longrightarrow> proc_set gs = pns \<Longrightarrow> proc_set_trace pns tr \<Longrightarrow>
   true_gassn pns gs0 gs tr"

definition false_gassn :: "'a gassn2" where
  "false_gassn s0 = (\<lambda>gs tr. False)"

definition init_global :: "'a gstate \<Rightarrow> 'a gs_assn" where
  "init_global s0 = (\<lambda>s. s = s0)"

lemma init_global_parallel:
  "init_global s0 (merge_state s1 s2) \<Longrightarrow>
   (\<And>s01 s02. s0 = merge_state s01 s02 \<Longrightarrow> init_global s01 s1 \<Longrightarrow> init_global s02 s2 \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding init_global_def by auto

inductive sync_gassn :: "cname set \<Rightarrow> pname set \<Rightarrow> pname set \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2" where
  "proc_set s11 = pns1 \<Longrightarrow> proc_set s12 = pns2 \<Longrightarrow>
   proc_set s21 = pns1 \<Longrightarrow> proc_set s22 = pns2 \<Longrightarrow>
   P s11 s21 tr1 \<Longrightarrow> Q s12 s22 tr2 \<Longrightarrow>
   combine_blocks chs tr1 tr2 tr \<Longrightarrow>
   sync_gassn chs pns1 pns2 P Q (merge_state s11 s12) (merge_state s21 s22) tr"

inductive init_single :: "pname set \<Rightarrow> 'a gassn2" where
  "proc_set gs = pns \<Longrightarrow> init_single pns gs gs []"

definition cond_gassn2 :: "pname \<Rightarrow> ('a estate \<Rightarrow> bool) \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2"
  ("IFG [_] _ THEN _ ELSE _ FI" [95,95,94] 93) where
  "IFG [pn] b THEN Q1 ELSE Q2 FI = (\<lambda>s0 s tr. if b (the (s0 pn)) then Q1 s0 s tr else Q2 s0 s tr)"

definition conj_gassn :: "'a gassn2 \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2" (infixr "\<and>\<^sub>g" 35) where
  "(P \<and>\<^sub>g Q) = (\<lambda>s0 s tr. P s0 s tr \<and> Q s0 s tr)"

definition disj_gassn :: "'a gassn2 \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2" (infixr "\<or>\<^sub>g" 35) where
  "(P \<or>\<^sub>g Q) = (\<lambda>s0 s tr. P s0 s tr \<or> Q s0 s tr)"

definition pure_gassn :: "('a gstate \<Rightarrow> bool) \<Rightarrow> pname set \<Rightarrow> 'a gassn2" ("!\<^sub>g[_] at _" [71,71] 70) where
  "(!\<^sub>g[b] at pns) = (\<lambda>s0 s tr. b s0 \<and> proc_set s0 = pns \<and> proc_set s = pns \<and> proc_set_trace pns tr)"

text \<open>Quantifiers on parallel assertions\<close>
definition exists_gassn :: "('b \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" (binder "\<exists>\<^sub>g" 10)where
  "(\<exists>\<^sub>gn. P n) = (\<lambda>s0 s tr. \<exists>n. P n s0 s tr)"

text \<open>Assertion for input\<close>
inductive wait_in_cg :: "cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" where
  "P 0 v s0 s tr \<Longrightarrow> wait_in_cg ch P s0 s (InBlockP ch v # tr)"
| "0 < d \<Longrightarrow> P d v s0 s tr \<Longrightarrow> wait_in_cg ch P s0 s (WaitBlkP d (\<lambda>\<tau>. s0) ({}, {ch}) # InBlockP ch v # tr)"

text \<open>Assertion for output\<close>
inductive wait_out_cg :: "cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" where
  "P 0 v s0 s tr \<Longrightarrow> wait_out_cg ch P s0 s (OutBlockP ch v # tr)"
| "0 < d \<Longrightarrow> P d v s0 s tr \<Longrightarrow>
   wait_out_cg ch P s0 s (WaitBlkP d (\<lambda>\<tau>. s0) ({ch}, {}) # OutBlockP ch v # tr)"

definition wait_out_cgv :: "cname \<Rightarrow> pname set \<Rightarrow> pname \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" where
  "wait_out_cgv ch pns pn e P = wait_out_cg ch (\<lambda>d v. !\<^sub>g[(\<lambda>gs0. v = e (the (gs0 pn)))] at pns \<and>\<^sub>g P d)"

text \<open>Assertion for wait\<close>
inductive wait_cg :: "pname \<Rightarrow> 'a eexp \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2" where
  "e (the (gs0 pn)) > 0 \<Longrightarrow> P gs0 gs tr \<Longrightarrow> d = e (the (gs0 pn)) \<Longrightarrow>
   wait_cg pn e P gs0 gs (WaitBlkP d (\<lambda>\<tau>. gs0) ({}, {}) # tr)"
| "\<not>e (the (gs0 pn)) > 0 \<Longrightarrow> P gs0 gs tr \<Longrightarrow> wait_cg pn e P gs0 gs tr"

text \<open>Action of an assertion on updated state: real part\<close>
definition updg_assn2 :: "'a gassn2 \<Rightarrow> var \<Rightarrow> 'a eexp \<Rightarrow> pname \<Rightarrow> 'a gassn2"
  ("_ {{_ := _}}\<^sub>g at _" [90,90,90,90] 91) where
  "P {{var := e}}\<^sub>g at pn = (\<lambda>ps s tr. ps pn \<noteq> None \<and> P (updg ps pn var (e (the (ps pn)))) s tr)"

text \<open>Action of an assertion on updated state: extra part\<close>
definition updeg_assn2 :: "'a gassn2 \<Rightarrow> ('a estate \<Rightarrow> 'a) \<Rightarrow> pname \<Rightarrow> 'a gassn2"
  ("_ {{_}}\<^sub>g at _" [90,90,90] 91) where
  "P {{f}}\<^sub>g at pn = (\<lambda>ps s tr. ps pn \<noteq> None \<and> P (updeg ps pn (f (the (ps pn)))) s tr)"

text \<open>Another generalization of wait_in_c\<close>
inductive wait_in_cg_alt :: "cname \<Rightarrow> pname \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a gassn2) \<Rightarrow> (real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" where
  "P 0 v s0 s tr \<Longrightarrow> wait_in_cg_alt ch pn e P Q s0 s (InBlockP ch v # tr)"
| "0 < d \<Longrightarrow> d \<le> e (the (s0 pn)) \<Longrightarrow> P d v s0 s tr \<Longrightarrow> wait_in_cg_alt ch pn e P Q s0 s (WaitBlkP d (\<lambda>\<tau>. s0) ({}, {ch}) # InBlockP ch v # tr)"
| "0 < e (the (s0 pn)) \<Longrightarrow> d \<ge> e (the (s0 pn)) \<Longrightarrow> Q d s0 s tr \<Longrightarrow> wait_in_cg_alt ch pn e P Q s0 s (WaitBlkP d (\<lambda>\<tau>. s0) ({}, {ch}) # tr)"
| "\<not>0 < e (the (s0 pn)) \<Longrightarrow> Q 0 s0 s tr \<Longrightarrow> wait_in_cg_alt ch pn e P Q s0 s tr"

text \<open>Version of wait_in_c with assumption of immediate communication\<close>
definition wait_in_c0 :: "cname \<Rightarrow> (real \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2" where
  "wait_in_c0 ch P = wait_in_c ch (\<lambda>d v. IFA (\<lambda>s. d = 0) THEN P v ELSE true_assn2 FI)"

definition wait_in_cg0 :: "pname \<Rightarrow> cname \<Rightarrow> pname set \<Rightarrow> (real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" where
  "wait_in_cg0 pn ch pns P = wait_in_cg ch (\<lambda>d v. IFG [pn] (\<lambda>s. d = 0) THEN P v ELSE true_gassn pns FI)"

subsubsection \<open>Conversion from sequential to parallel assertions\<close>

named_theorems single_assn_simps

inductive single_assn :: "pname \<Rightarrow> 'a assn2 \<Rightarrow> 'a gassn2" where
  "Q s s' tr \<Longrightarrow> ptrace_of pn tr tr' \<Longrightarrow> single_assn pn Q (State pn s) (State pn s') tr'"

lemma single_assn_true [single_assn_simps]:
  "single_assn pn true_assn2 = true_gassn {pn}"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases)
      apply auto apply (rule true_gassn.intros)
      using proc_set_trace_single by auto
    subgoal apply (elim true_gassn.cases)
      apply clarify
      apply (elim proc_set_single_elim)
      apply auto
      by (metis proc_set_trace_is_single single_assn.intros true_assn2.intros)
    done
  done

lemma single_assn_false [single_assn_simps]:
  "single_assn pn false_assn2 = false_gassn"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases)
      unfolding false_assn2_def by auto
    subgoal unfolding false_gassn_def by auto
    done
  done

lemma single_assn_exists [single_assn_simps]:
  "single_assn pn (\<exists>\<^sub>an. P n) = (\<exists>\<^sub>gn. single_assn pn (P n))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s tr s0
    apply (rule iffI)
    apply (auto simp add: exists_gassn_def exists_assn_def)
      by (auto elim: single_assn.cases intro: single_assn.intros)
    done

lemma single_assn_disj [single_assn_simps]:
  "single_assn pn (P \<or>\<^sub>a Q) = (single_assn pn P \<or>\<^sub>g single_assn pn Q)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0' s' tr'
        unfolding disj_gassn_def disj_assn_def
        by (auto intro: single_assn.intros)
      done
    subgoal unfolding disj_gassn_def disj_assn_def
      apply (elim disjE single_assn.cases)
      by (auto intro: single_assn.intros)
    done
  done

lemma single_assn_wait_in [single_assn_simps]:
  "single_assn pn (wait_in_c ch1 P) = wait_in_cg ch1 (\<lambda>d v. single_assn pn (P d v))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0' s' tr'
        apply (elim wait_in_c.cases) apply auto
         apply (elim ptrace_of_commE) apply auto
         apply (intro wait_in_cg.intros single_assn.intros) apply auto
        apply (elim ptrace_of_waitE ptrace_of_commE) apply auto
        apply (intro wait_in_cg.intros single_assn.intros) by auto
      done
    subgoal apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr'
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (rule single_assn.intros)
           apply (rule wait_in_c.intros(1))
          by (auto intro: ptrace_of.intros)
        done
      subgoal for d v tr'
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (rule single_assn.intros)
           apply (rule wait_in_c.intros(2))
          by (auto intro: ptrace_of.intros)
        done
      done
    done
  done

lemma single_assn_wait_out [single_assn_simps]:
  "single_assn pn (wait_out_c ch1 P) = wait_out_cg ch1 (\<lambda>d v. single_assn pn (P d v))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      apply (elim wait_out_c.cases) apply auto
      subgoal for v s0' s' tr'
        apply (elim ptrace_of_commE) apply auto
        apply (rule wait_out_cg.intros(1))
         apply (rule single_assn.intros)
        by (auto simp add: State_def)
      subgoal for d s0' s' tr'
        apply (elim ptrace_of_commE ptrace_of_waitE) apply auto
        apply (rule wait_out_cg.intros(2)) apply simp
         apply (rule single_assn.intros)
        by (auto simp add: State_def)
      done
    subgoal apply (elim wait_out_cg.cases) apply auto
      subgoal for tr'
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (rule single_assn.intros)
           apply (simp add: State_def)
           apply (rule wait_out_c.intros)
          by (auto intro: ptrace_of.intros)
        done
      subgoal for d tr'
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (rule single_assn.intros)
          apply (simp add: State_def)
           apply (rule wait_out_c.intros(2))
          by (auto intro: ptrace_of.intros)
        done
      done
    done
  done

lemma State_inj:
  "State pn s = State pn s' \<Longrightarrow> s = s'"
  unfolding State_def by (metis option.sel)

lemma ptrace_inj:
  "ptrace_of pn tr1 tr' \<Longrightarrow> ptrace_of pn tr2 tr' \<Longrightarrow> tr1 = tr2"
proof (induction arbitrary: tr2 rule: ptrace_of.induct)
  case (1 pn)
  then show ?case
    by (auto elim: ptrace_of_emptyE2)
next
  case (2 pn tr tr' ch_type ch v)
  then show ?case
    apply (elim ptrace_of_commE2) by auto
next
  case (3 pn tr tr' d p' rdy p)
  then show ?case
    apply (elim ptrace_of_waitE2) apply auto
    apply (elim WaitBlkP_eqE) apply auto
    apply (rule WaitBlk_eqI) apply auto
    by (metis State_inj)
qed

lemma single_assn_pure [single_assn_simps]:
  "single_assn pn (!\<^sub>a[b]) = !\<^sub>g[(\<lambda>gs0. b (the (gs0 pn)))] at {pn}"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for gs0 gs tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      unfolding pure_assn_def pure_gassn_def conj_gassn_def apply auto
      by (simp add: proc_set_trace_single)
    subgoal unfolding pure_gassn_def pure_assn_def conj_gassn_def
      apply clarify
      apply (elim proc_set_single_elim proc_set_trace_single_elim)
      by (auto intro: single_assn.intros)
    done
  done

lemma single_assn_conj [single_assn_simps]:
  "single_assn pn (P \<and>\<^sub>a Q) = (single_assn pn P \<and>\<^sub>g single_assn pn Q)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for gs0 gs tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      unfolding conj_assn_def conj_gassn_def
      by (auto intro: single_assn.intros)
    subgoal unfolding conj_assn_def conj_gassn_def apply auto
      apply (elim single_assn.cases) apply auto
      apply (rule single_assn.intros) apply auto
      using State_inj ptrace_inj by metis
    done
  done

lemma conj_gassn_assoc:
  "((P \<and>\<^sub>g Q) \<and>\<^sub>g R) = (P \<and>\<^sub>g (Q \<and>\<^sub>g R))"
  apply (rule ext) apply (rule ext)
  unfolding conj_gassn_def by auto

lemma single_assn_wait_out_v [single_assn_simps]:
  "single_assn pn (wait_out_cv ch1 e P) = wait_out_cgv ch1 {pn} pn e (\<lambda>d. single_assn pn (P d))"
  unfolding wait_out_cgv_def wait_out_cv_def single_assn_wait_out
  by (simp only: single_assn_simps conj_gassn_assoc)

lemma single_assn_wait [single_assn_simps]:
  "single_assn pn (wait_c e P) = wait_cg pn e (single_assn pn P)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for gs0 gs tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0 s tr'
        apply (cases "e s0 > 0")
        subgoal premises pre
        proof -
          have es0: "e s0 = e (the ((State pn s0) pn))"
            by auto
          then show ?thesis
            using pre apply (elim wait_c.cases) apply auto[2]
            apply (elim ptrace_of_waitE)
            apply auto apply (rule wait_cg.intros(1))
            by (auto intro: single_assn.intros)
        qed
        subgoal premises pre
        proof -
          have es0: "e s0 = e (the ((State pn s0) pn))"
            by auto
          then show ?thesis
            using pre apply (elim wait_c.cases) apply auto[1]
            apply (rule wait_cg.intros(2))
            by (auto intro: single_assn.intros)
        qed
        done
      done
    subgoal apply (elim wait_cg.cases) apply auto
      subgoal for tr'
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (rule single_assn.intros)
           apply (rule wait_c.intros)
          by (auto intro: ptrace_of.intros)
        done
      subgoal
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (rule single_assn.intros)
           apply (rule wait_c.intros(2))
          by (auto intro: ptrace_of.intros)
        done
      done
    done
  done

lemma single_assn_subst [single_assn_simps]:
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
          using pre apply auto
          by (metis State_eval map_upd_Some_unfold)
      qed
      done
    done
  done

lemma single_assn_subste [single_assn_simps]:
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
          using pre apply auto
          by (metis (full_types) State_eval fun_upd_same option.sel subste_assn2_def)
      qed
      done
    done
  done

lemma single_assn_init [single_assn_simps]:
  "single_assn pn init = init_single {pn}"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases)
      apply (auto simp add: init_def)
      apply (elim ptrace_of_emptyE) apply auto
      apply (rule init_single.intros) by auto
    subgoal
      apply (elim init_single.cases) apply clarify
      apply (elim proc_set_single_elim) apply auto
      apply (rule single_assn.intros)
       apply (auto simp add: init_def)
      by (auto intro: ptrace_of.intros)
    done
  done

lemma single_assn_cond [single_assn_simps]:
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

lemma single_assn_wait_in0 [single_assn_simps]:
  "single_assn pn (wait_in_c0 ch P) = wait_in_cg0 pn ch {pn} (\<lambda>v. single_assn pn (P v))"
  unfolding wait_in_c0_def wait_in_cg0_def
  apply (subst single_assn_wait_in)
  unfolding single_assn_cond single_assn_true by auto

subsubsection \<open>Set of procedure names for an assertion\<close>

text \<open>An assertion is compatible with a set of procedure names,
  if it holds only on those traces whose proc_set is exactly
  that set.
\<close>
definition proc_set_gassn :: "pname set \<Rightarrow> 'a gassn2 \<Rightarrow> bool" where
  "proc_set_gassn pns P \<longleftrightarrow>
    (\<forall>gs0 gs tr. P gs0 gs tr \<longrightarrow> proc_set gs0 = pns \<and> proc_set gs = pns \<and> proc_set_trace pns tr)"

lemma proc_set_sync_gassn [intro]:
  assumes "proc_set_gassn pns1 P"
    and "proc_set_gassn pns2 Q"
    and "pns1 \<union> pns2 = pns"
  shows "proc_set_gassn pns (sync_gassn chs pns1 pns2 P Q)"
  unfolding proc_set_gassn_def apply clarify
  apply (elim sync_gassn.cases) apply clarify
  apply simp
  subgoal for s11 s12 s21 s22 tr1 tr2 tr'
    apply (rule conjI) using assms apply auto[1]
    apply (rule proc_set_trace_combine[of chs tr1 tr2 _ pns1 pns2])
       apply auto[1] using assms(1)[unfolded proc_set_gassn_def] apply blast
    using assms(2)[unfolded proc_set_gassn_def] apply blast
    using assms(3) by auto
  done

lemma proc_set_single_gassn [intro]:
  "proc_set_gassn {pn} (single_assn pn P)"
  unfolding proc_set_gassn_def apply clarify
  apply (elim single_assn.cases) apply auto
  by (simp add: proc_set_trace_single)

lemma proc_set_wait_in_cg [intro!]:
  assumes "\<And>d v. proc_set_gassn pns (P d v)"
  shows "proc_set_gassn pns (wait_in_cg ch P)"
  unfolding proc_set_gassn_def apply clarify
  subgoal for gs0 gs tr
    apply (elim wait_in_cg.cases) apply clarify
    subgoal for _ v s0 s tr' ch'
      using assms[of 0 v] unfolding proc_set_gassn_def apply auto
      apply (rule proc_set_trace.intros) by blast
    subgoal for d P' v s0 s tr' ch'
      using assms[of d v] unfolding proc_set_gassn_def apply auto
      apply (rule proc_set_trace.intros) apply auto
      apply (rule proc_set_trace.intros) by blast
    done
  done

lemma proc_set_wait_out_cg [intro!]:
  assumes "\<And>d v. proc_set_gassn pns (P d v)"
  shows "proc_set_gassn pns (wait_out_cg ch P)"
  unfolding proc_set_gassn_def apply clarify
  subgoal for gs0 gs tr
    apply (elim wait_out_cg.cases) apply clarify
    subgoal
      using assms[of 0] unfolding proc_set_gassn_def apply auto
      apply (rule proc_set_trace.intros) by blast
    subgoal for d
      using assms[of d] unfolding proc_set_gassn_def apply auto
      apply (rule proc_set_trace.intros) apply auto
      apply (rule proc_set_trace.intros) by blast
    done
  done

lemma proc_set_wait_cg [intro!]:
  assumes "proc_set_gassn pns P"
  shows "proc_set_gassn pns (wait_cg pn e P)"
  unfolding proc_set_gassn_def apply clarify
  subgoal for gs0 gs tr
    apply (elim wait_cg.cases) apply clarify
    using assms unfolding proc_set_gassn_def apply auto
    apply (rule proc_set_trace.intros) by auto
  done

lemma proc_set_cond_gassn [intro!]:
  assumes "proc_set_gassn pns P"
    and "proc_set_gassn pns Q"
  shows "proc_set_gassn pns (IFG [pn] b THEN P ELSE Q FI)"
  unfolding proc_set_gassn_def apply clarify
  subgoal for gs0 gs tr
    unfolding cond_gassn2_def
    apply (cases "b (the (gs0 pn))")
    subgoal using assms(1) unfolding proc_set_gassn_def by auto
    subgoal using assms(2) unfolding proc_set_gassn_def by auto
    done
  done

lemma proc_set_true_gassn [intro]:
  "proc_set_gassn pns (true_gassn pns)"
  unfolding proc_set_gassn_def apply clarify
  apply (elim true_gassn.cases) by auto

lemma proc_set_updg_subst [intro!]:
  assumes "proc_set_gassn pns P"
    and "pn \<in> pns"
  shows "proc_set_gassn pns (P {{ x := v }}\<^sub>g at pn)"
  unfolding proc_set_gassn_def apply clarify
  unfolding updg_assn2_def using assms unfolding proc_set_gassn_def
  by (metis (mono_tags, lifting) mem_Collect_eq proc_set_def updg_proc_set)

lemma proc_set_init_single [intro]:
  "proc_set_gassn pn (init_single pn)"
  unfolding proc_set_gassn_def apply clarify
  subgoal for gs0 gs tr
    apply (induct rule: init_single.induct)
    by (auto intro: proc_set_trace.intros)
  done

lemma proc_set_conj [intro!]:
  assumes "proc_set_gassn pn P"
    and "proc_set_gassn pn Q"
  shows "proc_set_gassn pn (P \<and>\<^sub>g Q)"
  unfolding proc_set_gassn_def apply clarify
  using assms unfolding proc_set_gassn_def conj_gassn_def by auto

lemma proc_set_disj [intro!]:
  assumes "proc_set_gassn pn P"
    and "proc_set_gassn pn Q"
  shows "proc_set_gassn pn (P \<or>\<^sub>g Q)"
  unfolding proc_set_gassn_def apply clarify
  using assms unfolding proc_set_gassn_def disj_gassn_def by auto

lemma proc_set_pure [intro]:
  "proc_set_gassn pn (!\<^sub>g[b] at pn)"
  unfolding proc_set_gassn_def pure_gassn_def by auto

lemma proc_set_wait_out_cgv [intro!]:
  assumes "\<And>d. proc_set_gassn pns (P d)"
  shows "proc_set_gassn pns (wait_out_cgv ch pns pn e P)"
  unfolding wait_out_cgv_def using assms by auto

subsubsection \<open>Entailments on parallel assertions\<close>

lemma pure_gassn_intro:
  assumes "b s0" and "proc_set_gassn pns P"
  shows "P s0 \<Longrightarrow>\<^sub>g (!\<^sub>g[b] at pns) s0"
  unfolding entails_g_def pure_gassn_def
  using assms unfolding proc_set_gassn_def by auto

lemma conj_gassn_intro:
  assumes "P s0 \<Longrightarrow>\<^sub>g Q s0" "P s0 \<Longrightarrow>\<^sub>g R s0"
  shows "P s0 \<Longrightarrow>\<^sub>g (Q \<and>\<^sub>g R) s0"
  using assms unfolding conj_gassn_def entails_g_def by auto

lemma exists_gassn_elim:
  assumes "\<And>n. P n s0 \<Longrightarrow>\<^sub>g Q s0"
  shows "(\<exists>\<^sub>gn. P n) s0 \<Longrightarrow>\<^sub>g Q s0"
  using assms unfolding exists_gassn_def entails_g_def by auto

lemma conj_pure_gassn_elim:
  assumes "b s0 \<Longrightarrow> proc_set s0 = pn \<Longrightarrow> P s0 \<Longrightarrow>\<^sub>g Q s0"
  shows "(!\<^sub>g[b] at pn \<and>\<^sub>g P) s0 \<Longrightarrow>\<^sub>g Q s0"
  using assms unfolding entails_g_def conj_gassn_def pure_gassn_def
  by auto

lemma entails_g_disj:
  assumes "P1 gs0 \<Longrightarrow>\<^sub>g R gs0"
    and "P2 gs0 \<Longrightarrow>\<^sub>g R gs0"
  shows "(P1 \<or>\<^sub>g P2) gs0 \<Longrightarrow>\<^sub>g R gs0"
  using assms unfolding entails_g_def disj_gassn_def by auto

lemma entails_g_disj2:
  assumes "P1 gs0 \<Longrightarrow>\<^sub>g R1 gs0"
    and "P2 gs0 \<Longrightarrow>\<^sub>g R2 gs0"
  shows "(P1 \<or>\<^sub>g P2) gs0 \<Longrightarrow>\<^sub>g (R1 \<or>\<^sub>g R2) gs0"
  using assms unfolding entails_g_def disj_gassn_def by auto

lemma cond_gassn_true:
  "b \<Longrightarrow> (IFG [pn] (\<lambda>_. b) THEN P ELSE Q FI = P)"
  unfolding cond_gassn2_def by auto

lemma cond_gassn_false:
  "\<not>b \<Longrightarrow> (IFG [pn] (\<lambda>_. b) THEN P ELSE Q FI = Q)"
  unfolding cond_gassn2_def by auto

lemma sync_gassn_false_left:
  "sync_gassn chs pns1 pns2 false_gassn Q s0 \<Longrightarrow>\<^sub>g R s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases)
    unfolding false_gassn_def by auto
  done

lemma sync_gassn_false_right:
  "sync_gassn chs pns1 pns2 P false_gassn s0 \<Longrightarrow>\<^sub>g R s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases)
    unfolding false_gassn_def by auto
  done

lemma sync_gassn_disj:
  assumes "sync_gassn chs pns1 pns2 P1 Q gs0 \<Longrightarrow>\<^sub>g R"
    and "sync_gassn chs pns1 pns2 P2 Q gs0 \<Longrightarrow>\<^sub>g R"
  shows "sync_gassn chs pns1 pns2 (P1 \<or>\<^sub>g P2) Q gs0 \<Longrightarrow>\<^sub>g R"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    using assms unfolding disj_gassn_def entails_g_def
    by (auto simp add: sync_gassn.intros)
  done

lemma sync_gassn_disj2:
  assumes "sync_gassn chs pns1 pns2 P1 Q gs0 \<Longrightarrow>\<^sub>g R1 gs1"
    and "sync_gassn chs pns1 pns2 P2 Q gs0 \<Longrightarrow>\<^sub>g R2 gs1"
  shows "sync_gassn chs pns1 pns2 (P1 \<or>\<^sub>g P2) Q gs0 \<Longrightarrow>\<^sub>g (R1 \<or>\<^sub>g R2) gs1"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    using assms unfolding disj_gassn_def entails_g_def
    by (auto simp add: sync_gassn.intros)
  done

lemma sync_gassn_ifg_left:
  assumes
    "b (the (s0 pn)) \<Longrightarrow> sync_gassn chs pns1 pns2 P1 Q s0 \<Longrightarrow>\<^sub>g R s0"
    "\<not>b (the (s0 pn)) \<Longrightarrow> sync_gassn chs pns1 pns2 P2 Q s0 \<Longrightarrow>\<^sub>g R s0"
    "pn \<in> pns1"
  shows
    "sync_gassn chs pns1 pns2 (IFG [pn] b THEN P1 ELSE P2 FI) Q s0 \<Longrightarrow>\<^sub>g R s0"
  unfolding cond_gassn2_def entails_g_def
  apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply clarify
    subgoal premises pre for s11 _ s12 _ s21 s22 _ tr1 _ tr2 _ tr'
    proof (cases "b (the (s11 pn))")
      case True
      show ?thesis
      proof -
        have "b (the (s0 pn))"
          unfolding pre(1) using assms(3)
          by (simp add: True merge_state_eval1 pre(7))
        moreover have "sync_gassn chs pns1 pns2 P1 Q s0 s tr"
          unfolding pre(1,2)
          apply (rule sync_gassn.intros)
          using pre True by auto
        ultimately show ?thesis
          using assms(1)[unfolded cond_gassn2_def entails_g_def]
          unfolding pre(1,2) by auto
      qed
    next
      case False
      show ?thesis
      proof -
        have "\<not>b (the (s0 pn))"
          unfolding pre(1) using assms(3)
          by (simp add: False merge_state_eval1 pre(7))
        moreover have "sync_gassn chs pns1 pns2 P2 Q s0 s tr"
          unfolding pre(1,2)
          apply (rule sync_gassn.intros)
          using pre False by auto
        ultimately show ?thesis
          using assms(2)[unfolded cond_gassn2_def entails_g_def]
          unfolding pre(1,2) by auto
      qed
    qed
    done
  done

lemma sync_gassn_true_left:
  assumes "proc_set_gassn pns2 Q"
  shows "sync_gassn chs pns1 pns2 (true_gassn pns1) Q s0 \<Longrightarrow>\<^sub>g true_gassn (pns1 \<union> pns2) s0"
  unfolding entails_g_def apply auto
  apply (elim sync_gassn.cases)
  apply auto apply (rule true_gassn.intros)
    apply auto subgoal for s11 s12 s21 s22 tr1 tr2 tr'
    apply (rule proc_set_trace_combine[of chs tr1 tr2])
      apply auto apply (elim true_gassn.cases) apply blast
    using assms[unfolded proc_set_gassn_def] by blast
  done

lemma sync_gassn_true_left':
  assumes "proc_set_gassn pns2 Q"
  shows "sync_gassn chs pns1 pns2 (true_gassn pns1) Q s0 s tr \<Longrightarrow> true_gassn (pns1 \<union> pns2) s0 s tr"
  using sync_gassn_true_left[OF assms] unfolding entails_g_def by auto

lemma entails_true_gassn:
  assumes "proc_set_gassn pns P"
  shows "P s0 \<Longrightarrow>\<^sub>g true_gassn pns s0"
  unfolding entails_g_def apply auto
  apply (intro true_gassn.intros)
  using assms unfolding proc_set_gassn_def by auto

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
        using assms by (auto simp add: merge_state_eval1)
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
        using assms by (auto simp add: merge_state_eval2)
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
        using assms by (auto simp add: merge_state_eval1)
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
        using assms by (auto simp add: merge_state_eval2)
      done
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

lemma sync_gassn_triv:
  assumes "s1 = s2"
  shows "sync_gassn chs pns1 pns2 P Q s1 \<Longrightarrow>\<^sub>g sync_gassn chs pns1 pns2 P Q s2"
  apply (simp add: assms)
  by (rule entails_g_triv)

lemma exists_gassn_intro:
  assumes "\<exists>n. P s0 \<Longrightarrow>\<^sub>g Q n s0"
  shows "P s0 \<Longrightarrow>\<^sub>g (\<exists>\<^sub>g n. Q n) s0"
  using assms unfolding exists_gassn_def entails_g_def by auto

lemma sync_gassn_exists_left:
  "sync_gassn chs pns1 pns2 (\<exists>\<^sub>gn. P n) Q = (\<exists>\<^sub>gn. sync_gassn chs pns1 pns2 (P n) Q)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s tr s0
    apply (rule iffI)
     apply (auto simp add: exists_gassn_def)
    by (auto elim: sync_gassn.cases intro: sync_gassn.intros)
  done

lemma sync_gassn_exists_right:
  "sync_gassn chs pns1 pns2 P (\<exists>\<^sub>gn. Q n) = (\<exists>\<^sub>gn. sync_gassn chs pns1 pns2 P (Q n))"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s tr s0
    apply (rule iffI)
     apply (auto simp add: exists_gassn_def)
    by (auto elim: sync_gassn.cases intro: sync_gassn.intros)
  done

subsubsection \<open>Monotonicity rules\<close>

lemma exists_gassn_mono:
  assumes "\<And>n. P1 n s0 \<Longrightarrow>\<^sub>g P2 n s0"
  shows "(\<exists>\<^sub>gn. P1 n) s0 \<Longrightarrow>\<^sub>g (\<exists>\<^sub>gn. P2 n) s0"
  using assms unfolding entails_g_def exists_gassn_def by auto

lemma conj_pure_gassn_mono:
  assumes "b s0 \<Longrightarrow> Q1 s0 \<Longrightarrow>\<^sub>g Q2 s0"
  shows "(!\<^sub>g[b] at pns \<and>\<^sub>g Q1) s0 \<Longrightarrow>\<^sub>g (!\<^sub>g[b] at pns \<and>\<^sub>g Q2) s0"
  using assms unfolding entails_g_def conj_gassn_def pure_gassn_def by auto

lemma cond_gassn_mono:
  assumes "P1 s0 \<Longrightarrow>\<^sub>g P2 s0"
    and "Q1 s0 \<Longrightarrow>\<^sub>g Q2 s0"
  shows "(IFG [pn] b THEN P1 ELSE Q1 FI) s0 \<Longrightarrow>\<^sub>g (IFG [pn] b THEN P2 ELSE Q2 FI) s0"
  unfolding entails_g_def apply clarify
  subgoal for s tr
    unfolding cond_gassn2_def
    apply auto using assms unfolding entails_g_def by auto
  done

lemma updg_mono:
  assumes "P (updg s0 pn v (e (the (s0 pn)))) \<Longrightarrow>\<^sub>g Q (updg s0 pn v (e (the (s0 pn))))"
  shows "(P {{v := e}}\<^sub>g at pn) s0 \<Longrightarrow>\<^sub>g (Q {{v := e}}\<^sub>g at pn) s0"
  apply (auto simp add: entails_g_def)
  subgoal for s tr
    unfolding updg_assn2_def
    using assms unfolding entails_g_def by auto
  done

lemma wait_out_cg_mono:
  assumes "\<And>d v. P d v s0 \<Longrightarrow>\<^sub>g Q d v s0"
  shows "wait_out_cg ch P s0 \<Longrightarrow>\<^sub>g wait_out_cg ch Q s0"
  apply (auto simp add: entails_g_def)
  subgoal for s tr
    apply (elim wait_out_cg.cases) apply auto
    subgoal apply (rule wait_out_cg.intros)
      using assms unfolding entails_g_def by auto
    subgoal apply (rule wait_out_cg.intros)
      using assms unfolding entails_g_def by auto
    done
  done

lemma wait_in_cg_mono:
  assumes "\<And>d v. P d v s0 \<Longrightarrow>\<^sub>g Q d v s0"
  shows "wait_in_cg ch P s0 \<Longrightarrow>\<^sub>g wait_in_cg ch Q s0"
  apply (auto simp add: entails_g_def)
  subgoal for s tr
    apply (elim wait_in_cg.cases) apply auto
    subgoal apply (rule wait_in_cg.intros)
      using assms unfolding entails_g_def by auto
    subgoal apply (rule wait_in_cg.intros)
      using assms unfolding entails_g_def by auto
    done
  done

lemma wait_cg_mono:
  assumes "P s0 \<Longrightarrow>\<^sub>g Q s0"
  shows "wait_cg pn e P s0 \<Longrightarrow>\<^sub>g wait_cg pn e Q s0"
  apply (auto simp add: entails_g_def)
  subgoal for s tr
    apply (elim wait_cg.cases) apply auto
    subgoal apply (rule wait_cg.intros)
       using assms unfolding entails_g_def by auto
    subgoal apply (rule wait_cg.intros)
      using assms unfolding entails_g_def by auto
    done
  done

lemma wait_in_cg_alt_mono:
  assumes "\<And>d v. P1 d v s0 \<Longrightarrow>\<^sub>g P2 d v s0"
    and "\<And>d. Q1 d s0 \<Longrightarrow>\<^sub>g Q2 d s0"
  shows "wait_in_cg_alt ch pn e P1 Q1 s0 \<Longrightarrow>\<^sub>g wait_in_cg_alt ch pn e P2 Q2 s0"
  apply (auto simp add: entails_g_def)
  subgoal for s tr
    apply (elim wait_in_cg_alt.cases) apply auto
    subgoal for v tr'
      apply (rule wait_in_cg_alt.intros)
      using assms(1) unfolding entails_g_def by auto
    subgoal for d v tr'
      apply (rule wait_in_cg_alt.intros)
      using assms(1) unfolding entails_g_def by auto
    subgoal for d tr'
      apply (rule wait_in_cg_alt.intros)
      using assms(2) unfolding entails_g_def by auto
    subgoal
      apply (rule wait_in_cg_alt.intros)
      using assms(2) unfolding entails_g_def by auto
    done
  done

subsection \<open>Hoare logic for parallel programs\<close>

definition ParValid :: "'a gs_assn \<Rightarrow> 'a pproc \<Rightarrow> 'a gassn \<Rightarrow> bool" ("\<Turnstile>\<^sub>p ({(1_)}/ (_)/ {(1_)})" 50) where
  "(\<Turnstile>\<^sub>p {P} c {Q}) \<longleftrightarrow> (\<forall>s1 s2 tr2. P s1 \<longrightarrow> par_big_step c s1 tr2 s2 \<longrightarrow> Q s2 tr2)"

definition spec_of_global :: "'a pproc \<Rightarrow> 'a gassn2 \<Rightarrow> bool" where
  "spec_of_global c Q \<longleftrightarrow> (\<forall>s0. \<Turnstile>\<^sub>p {init_global s0} c {Q s0})"

lemma spec_of_globalE:
  "spec_of_global c Q \<Longrightarrow> \<Turnstile>\<^sub>p {init_global s0} c {Q s0}"
  unfolding spec_of_global_def by auto

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

subsection \<open>Elimination rules for synchronization\<close>

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
  "combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) (WaitBlkP d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2' [sync_elims]:
  "combine_blocks comms (WaitBlkP d1 p1 rdy1 # tr1) (CommBlockP ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3 [sync_elims]:
  "combine_blocks comms (CommBlockP ch_type1 ch1 v1 # tr1) (WaitBlkP d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlockP ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlkP d2 p2 rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3' [sync_elims]:
  "combine_blocks comms (WaitBlkP d1 p1 rdy1 # tr1) (CommBlockP ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlockP ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlkP d1 p1 rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_waitE1 [sync_elims]:
  "combine_blocks comms (WaitBlkP d1 p1 rdy1 # tr1) (WaitBlkP d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   \<not>compat_rdy rdy1 rdy2 \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto elim: WaitBlkP_eqE)

lemma combine_blocks_waitE2 [sync_elims]:
  "combine_blocks comms (WaitBlkP d (\<lambda>t. p1 t) rdy1 # tr1) (WaitBlkP d (\<lambda>t. p2 t) rdy2 # tr2) tr \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlkP d (\<lambda>t. merge_state (p1 t) (p2 t)) (merge_rdy comms rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: combine_blocks.cases, auto elim: WaitBlkP_eqE)
  subgoal premises pre for blks a b a' b' hist1 hist2 t
    apply (rule pre(6)) apply (rule WaitBlkP_eqI)
    using pre by (auto elim!: WaitBlkP_eqE)
  done

lemma combine_blocks_waitE3 [sync_elims]:
  "combine_blocks comms (WaitBlkP d1 (\<lambda>t. p1 t) rdy1 # tr1) (WaitBlkP d2 (\<lambda>t. p2 t) rdy2 # tr2) tr \<Longrightarrow>
   0 < d1 \<Longrightarrow> d1 < d2 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlkP d1 (\<lambda>t. merge_state (p1 t) (p2 t)) (merge_rdy comms rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlkP (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: combine_blocks.cases, auto elim!: WaitBlkP_eqE)
  subgoal premises pre for hist2 a b blks a' b' hist1
    apply (rule pre(5)) apply (rule WaitBlkP_eqI)
    using pre apply (auto elim!: WaitBlkP_eqE)
    subgoal proof -
      have "WaitBlkP (d2 - d1) (\<lambda>\<tau>. hist2 (\<tau> + d1)) (a, b) = WaitBlkP (d2 - d1) (\<lambda>\<tau>. p2 (\<tau> + d1)) (a, b)"
        apply (rule WaitBlkP_eqI) using pre by (auto elim!: WaitBlkP_eqE)
      then show ?thesis
        using pre by auto
    qed
    done
  done

lemma combine_blocks_waitE4 [sync_elims]:
  "combine_blocks comms (WaitBlkP d1 (\<lambda>t. p1 t) rdy1 # tr1) (WaitBlkP d2 (\<lambda>t. p2 t) rdy2 # tr2) tr \<Longrightarrow>
   0 < d2 \<Longrightarrow> d2 < d1 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlkP d2 (\<lambda>t. merge_state (p1 t) (p2 t)) (merge_rdy comms rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlkP (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: combine_blocks.cases, auto elim!: WaitBlkP_eqE)
  subgoal premises pre for hist2 a b blks a' b' hist1
    apply (rule pre(5)) apply (rule WaitBlkP_eqI)
    using pre apply (auto elim!: WaitBlkP_eqE)
    subgoal proof -
      have "WaitBlkP (d1 - d2) (\<lambda>\<tau>. hist2 (\<tau> + d2)) (a, b) = WaitBlkP (d1 - d2) (\<lambda>\<tau>. p1 (\<tau> + d2)) (a, b)"
        apply (rule WaitBlkP_eqI) using pre by (auto elim!: WaitBlkP_eqE)
      then show ?thesis
        using pre by auto
    qed
    done
  done

lemma combine_blocks_emptyE1 [sync_elims]:
  "combine_blocks comms [] [] tr \<Longrightarrow> tr = []"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2 [sync_elims]:
  "combine_blocks comms (WaitBlkP d1 p1 rdy1 # tr1) [] tr \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2' [sync_elims]:
  "combine_blocks comms [] (WaitBlkP d2 p2 rdy2 # tr2) tr \<Longrightarrow> P"
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

lemma entailsD:
  "P s tr \<Longrightarrow> P \<Longrightarrow>\<^sub>g Q \<Longrightarrow> Q s tr"
  unfolding entails_g_def by auto

lemma sync_gassn_conj_pure_left:
  assumes "pns = pns1 \<union> pns2"
    and "pns1 \<inter> pns2 = {}"
    and "proc_set_gassn pns2 P2"
  shows "sync_gassn chs pns1 pns2 (!\<^sub>g[R] at pns1 \<and>\<^sub>g P1) P2 s0 \<Longrightarrow>\<^sub>g
         (!\<^sub>g[(\<lambda>gs. R (restrict_state pns1 gs))] at pns \<and>\<^sub>g sync_gassn chs pns1 pns2 P1 P2) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases)
    using assms apply (auto simp add: conj_gassn_def pure_gassn_def)
    subgoal for s11 s12 s21 s22 tr1 tr2
      by (simp add: restrict_state_merge1)
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (rule proc_set_trace_combine) apply auto
      using assms(3) unfolding proc_set_gassn_def by blast
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (rule sync_gassn.intros) by auto
    done
  done

lemma sync_gassn_conj_pure_right:
  assumes "R (restrict_state pns2 s0) \<Longrightarrow> sync_gassn chs pns1 pns2 P1 P2 s0 \<Longrightarrow>\<^sub>g Q s0"
    and "pns1 \<inter> pns2 = {}"
  shows "sync_gassn chs pns1 pns2 P1 (!\<^sub>g[R] at pn \<and>\<^sub>g P2) s0 \<Longrightarrow>\<^sub>g Q s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply (auto simp add: conj_gassn_def pure_gassn_def)
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (rule entailsD[where P="sync_gassn chs pns1 pns2 P1 P2 s0"]) apply auto
       apply (rule sync_gassn.intros) apply auto
      by (metis assms restrict_state_merge2)
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

lemma sync_gassn_in_out:
  "ch \<in> chs \<Longrightarrow>
   pn \<in> pns2 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_in_cg ch P) (wait_out_cg ch Q) s0 \<Longrightarrow>\<^sub>g
   (\<exists>\<^sub>gv. sync_gassn chs pns1 pns2 (P 0 v) (Q 0 v)) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for v' tr2'
          apply (elim combine_blocks_pairE) apply (auto simp add: exists_gassn_def)
          apply (rule exI[where x=v])
          by (auto simp add: merge_state_eval2 exists_gassn_def sync_gassn.intros)
        subgoal for d v' tr2'
          apply (elim combine_blocks_pairE2) by auto
        done
      subgoal for d v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for v' tr'
          apply (elim combine_blocks_pairE2') by auto
        subgoal for d' v' tr'
          apply (elim combine_blocks_waitE1) by auto
        done
      done
    done
  done

lemma sync_gassn_in_outv:
  "ch \<in> chs \<Longrightarrow>
   pn \<in> pns2 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_in_cg ch P) (wait_out_cgv ch pns2 pn e Q) s0 \<Longrightarrow>\<^sub>g
   sync_gassn chs pns1 pns2 (P 0 (e (the (s0 pn)))) (Q 0) s0"
  unfolding wait_out_cgv_def
  apply (rule entails_g_trans)
   apply (rule sync_gassn_in_out) apply auto
  apply (rule exists_gassn_elim)
  subgoal for v
    apply (rule sync_gassn_conj_pure_right)
    apply (simp add: restrict_state_def)
    by (rule entails_g_triv)
  done

lemma sync_gassn_out_in:
  "ch \<in> chs \<Longrightarrow>
   pn \<in> pns1 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_out_cg ch Q) (wait_in_cg ch P) s0 \<Longrightarrow>\<^sub>g
   (\<exists>\<^sub>gv. sync_gassn chs pns1 pns2 (Q 0 v) (P 0 v)) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for v' tr2'
          apply (elim combine_blocks_pairE) apply (auto simp add: exists_gassn_def)
          apply (rule exI[where x=v])
          by (auto simp add: merge_state_eval1 sync_gassn.intros)
        subgoal for d v' tr2'
          apply (elim combine_blocks_pairE2') by auto
        done
      subgoal for d v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for v' tr'
          apply (elim combine_blocks_pairE2) by auto
        subgoal for d' v' tr'
          apply (elim combine_blocks_waitE1) by auto
        done
      done
    done
  done

lemma sync_gassn_outv_in:
  "ch \<in> chs \<Longrightarrow>
   pn \<in> pns1 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   (\<And>d v. proc_set_gassn pns2 (P d v)) \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_out_cgv ch pns1 pn e Q) (wait_in_cg ch P) s0 \<Longrightarrow>\<^sub>g
   sync_gassn chs pns1 pns2 (Q 0) (P 0 (e (the (s0 pn)))) s0"
  unfolding wait_out_cgv_def
  apply (rule entails_g_trans)
   apply (rule sync_gassn_out_in) apply auto
  apply (rule exists_gassn_elim)
  subgoal for v
    apply (rule entails_g_trans)
     apply (rule sync_gassn_conj_pure_left) apply auto
    apply (rule conj_pure_gassn_elim)
    apply (simp add: restrict_state_def)
    by (rule entails_g_triv)
  done

lemma sync_gassn_out_emp:
  "ch \<notin> chs \<Longrightarrow>
   pn \<in> pns1 \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_out_cg ch Q) (init_single pns2) s0 \<Longrightarrow>\<^sub>g
   wait_out_cg ch (\<lambda>d v. sync_gassn chs pns1 pns2 (Q d v) (init_single pns2)) s0"
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
           apply (rule init_single.intros) by auto
        done
      subgoal for d tr'
        apply (elim init_single.cases) apply auto
        by (elim sync_elims)
      done
    done
  done

lemma sync_gassn_outv_emp:
  "ch \<notin> chs \<Longrightarrow>
   pn \<in> pns1 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   (\<And>d. proc_set_gassn pns1 (Q d)) \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_out_cgv ch pns1 pn e Q) (init_single pns2) s0 \<Longrightarrow>\<^sub>g
   wait_out_cgv ch (pns1 \<union> pns2) pn e (\<lambda>d. sync_gassn chs pns1 pns2 (Q d) (init_single pns2)) s0"
  unfolding wait_out_cgv_def
  apply (rule entails_g_trans)
   apply (rule sync_gassn_out_emp) apply auto
  apply (rule wait_out_cg_mono) subgoal for d v
    apply (rule entails_g_trans)
     apply (rule sync_gassn_conj_pure_left) apply auto
    apply (rule conj_pure_gassn_elim)
    apply (intro conj_gassn_intro pure_gassn_intro)
    subgoal by (simp add: restrict_state_def)
    subgoal by auto
    by (rule entails_g_triv)
  done

lemma sync_gassn_out_emp_unpair:
  "ch \<in> chs \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_out_cg ch Q) (init_single pns2) s0 \<Longrightarrow>\<^sub>g P"
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

lemma sync_gassn_outv_emp_unpair:
  "ch \<in> chs \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_out_cgv ch pns1 pn e Q) (init_single pns2) s0 \<Longrightarrow>\<^sub>g P"
  unfolding wait_out_cgv_def
  apply (rule sync_gassn_out_emp_unpair) by auto

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

lemma set_minus_simp1 [simp]:
  "ch \<notin> chs \<Longrightarrow> {ch} - chs = {ch}"
  by auto

text \<open>Left side has unpaired input, right side is communication.
  Then the left side always happen first.
\<close>
lemma sync_gassn_in_unpair_left:
  "ch1 \<notin> chs \<Longrightarrow>
   ch2 \<in> chs \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_in_cg ch1 P) (wait_out_cg ch2 Q) s0 \<Longrightarrow>\<^sub>g
   wait_in_cg ch1
     (\<lambda>d v. sync_gassn chs pns1 pns2 (P d v) (wait_out_cg ch2 (\<lambda>d2. Q (d2 + d)))) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr2'
          apply (elim combine_blocks_unpairE1)
            apply auto
          apply (rule wait_in_cg.intros)
          apply (rule sync_gassn.intros) apply auto
          apply (rule wait_out_cg.intros) by auto
        subgoal for d tr2'
          apply (elim combine_blocks_unpairE3)
           apply auto
          apply (rule wait_in_cg.intros)
          apply (rule sync_gassn.intros) apply auto
          apply (rule wait_out_cg.intros) by auto
        done
      subgoal for d v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr2'
          apply (elim sync_elims) by auto
        subgoal for d2 tr2'
          apply (cases rule: linorder_cases[of d d2])
          subgoal
            apply (elim combine_blocks_waitE3) apply auto
            apply (elim combine_blocks_unpairE3) apply auto
            apply (rule wait_in_cg.intros(2)) apply auto
            apply (rule sync_gassn.intros) apply auto
            apply (rule wait_out_cg.intros) by auto
          subgoal apply auto
            apply (elim combine_blocks_waitE2) apply auto
            apply (elim combine_blocks_unpairE1) apply auto
            apply (rule wait_in_cg.intros(2)) apply auto
            apply (rule sync_gassn.intros) apply auto
            apply (rule wait_out_cg.intros) by auto
          subgoal
            apply (elim combine_blocks_waitE4) apply auto
            apply (elim sync_elims) by auto
          done
        done
      done
    done
  done

text \<open>Left side has unpaired input, right side is wait\<close>
lemma sync_gassn_in_unpair_left_wait:
  "ch1 \<notin> chs \<Longrightarrow>
   pn \<in> pns2 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_in_cg ch1 P) (wait_cg pn e Q) s0 \<Longrightarrow>\<^sub>g
   wait_in_cg_alt ch1 pn e
    (\<lambda>d v. sync_gassn chs pns1 pns2 (P d v) (wait_cg pn (\<lambda>s. e s - d) Q))
    (\<lambda>d. sync_gassn chs pns1 pns2 (wait_in_cg ch1 (\<lambda>d' v. P (d + d') v)) Q) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr1'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr2'
          apply (elim combine_blocks_unpairE3)
            apply auto
          apply (rule wait_in_cg_alt.intros(1))
          apply (rule sync_gassn.intros) apply auto
          apply (rule wait_cg.intros) by auto
        subgoal
          apply (rule wait_in_cg_alt.intros(4))
           apply (auto simp: merge_state_eval2)[1]
          apply (rule sync_gassn.intros) apply auto
          apply (rule wait_in_cg.intros) by auto
        done
      subgoal for d v tr1'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr2'
          apply (cases rule: linorder_cases[of d "e (the (s12 pn))"])
          subgoal
            apply (elim combine_blocks_waitE3) apply auto
            apply (elim combine_blocks_unpairE3) apply auto
            apply (rule wait_in_cg_alt.intros(2)) apply (auto simp add: merge_state_eval2)
            apply (rule sync_gassn.intros) apply auto
            apply (rule wait_cg.intros) by auto
          subgoal apply auto
            apply (elim combine_blocks_waitE2) apply auto
            apply (rule wait_in_cg_alt.intros(3)) apply (auto simp add: merge_state_eval2)
            apply (rule sync_gassn.intros) apply auto
            apply (rule wait_in_cg.intros) by auto
          subgoal
            apply (elim combine_blocks_waitE4) apply auto
            apply (rule wait_in_cg_alt.intros(3)) apply (auto simp add: merge_state_eval2)
            apply (rule sync_gassn.intros) apply auto
            apply (rule wait_in_cg.intros(2)) by auto
          done
        subgoal
          apply (rule wait_in_cg_alt.intros(4)) apply (auto simp add: merge_state_eval2)
          apply (rule sync_gassn.intros) apply auto
          apply (rule wait_in_cg.intros(2)) by auto
        done
      done
    done
  done

text \<open>Specialization of sync_gassn_in_unpair_left, when assuming
  immediate communication.
\<close>
lemma sync_gassn_out_unpair0:
  "ch1 \<notin> chs \<Longrightarrow>
   ch2 \<in> chs \<Longrightarrow>
   pn \<in> pns1 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   (\<And>d v. proc_set_gassn pns2 (Q d v)) \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_in_cg0 pn ch1 pns1 P) (wait_out_cg ch2 Q) s0 \<Longrightarrow>\<^sub>g
   wait_in_cg0 pn ch1 (pns1 \<union> pns2) (\<lambda>v. sync_gassn chs pns1 pns2 (P v) (wait_out_cg ch2 Q)) s0"
  unfolding wait_in_cg0_def
  apply (rule entails_g_trans)
   apply (rule sync_gassn_in_unpair_left) apply auto
  apply (rule entails_g_trans)
   apply (rule wait_in_cg_mono)
   apply (rule entails_g_triv)
  apply (rule wait_in_cg_mono)
  subgoal for d v
    apply (rule sync_gassn_ifg_left)
    subgoal unfolding cond_gassn_true
      apply simp by (rule entails_g_triv)
    subgoal unfolding cond_gassn_false
      apply (rule sync_gassn_true_left)
      apply (rule proc_set_wait_out_cg) by auto
    subgoal by auto
    done
  done

text \<open>Specialization of sync_gassn_in_unpair_left_wait, when
  assuming immediate communication.
\<close>
lemma sync_gassn_out_unpair_wait0:
  "ch1 \<notin> chs \<Longrightarrow>
   pn1 \<in> pns1 \<Longrightarrow>
   pn2 \<in> pns2 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   (\<And>v. proc_set_gassn pns1 (P v)) \<Longrightarrow>
   proc_set_gassn pns2 Q \<Longrightarrow>
   sync_gassn chs pns1 pns2
     (wait_in_cg0 pn1 ch1 pns1 P) (wait_cg pn2 e Q) s0 \<Longrightarrow>\<^sub>g
   wait_in_cg_alt ch1 pn2 e
     (\<lambda>d v. (IFG [pn1] (\<lambda>s. d = 0) THEN sync_gassn chs pns1 pns2 (P v) (wait_cg pn2 e Q)
             ELSE true_gassn (pns1 \<union> pns2) FI))
     (\<lambda>v. true_gassn (pns1 \<union> pns2)) s0"
  unfolding wait_in_cg0_def
  apply (rule entails_g_trans)
   apply (rule sync_gassn_in_unpair_left_wait) apply auto
  apply (rule wait_in_cg_alt_mono)
  subgoal for d v
    apply (rule sync_gassn_ifg_left) apply auto
    subgoal apply (simp add: cond_gassn_true)
      by (rule entails_g_triv)
    subgoal apply (simp add: cond_gassn_false)
      apply (rule sync_gassn_true_left)
      apply (rule proc_set_wait_cg) by auto
    done
  subgoal for d
    apply (rule entails_true_gassn) 
    apply (rule proc_set_sync_gassn) by auto
  done

lemma sync_gassn_wait_same:
  "pns1 \<inter> pns2 = {} \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_cg pn1 (\<lambda>_. v) P) (wait_cg pn2 (\<lambda>_. v) Q) s0 \<Longrightarrow>\<^sub>g
   wait_cg pn1 (\<lambda>_. v) (sync_gassn chs pns1 pns2 P Q) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_cg.cases) apply auto
      subgoal for tr1' tr2'
        apply (elim combine_blocks_waitE2) apply auto
        apply (rule wait_cg.intros(1)) apply auto
        apply (intro sync_gassn.intros) by auto
      subgoal
        apply (rule wait_cg.intros(2)) apply auto
        apply (intro sync_gassn.intros) by auto
      done
    done
  done

lemma sync_gassn_in_alt_out:
  "ch \<in> chs \<Longrightarrow>
   pn1 \<in> pns1 \<Longrightarrow>
   pn2 \<in> pns1 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   d > 0 \<Longrightarrow>
   sync_gassn chs pns1 pns2
      (wait_in_cg_alt ch pn1 (\<lambda>_. d)
        (\<lambda>d v. IFG [pn2] (\<lambda>s. d = 0) THEN P v ELSE true_gassn pns1 FI)
        (\<lambda>v. true_gassn pns1))
      (wait_out_cg ch Q) s0 \<Longrightarrow>\<^sub>g
   (\<exists>\<^sub>gv. sync_gassn chs pns1 pns2 (P v) (Q 0 v)) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg_alt.cases) apply auto
      subgoal for v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for v' tr2'
          apply (elim combine_blocks_pairE)
            apply (auto simp add: merge_state_eval2 cond_gassn_true exists_gassn_def)
          apply (rule exI[where x=v])
          apply (rule sync_gassn.intros) by auto
        subgoal for d tr2'
          apply (elim sync_elims) by auto
        done
      subgoal for d v tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr2'
          apply (elim sync_elims) by auto
        subgoal for d' tr2'
          apply (elim sync_elims) by auto
        done
      subgoal for d tr1'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr2'
          apply (elim sync_elims) by auto
        subgoal for d' tr2'
          apply (elim sync_elims) by auto
        done
      done
    done
  done

lemma sync_gassn_in_alt_outv:
  "ch \<in> chs \<Longrightarrow>
   pn1 \<in> pns1 \<Longrightarrow>
   pn2 \<in> pns1 \<Longrightarrow>
   pn3 \<in> pns2 \<Longrightarrow>
   pns1 \<inter> pns2 = {} \<Longrightarrow>
   d > 0 \<Longrightarrow>
   sync_gassn chs pns1 pns2
      (wait_in_cg_alt ch pn1 (\<lambda>_. d)
        (\<lambda>d v. IFG [pn2] (\<lambda>s. d = 0) THEN P v ELSE true_gassn pns1 FI)
        (\<lambda>v. true_gassn pns1))
      (wait_out_cgv ch pns2 pn3 e Q) s0 \<Longrightarrow>\<^sub>g
   (sync_gassn chs pns1 pns2 (P (e (the (s0 pn3)))) (Q 0)) s0"
  unfolding wait_out_cgv_def
  apply (rule entails_g_trans)
   apply (rule sync_gassn_in_alt_out) apply auto
  apply (rule exists_gassn_elim)
  subgoal for v
    apply (rule sync_gassn_conj_pure_right)
     apply (simp add: restrict_state_def)
    by (rule entails_g_triv)
  done

subsection \<open>General specification\<close>

definition spec_of_global_gen :: "('a gstate \<Rightarrow> bool) \<Rightarrow> 'a pproc \<Rightarrow> 'a gassn2 \<Rightarrow> bool" where
  "spec_of_global_gen P c Q \<longleftrightarrow> (\<forall>s0. P s0 \<longrightarrow> \<Turnstile>\<^sub>p {init_global s0} c {Q s0})"

end
