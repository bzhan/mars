theory Coinductive
  imports Main "HOL-Library.BNF_Corec" "ext/ext_BigStepSimple"
begin

codatatype 'a stream = SCons (shd: 'a) (stl: "'a stream")

type_synonym 'a strace = "'a trace_block stream"

type_synonym 'a stassn = "'a strace \<Rightarrow> bool"

subsection \<open>Combining two traces\<close>

text \<open>Whether two rdy_infos from different processes are compatible.\<close>
fun compat_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

text \<open>Merge two rdy infos\<close>
fun merge_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> rdy_info" where
  "merge_rdy (r11, r12) (r21, r22) = (r11 \<union> r21, r12 \<union> r22)"

lemma WaitBlk_eq_combine:
  assumes "WaitBlk d1 p1 rdy1 = WaitBlk d1' p1' rdy1'"
    and "WaitBlk d1 p2 rdy2 = WaitBlk d1' p2' rdy2'"
   shows "WaitBlk d1 (\<lambda>\<tau>. ParState (p1 \<tau>) (p2 \<tau>)) (merge_rdy rdy1 rdy2) =
          WaitBlk d1' (\<lambda>\<tau>. ParState (p1' \<tau>) (p2' \<tau>)) (merge_rdy rdy1' rdy2')"
proof -
  have a1: "d1 = d1'" "rdy1 = rdy1'" "rdy2 = rdy2'"
    using assms WaitBlk_cong by blast+
  have a2: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> d1 \<Longrightarrow> p1 t = p1' t"
    using assms(1) WaitBlk_cong2 by blast
  have a3: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> d1 \<Longrightarrow> p2 t = p2' t"
    using assms(2) WaitBlk_cong2 by blast
  show ?thesis
  proof (cases d1)
    case (real r)
    have b: "d1' = ereal r"
      using real a1(1) by auto
    show ?thesis
      unfolding real b apply (auto simp add: WaitBlk_simps)
       apply (rule ext) apply auto
      subgoal for x apply (rule a2) by (auto simp add: real)
      subgoal for x apply (rule a3) by (auto simp add: real)
      using a1 by auto
  next
    case PInf
    have b: "d1' = \<infinity>"
      using PInf a1 by auto
    show ?thesis
      unfolding PInf b infinity_ereal_def
      apply (auto simp: WaitBlk_simps)
       apply (rule ext) apply auto
      subgoal for x apply (rule a2) by (auto simp add: PInf)
      subgoal for x apply (rule a3) by (auto simp add: PInf)
      using a1 by auto
  next
    case MInf
    have b: "d1' = - \<infinity>"
      using MInf a1 by auto
    show ?thesis
      unfolding MInf b
      by (auto simp: a1 WaitBlk_simps)
  qed
qed

coinductive combine_blocks :: "cname set \<Rightarrow> 'a strace \<Rightarrow> 'a strace \<Rightarrow> 'a strace \<Rightarrow> bool" where
  \<comment> \<open>Paired communication\<close>
  combine_blocks_pair1:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (SCons (InBlock ch v) blks1) (SCons (OutBlock ch v) blks2)
                  (SCons (IOBlock ch v) blks)"
| combine_blocks_pair2:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (SCons (OutBlock ch v) blks1) (SCons (InBlock ch v) blks2)
                  (SCons (IOBlock ch v) blks)"

  \<comment> \<open>Paired communication\<close>
| combine_blocks_unpair1:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (SCons (CommBlock ch_type ch v) blks1) blks2
                  (SCons (CommBlock ch_type ch v) blks)"
| combine_blocks_unpair2:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (SCons (CommBlock ch_type ch v) blks2)
                  (SCons (CommBlock ch_type ch v) blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_wait:
  "combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (SCons (WaitBlk t (\<lambda>x::real. hist1 x) rdy1) blks1)
                        (SCons (WaitBlk t (\<lambda>x::real. hist2 x) rdy2) blks2)
                        (SCons (WaitBlk t hist rdy) blks)"

lemma combine_blocks_waitE:
  "combine_blocks comms (SCons (WaitBlk d1 p1 rdy1) blks1)
                        (SCons (WaitBlk d2 p2 rdy2) blks2) blks \<Longrightarrow>
   (\<And>blks'. d1 = d2 \<Longrightarrow>
             compat_rdy rdy1 rdy2 \<Longrightarrow>
             blks = SCons (WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t))
                             (merge_rdy rdy1 rdy2)) blks' \<Longrightarrow>
            combine_blocks comms blks1 blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induction rule: combine_blocks.cases)
  case (combine_blocks_wait comms' blks1' blks2' blks' rdy1' rdy2' hist hist1 hist2 rdy t)
  have a1: "blks1 = blks1'" "blks2 = blks2'"
       "WaitBlk d1 p1 rdy1 = WaitBlk t hist1 rdy1'"
       "WaitBlk d2 p2 rdy2 = WaitBlk t hist2 rdy2'"
    using combine_blocks_wait(2,3) by auto
  have a2: "d1 = d2"
    using WaitBlk_cong a1(3,4) by blast
  have a3: "WaitBlk d1 p2 rdy2 = WaitBlk t hist2 rdy2'"
    using a2 a1(4) by auto
  have a4: "WaitBlk d1 (\<lambda>\<tau>. ParState (p1 \<tau>) (p2 \<tau>)) (merge_rdy rdy1 rdy2) =
            WaitBlk t (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (merge_rdy rdy1' rdy2')"
    using WaitBlk_eq_combine[OF a1(3) a3] by auto
  show ?case
    apply (rule combine_blocks_wait(9))
    sorry
qed (auto)

lemma combine_blocks_pairE2:
  "combine_blocks comms (SCons (CommBlock ch_type ch v) blks1) (SCons (WaitBlk d p rdy) blks2) blks \<Longrightarrow>
   ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2':
  "combine_blocks comms  (SCons (WaitBlk d p rdy) blks1) (SCons (CommBlock ch_type ch v) blks2) blks \<Longrightarrow>
   ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

type_synonym tid = real

datatype status =
  WAIT | READY | RUNNING


datatype estate =
  Sch (pool:"(real \<times> tid) list") (run_now:tid) (run_prior:real)
| Task (status:status) (entered:nat) (task_prior:real)
| None


fun sched_push :: "tid \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_push t (Sch p rn rp) s = Sch (p @ [(s (CHR ''p''), t)]) rn rp"
| "sched_push t (Task st ent tp) s = undefined"
| "sched_push t None s = undefined"

fun sched_assign :: "tid \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_assign t (Sch p rn rp) s = Sch p t (s (CHR ''p''))"
| "sched_assign t (Task st ent tp) s = undefined"
| "sched_assign t None s = undefined"

fun get_max_default :: "real \<times> tid \<Rightarrow> (real \<times> tid) list \<Rightarrow> real \<times> tid" where
  "get_max_default (prior, t) [] = (prior, t)"
| "get_max_default (prior, t) ((prior2, t2) # rest) =
    (if prior \<ge> prior2 then
       get_max_default (prior, t) rest
     else
       get_max_default (prior2, t2) rest)"

fun get_max :: "(real \<times> tid) list \<Rightarrow> real \<times> tid" where
  "get_max [] = (-1, -1)"
| "get_max ((prior, t) # rest) = get_max_default (prior, t) rest"

fun del_proc :: "(real \<times> tid) list \<Rightarrow> tid \<Rightarrow> (real \<times> tid) list" where
  "del_proc [] t = []"
| "del_proc ((prior, t) # rest) t2 =
    (if t = t2 then rest
     else (prior, t) # del_proc rest t)"

fun sched_get_max :: "estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_get_max (Sch p rn rp) s =
    (let (prior, t) = get_max p in Sch (del_proc p t) t prior)"
| "sched_get_max (Task st ent tp) s = undefined"
| "sched_get_max None s = undefined"

fun sched_clear :: "estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_clear (Sch p rn rp) s = Sch [] (-1) (-1)"
| "sched_clear (Task st ent tp) s = undefined"
| "sched_clear None s = undefined"

fun sched_del_proc :: "tid \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_del_proc t (Sch p rn rp) s = Sch (del_proc p t) rn rp"
| "sched_del_proc t (Task st ent tp) s = undefined"
| "sched_del_proc t None s = undefined"

definition req_ch :: "tid \<Rightarrow> string" where
  "req_ch tid = (
    if tid = 1 then ''reqProcessor1''
    else if tid = 2 then ''reqProcessor2''
    else if tid = 3 then ''reqProcessor3''
    else undefined)"

definition preempt_ch :: "tid \<Rightarrow> string" where
  "preempt_ch tid = (
    if tid = 1 then ''preempt1''
    else if tid = 2 then ''preempt2''
    else if tid = 3 then ''preempt3''
    else undefined)"

definition run_ch :: "tid \<Rightarrow> string" where
  "run_ch tid = (
    if tid = 1 then ''run1''
    else if tid = 2 then ''run2''
    else if tid = 3 then ''run3''
    else undefined)"

definition free_ch :: "tid \<Rightarrow> string" where
  "free_ch tid = (
    if tid = 1 then ''free1''
    else if tid = 2 then ''free2''
    else if tid = 3 then ''free3''
    else undefined)"

definition exit_ch :: "tid \<Rightarrow> string" where
  "exit_ch tid = (
    if tid = 1 then ''exit1''
    else if tid = 2 then ''exit2''
    else if tid = 3 then ''exit3''
    else undefined)"

definition dispatch_ch :: "tid \<Rightarrow> string" where
  "dispatch_ch tid = (
    if tid = 1 then ''dis1''
    else if tid = 2 then ''dis2''
    else if tid = 3 then ''dis3''
    else undefined)"

coinductive dispatch_assn :: "tid \<Rightarrow> state \<Rightarrow> estate stassn" where
  "init_t' = start_s (CHR ''t'') \<Longrightarrow>
   init_t' < 0.045 \<Longrightarrow>
   wt \<le> 0.045 - init_t' \<Longrightarrow>
   blk1 = WaitBlk (ereal wt) (\<lambda>t. EState (None, start_s(CHR ''t'' := init_t' + t))) ({}, {}) \<Longrightarrow>
   dispatch_assn i (start_s(CHR ''t'' := init_t' + wt)) rest \<Longrightarrow>
   dispatch_assn i start_s (SCons blk1 rest)"
| "init_t' = start_s (CHR ''t'') \<Longrightarrow>
   init_t' = 0.045 \<Longrightarrow>
   blk1 = OutBlock (dispatch_ch i) 0 \<Longrightarrow>
   dispatch_assn i (start_s(CHR ''t'' := 0)) rest \<Longrightarrow>
   dispatch_assn i start_s (SCons blk1 rest)"
thm dispatch_assn.coinduct
thm dispatch_assn.cases

coinductive task_assn :: "tid \<Rightarrow> string \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate stassn" where
  "start_es = Task WAIT ent tp \<Longrightarrow>
   wt > 0 \<Longrightarrow>
   blk1 = WaitBlk (ereal wt) (\<lambda>_. EState (start_es, start_s)) ({}, {dispatch_ch i}) \<Longrightarrow>
   task_assn i ''p1'' start_es start_s rest \<Longrightarrow>
   task_assn i ''p1'' start_es start_s (SCons blk1 rest)"
| "start_es = Task WAIT ent tp \<Longrightarrow>
   blk1 = InBlock (dispatch_ch i) 0 \<Longrightarrow>
   task_assn i ''p2'' (Task READY 0 tp) (start_s(CHR ''t'' := 0)) rest \<Longrightarrow>
   task_assn i ''p1'' start_es start_s (SCons blk1 rest)"
| "start_es = Task READY ent tp \<Longrightarrow>
   blk1 = OutBlock (req_ch i) tp \<Longrightarrow>
   task_assn i ''p3'' start_es start_s rest \<Longrightarrow>
   task_assn i ''p2'' start_es start_s (SCons blk1 rest)"
| "start_es = Task READY ent tp \<Longrightarrow>
   init_t = start_s (CHR ''t'') \<Longrightarrow>
   init_t < 0.045 \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   blk1 = WaitBlk (ereal wt) (\<lambda>t. EState (start_es, start_s(CHR ''t'' := init_t + t))) ({}, {run_ch i}) \<Longrightarrow>
   task_assn i ''p3'' start_es (start_s(CHR ''t'' := init_t + wt)) rest \<Longrightarrow>
   task_assn i ''p3'' start_es start_s (SCons blk1 rest)"
| "start_es = Task READY ent tp \<Longrightarrow>
   init_t = start_s (CHR ''t'') \<Longrightarrow>
   init_t = 0.045 \<Longrightarrow>
   blk1 = OutBlock (exit_ch i) 0 \<Longrightarrow>
   task_assn i ''p1'' start_es start_s rest \<Longrightarrow>
   task_assn i ''p3'' start_es start_s (SCons blk1 rest)"
| "start_es = Task READY 0 tp \<Longrightarrow>
   blk1 = InBlock (run_ch i) 0 \<Longrightarrow>
   task_assn i ''p4'' (Task RUNNING 1 tp) (start_s(CHR ''c'' := 0)) rest \<Longrightarrow>
   task_assn i ''p3'' start_es start_s (SCons blk1 rest)"
| "start_es = Task READY 1 tp \<Longrightarrow>
   blk1 = InBlock (run_ch i) 0 \<Longrightarrow>
   task_assn i ''p4'' (Task RUNNING 1 tp) start_s rest \<Longrightarrow>
   task_assn i ''p3'' start_es start_s (SCons blk1 rest)"
| "start_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = start_s (CHR ''t'') \<Longrightarrow>
   init_c = start_s (CHR ''c'') \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   wt \<le> 0.01 - init_c \<Longrightarrow>
   wt > 0 \<Longrightarrow>
   blk1 = WaitBlk (ereal d)
      (\<lambda>t. EState (start_es, start_s(CHR ''t'' := init_t + t,
                                     CHR ''c'' := init_c + t))) ({}, {preempt_ch i}) \<Longrightarrow>
   task_assn i ''p4'' start_es (start_s(CHR ''t'' := init_t + wt,
                                        CHR ''c'' := init_c + wt)) rest \<Longrightarrow>
   task_assn i ''p4'' start_es start_s (SCons blk1 rest)"
| "start_es = Task RUNNING 1 tp \<Longrightarrow>
   blk1 = InBlock (preempt_ch i) 0 \<Longrightarrow>
   task_assn i ''p2'' (Task READY 1 tp) start_s rest \<Longrightarrow>
   task_assn i ''p4'' start_es start_s (SCons blk1 rest)"
| "start_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = start_s (CHR ''t'') \<Longrightarrow>
   init_c = start_s (CHR ''c'') \<Longrightarrow>
   init_c = 0.01 \<or> init_t = 0.045 \<Longrightarrow>
   blk1 = OutBlock (free_ch i) 0 \<Longrightarrow>
   task_assn i ''p1'' (Task READY 1 tp) start_s rest \<Longrightarrow>
   task_assn i ''p4'' start_es start_s (SCons blk1 rest)"

coinductive task_dis_assn :: "tid \<Rightarrow> string \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate stassn" where
  "start_es = Task WAIT ent tp \<Longrightarrow>
   init_t' = dis_s (CHR ''t'') \<Longrightarrow>
   init_t' < 0.045 \<Longrightarrow>
   wt \<le> 0.045 - init_t' \<Longrightarrow>
   blk1 = WaitBlk (ereal wt) (\<lambda>t. ParState
      (EState (None, dis_s(CHR ''t'' := init_t' + t)))
      (EState (start_es, task_s))) ({}, {dispatch_ch i}) \<Longrightarrow>
   task_dis_assn i ''p1'' (dis_s(CHR ''t'' := init_t' + wt)) start_es task_s rest \<Longrightarrow>
   task_dis_assn i ''p1'' dis_s start_es task_s (SCons blk1 rest)"
| "start_es = Task WAIT ent tp \<Longrightarrow>
   init_t' = dis_s (CHR ''t'') \<Longrightarrow>
   init_t' = 0.045 \<Longrightarrow>
   blk1 = IOBlock (dispatch_ch i) 0 \<Longrightarrow>
   task_dis_assn i ''p2'' (dis_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0)) rest \<Longrightarrow>
   task_dis_assn i ''p1'' dis_s start_es task_s (SCons blk1 rest)"
| "start_es = Task READY ent tp \<Longrightarrow>
   blk1 = OutBlock (req_ch i) tp \<Longrightarrow>
   task_dis_assn i ''p3'' dis start_es task_s rest \<Longrightarrow>
   task_dis_assn i ''p2'' dis start_es task_s (SCons blk1 rest)"
| "start_es = Task READY ent tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_t' = dis_s (CHR ''t'') \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   wt \<le> 0.045 - init_t' \<Longrightarrow>
   blk1 = WaitBlk (ereal wt) (\<lambda>t. ParState
      (EState (None, dis_t(CHR ''t'' := init_t' + t)))
      (EState (start_es, task_s(CHR ''t'' := init_t + t)))) ({}, {run_ch i}) \<Longrightarrow>
   task_dis_assn i ''p3'' (dis_s(CHR ''t'' := init_t' + wt))
      start_es (task_s(CHR ''t'' := init_t + wt)) rest \<Longrightarrow>
   task_dis_assn i ''p3'' dis_s start_es task_s (SCons blk1 rest)"
| "start_es = Task READY ent tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_t = 0.045 \<Longrightarrow>
   blk1 = OutBlock (exit_ch i) 0 \<Longrightarrow>
   task_dis_assn i ''p1'' dis_s start_es task_s rest \<Longrightarrow>
   task_dis_assn i ''p3'' dis_s start_es task_s (SCons blk1 rest)"
| "start_es = Task READY 0 tp \<Longrightarrow>
   blk1 = InBlock (run_ch i) 0 \<Longrightarrow>
   task_dis_assn i ''p4'' dis_s (Task RUNNING 1 tp) (task_s(CHR ''c'' := 0)) rest \<Longrightarrow>
   task_dis_assn i ''p3'' dis_s start_es task_s (SCons blk1 rest)"
| "start_es = Task READY 1 tp \<Longrightarrow>
   blk1 = InBlock (run_ch i) 0 \<Longrightarrow>
   task_dis_assn i ''p4'' dis_s (Task RUNNING 1 tp) task_s rest \<Longrightarrow>
   task_dis_assn i ''p3'' dis_s start_es task_s (SCons blk1 rest)"
| "start_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_c = task_s (CHR ''c'') \<Longrightarrow>
   init_t' = dis_s (CHR ''t'') \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   wt \<le> 0.01 - init_c \<Longrightarrow>
   wt \<le> 0.045 - init_t' \<Longrightarrow>
   wt > 0 \<Longrightarrow>
   blk1 = WaitBlk (ereal d) (\<lambda>t. ParState
      (EState (None, dis_s(CHR ''t'' := init_t' + t)))
      (EState (start_es, task_s(CHR ''t'' := init_t + t, CHR ''c'' := init_c + t))))
      ({}, {preempt_ch i}) \<Longrightarrow>
   task_dis_assn i ''p4'' dis_s start_es (task_s(CHR ''t'' := init_t + wt,
                                                 CHR ''c'' := init_c + wt)) rest \<Longrightarrow>
   task_dis_assn i ''p4'' dis_s start_es task_s (SCons blk1 rest)"
| "start_es = Task RUNNING 1 tp \<Longrightarrow>
   blk1 = InBlock (preempt_ch i) 0 \<Longrightarrow>
   task_dis_assn i ''p2'' dis_s (Task READY 1 tp) task_s rest \<Longrightarrow>
   task_dis_assn i ''p4'' dis_s start_es task_s (SCons blk1 rest)"
| "start_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_c = task_s (CHR ''c'') \<Longrightarrow>
   init_c = 0.01 \<or> init_t = 0.045 \<Longrightarrow>
   blk1 = OutBlock (free_ch i) 0 \<Longrightarrow>
   task_dis_assn i ''p1'' dis_s (Task READY 1 tp) task_s rest \<Longrightarrow>
   task_dis_assn i ''p4'' dis_s start_es task_s (SCons blk1 rest)"
thm task_dis_assn.coinduct

theorem combine_task_dis:
  "dispatch_assn i (\<lambda>_. 0) blks1 \<Longrightarrow>
   task_assn i ''p1'' (Task WAIT 0 tp) (\<lambda>_. 0) blks2 \<Longrightarrow>
   combine_blocks {dispatch_ch i} blks1 blks2 blks \<Longrightarrow>
   task_dis_assn i ''p1'' (\<lambda>_. 0) (Task WAIT 0 tp) (\<lambda>_. 0) blks"
proof (coinduction rule: task_dis_assn.coinduct)
  case task_dis_assn
  from task_dis_assn(1) show ?case
  proof (cases rule: dispatch_assn.cases)
    case (1 init_t' wt1 blk1 rest1)
    note d1 = 1
    from task_dis_assn(2) show ?thesis
    proof (cases rule: task_assn.cases)
      case (1 ent tp wt2 blk2 rest2)
      note t1 = 1
      show ?thesis
        thm d1 t1
        thm task_dis_assn
        using task_dis_assn(3)
        unfolding d1(1) t1(1) d1(5) t1(4)
        sorry
    next
      case (2 ent tp blk1 rest)
      note t2 = 2
      show ?thesis 
        thm t2 d1
        using task_dis_assn(3)
        unfolding d1(1) t2(1) d1(5) t2(3)
        by(auto elim!:combine_blocks_pairE2')
    next
      case (3 ent tp blk1 rest)
      then show ?thesis by auto
    next
      case (4 ent tp init_t wt blk1 rest)
      then show ?thesis by auto
    next
      case (5 ent tp init_t blk1 rest)
      then show ?thesis by auto
    next
      case (6 tp blk1 rest)
      then show ?thesis by auto
    next
      case (7 tp blk1 rest)
      then show ?thesis by auto
    next
      case (8 tp init_t init_c wt blk1 d rest)
      then show ?thesis by auto
    next
      case (9 tp blk1 rest)
      then show ?thesis by auto
    next
      case (10 tp init_t init_c blk1 rest)
      then show ?thesis by auto
    qed
  next
    case (2 init_t' blk1 rest1)
    note d2 = 2
    from task_dis_assn(2) show ?thesis
    proof (cases rule: task_assn.cases)
      case (1 ent tp wt blk1 rest)
      note t1 = 1
      show ?thesis 
        using task_dis_assn(3)
        unfolding d2(1) t1(1) d2(4) t1(4)
        by(auto elim!:combine_blocks_pairE2)
    next
      case (2 ent tp blk1 rest)
      note t2 = 2
      show ?thesis 
        thm d2
        thm t2
        using task_dis_assn(3)
        unfolding d2(1) t2(1) d2(4) t2(3)
        sorry
    next
      case (3 ent tp blk1 rest)
      then show ?thesis by auto
    next
      case (4 ent tp init_t wt blk1 rest)
      then show ?thesis by auto
    next
      case (5 ent tp init_t blk1 rest)
      then show ?thesis by auto
    next
      case (6 tp blk1 rest)
      then show ?thesis by auto
    next
      case (7 tp blk1 rest)
      then show ?thesis by auto
    next
      case (8 tp init_t init_c wt blk1 d rest)
      then show ?thesis by auto
    next
      case (9 tp blk1 rest)
      then show ?thesis by auto
    next
      case (10 tp init_t init_c blk1 rest)
      then show ?thesis by auto
    qed
  qed
qed


end
