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
  have a2: "d1 = d2" "rdy1 = rdy1'" "rdy2 = rdy2'" "d1 = t" "d2 = t"
    using WaitBlk_cong a1(3,4) by blast+
  have a3: "WaitBlk d1 p2 rdy2 = WaitBlk t hist2 rdy2'"
    using a2 a1(4) by auto
  have a4: "WaitBlk d1 (\<lambda>\<tau>. ParState (p1 \<tau>) (p2 \<tau>)) (merge_rdy rdy1 rdy2) =
            WaitBlk t (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (merge_rdy rdy1' rdy2')"
    using WaitBlk_eq_combine[OF a1(3) a3] by auto
  show ?case
    using combine_blocks_wait a1 a2 a4 by auto
qed (auto)

lemma combine_blocks_waitCommE:
  assumes "ch \<in> comms"
  shows
    "combine_blocks comms (SCons (WaitBlk d1 p1 rdy1) blks1)
                          (SCons (CommBlock ch_type ch v) blks2) blks \<Longrightarrow> P"
  apply (induction rule: combine_blocks.cases)
  using assms by auto

lemma combine_blocks_waitCommE':
  assumes "ch \<in> comms"
  shows
    "combine_blocks comms (SCons (CommBlock ch_type ch v) blks1) 
                          (SCons (WaitBlk d1 p1 rdy1) blks2) blks \<Longrightarrow> P"
  apply (induction rule: combine_blocks.cases)
  using assms by auto

lemma combine_blocks_waitCommE2:
  assumes "ch \<notin> comms"
  shows
    "combine_blocks comms (SCons (WaitBlk d1 p1 rdy1) blks1)
                          (SCons (CommBlock ch_type ch v) blks2) blks \<Longrightarrow>
     (\<And>blks'. blks = SCons (CommBlock ch_type ch v) blks' \<Longrightarrow>
              combine_blocks comms (SCons (WaitBlk d1 p1 rdy1) blks1) blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induction rule: combine_blocks.cases)
  case (combine_blocks_unpair2 ch' comms' blks1' blks2' blks' ch_type' v')
  have a1: "blks2 = blks2'" "CommBlock ch_type ch v = CommBlock ch_type' ch' v'"
    using combine_blocks_unpair2(3) by auto
  have a2: "ch_type = ch_type'" "ch = ch'" "v = v'"
    using a1 by auto
  show ?case
    using combine_blocks_unpair2 a1 a2 by auto
qed (auto simp: assms)

lemma combine_blocks_waitCommE2':
  assumes "ch \<notin> comms"
  shows
    "combine_blocks comms (SCons (CommBlock ch_type ch v) blks1)
                          (SCons (WaitBlk d1 p1 rdy1) blks2) blks \<Longrightarrow>
     (\<And>blks'. blks = SCons (CommBlock ch_type ch v) blks' \<Longrightarrow>
              combine_blocks comms blks1 (SCons (WaitBlk d1 p1 rdy1) blks2)  blks' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induction rule: combine_blocks.cases)
  case (combine_blocks_unpair2 ch' comms' blks1' blks2' blks' ch_type' v')
  have a1: "blks2 = blks2'" "CommBlock ch_type ch v = CommBlock ch_type' ch' v'"
    using combine_blocks_unpair2(3) by auto
  have a2: "ch_type = ch_type'" "ch = ch'" "v = v'"
    using a1 by auto
  show ?case
    using combine_blocks_unpair2 a1 a2 by auto
qed (auto simp: assms)

lemma combine_blocks_pairE:
  assumes "ch1 \<in> comms"
    and "ch2 \<in> comms"
  shows "combine_blocks comms (SCons (CommBlock ch_type1 ch1 v1) blks1) (SCons (CommBlock ch_type2 ch2 v2) blks2) blks \<Longrightarrow>
    (\<And>blks'. ch1 = ch2 \<Longrightarrow> v1 = v2 \<Longrightarrow> (ch_type1 = In \<and> ch_type2 = Out \<or> ch_type1 = Out \<and> ch_type2 = In) \<Longrightarrow>
   blks = SCons (IOBlock ch1 v1) blks' \<Longrightarrow> combine_blocks comms blks1 blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto simp:assms)

lemma combine_blocks_unpairE1:
  assumes "ch1 \<notin> comms "
    and "ch2 \<in> comms "
  shows "combine_blocks comms (SCons (CommBlock ch_type1 ch1 v1) blks1) (SCons (CommBlock ch_type2 ch2 v2) blks2) blks \<Longrightarrow>
   (\<And>blks'. blks = SCons (CommBlock ch_type1 ch1 v1) blks' \<Longrightarrow>
           combine_blocks comms blks1 (SCons (CommBlock ch_type2 ch2 v2) blks2) blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto simp:assms)

lemma combine_blocks_unpairE1':
  assumes "ch1 \<in> comms"  
  and "ch2 \<notin> comms"
shows "combine_blocks comms (SCons (CommBlock ch_type1 ch1 v1) blks1) (SCons (CommBlock ch_type2 ch2 v2) blks2) blks \<Longrightarrow>
   (\<And>blks'. blks = SCons (CommBlock ch_type2 ch2 v2) blks' \<Longrightarrow>
           combine_blocks comms (SCons (CommBlock ch_type1 ch1 v1) blks1) blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: combine_blocks.cases)
  using assms by auto

lemma combine_blocks_unpairE2:
  assumes "ch1 \<notin> comms" 
    and " ch2 \<notin> comms"
  shows "combine_blocks comms (SCons (CommBlock ch_type1 ch1 v1) blks1) (SCons (CommBlock ch_type2 ch2 v2 ) blks2) blks \<Longrightarrow>
   (\<And>blks'. blks = SCons (CommBlock ch_type1 ch1 v1) blks' \<Longrightarrow>
           combine_blocks comms blks1 (SCons (CommBlock ch_type2 ch2 v2) blks2) blks' \<Longrightarrow> P) \<Longrightarrow>
   (\<And>blks'. blks = SCons (CommBlock ch_type2 ch2 v2) blks' \<Longrightarrow>
           combine_blocks comms (SCons (CommBlock ch_type1 ch1 v1) blks1) blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto simp add:assms)

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
   blk1 = WaitBlk (ereal wt)
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
   blk1 = WaitBlk (ereal wt) (\<lambda>t. ParState
      (EState (None, dis_s(CHR ''t'' := init_t' + t)))
      (EState (start_es, task_s(CHR ''t'' := init_t + t, CHR ''c'' := init_c + t))))
      ({}, {preempt_ch i}) \<Longrightarrow>
   task_dis_assn i ''p4'' (dis_s(CHR ''t'' := init_t' + wt)) start_es (task_s(CHR ''t'' := init_t + wt,
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
  assumes "i \<in> {1,2,3}"
  shows
    "dispatch_assn i dis_s blks1 \<Longrightarrow>
     task_assn i pc start_es task_s blks2 \<Longrightarrow>
     combine_blocks {dispatch_ch i} blks1 blks2 blks \<Longrightarrow>
     task_dis_assn i pc dis_s start_es task_s blks"
proof (coinduction arbitrary: pc dis_s start_es task_s blks1 blks2 blks rule: task_dis_assn.coinduct)
  have comm_in: "dispatch_ch i \<in> {dispatch_ch i}"
    by auto
  have req_not_in: "req_ch i \<notin> {dispatch_ch i}"
    unfolding req_ch_def dispatch_ch_def
    using assms by auto
  have exit_not_in: "exit_ch i \<notin> {dispatch_ch i}"
    unfolding exit_ch_def dispatch_ch_def
    using assms by auto
  have run_not_in: "run_ch i \<notin> {dispatch_ch i}"
    unfolding run_ch_def dispatch_ch_def
    using assms by auto
  have preempt_not_in: "preempt_ch i \<notin> {dispatch_ch i}"
    unfolding preempt_ch_def dispatch_ch_def
    using assms by auto
  have free_not_in: "free_ch i \<notin> {dispatch_ch i}"
    unfolding free_ch_def dispatch_ch_def
    using assms by auto
  case task_dis_assn
  from task_dis_assn(1) show ?case
  proof (cases rule: dispatch_assn.cases)
    case (1 init_t' wt1 blk1' rest1)
    note d1 = 1
    from task_dis_assn(2) show ?thesis
    proof (cases rule: task_assn.cases)
      case (1 ent' tp' wt2 blk2' rest2)
      note t1 = 1
      obtain rest where rest:
        "ereal wt1 = ereal wt2"
        "blks = SCons (WaitBlk (ereal wt1) (\<lambda>t. ParState
            (EState (estate.None, dis_s(CHR ''t'' := init_t' + t)))
            (EState (start_es, task_s))) (merge_rdy ({}, {}) ({}, {dispatch_ch i}))) rest"
        "combine_blocks {dispatch_ch i} rest1 rest2 rest"
        using task_dis_assn(3)[unfolded d1(1) t1(2) d1(5) t1(5)]
        apply (elim combine_blocks_waitE) by blast
      then show ?thesis
        using d1 t1 by auto
    next
      case (2 ent tp blk2' rest2)
      note t2 = 2
      from task_dis_assn(3)[unfolded d1(1) t2(2) d1(5) t2(4)]
      show ?thesis
        by (elim combine_blocks_waitCommE[OF comm_in])
    next
      case (3 ent tp blk2' rest2)
      note t3 = 3
      obtain rest where rest:
        "blks = SCons (OutBlock (req_ch i) tp) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (WaitBlk (ereal wt1) (\<lambda>t. EState (estate.None, dis_s(CHR ''t'' := init_t' + t)))
                          ({}, {})) rest1)
          rest2 rest"
        using task_dis_assn(3)[unfolded d1(1) t3(2) d1(5) t3(4)]
        apply (elim combine_blocks_waitCommE2[OF req_not_in]) by blast
      then show ?thesis
        using t3 d1 task_dis_assn(1) by auto
    next
      case (4 ent' tp' init_t2 wt2 blk2' rest2)
      note t4 = 4
      obtain rest where
        "ereal wt1 = ereal wt2"
        "blks = SCons (WaitBlk (ereal wt1) (\<lambda>t. ParState
            (EState (estate.None, dis_s(CHR ''t'' := init_t' + t)))
            (EState (start_es, task_s(CHR ''t'' := init_t2 + t))))
            (merge_rdy ({}, {}) ({}, {run_ch i}))) rest"
        "combine_blocks {dispatch_ch i} rest1 rest2 rest"
        using task_dis_assn(3)[unfolded d1(1) t4(2) d1(5) t4(7)]
        apply (elim combine_blocks_waitE) by blast
      then show ?thesis
        using t4 d1 by auto
    next
      case (5 ent tp init_t blk2' rest2)
      note t5 = 5
      obtain rest where rest:
        "blks = SCons (OutBlock (exit_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (WaitBlk (ereal wt1) (\<lambda>t. EState (estate.None, dis_s(CHR ''t'' := init_t' + t)))
                          ({}, {})) rest1)
          rest2 rest"
        using task_dis_assn(3)[unfolded d1(1) t5(2) d1(5) t5(6)]
        apply (elim combine_blocks_waitCommE2[OF exit_not_in]) by blast
      then show ?thesis
        using t5 d1 task_dis_assn(1) by auto
    next
      case (6 tp blk2' rest2)
      note t6 = 6
      obtain rest where rest:
        "blks = SCons (InBlock (run_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (WaitBlk (ereal wt1) (\<lambda>t. EState (estate.None, dis_s(CHR ''t'' := init_t' + t)))
                          ({}, {})) rest1)
          rest2 rest"
        using task_dis_assn(3)[unfolded d1(1) t6(2) d1(5) t6(4)]
        apply (elim combine_blocks_waitCommE2[OF run_not_in]) by blast
      then show ?thesis
        using t6 d1 task_dis_assn(1) by auto
    next
      case (7 tp blk1 rest2)
      note t7 = 7      
      obtain rest where rest:
        "blks = SCons (InBlock (run_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (WaitBlk (ereal wt1) (\<lambda>t. EState (estate.None, dis_s(CHR ''t'' := init_t' + t)))
                          ({}, {})) rest1)
          rest2 rest"
        using task_dis_assn(3)[unfolded d1(1) t7(2) d1(5) t7(4)]
        apply (elim combine_blocks_waitCommE2[OF run_not_in]) by blast
      then show ?thesis
        using t7 d1 task_dis_assn(1) by auto
    next
      case (8 tp init_t init_c wt2 blk2' rest2)
      note t8 = 8
      thm d1
      obtain rest where rest:
        "ereal wt1 = ereal wt2"
        "blks = SCons (WaitBlk (ereal wt1) (\<lambda>t. ParState
            (EState (estate.None, dis_s(CHR ''t'' := init_t' + t)))
            (EState (start_es, task_s(CHR ''t'' := init_t + t, CHR ''c'' := init_c + t)))) (merge_rdy ({}, {}) ({}, {preempt_ch i}))) rest"
        "combine_blocks {dispatch_ch i} rest1 rest2 rest"
        using task_dis_assn(3) [unfolded d1(1) d1(5) t8(2) t8(9)]
        apply (elim combine_blocks_waitE) by blast
      then show ?thesis using d1 t8 by auto
    next
      case (9 tp blk2' rest2)
      note t9 = 9
      thm d1
      obtain rest where rest:
        "blks = SCons (InBlock (preempt_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (WaitBlk (ereal wt1) (\<lambda>t. EState (estate.None, dis_s(CHR ''t'' := init_t' + t)))
                          ({}, {})) rest1)
          rest2 rest"
        using task_dis_assn(3)[unfolded d1(1) t9(2) d1(5) t9(4)]
        apply (elim combine_blocks_waitCommE2[OF preempt_not_in]) by blast
      then show ?thesis
        using d1 t9 task_dis_assn by auto
    next
      case (10 tp init_t init_c blk2' rest2)
      note t10 = 10
      obtain rest where rest:
        "blks = SCons (OutBlock (free_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (WaitBlk (ereal wt1) (\<lambda>t. EState (estate.None, dis_s(CHR ''t'' := init_t' + t)))
                          ({}, {})) rest1)
          rest2 rest"
        using task_dis_assn(3)[unfolded d1(1) t10(2) d1(5) t10(7)]
        apply (elim combine_blocks_waitCommE2[OF free_not_in]) by blast
      then show ?thesis
        using d1 t10 task_dis_assn by auto
    qed
  next
    case (2 init_t' blk1' rest1)
    note d2 = 2
    from task_dis_assn(2) show ?thesis
    proof (cases rule: task_assn.cases)
      case (1 ent tp wt blk2' rest2)
      note t1 = 1
      from task_dis_assn(3)[unfolded d2(1) t1(2) d2(4) t1(5)]
      show ?thesis
        by (elim combine_blocks_waitCommE'[OF comm_in])
    next
      case (2 ent tp blk2' rest2)
      note t2 = 2
      obtain rest where rest:
        "blks = SCons (IOBlock (dispatch_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          rest1 rest2 rest"
        using task_dis_assn(3)[unfolded d2(1,4) t2(2,4)]
        apply(elim combine_blocks_pairE[OF comm_in comm_in]) by blast
      then show ?thesis 
        using d2 t2 task_dis_assn by auto
    next
      case (3 ent tp blk2' rest2)
      note t3=3
      obtain rest where rest:
        "blks = SCons (OutBlock (req_ch i) tp) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (OutBlock (dispatch_ch i) 0) rest1)
          rest2 rest"
        using task_dis_assn(3) [unfolded d2(1,4) t3(2,4)]
        apply(elim combine_blocks_unpairE1'[OF comm_in req_not_in]) by blast
      then show ?thesis 
        using task_dis_assn d2 t3 by auto
    next
      case (4 ent tp init_t wt blk1 rest)
      note t4 = 4
      from task_dis_assn(3)[unfolded d2(1,4) t4(2,7)]
      show ?thesis 
        by (elim combine_blocks_waitCommE'[OF comm_in])
    next
      case (5 ent tp init_t blk2' rest2)
      note t5 = 5
      obtain rest where rest:
        "blks = SCons (OutBlock (exit_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (OutBlock (dispatch_ch i) 0) rest1)
          rest2 rest"
        using task_dis_assn(3) [unfolded d2(1,4) t5(2,6)]
        apply(elim combine_blocks_unpairE1'[OF comm_in exit_not_in]) by blast
      then show ?thesis using task_dis_assn d2 t5 by auto
    next
      case (6 tp blk2' rest2)
      note t6 = 6
      obtain rest where rest:
        "blks = SCons (InBlock (run_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (OutBlock (dispatch_ch i) 0) rest1)
          rest2 rest"
        using task_dis_assn(3) [unfolded d2(1,4) t6(2,4)]
        apply(elim combine_blocks_unpairE1'[OF comm_in run_not_in]) by blast
      then show ?thesis using task_dis_assn d2 t6 by auto
    next
      case (7 tp blk2' rest2)
      note t7 = 7
      obtain rest where rest:
        "blks = SCons (InBlock (run_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (OutBlock (dispatch_ch i) 0) rest1)
          rest2 rest"
        using task_dis_assn(3) [unfolded d2(1,4) t7(2,4)]
        apply(elim combine_blocks_unpairE1'[OF comm_in run_not_in]) by blast
      then show ?thesis using task_dis_assn d2 t7 by auto
    next
      case (8 tp init_t init_c wt blk1 rest)
      note t8 = 8
      from task_dis_assn(3)[unfolded d2(1,4) t8(2,9)]
      show ?thesis 
        by (elim combine_blocks_waitCommE'[OF comm_in])
    next
      case (9 tp blk2' rest2)
      note t9 = 9
      obtain rest where rest:
        "blks = SCons (InBlock (preempt_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (OutBlock (dispatch_ch i) 0) rest1)
          rest2 rest"
        using task_dis_assn(3) [unfolded d2(1,4) t9(2,4)]
        apply(elim combine_blocks_unpairE1'[OF comm_in preempt_not_in]) by blast
      then show ?thesis using task_dis_assn d2 t9 by auto
    next
      case (10 tp init_t init_c blk2' rest2)
      note t10 = 10
      obtain rest where rest:
        "blks = SCons (OutBlock (free_ch i) 0) rest"
        "combine_blocks {dispatch_ch i}
          (SCons (OutBlock (dispatch_ch i) 0) rest1)
          rest2 rest"
        using task_dis_assn(3) [unfolded d2(1,4) t10(2,7)]
        apply(elim combine_blocks_unpairE1'[OF comm_in free_not_in]) by blast
      then show ?thesis using task_dis_assn d2 t10 by auto
    qed
qed
qed

definition sch :: "estate proc" where
"sch = EChoice 
[((req_ch 1)[?]CHR ''p'',
        (CHR ''i'' ::= (\<lambda>_ . 1));
         IF (\<lambda> (a,s) . run_prior a \<ge> s (CHR ''p'')) 
           THEN Basic (sched_push 1) 
           ELSE (IF (\<lambda> (a,s) . run_now a \<noteq> -1) 
                   THEN (Cm (preempt_ch 1 [!] (\<lambda>_. 0))) 
                   ELSE Skip 
                 FI);
                 Basic (sched_assign 1); 
                 Cm (run_ch 1[!](\<lambda>_ . 0)) 
         FI),
 ((free_ch 1)[?]CHR ''F'',
        (CHR ''i'' ::= (\<lambda>_ . 1));
         IF (\<lambda> (a,s) . length (pool a) > 0) 
           THEN (Basic (sched_get_max) ; Cm (run_ch 1[!](\<lambda>_ . 0))) 
           ELSE Basic sched_clear 
         FI),
 ((exit_ch 1)[?]CHR ''E'',
        (CHR ''i'' ::= (\<lambda>_ . 1)); 
         Basic (sched_del_proc 1)),
 ((req_ch 2)[?]CHR ''p'',
        (CHR ''i'' ::= (\<lambda>_ . 2));
         IF (\<lambda> (a,s) . run_prior a \<ge> s (CHR ''p'')) 
           THEN Basic (sched_push 2) 
           ELSE (IF (\<lambda> (a,s) . run_now a \<noteq> -1) 
                   THEN (Cm (preempt_ch 2 [!] (\<lambda>_. 0))) 
                   ELSE Skip 
                 FI);
                 Basic (sched_assign 2); 
                 Cm (run_ch 2[!](\<lambda>_ . 0)) 
         FI),
 ((free_ch 2)[?]CHR ''F'',
        (CHR ''i'' ::= (\<lambda>_ . 2));
         IF (\<lambda> (a,s) . length (pool a) > 0) 
           THEN (Basic (sched_get_max) ; Cm (run_ch 2[!](\<lambda>_ . 0))) 
           ELSE Basic sched_clear 
         FI),
 ((exit_ch 2)[?]CHR ''E'',
        (CHR ''i'' ::= (\<lambda>_ . 2)); 
         Basic (sched_del_proc 2)),
 ((req_ch 3)[?]CHR ''p'',
        (CHR ''i'' ::= (\<lambda>_ . 3));
         IF (\<lambda> (a,s) . run_prior a \<ge> s (CHR ''p'')) 
           THEN Basic (sched_push 3) 
           ELSE (IF (\<lambda> (a,s) . run_now a \<noteq> -1) 
                   THEN (Cm (preempt_ch 3 [!] (\<lambda>_. 0))) 
                   ELSE Skip 
                 FI);
                 Basic (sched_assign 3); 
                 Cm (run_ch 3[!](\<lambda>_ . 0)) 
         FI),
 ((free_ch 3)[?]CHR ''F'',
        (CHR ''i'' ::= (\<lambda>_ . 3));
         IF (\<lambda> (a,s) . length (pool a) > 0) 
           THEN (Basic (sched_get_max) ; Cm (run_ch 3[!](\<lambda>_ . 0))) 
           ELSE Basic sched_clear 
         FI),
 ((exit_ch 3)[?]CHR ''E'',
        (CHR ''i'' ::= (\<lambda>_ . 3)); 
         Basic (sched_del_proc 3))]"


coinductive sch_assn :: "string \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate stassn" where
  "sch_es = Sch p r_now r_prior \<Longrightarrow>
   wt > 0 \<Longrightarrow>
   blk1 = WaitBlk (ereal wt) (\<lambda>_. EState (sch_es, sch_s)) ({}, image req_ch {1,2,3} \<union> image free_ch {1,2,3} \<union> image exit_ch {1,2,3}) \<Longrightarrow>
   sch_assn ''q0'' sch_es sch_s rest \<Longrightarrow>
   sch_assn ''q0'' sch_es sch_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   blk1 = InBlock (req_ch i) prior \<Longrightarrow>
   i \<in> {1,2,3}\<Longrightarrow>
   sch_assn ''q1'' sch_es (sch_s(CHR ''p'' := prior, CHR ''i'' := i)) rest \<Longrightarrow>
   sch_assn ''q0'' sch_es sch_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   i = sch_s CHR ''i'' \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior \<ge> prior \<Longrightarrow>
   sch_assn ''q0'' (sched_push i sch_es sch_s) sch_s rest \<Longrightarrow>
   sch_assn ''q1'' sch_es sch_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   i = sch_s CHR ''i'' \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior < prior \<Longrightarrow>
   r_now \<noteq> -1 \<Longrightarrow>
   blk1 = OutBlock (preempt_ch r_now) 0 \<Longrightarrow>
   sch_assn ''q2'' sch_es  sch_s rest \<Longrightarrow>
   sch_assn ''q1'' sch_es sch_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   i = sch_s CHR ''i'' \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior < prior \<Longrightarrow>
   r_now = -1 \<Longrightarrow>
   sch_assn ''q2'' sch_es sch_s rest \<Longrightarrow>
   sch_assn ''q1'' sch_es sch_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   i = sch_s CHR ''i'' \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   blk1 = OutBlock (run_ch i) 0 \<Longrightarrow>
   sch_assn ''q0'' (sched_assign i sch_es sch_s) sch_s rest \<Longrightarrow>
   sch_assn ''q2'' sch_es sch_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   blk1 = InBlock (free_ch i) 0 \<Longrightarrow>
   sch_assn ''q3'' sch_es (sch_s(CHR ''i'' := i)) rest \<Longrightarrow>
   sch_assn ''q0'' sch_es sch_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   length p > 0 \<Longrightarrow>
   blk1 = OutBlock (run_ch (snd (get_max p))) 0 \<Longrightarrow>
   sch_assn ''q0'' (sched_get_max sch_es sch_s) sch_s rest \<Longrightarrow>
   sch_assn ''q3'' sch_es sch_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   length p = 0 \<Longrightarrow>
   sch_assn ''q0'' (sched_clear sch_es sch_s) sch_s rest \<Longrightarrow>
   sch_assn ''q3'' sch_es sch_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   blk1 = InBlock (exit_ch i) 0 \<Longrightarrow>
   sch_assn ''q4'' sch_es (sch_s(CHR ''i'' := i)) rest \<Longrightarrow>
   sch_assn ''q0'' sch_es sch_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   sch_assn ''q0'' (sched_del_proc (sch_s CHR ''i'') sch_es sch_s) sch_s rest \<Longrightarrow>
   sch_assn ''q4'' sch_es sch_s rest"



coinductive sch_task_dis_assn :: "tid \<Rightarrow> string \<Rightarrow> string \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate stassn" where
  "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   init_t' = dis_s (CHR ''t'') \<Longrightarrow>
   init_t' < 0.045 \<Longrightarrow>
   wt \<le> 0.045 - init_t' \<Longrightarrow>
   blk1 = WaitBlk (ereal wt) (\<lambda>t. ParState (EState (sch_es, sch_s))(ParState
      (EState (None, dis_s(CHR ''t'' := init_t' + t)))
      (EState (start_es, task_s)))) 
       ({}, {dispatch_ch i} \<union> image req_ch {1,2,3} \<union> image free_ch {1,2,3} \<union> image exit_ch {1,2,3}) \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' sch_es sch_s (dis_s(CHR ''t'' := init_t' + wt)) start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   blk1 = InBlock (req_ch j) prior \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p1'' sch_es (sch_s(CHR ''p'' := prior, CHR ''i'' := j)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior \<ge> prior \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' (sched_push j sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p1'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior < prior \<Longrightarrow>
   r_now \<noteq> -1 \<Longrightarrow>
   blk1 = OutBlock (preempt_ch r_now) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p1'' sch_es sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p1'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior < prior \<Longrightarrow>
   r_now = -1 \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p1'' sch_es sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p1'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   blk1 = OutBlock (run_ch j) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' (sched_assign i sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p1'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   blk1 = InBlock (free_ch j) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p1'' sch_es (sch_s(CHR ''i'' := j)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   length p > 0 \<Longrightarrow>
   blk1 = OutBlock (run_ch (snd (get_max p))) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' (sched_get_max sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p1'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   length p = 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' (sched_clear sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p1'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   blk1 = InBlock (exit_ch j) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q4'' ''p1'' sch_es (sch_s(CHR ''i'' := j)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' (sched_del_proc (sch_s CHR ''i'') sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q4'' ''p1'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task WAIT ent tp \<Longrightarrow>
   init_t' = dis_s (CHR ''t'') \<Longrightarrow>
   init_t' = 0.045 \<Longrightarrow>
   blk1 = IOBlock (dispatch_ch i) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p2'' sch_es sch_s (dis_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0)) rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p1'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   blk1 = IOBlock (req_ch i) prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   blk1 = OutBlock (req_ch i) tp \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p3'' sch_es (sch_s(CHR ''p'' := prior, CHR ''i'' := i)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p2'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   i = sch_s CHR ''i'' \<Longrightarrow>
   r_prior \<ge> sch_s CHR ''p'' \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' (sched_push i sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p3'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_t' = dis_s (CHR ''t'') \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   wt \<le> 0.045 - init_t' \<Longrightarrow>
   blk1 = WaitBlk (ereal wt) (\<lambda>t. ParState (EState (sch_es,sch_s))(ParState
      (EState (None, dis_t(CHR ''t'' := init_t' + t)))
      (EState (start_es, task_s(CHR ''t'' := init_t + t))))) ({}, {run_ch i} \<union> image req_ch {1,2,3} \<union> image free_ch {1,2,3} \<union> image exit_ch {1,2,3}) \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' sch_es sch_s (dis_s(CHR ''t'' := init_t' + wt))
      start_es (task_s(CHR ''t'' := init_t + wt)) rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   blk1 = InBlock (req_ch j) prior \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p3'' sch_es (sch_s(CHR ''p'' := prior, CHR ''i'' := j)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior \<ge> prior \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' (sched_push j sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p3'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior < prior \<Longrightarrow>
   r_now \<noteq> -1 \<Longrightarrow>
   blk1 = OutBlock (preempt_ch r_now) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p3'' sch_es sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior < prior \<Longrightarrow>
   r_now = -1 \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p3'' sch_es sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p3'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   blk1 = OutBlock (run_ch j) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' (sched_assign j sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   blk1 = InBlock (free_ch j) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p3'' sch_es (sch_s(CHR ''i'' := j)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   length p > 0 \<Longrightarrow>
   snd (get_max p) \<noteq> i \<Longrightarrow>
   blk1 = OutBlock (run_ch (snd (get_max p))) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' (sched_get_max sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
(*  
Task READY 0 tp   and   Task READY 1 tp
*)
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   length p > 0 \<Longrightarrow>
   snd (get_max p) = i \<Longrightarrow>
   blk1 = IOBlock (run_ch i) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' (sched_get_max sch_es sch_s) sch_s dis_s (Task RUNNING 1 tp) task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
(* length p must be greater than 0
*)
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   length p = 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' (sched_clear sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p3'' sch_es sch_s dis_s start_es task_s rest"

| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   blk1 = InBlock (exit_ch j) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q4'' ''p3'' sch_es (sch_s(CHR ''i'' := j)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' (sched_del_proc (sch_s CHR ''i'') sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q4'' ''p3'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_t = 0.045 \<Longrightarrow>
   blk1 = IOBlock (exit_ch i) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q4'' ''p1'' sch_es sch_s dis_s (Task WAIT ent tp) task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   i = sch_s CHR ''i'' \<Longrightarrow>
   r_prior < sch_s CHR ''p'' \<Longrightarrow>
   r_now \<noteq> -1 \<Longrightarrow>
   blk1 = OutBlock (preempt_ch r_now) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p3'' sch_es sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY ent tp \<Longrightarrow>
   i = sch_s CHR ''i'' \<Longrightarrow>
   r_prior < sch_s CHR ''p'' \<Longrightarrow>
   r_now = -1 \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p3'' sch_es sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p3'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   i = sch_s CHR ''i'' \<Longrightarrow>
   start_es = Task READY 0 tp \<Longrightarrow>
   blk1 = IOBlock (run_ch i) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' (sched_assign i sch_es sch_s) sch_s dis_s (Task RUNNING 1 tp) (task_s(CHR ''c'' := 0)) rest \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   i = sch_s CHR ''i'' \<Longrightarrow>
   start_es = Task READY 1 tp \<Longrightarrow>
   blk1 = IOBlock (run_ch i) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' (sched_assign i sch_es sch_s) sch_s dis_s (Task RUNNING 1 tp) task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p3'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_c = task_s (CHR ''c'') \<Longrightarrow>
   init_t' = dis_s (CHR ''t'') \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   wt \<le> 0.01 - init_c \<Longrightarrow>
   wt \<le> 0.045 - init_t' \<Longrightarrow>
   wt > 0 \<Longrightarrow>
   blk1 = WaitBlk (ereal wt) (\<lambda>t. ParState (EState (sch_es, sch_s)) (ParState
      (EState (None, dis_s(CHR ''t'' := init_t' + t)))
      (EState (start_es, task_s(CHR ''t'' := init_t + t, CHR ''c'' := init_c + t)))))
      ({}, {preempt_ch i}\<union> image req_ch {1,2,3} \<union> image free_ch {1,2,3} \<union> image exit_ch {1,2,3}) \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' sch_es sch_s (dis_s(CHR ''t'' := init_t' + wt)) start_es (task_s(CHR ''t'' := init_t + wt,
                                                 CHR ''c'' := init_c + wt)) rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_c = task_s (CHR ''c'') \<Longrightarrow>
   init_c = 0.01 \<or> init_t = 0.045 \<Longrightarrow>
   blk1 = IOBlock (free_ch i) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p1'' sch_es (sch_s(CHR ''i'' := i)) dis_s (Task READY 1 tp) task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"

| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task RUNNING 1 tp \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   blk1 = InBlock (req_ch j) prior \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p4'' sch_es (sch_s(CHR ''p'' := prior, CHR ''i'' := j)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task RUNNING 1 tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior \<ge> prior \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' (sched_push j sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p4'' sch_es sch_s dis_s start_es task_s rest"

(* 
r_now = i, r_prior = tp
*)
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task RUNNING 1 tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>   
   prior = sch_s CHR ''p'' \<Longrightarrow>
   r_prior < prior \<Longrightarrow>
   blk1 = IOBlock (preempt_ch i) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p2'' sch_es sch_s dis_s (Task READY 1 tp) task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q1'' ''p4'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY 1 tp \<Longrightarrow>
   j = sch_s CHR ''i'' \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   prior = sch_s CHR ''p'' \<Longrightarrow>
   blk1 = OutBlock (run_ch j) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p2'' (sched_assign j sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q2'' ''p2'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY 1 tp \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   blk1 = InBlock (free_ch j) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p4'' sch_es (sch_s(CHR ''i'' := j)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY 1 tp  \<Longrightarrow>
   length p > 0 \<Longrightarrow>
   blk1 = OutBlock (run_ch (snd (get_max p))) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' (sched_get_max sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p4'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY 1 tp \<Longrightarrow>
   length p = 0 \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' (sched_clear sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q3'' ''p4'' sch_es sch_s dis_s start_es task_s rest"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY 1 tp \<Longrightarrow>
   j \<noteq> i \<Longrightarrow>
   blk1 = InBlock (exit_ch j) 0 \<Longrightarrow>
   sch_task_dis_assn i ''q4'' ''p4'' sch_es (sch_s(CHR ''i'' := j)) dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' sch_es sch_s dis_s start_es task_s (SCons blk1 rest)"
| "sch_es = Sch p r_now r_prior \<Longrightarrow>
   start_es = Task READY 1 tp \<Longrightarrow>
   sch_task_dis_assn i ''q0'' ''p4'' (sched_del_proc (sch_s CHR ''i'') sch_es sch_s) sch_s dis_s start_es task_s rest \<Longrightarrow>
   sch_task_dis_assn i ''q4'' ''p4'' sch_es sch_s dis_s start_es task_s rest"


theorem combine_sch_task_dis:
  assumes "i \<in> {1,2,3}"
  shows "sch_assn qc sch_es sch_s blks1 \<Longrightarrow>
         task_dis_assn i pc dis_s start_es task_s blks2 \<Longrightarrow>
         combine_blocks {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i} blks1 blks2 blks \<Longrightarrow>
         sch_task_dis_assn i qc pc sch_es sch_s dis_s start_es task_s blks"
proof (coinduction arbitrary: qc pc sch_es sch_s dis_s start_es task_s blks1 blks2 blks rule: sch_task_dis_assn.coinduct)
  have comm_in_req:"req_ch i \<in> {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i}"
    by auto
  have comm_in_exit:"exit_ch i \<in> {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i}"
    by auto
  have comm_in_run:"run_ch i \<in> {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i}"
    by auto
  have comm_in_preempt:"preempt_ch i \<in> {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i}"
    by auto
  have comm_in_free:"free_ch i \<in> {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i}"
    by auto
  have comm_not_in_dis:"dispatch_ch i \<notin> {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i}"
    apply(auto simp add: dispatch_ch_def req_ch_def run_ch_def free_ch_def preempt_ch_def exit_ch_def)
    using assms by auto
  case sch_task_dis_assn
  from sch_task_dis_assn(1) 
  show ?case
  proof (cases rule: sch_assn.cases)
    case (1 p r_now r_prior wt1 blk1 rest1)
    note s1 = 1
    from sch_task_dis_assn(2) 
    show ?thesis 
    proof (cases rule : task_dis_assn.cases)
      case (1 ent tp init_t' wt2 blk2 rest2)
      note t1 = 1
      obtain rest where rest:   
        "ereal wt1 = ereal wt2"
        "blks = SCons (WaitBlk (ereal wt1) (\<lambda>t. ParState (EState (sch_es, sch_s)) 
        (ParState (EState (None, dis_s(CHR ''t'' := init_t' + t))) (EState (start_es, task_s))))
            ({}, {dispatch_ch i} \<union> req_ch ` {1, 2, 3} \<union> free_ch ` {1, 2, 3} \<union> exit_ch ` {1, 2, 3})) rest"
        "combine_blocks {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i} rest1 rest2 rest"
        using sch_task_dis_assn(3)[unfolded s1(2,5) t1(2,7)]
        apply (elim combine_blocks_waitE)
        by (smt merge_rdy.simps sup_assoc sup_commute sup_idem)
      then show ?thesis using s1 t1 sch_task_dis_assn by auto
    next
      case (2 ent tp init_t' blk2 rest2)
      note t2 = 2
        obtain rest where rest:   
        "blks = SCons (IOBlock (dispatch_ch i) 0) rest"
        "combine_blocks {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i} blks1 rest2 rest"
          using sch_task_dis_assn(3)[unfolded s1(2,5) t2(2,6)]
          apply(simp add: s1(2,5) t2(2,6))
          apply(elim combine_blocks_waitCommE2[OF comm_not_in_dis]) by blast
      then show ?thesis using s1 t2 sch_task_dis_assn by auto
    next
      case (3 ent tp blk1 rest)
      note t3 = 3
      from sch_task_dis_assn(3)[unfolded s1(2,5) t3(2,4)]
      show ?thesis by(elim combine_blocks_waitCommE[OF comm_in_req])
    next
      case (4 ent tp init_t init_t' wt2 blk2 dis_s rest2)
      note t4 = 4
      obtain rest where 
        "ereal wt1 = ereal wt2"
        "blks = SCons (WaitBlk (ereal wt1) (\<lambda>t. ParState (EState (sch_es, sch_s)) 
        (ParState (EState (None, dis_s(CHR ''t'' := init_t' + t))) (EState (start_es, task_s(CHR ''t'' := init_t + t)))))
            ({}, {run_ch i} \<union> req_ch ` {1, 2, 3} \<union> free_ch ` {1, 2, 3} \<union> exit_ch ` {1, 2, 3})) rest"
        "combine_blocks {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i} rest1 rest2 rest"
        using sch_task_dis_assn(3)[unfolded s1(2,5) t4(2,8)]
        apply (elim combine_blocks_waitE) 
        by (smt (verit, ccfv_threshold) Un_insert_left Un_insert_right merge_rdy.simps sup_bot.left_neutral sup_bot_right)
        then show ?thesis using s1 t4 sch_task_dis_assn by auto
    next
      case (5 ent tp init_t blk1 rest)
      note t5 = 5
      from sch_task_dis_assn(3)[unfolded s1(2,5) t5(2,6)]
      show ?thesis by(elim combine_blocks_waitCommE[OF comm_in_exit])
    next
      case (6 tp blk1 rest)
      note t6 = 6
      from sch_task_dis_assn(3)[unfolded s1(2,5) t6(2,4)]
      show ?thesis by(elim combine_blocks_waitCommE[OF comm_in_run])
    next
      case (7 tp blk1 rest)
      note t7 = 7
      from sch_task_dis_assn(3)[unfolded s1(2,5) t7(2,4)]
      show ?thesis by(elim combine_blocks_waitCommE[OF comm_in_run])
    next
      case (8 tp init_t init_c init_t' wt2 blk2 rest2)
      note t8 = 8
      obtain rest where 
        "ereal wt1 = ereal wt2"
        "blks = SCons (WaitBlk (ereal wt1) (\<lambda>t. ParState (EState (sch_es, sch_s)) 
        (ParState (EState (None, dis_s(CHR ''t'' := init_t' + t))) (EState (start_es, task_s(CHR ''t'' := init_t + t, CHR ''c'' := init_c + t)))))
            ({}, {preempt_ch i} \<union> req_ch ` {1, 2, 3} \<union> free_ch ` {1, 2, 3} \<union> exit_ch ` {1, 2, 3})) rest"
        "combine_blocks {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i} rest1 rest2 rest"
        using sch_task_dis_assn(3)[unfolded s1(2,5) t8(2,11)]
        apply (elim combine_blocks_waitE) 
        by (simp add: insert_commute)
      then show ?thesis using s1 t8 sch_task_dis_assn by auto
    next
      case (9 tp blk1 rest)
      note t9 = 9
      from sch_task_dis_assn(3)[unfolded s1(2,5) t9(2,4)]
      show ?thesis by(elim combine_blocks_waitCommE[OF comm_in_preempt])
    next
      case (10 tp init_t init_c blk1 rest)
      note t10 =10
      from sch_task_dis_assn(3)[unfolded s1(2,5) t10(2,7)]
      show ?thesis by(elim combine_blocks_waitCommE[OF comm_in_free])
    qed
  next
    case (2 p r_now r_prior blk1 j prior rest1)
    note s2 = 2
    from sch_task_dis_assn(2) 
    show ?thesis 
    proof (cases rule : task_dis_assn.cases)
      case (1 ent tp init_t' wt blk2 rest2)
      note t1 = 1
      show ?thesis
      proof (cases "j = i")
        case True
        from sch_task_dis_assn(3)[unfolded s2(2,4) t1(2,7) True]
        show ?thesis by(elim combine_blocks_waitCommE'[OF comm_in_req])
      next
        case False
        then have comm_not_in:"(req_ch j) \<notin> {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i}"
          apply(simp add: dispatch_ch_def req_ch_def run_ch_def free_ch_def preempt_ch_def exit_ch_def)
          using assms s2(5) by auto 
        obtain rest where rest:
        "blks = SCons (InBlock (req_ch j) prior) rest"
        "combine_blocks {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i} rest1 blks2 rest"
          using sch_task_dis_assn(3)[unfolded s2(2,4) t1(2,7)]
          apply(simp add: t1(2,7))
          apply(elim combine_blocks_waitCommE2'[OF comm_not_in]) by auto
        show ?thesis 
         apply(rule disjI2)
          apply(rule disjI1)
          apply(rule exI[where x="sch_es"])
          apply(rule exI[where x="pool sch_es"])
          apply(rule exI[where x="run_now sch_es"])
          apply(rule exI[where x="run_prior sch_es"])
          apply(rule exI[where x="start_es"])
          apply(rule exI[where x="entered start_es"])
          apply(rule exI[where x="task_prior start_es"])
          apply(rule exI[where x="j"])
          apply(rule exI[where x="i"])
          apply(rule exI[where x="(InBlock (req_ch j) prior)"])
          apply(rule exI[where x="prior"])
          apply(rule exI[where x="sch_s"])
          apply(rule exI[where x="dis_s"])
          apply(rule exI[where x="task_s"])
          apply(rule exI[where x="rest"])
          apply(intro conjI)
          apply(rule refl, simp add: s2 t1)+
          using t1 apply simp
          apply(rule refl)+
          using rest apply simp
          using s2 apply simp
          using t1 apply simp
          using False apply simp
          apply(rule refl)
          apply(rule disjI1)
          apply(rule exI[where x="''q1''"])
          apply(rule exI[where x="''p1''"])
          apply(rule exI[where x="sch_es"])
          apply(rule exI[where x="sch_s(CHR ''p'' := prior, CHR ''i'' := j)"])
          apply(rule exI[where x="dis_s"])
          apply(rule exI[where x="start_es"])
          apply(rule exI[where x="task_s"])
          apply(rule exI[where x="rest1"])
          apply(rule exI[where x="blks2"])
          apply(rule exI[where x="rest"])
          apply(intro conjI)
          apply(rule refl)+
          using s2 apply simp
          using sch_task_dis_assn t1 apply simp
          using rest apply simp
          done
      qed
    next
      case (2 ent tp init_t' blk2 rest2)
      note t2 = 2
      show ?thesis 
      proof (cases " j = i")
        case True
        obtain rest where
          "blks = SCons (IOBlock (dispatch_ch i) 0) rest"
          "combine_blocks {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i} blks1 rest2 rest"
          using sch_task_dis_assn(3)[unfolded s2(2,4) t2(2,6) True]
          apply (simp add: s2(2,4) t2(2,6) True)
          apply(elim combine_blocks_unpairE1'[OF comm_in_req comm_not_in_dis]) by blast
        then show ?thesis using sch_task_dis_assn s2 t2 True by auto
      next
        case False
        then have comm_not_in:"(req_ch j) \<notin> {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i}"
          apply(simp add: dispatch_ch_def req_ch_def run_ch_def free_ch_def preempt_ch_def exit_ch_def)
          using assms s2(5) by auto 
        obtain rest where
          "blks = SCons (InBlock (req_ch j) prior) rest"
          "combine_blocks {req_ch i, run_ch i, free_ch i, preempt_ch i, exit_ch i} rest1 blks2 rest"
          using sch_task_dis_assn(3)[unfolded s2(2,4) t2(2,6)]
          apply (simp add: s2(2,4) t2(2,6))
          apply(elim combine_blocks_unpairE2[OF comm_not_in comm_not_in_dis]) 
        then show ?thesis sorry
      qed

    next
      case (3 ent tp blk1 rest)
      then show ?thesis sorry
    next
      case (4 ent tp init_t init_t' wt blk1 dis_t rest)
      then show ?thesis sorry
    next
      case (5 ent tp init_t blk1 rest)
      then show ?thesis sorry
    next
      case (6 tp blk1 rest)
      then show ?thesis sorry
    next
      case (7 tp blk1 rest)
      then show ?thesis sorry
    next
      case (8 tp init_t init_c init_t' wt blk1 rest)
      then show ?thesis sorry
    next
      case (9 tp blk1 rest)
      then show ?thesis sorry
    next
      case (10 tp init_t init_c blk1 rest)
      then show ?thesis sorry
    qed
  next
    case (3 p r_now r_prior i prior)
    then show ?thesis sorry
  next
    case (4 p r_now r_prior i prior blk1 rest)
    then show ?thesis sorry
  next
    case (5 p r_now r_prior i prior)
    then show ?thesis sorry
  next
    case (6 p r_now r_prior i prior blk1 rest)
    then show ?thesis sorry
  next
    case (7 p r_now r_prior blk1 i rest)
    then show ?thesis sorry
  next
    case (8 p r_now r_prior blk1 rest)
    then show ?thesis sorry
  next
    case (9 p r_now r_prior)
    then show ?thesis sorry
  next
    case (10 p r_now r_prior blk1 i rest)
    then show ?thesis sorry
  next
    case (11 p r_now r_prior)
    then show ?thesis sorry
  qed
qed

end
