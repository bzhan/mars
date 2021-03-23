theory BigStepParallel
  imports BigStepContinuous
begin


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
    using assms(1) WaitBlk_cong2 by auto
  have a3: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> d1 \<Longrightarrow> p2 t = p2' t"
    using assms(2) WaitBlk_cong2 by auto
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
   combine_blocks comms (CommBlock ch_type ch v # blks1) blks2 (CommBlock ch_type ch v # blks)"
| combine_blocks_unpair2:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (CommBlock ch_type ch v # blks2) (CommBlock ch_type ch v # blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_wait1:
  "combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t hist rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlk (t2 - t1) (\<lambda>\<tau>. (\<lambda>x::real. hist2 x) (\<tau> + t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow> t1 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t1 hist rdy # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlk (t1 - t2) (\<lambda>\<tau>. (\<lambda>x::real. hist1 x) (\<tau> + t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow> t2 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t2 hist rdy # blks)"

subsection \<open>Basic elimination rules\<close>

named_theorems sync_elims

lemma combine_blocks_pairE [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. ch1 = ch2 \<Longrightarrow> v1 = v2 \<Longrightarrow> (ch_type1 = In \<and> ch_type2 = Out \<or> ch_type1 = Out \<and> ch_type2 = In) \<Longrightarrow>
   tr = IOBlock ch1 v1 # tr' \<Longrightarrow> combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlock ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1' [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE2 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlock ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2' [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlk d2 p2 rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3' [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_waitE1 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   \<not>compat_rdy rdy1 rdy2 \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  then show ?case
    by (metis WaitBlk_cong list.inject)
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  then show ?case 
    by (metis WaitBlk_cong list.inject)
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  then show ?case 
    by (metis WaitBlk_cong list.inject)
qed (auto)

lemma combine_blocks_waitE2 [sync_elims]:
  "combine_blocks comms (WaitBlk d p1 rdy1 # tr1) (WaitBlk d p2 rdy2 # tr2) tr \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms' blks1 blks2 blks rdy1' rdy2' hist hist1 hist2 rdy t)
  have a: "d = t" "rdy1 = rdy1'" "rdy2 = rdy2'" "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait1(2,3) by (auto simp add: WaitBlk_cong)
  have b: "WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk t (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine) using combine_blocks_wait1(2,3) by auto 
  show ?case
    apply (rule combine_blocks_wait1)
    unfolding b using combine_blocks_wait1(4) unfolding a combine_blocks_wait1(7,8)
    by (auto simp add: combine_blocks_wait1(1,5))
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have a: "d = ereal t1" "d = t2"
    using combine_blocks_wait2(2,3) by (auto simp add: WaitBlk_cong)
  show ?case
    using a combine_blocks_wait2(7) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have a: "d = ereal t2" "d = t1"
    using combine_blocks_wait3(2,3) by (auto simp add: WaitBlk_cong)
  show ?case
    using a combine_blocks_wait3(7) by auto
qed (auto)

lemma combine_blocks_waitE3 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   0 < d1 \<Longrightarrow> d1 < d2 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  have a: "t = ereal d1" "t = d2"
    using combine_blocks_wait1(2,3) WaitBlk_cong by blast+
  then show ?case
    using combine_blocks_wait1(10) by auto
next
  case (combine_blocks_wait2 comms' blks1 t2 t1 hist2 rdy2' blks2 blks rdy1' hist hist1 rdy)
  have a: "d1 = t1" "d2 = t2" "rdy1 = rdy1'" "rdy2 = rdy2'" "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait2(2,3) using WaitBlk_cong by blast+
  have a2: "WaitBlk d2 p2 rdy2 = WaitBlk d2 hist2 rdy2"
    using combine_blocks_wait2(3) unfolding a[symmetric] by auto
  have a3: "WaitBlk d1 p2 rdy2 = WaitBlk d1 hist2 rdy2"
           "WaitBlk (d2 - d1) (\<lambda>\<tau>. p2 (\<tau> + d1)) rdy2 = WaitBlk (d2 - d1) (\<lambda>\<tau>. hist2 (\<tau> + d1)) rdy2"
    using WaitBlk_split[OF a2] combine_blocks_wait2 by auto
  have b: "WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk t1 (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine)
    using combine_blocks_wait2.hyps(2) a(1,4) a3 by auto
  show ?case
    apply (rule combine_blocks_wait2) unfolding a3 b
    using combine_blocks_wait2(4) unfolding combine_blocks_wait2(9,10)
    by (auto simp add: a combine_blocks_wait2(1,5))
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have "ereal d1 = t1" "d2 = ereal t2"
    using combine_blocks_wait3(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait3(7,12) by auto
qed (auto)

lemma combine_blocks_waitE4 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   0 < d2 \<Longrightarrow> d2 < d1 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  have "d1 = t" "ereal d2 = t"
    using combine_blocks_wait1(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait1(10) by auto
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have "d1 = ereal t1" "ereal d2 = t2"
    using combine_blocks_wait2(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait2(7,12) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1' blks1 blks2 blks rdy2' hist hist2 rdy)
  have a: "d1 = t1" "d2 = t2" "rdy1 = rdy1'" "rdy2 = rdy2'"
          "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait3(2,3) using WaitBlk_cong by blast+
  have a2: "WaitBlk d1 p1 rdy1 = WaitBlk d1 hist1 rdy1"
    using combine_blocks_wait3(2) unfolding a[symmetric] by auto
  have a3: "WaitBlk d2 p1 rdy1 = WaitBlk d2 hist1 rdy1"
           "WaitBlk (d1 - d2) (\<lambda>\<tau>. p1 (\<tau> + d2)) rdy1 = WaitBlk (d1 - d2) (\<lambda>\<tau>. hist1 (\<tau> + d2)) rdy1"
    using WaitBlk_split[OF a2] combine_blocks_wait3 by auto
  have b: "WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk d2 (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine)
    using combine_blocks_wait3 a(2,3) a3 by auto
  show ?case
    apply (rule combine_blocks_wait3) unfolding a3 b
    using combine_blocks_wait3(4) unfolding combine_blocks_wait3(9,10)
    by (auto simp add: a combine_blocks_wait3)
qed (auto)

lemma combine_blocks_emptyE1 [sync_elims]:
  "combine_blocks comms [] [] tr \<Longrightarrow> tr = []"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) [] tr \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2' [sync_elims]:
  "combine_blocks comms [] (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE3 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) [] tr \<Longrightarrow>
   (\<And>tr'. ch1 \<notin> comms \<Longrightarrow> tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 [] tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE3' [sync_elims]:
  "combine_blocks comms [] (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   (\<And>tr'. ch2 \<notin> comms \<Longrightarrow> tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms [] tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)


subsection \<open>Big-step semantics for parallel processes.\<close>

inductive par_big_step :: "pproc \<Rightarrow> gstate \<Rightarrow> trace \<Rightarrow> gstate \<Rightarrow> bool" where
  SingleB: "big_step p s1 tr s2 \<Longrightarrow> par_big_step (Single p) (State s1) tr (State s2)"
| ParallelB:
    "par_big_step p1 s11 tr1 s12 \<Longrightarrow>
     par_big_step p2 s21 tr2 s22 \<Longrightarrow>
     combine_blocks chs tr1 tr2 tr \<Longrightarrow>
     par_big_step (Parallel p1 chs p2) (ParState s11 s21) tr (ParState s12 s22)"


subsection \<open>Validity for parallel programs\<close>

text \<open>Assertion on global state\<close>
type_synonym gs_assn = "gstate \<Rightarrow> bool"

text \<open>Assertion on global state and trace\<close>
type_synonym gassn = "gstate \<Rightarrow> trace \<Rightarrow> bool"

fun par_assn :: "gs_assn \<Rightarrow> gs_assn \<Rightarrow> gs_assn" where
  "par_assn P Q (State s) \<longleftrightarrow> False"
| "par_assn P Q (ParState l r) \<longleftrightarrow> P l \<and> Q r"

fun sing_assn :: "fform \<Rightarrow> gs_assn" where
  "sing_assn P (State s) = P s"
| "sing_assn P (ParState _ _) = False"

fun sing_gassn :: "assn \<Rightarrow> gassn" where
  "sing_gassn Q (State s) tr = Q s tr"
| "sing_gassn Q (ParState _ _) tr = False"

definition pair_assn :: "fform \<Rightarrow> fform \<Rightarrow> gs_assn" where
  "pair_assn P Q = par_assn (sing_assn P) (sing_assn Q)"

fun sync_gassn :: "cname set \<Rightarrow> gassn \<Rightarrow> gassn \<Rightarrow> gassn" where
  "sync_gassn chs P Q (State s) tr = False"
| "sync_gassn chs P Q (ParState l r) tr \<longleftrightarrow> (\<exists>tr1 tr2. P l tr1 \<and> Q r tr2 \<and> combine_blocks chs tr1 tr2 tr)"

definition ParValid :: "gs_assn \<Rightarrow> pproc \<Rightarrow> gassn \<Rightarrow> bool" ("\<Turnstile>\<^sub>p ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile>\<^sub>p {P} c {Q} \<longleftrightarrow> (\<forall>s1 s2 tr2. P s1 \<longrightarrow> par_big_step c s1 tr2 s2 \<longrightarrow> Q s2 tr2)"


inductive_cases SingleE: "par_big_step (Single p) s1 tr s2"
thm SingleE

inductive_cases ParallelE: "par_big_step (Parallel p1 ch p2) s1 tr s2"
thm ParallelE

lemma ParValid_Single:
  assumes "\<Turnstile> {\<lambda>s tr. P s \<and> tr = []} c {Q}"
  shows "\<Turnstile>\<^sub>p {sing_assn P} Single c {sing_gassn Q}"
  using assms unfolding ParValid_def Valid_def
  by (metis SingleE append_Nil gstate.inject(1) sing_assn.elims(2) sing_gassn.simps(1))

lemma ParValid_Parallel:
  assumes "\<Turnstile>\<^sub>p {P1} p1 {Q1}"
    and "\<Turnstile>\<^sub>p {P2} p2 {Q2}"
  shows "\<Turnstile>\<^sub>p {par_assn P1 P2} Parallel p1 chs p2 {sync_gassn chs Q1 Q2}"
  unfolding ParValid_def apply clarify
  apply (elim ParallelE) apply auto
  subgoal for tr2 s11 tr1 s12 s21 tr2' s22
    apply (rule exI[where x=tr1])
    apply auto
    subgoal using assms(1) unfolding ParValid_def by auto
    apply (rule exI[where x=tr2'])
    using assms(2) unfolding ParValid_def by auto
  done

lemma ParValid_conseq:
  assumes "\<Turnstile>\<^sub>p {P} c {Q}"
    and "\<And>s. P' s \<Longrightarrow> P s"
    and "\<And>s tr. Q s tr \<Longrightarrow> Q' s tr"
  shows "\<Turnstile>\<^sub>p {P'} c {Q'}"
  using assms unfolding ParValid_def by blast

text \<open>Version for two processes\<close>

lemma ParValid_Parallel':
  assumes "\<Turnstile> {\<lambda>s tr. P1 s \<and> emp\<^sub>t tr} p1 {Q1}"
    and "\<Turnstile> {\<lambda>s tr. P2 s \<and> emp\<^sub>t tr} p2 {Q2}"
  shows "\<Turnstile>\<^sub>p
    {pair_assn P1 P2}
      Parallel (Single p1) chs (Single p2)
    {sync_gassn chs (sing_gassn Q1) (sing_gassn Q2)}"
  unfolding pair_assn_def
  apply (rule ParValid_Parallel)
  using ParValid_Single assms unfolding emp_assn_def by auto


subsection \<open>Combination on assertions\<close>

definition combine_assn :: "cname set \<Rightarrow> tassn \<Rightarrow> tassn \<Rightarrow> tassn" where
  "combine_assn chs P Q = (\<lambda>tr. \<exists>tr1 tr2. P tr1 \<and> Q tr2 \<and> combine_blocks chs tr1 tr2 tr)"

lemma combine_assn_ex_pre_left:
  assumes "\<And>x. combine_assn chs (P x) Q \<Longrightarrow>\<^sub>t R"
  shows "combine_assn chs (\<lambda>tr. \<exists>x. P x tr) Q \<Longrightarrow>\<^sub>t R"
  using assms by (auto simp add: combine_assn_def entails_tassn_def)

lemma combine_assn_ex_pre_right:
  assumes "\<And>x. combine_assn chs P (Q x) \<Longrightarrow>\<^sub>t R"
  shows "combine_assn chs P (\<lambda>tr. \<exists>x. Q x tr) \<Longrightarrow>\<^sub>t R"
  using assms by (auto simp add: combine_assn_def entails_tassn_def)

lemma combine_assn_mono:
  assumes "P \<Longrightarrow>\<^sub>t P'"
    and "Q \<Longrightarrow>\<^sub>t Q'"
  shows "combine_assn chs P Q \<Longrightarrow>\<^sub>t combine_assn chs P' Q'"
  using assms by (auto simp add: combine_assn_def entails_tassn_def)

lemma combine_assn_emp [simp]:
  "combine_assn chs emp\<^sub>t emp\<^sub>t = emp\<^sub>t"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: emp_assn_def elim: sync_elims)
  by (rule combine_blocks_empty)

lemma combine_assn_emp_in:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (In\<^sub>t s ch v @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_in_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (In\<^sub>t s ch v @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_emp_out:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (Out\<^sub>t s ch v @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_out_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (Out\<^sub>t s ch v @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_out_in:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Out\<^sub>t s1 ch v @\<^sub>t P) (In\<^sub>t s2 ch w @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_assn.simps
                        out_assn.simps in_assn.simps)
  subgoal by (auto elim: sync_elims)
  subgoal apply (elim combine_blocks_pairE) by auto
  by (auto elim!: sync_elims)

lemma combine_assn_out_in':
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Out\<^sub>t s1 ch v) (In\<^sub>t s2 ch w) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def
                        io_assn.simps out_assn.simps in_assn.simps)
  by (auto elim: sync_elims)

lemma combine_assn_out_in'_tr:
  "combine_assn chs (Out\<^sub>t s1 ch v) (In\<^sub>t s2 ch w) tr \<Longrightarrow>
   ch \<in> chs \<Longrightarrow>
   v = w \<and> IO\<^sub>t ch v tr"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def
                        io_assn.simps out_assn.simps in_assn.simps)
  by (auto elim: sync_elims)

lemma combine_assn_in_out:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (In\<^sub>t s1 ch v @\<^sub>t P) (Out\<^sub>t s2 ch w @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_assn.simps
                        out_assn.simps in_assn.simps)
  subgoal by (auto elim: sync_elims)
  subgoal apply (elim combine_blocks_pairE) by auto
  by (auto elim!: sync_elims)

lemma combine_assn_wait_emp:
  "combine_assn chs (Wait\<^sub>t d p rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def false_assn_def)
  by (auto elim!: sync_elims)

lemma combine_assn_emp_wait:
  "combine_assn chs emp\<^sub>t (Wait\<^sub>t d p rdy @\<^sub>t P) \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def false_assn_def)
  by (auto elim!: sync_elims)

lemma combine_assn_wait:
  "compat_rdy rdy1 rdy2 \<Longrightarrow>
   combine_assn chs (Wait\<^sub>t d p rdy1 @\<^sub>t P) (Wait\<^sub>t d q rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Wait\<^sub>t d (\<lambda>t. ParState (p t) (q t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P Q)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def wait_assn.simps)
  apply (elim combine_blocks_waitE2) by auto

lemma combine_assn_wait_in:
  assumes "ch \<in> chs"
    and "compat_rdy rdy1 ({}, {ch})"
    and "d > 0"
  shows "combine_assn chs (Wait\<^sub>t d p rdy1 @\<^sub>t P) (In\<^sub>t s ch v @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Wait\<^sub>t d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q))"
proof -
  have *: "(Wait\<^sub>t d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q)) tr"
    if "(Wait\<^sub>t d p rdy1 @\<^sub>t P) tr1" "(In\<^sub>t s ch v @\<^sub>t Q) tr2" "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "Wait\<^sub>t d p rdy1 tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "In\<^sub>t s ch v tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    have c: "tr11 = [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy1]"
      using a(1) wait_assn.cases by blast
    have d: "(Wait\<^sub>t d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
             combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q)) tr"
      if "0 < (d2::real)"
         "combine_blocks chs (WaitBlk d p rdy1 # tr12)
          (WaitBlk d2 (\<lambda>_. s) ({}, {ch}) # InBlock ch v # tr22) tr" for d2
    proof -
      have "d < d2 \<or> d = d2 \<or> d > d2" by auto
      then show ?thesis
      proof (elim disjE)
        assume d1: "d < d2"
        have d1': "ereal d < ereal d2"
          using d1 by auto
        show ?thesis
          using that(2)
          apply (elim combine_blocks_waitE3)
            apply (rule assms(3)) apply (rule d1') using assms(2) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal by (simp add: wait_assn.simps)
            apply (rule conjI)
             prefer 2 subgoal using d1 by auto
            unfolding combine_assn_def
            apply (rule exI[where x=tr12])
            apply (rule exI[where x="WaitBlk (d2 - d) (\<lambda>_. s) ({}, {ch}) # InBlock ch v # tr22"])
            apply (rule conjI)
            subgoal by (rule a(2))
            apply (rule conjI)
             prefer 2 subgoal by auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk (d2 - d) (\<lambda>_. s) ({}, {ch}), InBlock ch v]"])
            apply (rule exI[where x=tr22])
            using b(2) d1 by (auto intro: in_assn.intros)
          done
      next
        assume d2: "d = d2"
        show ?thesis
          using that(2) unfolding d2[symmetric]
          apply (elim combine_blocks_waitE2)
          using assms(2) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal by (simp add: wait_assn.simps)
            apply (rule conjI)
             prefer 2 subgoal by auto
            unfolding combine_assn_def
            apply (rule exI[where x=tr12])
            apply (rule exI[where x="InBlock ch v # tr22"])
            apply (rule conjI)
            subgoal using a(2) by auto
            apply (rule conjI)
            subgoal apply (subst join_assn_def)
              apply (rule exI[where x="[InBlock ch v]"])
              apply (rule exI[where x=tr22])
              by (auto intro: in_assn.intros b(2))
            by auto
          done
      next
        assume d3: "d > d2"
        have d3': "ereal d > ereal d2"
          using d3 by auto
        show ?thesis
          using that(2)
          apply (elim combine_blocks_waitE4)
          apply (rule that(1)) apply (rule d3')
           using assms(2) apply simp
          apply (elim combine_blocks_pairE2')
          using assms by auto
      qed
    qed
    have e: "(Wait\<^sub>t d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
             combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q)) tr"
      if "combine_blocks chs (WaitBlk d p rdy1 # tr12)
          (WaitBlk \<infinity> (\<lambda>_. s) ({}, {ch}) # tr22) tr"
    proof -
      have e1: "\<infinity> - ereal d = \<infinity>"
        by auto
      show ?thesis
        using that
        apply (elim combine_blocks_waitE3)
           apply (rule assms(3)) apply simp using assms(2) apply simp
        subgoal for blks'
          apply (subst join_assn_def)
          apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
          apply (rule exI[where x=blks'])
          apply (rule conjI)
            subgoal by (simp add: wait_assn.simps)
            apply (rule conjI)
             prefer 2 apply simp
            unfolding combine_assn_def
            apply (rule exI[where x=tr12])
            apply (rule exI[where x="WaitBlk \<infinity> (\<lambda>_. s) ({}, {ch}) # tr22"])
            apply (rule conjI)
            subgoal by (rule a(2))
            apply (rule conjI)
             prefer 2 apply auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk \<infinity> (\<lambda>_. s) ({}, {ch})]"])
            apply (rule exI[where x=tr22])
            using b(2) apply (auto intro: in_assn.intros)
          done
        done
    qed
    show ?thesis
      using b(1) apply (cases rule: in_assn.cases)
      subgoal
        by (metis Cons_eq_appendI a(3) assms(1) b(3) c combine_blocks_pairE2' that(3))
      subgoal for d2
        using that(3) unfolding a(3) b(3) c
        using d assms(2) by auto
      subgoal
        using that(3) unfolding a(3) b(3) c
        using e assms(2) by auto
      done
  qed
  show ?thesis
    apply (subst combine_assn_def)
    apply (auto simp add: entails_tassn_def)
    using * by auto
qed

lemma combine_assn_waitout_wait:
  assumes "ch \<in> chs"
    and "compat_rdy rdy rdy2"
    and "d2 > 0"
  shows "combine_assn chs (WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) (Wait\<^sub>t d2 p2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         (\<up>(d \<ge> d2) \<and>\<^sub>t (Wait\<^sub>t d2 (\<lambda>t. ParState (State (p t)) (p2 t)) (merge_rdy rdy rdy2) @\<^sub>t
                        combine_assn chs (WaitOut\<^sub>t (d - d2) (\<lambda>t. p (t + d2)) ch e rdy @\<^sub>t P) Q))"
proof -
  have *: "(\<up> (d2 \<le> d) \<and>\<^sub>t
        Wait\<^sub>t d2 (\<lambda>t. ParState (State (p t)) (p2 t)) (merge_rdy rdy rdy2) @\<^sub>t
        combine_assn chs (WaitOut\<^sub>t (d - d2) (\<lambda>t. p (t + d2)) ch e rdy @\<^sub>t P) Q) tr"
    if "(WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) tr1"
       "(Wait\<^sub>t d2 p2 rdy2 @\<^sub>t Q) tr2"
       "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "WaitOut\<^sub>t d p ch e rdy tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "Wait\<^sub>t d2 p2 rdy2 tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    have c: "tr21 = [WaitBlk d2 p2 rdy2]"
      using b(1) wait_assn.cases by blast
    have d: "(\<up> (d2 \<le> d) \<and>\<^sub>t
             Wait\<^sub>t d2 (\<lambda>t. ParState (State (p t)) (p2 t)) (merge_rdy rdy rdy2) @\<^sub>t
             combine_assn chs (WaitOut\<^sub>t (d - d2) (\<lambda>t. p (t + d2)) ch e rdy @\<^sub>t P) Q) tr"
      if "0 < (d::real)"
         "combine_blocks chs (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy # OutBlock ch (e (p d)) # tr12)
                             (WaitBlk d2 p2 rdy2 # tr22) tr"
    proof -
      have "d < d2 \<or> d = d2 \<or> d > d2" by auto
      then show ?thesis
      proof (elim disjE)
        assume d1: "d < d2"
        have d1': "ereal d < ereal d2"
          using d1 by auto
        show ?thesis
          using that(2)
          apply (elim combine_blocks_waitE3) apply (rule that(1))
            apply (rule d1') apply (rule assms(2))
          using assms(1) combine_blocks_pairE2 by blast
      next
        assume d2: "d = d2"
        show ?thesis
          using that(2)
          unfolding d2[symmetric]
          apply (elim combine_blocks_waitE2)
           apply (rule assms(2))
          subgoal for blks'
            unfolding pure_assn_def conj_assn_def
            apply (rule conjI)
            subgoal by auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (State (p t)) (p2 t)) (merge_rdy rdy rdy2)]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal by (auto intro: wait_assn.intros)
            apply (rule conjI)
             prefer 2 subgoal by auto
            unfolding combine_assn_def
            apply (rule exI[where x="OutBlock ch (e (p d)) # tr12"])
            apply (rule exI[where x=tr22])
            apply (rule conjI)
             prefer 2 subgoal using b(2) by auto
            unfolding join_assn_def
            apply (rule exI[where x="[OutBlock ch (e (p d))]"])
            apply (rule exI[where x=tr12])
            by (auto simp add: a(2) wait_out_assn.simps)
          done
      next
        assume d3: "d > d2"
        have d3': "ereal d > ereal d2"
          using d3 by auto
        show ?thesis
          using that(2)
          apply (elim combine_blocks_waitE4) apply (rule \<open>0 < d2\<close>)
            apply (rule d3') apply (rule assms(2))
          subgoal for blks'
            unfolding pure_assn_def conj_assn_def
            apply (rule conjI)
            subgoal using d3 by auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d2 (\<lambda>t. ParState (State (p t)) (p2 t)) (merge_rdy rdy rdy2)]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal by (auto intro: wait_assn.intros)
            apply (rule conjI)
             prefer 2 subgoal by auto
            unfolding combine_assn_def
            apply (rule exI[where x="WaitBlk (d - d2) (\<lambda>t. State (p (t + d2))) rdy # OutBlock ch (e (p d)) # tr12"])
            apply (rule exI[where x=tr22])
            apply (rule conjI)
             prefer 2 subgoal apply (rule conjI)
               apply (rule b(2)) by auto
            unfolding join_assn_def
            apply (rule exI[where x="[WaitBlk (d - d2) (\<lambda>t. State (p (t + d2))) rdy, OutBlock ch (e (p d))]"])
            apply (rule exI[where x=tr12])
            apply (rule conjI)
            subgoal
              using wait_out_assn.intros(2)[of "d - d2" "\<lambda>t. p (t + d2)" ch e rdy]
              by (simp add: d3)
            using a(2) by auto
          done
      qed
    qed
    show ?thesis
      using a(1) apply (cases rule: wait_out_assn.cases)
      subgoal
        using that(3) unfolding a(3) b(3) c
        apply auto
        using assms combine_blocks_pairE2 by blast
      subgoal
        using that(3) unfolding a(3) b(3) c
        apply auto using d by auto
      done
  qed
  show ?thesis
    apply (subst combine_assn_def)
    apply (auto simp add: entails_tassn_def)
    using * by auto
qed

lemma combine_assn_waitout_in:
  assumes "ch \<in> chs"
    and "ch \<in> fst rdy"
  shows "combine_assn chs (WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) (In\<^sub>t s ch v @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         (\<up>(d = 0) \<and>\<^sub>t \<up>(v = e (p 0)) \<and>\<^sub>t
          (IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q))"
proof -
  have *: "(\<up> (d = 0) \<and>\<^sub>t \<up> (v = e (p 0)) \<and>\<^sub>t IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q) tr"
    if "(WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) tr1"
       "(In\<^sub>t s ch v @\<^sub>t Q) tr2"
       "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "WaitOut\<^sub>t d p ch e rdy tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "In\<^sub>t s ch v tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    show ?thesis
      using a(1) apply (cases rule: wait_out_assn.cases)
      subgoal
        using b(1) apply (cases rule: in_assn.cases)
        subgoal
          using that(3) unfolding a(3) b(3) apply auto
          apply (elim combine_blocks_pairE) using assms(1) apply auto
          apply (auto simp add: conj_assn_def pure_assn_def join_assn_def)
          apply (rule exI[where x="[IOBlock ch (e (p 0))]"])
          apply (auto intro: io_assn.intros)
          unfolding combine_assn_def using a(2) b(2) by auto
        subgoal
          using that(3) unfolding a(3) b(3) apply auto
          apply (elim combine_blocks_pairE2) by (rule assms)
        subgoal
          using that(3) unfolding a(3) b(3) apply auto
          apply (elim combine_blocks_pairE2) by (rule assms)
        done
      using b(1) apply (cases rule: in_assn.cases)
      using that(3) unfolding a(3) b(3) apply auto
      subgoal apply (elim combine_blocks_pairE2') by (rule assms)
      subgoal for d' apply (elim combine_blocks_waitE1)
        using assms(2) apply (cases rdy) by auto
      subgoal apply (elim combine_blocks_waitE1)
        using assms(2) apply (cases rdy) by auto
      done
  qed
  show ?thesis
    apply (subst combine_assn_def)
    apply (auto simp add: entails_tassn_def)
    using * by auto
qed

lemma combine_assn_waitout_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def wait_out_assn.simps)
  using assms by (auto elim: sync_elims)

subsection \<open>Assertions for global states\<close>

definition entails_gassn :: "gassn \<Rightarrow> gassn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>g" 25) where
  "(P \<Longrightarrow>\<^sub>g Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

definition state_gassn :: "gs_assn \<Rightarrow> gassn" where
  "state_gassn P = (\<lambda>s tr. P s)"

fun left_gassn :: "gs_assn \<Rightarrow> gassn" where
  "left_gassn P (State s) tr = False"
| "left_gassn P (ParState s1 s2) tr = P s1"

fun right_gassn :: "gs_assn \<Rightarrow> gassn" where
  "right_gassn P (State s) tr = False"
| "right_gassn P (ParState s1 s2) tr = P s2"

definition trace_gassn :: "tassn \<Rightarrow> gassn" where
  "trace_gassn P = (\<lambda>s tr. P tr)"

definition and_gassn :: "gassn \<Rightarrow> gassn \<Rightarrow> gassn" (infixr "\<and>\<^sub>g" 35) where
  "(P \<and>\<^sub>g Q) = (\<lambda>s tr. P s tr \<and> Q s tr)"

definition ex_gassn :: "('a \<Rightarrow> gassn) \<Rightarrow> gassn" (binder "\<exists>\<^sub>g" 10) where
  "(\<exists>\<^sub>g x. P x) = (\<lambda>s tr. \<exists>x. P x s tr)"

lemma ParValid_conseq':
  assumes "\<Turnstile>\<^sub>p {P} c {Q}"
    and "\<And>s. P' s \<Longrightarrow> P s"
    and "Q \<Longrightarrow>\<^sub>g Q'"
  shows "\<Turnstile>\<^sub>p {P'} c {Q'}"
  using assms ParValid_conseq unfolding entails_gassn_def by auto

lemma sync_gassn_ex_pre_left:
  assumes "\<And>x. sync_gassn chs (P x) Q \<Longrightarrow>\<^sub>g R"
  shows "sync_gassn chs (\<exists>\<^sub>g x. P x) Q \<Longrightarrow>\<^sub>g R"
  apply (auto simp add: entails_gassn_def)
  subgoal for s tr
    apply (cases s) apply auto
    unfolding ex_gassn_def apply auto
    using assms entails_gassn_def by fastforce
  done

lemma sync_gassn_ex_pre_right:
  assumes "\<And>x. sync_gassn chs P (Q x) \<Longrightarrow>\<^sub>g R"
  shows "sync_gassn chs P (\<exists>\<^sub>g x. Q x) \<Longrightarrow>\<^sub>g R"
  apply (auto simp add: entails_gassn_def)
  subgoal for s tr
    apply (cases s) apply auto
    unfolding ex_gassn_def apply auto
    using assms entails_gassn_def by fastforce
  done

lemma entails_ex_gassn:
  assumes "\<exists>x. P \<Longrightarrow>\<^sub>g Q x"
  shows "P \<Longrightarrow>\<^sub>g (\<exists>\<^sub>g x. Q x)"
  using assms unfolding entails_gassn_def ex_gassn_def by auto

lemma sing_gassn_split:
  "sing_gassn (\<lambda>s tr. P s \<and> Q tr) = (state_gassn (sing_assn P) \<and>\<^sub>g trace_gassn Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: state_gassn_def trace_gassn_def and_gassn_def)
  done

lemma sing_gassn_split2:
  "sing_gassn (\<lambda>s. \<up>(b s) \<and>\<^sub>t Q s) = (state_gassn (sing_assn b) \<and>\<^sub>g sing_gassn Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s)
    by (auto simp add: state_gassn_def trace_gassn_def and_gassn_def conj_assn_def pure_assn_def)
  done

lemma sing_gassn_ex:
  "sing_gassn (\<lambda>s tr. \<exists>x. P x s tr) = (\<exists>\<^sub>gx. sing_gassn (\<lambda>s tr. P x s tr))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: ex_gassn_def)
  done

lemma sync_gassn_state_left:
  "sync_gassn chs (state_gassn P1 \<and>\<^sub>g P2) Q = (left_gassn P1 \<and>\<^sub>g sync_gassn chs P2 Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: and_gassn_def state_gassn_def)
  done

lemma sync_gassn_state_right:
  "sync_gassn chs P (state_gassn Q1 \<and>\<^sub>g Q2) = (right_gassn Q1 \<and>\<^sub>g sync_gassn chs P Q2)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: and_gassn_def state_gassn_def)
  done

lemma sync_gassn_traces:
  "sync_gassn chs (trace_gassn P) (trace_gassn Q) \<Longrightarrow>\<^sub>g trace_gassn (combine_assn chs P Q)"
  unfolding entails_gassn_def apply auto
  subgoal for s tr
    apply (cases s) by (auto simp add: trace_gassn_def combine_assn_def)
  done

lemma entails_trace_gassn:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> trace_gassn P \<Longrightarrow>\<^sub>g trace_gassn Q"
  unfolding entails_tassn_def entails_gassn_def trace_gassn_def by auto 

lemma and_entails_gassn:
  "P2 \<Longrightarrow>\<^sub>g P2' \<Longrightarrow> P1 \<and>\<^sub>g P2' \<Longrightarrow>\<^sub>g Q \<Longrightarrow> P1 \<and>\<^sub>g P2 \<Longrightarrow>\<^sub>g Q"
  unfolding entails_gassn_def and_gassn_def by auto

lemma and_entails_gassn2:
  "P3 \<Longrightarrow>\<^sub>g P3' \<Longrightarrow> P1 \<and>\<^sub>g P2 \<and>\<^sub>g P3' \<Longrightarrow>\<^sub>g Q \<Longrightarrow> P1 \<and>\<^sub>g P2 \<and>\<^sub>g P3 \<Longrightarrow>\<^sub>g Q"
  unfolding entails_gassn_def and_gassn_def by auto

lemma sync_gassn_expand:
  "sync_gassn chs (sing_gassn P) (sing_gassn Q) s tr \<Longrightarrow>
    (\<And>s1 s2. s = ParState (State s1) (State s2) \<Longrightarrow> combine_assn chs (P s1) (Q s2) tr \<Longrightarrow> R) \<Longrightarrow> R"
  apply (cases s)
  subgoal for s' by auto
  subgoal for s1 s2
    apply (cases s1) subgoal for s1'
      apply (cases s2) subgoal for s2'
        by (auto simp add: combine_assn_def)
      by auto
    by auto
  done

lemma combine_assn_and_left:
  "combine_assn chs (\<up>b \<and>\<^sub>t P) Q = ((\<up>b) \<and>\<^sub>t combine_assn chs P Q)"
  by (auto simp add: combine_assn_def conj_assn_def pure_assn_def)

lemma combine_assn_and_right:
  "combine_assn chs P (\<up>b \<and>\<^sub>t Q) = ((\<up>b) \<and>\<^sub>t combine_assn chs P Q)"
  by (auto simp add: combine_assn_def conj_assn_def pure_assn_def)


end
