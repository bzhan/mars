theory Coinductive_par
  imports Main "HOL-Library.BNF_Corec" Ordinary_Differential_Equations.Flow
begin

subsection \<open>Definition of states\<close>

text \<open>Variable names\<close>
type_synonym var = char

text \<open>State\<close>
type_synonym state = "var \<Rightarrow> real"

text \<open>Expressions\<close>
type_synonym exp = "state \<Rightarrow> real"

text \<open>Predicates\<close>
type_synonym fform = "state \<Rightarrow> bool"

text \<open>States as a vector\<close>
type_synonym vec = "real^(var)"

type_synonym tid = real

text \<open>Conversion between state and vector\<close>
definition state2vec :: "state \<Rightarrow> vec" where
  "state2vec s = (\<chi> x. s x)"

definition vec2state :: "vec \<Rightarrow> state" where
  "(vec2state v) x = v $ x"



type_synonym 'a ext_state = "'a \<times> state"

type_synonym 'a ext_exp = "'a ext_state \<Rightarrow> real"

type_synonym 'a ext_fform = "'a ext_state \<Rightarrow> bool"

type_synonym cname = string

type_synonym rdy_info = "cname set \<times> cname set"

(*
datatype 'a gstate =
  EmptyState
| EState "'a ext_state"
| ParState "'a gstate"  "'a gstate"
*)

type_synonym 'a gstate = "tid \<Rightarrow> 'a ext_state"

definition Estate :: "tid \<Rightarrow> 'a ext_state \<Rightarrow> 'a gstate" where
"Estate i s = (\<lambda> id . if id = i then s else undefined)"

definition supp_gstate :: "'a gstate \<Rightarrow> tid set" where
"supp_gstate a = {i. a i \<noteq> undefined}"

definition supp_gstateb :: "'a gstate set \<Rightarrow> bool" where
"supp_gstateb S = (\<forall> a b. a\<in>S \<longrightarrow> b\<in>S \<longrightarrow> a\<noteq> b \<longrightarrow>supp_gstate a \<inter> supp_gstate b = {})"

definition supp_gstate_set :: "'a gstate set \<Rightarrow> tid \<Rightarrow> 'a gstate set" where
"supp_gstate_set S i = {s. i \<in> supp_gstate s}"

definition ParState :: "'a gstate set \<Rightarrow> 'a gstate" where
"ParState S = (if supp_gstateb S then undefined else (\<lambda> i. undefined)) "


datatype comm_type = In | Out | IO

datatype 'a trace_block =
  CommBlock comm_type cname real
| WaitBlock ereal "real \<Rightarrow> 'a gstate" rdy_info

abbreviation "InBlock ch v \<equiv> CommBlock In ch v"
abbreviation "OutBlock ch v \<equiv> CommBlock Out ch v"
abbreviation "IOBlock ch v \<equiv> CommBlock IO ch v"

fun WaitBlk :: "ereal \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> 'a trace_block" where
  "WaitBlk (ereal d) p rdy = WaitBlock (ereal d) (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"
| "WaitBlk PInfty p rdy = WaitBlock PInfty (\<lambda>\<tau>\<in>{0..}. p \<tau>) rdy"
| "WaitBlk MInfty p rdy = WaitBlock MInfty (\<lambda>_. undefined) rdy"

lemma WaitBlk_simps [simp]:
  "WaitBlk (ereal d) p rdy = WaitBlock (ereal d) (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"
  "WaitBlk \<infinity> p rdy = WaitBlock \<infinity> (\<lambda>\<tau>\<in>{0..}. p \<tau>) rdy"
  "WaitBlk (-\<infinity>) p rdy = WaitBlock (-\<infinity>) (\<lambda>_. undefined) rdy"
  apply auto
  using WaitBlk.simps(2) infinity_ereal_def 
  apply metis
  using WaitBlk.simps(3) 
  by (metis MInfty_eq_minfinity)

declare WaitBlk.simps [simp del]

lemma WaitBlk_not_Comm [simp]:
  "WaitBlk d p rdy \<noteq> CommBlock ch_type ch v"
  "CommBlock ch_type ch v \<noteq> WaitBlk d p rdy"
  by (cases d, auto)+


lemma restrict_cong_to_eq:
  fixes x :: real
  shows "restrict p1 {0..t} = restrict p2 {0..t} \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma restrict_cong_to_eq2:
  fixes x :: real
  shows "restrict p1 {0..} = restrict p2 {0..} \<Longrightarrow> 0 \<le> x \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma WaitBlk_ext:
  fixes t1 t2 :: ereal
    and hist1 hist2 :: "real \<Rightarrow> 'a gstate"
  shows "t1 = t2 \<Longrightarrow>
   (\<And>\<tau>::real. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
   WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
  apply (cases t1)
  apply (auto simp add: restrict_def)
  apply (rule ext) by auto

lemma WaitBlk_ext_real:
  fixes t1 :: real
    and t2 :: real
  shows "t1 = t2 \<Longrightarrow> (\<And>\<tau>. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
         WaitBlk (ereal t1) hist1 rdy1 = WaitBlk (ereal t2) hist2 rdy2"
  by (auto simp add: restrict_def)

lemma WaitBlk_cong:
  "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2 \<Longrightarrow> t1 = t2 \<and> rdy1 = rdy2"
  apply (cases t1) by (cases t2, auto)+

lemma WaitBlk_cong2:
  assumes "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
    and "0 \<le> t" "t \<le> t1"
  shows "hist1 t = hist2 t"
proof -
  have a: "t1 = t2" "rdy1 = rdy2"
    using assms WaitBlk_cong 
    by blast+
  show ?thesis
  proof (cases t1)
    case (real r)
    have real2: "t2 = ereal r"
      using real a by auto
    show ?thesis
      using assms(1)[unfolded real real2]
      apply auto using restrict_cong_to_eq assms ereal_less_eq(3) real by blast
  next
    case PInf
    have PInf2: "t2 = \<infinity>"
      using PInf a by auto
    show ?thesis
      using assms(1)[unfolded PInf PInf2] restrict_cong_to_eq2 assms by auto
  next
    case MInf
    show ?thesis
      using assms MInf by auto
  qed
qed

lemma WaitBlk_split1:
  fixes t1 :: real
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "ereal t1 < t"
  shows "WaitBlk (ereal t1) p1 rdy = WaitBlk (ereal t1) p2 rdy"
proof (cases t)
  case (real r)
  show ?thesis
    apply auto apply (rule ext) subgoal for x
      using assms[unfolded real] 
      using restrict_cong_to_eq[of p1 r p2 x] by auto
    done
next
  case PInf
  show ?thesis
    apply auto apply (rule ext) subgoal for x
      using assms[unfolded PInf] restrict_cong_to_eq2[of p1 p2 x] by auto
    done
next
  case MInf
  then show ?thesis
    using assms by auto
qed

lemma WaitBlk_split2:
  fixes t1 :: real
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "ereal t1 < t"
  shows "WaitBlk (t - ereal t1) (\<lambda>\<tau>::real. p1 (\<tau> + t1)) rdy =
         WaitBlk (t - ereal t1) (\<lambda>\<tau>::real. p2 (\<tau> + t1)) rdy"
proof (cases t)
  case (real r)
  have a: "t - ereal t1 = ereal (r - t1)"
    unfolding real by auto
  show ?thesis
    unfolding a apply auto apply (rule ext) subgoal for x
      using assms[unfolded real]
      using restrict_cong_to_eq[of p1 r p2 "x + t1"] by auto
    done
next
  case PInf
  have a: "t - ereal t1 = \<infinity>"
    unfolding PInf by auto
  show ?thesis
    unfolding a
    apply auto
    apply (rule ext) subgoal for x
      using assms[unfolded PInf] restrict_cong_to_eq2[of p1 p2 "x + t1"] by auto
    done
next
  case MInf
  then show ?thesis
    using assms by auto
qed

lemmas WaitBlk_split = WaitBlk_split1 WaitBlk_split2
declare WaitBlk_simps [simp del]



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
(*
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
*)



fun compat_rdy_set :: "rdy_info set \<Rightarrow> bool" where
  "compat_rdy_set S = (\<forall> i \<in> S . \<forall> j \<in> S . i \<noteq> j \<longrightarrow> fst i \<inter> snd j = {})"

fun merge_rdy_set :: "rdy_info set \<Rightarrow> rdy_info " where
  "merge_rdy_set S  = (\<Union> (image fst S), \<Union> (image snd S))"


coinductive combine_blocks_set :: "cname set \<Rightarrow> tid set \<Rightarrow> (tid \<Rightarrow> 'a strace) \<Rightarrow> 'a strace \<Rightarrow> bool" where
  \<comment> \<open>Paired communication\<close>
  combine_blocks_pair:
  "ch \<in> comms \<Longrightarrow>
   i \<in> S \<Longrightarrow> j \<in> S \<Longrightarrow>
   f i = (SCons (InBlock ch v) blksi) \<Longrightarrow>
   f j = (SCons (OutBlock ch v) blksj) \<Longrightarrow>
   g = f(i := blksi, j := blksj) \<Longrightarrow> 
   combine_blocks_set comms S g blks \<Longrightarrow>
   combine_blocks_set comms S f (SCons (IOBlock ch v) blks)"

  \<comment> \<open>Paired communication\<close>
| combine_blocks_unpair1:
  "ch \<notin> comms \<Longrightarrow>
   i \<in> S \<Longrightarrow>
   f i = (SCons (CommBlock ch_type ch v) blksi) \<Longrightarrow>
   g = f(i := blksi) \<Longrightarrow>
   combine_blocks_set comms S g blks \<Longrightarrow>
   combine_blocks_set comms S f (SCons (CommBlock ch_type ch v) blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_wait:
  "combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (SCons (WaitBlk t (\<lambda>x::real. hist1 x) rdy1) blks1)
                        (SCons (WaitBlk t (\<lambda>x::real. hist2 x) rdy2) blks2)
                        (SCons (WaitBlk t hist rdy) blks)"



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



end
