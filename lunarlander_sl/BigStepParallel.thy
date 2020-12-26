theory BigStepParallel
  imports BigStepSimple
begin


subsection \<open>Combining two traces\<close>

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
   hist = (\<lambda>\<tau>\<in>{0..t}. ParState (hist1 \<tau>) (hist2 \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlock t hist1 rdy1 # blks1) (WaitBlock t hist2 rdy2 # blks2)
                  (WaitBlock t hist rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlock (t2 - t1) (\<lambda>\<tau>\<in>{0..t2-t1}. hist2 (\<tau> + t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow> t1 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>\<in>{0..t1}. ParState (hist1 \<tau>) (hist2 \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlock t1 hist1 rdy1 # blks1) (WaitBlock t2 hist2 rdy2 # blks2)
                  (WaitBlock t1 hist rdy # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlock (t1 - t2) (\<lambda>\<tau>\<in>{0..t1-t2}. hist1 (\<tau> + t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow> t2 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>\<in>{0..t2}. ParState (hist1 \<tau>) (hist2 \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlock t1 hist1 rdy1 # blks1) (WaitBlock t2 hist2 rdy2 # blks2)
                  (WaitBlock t2 hist rdy # blks)"


subsection \<open>Basic elimination rules\<close>

text \<open>Empty case\<close>
lemma combine_blocks_elim1:
  "combine_blocks comms [] [] blks \<Longrightarrow> blks = []"
  by (induct rule: combine_blocks.cases, auto)

text \<open>IO cases\<close>
lemma combine_blocks_elim2:
  "combine_blocks comms (InBlock ch v # blks1) (OutBlock ch w # blks2) blks \<Longrightarrow>
   ch \<in> comms \<Longrightarrow>
   (\<And>blks'. w = v \<Longrightarrow> blks = IOBlock ch v # blks' \<Longrightarrow> combine_blocks comms blks1 blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2a:
  "combine_blocks comms (OutBlock ch v # blks1) (InBlock ch w # blks2) blks \<Longrightarrow>
   ch \<in> comms \<Longrightarrow>
   (\<And>blks'. w = v \<Longrightarrow> blks = IOBlock ch v # blks' \<Longrightarrow> combine_blocks comms blks1 blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2b:
  "combine_blocks comms (OutBlock ch v # blks1) (WaitBlock d p rdy # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2c:
  "combine_blocks comms (InBlock ch v # blks1) (WaitBlock d p rdy # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2d:
  "combine_blocks comms (WaitBlock d p rdy # blks1) (OutBlock ch v # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2e:
  "combine_blocks comms (WaitBlock d p rdy # blks1) (InBlock ch v # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2f:
  "combine_blocks comms [] (InBlock ch v # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2g:
  "combine_blocks comms [] (OutBlock ch v # blks2) blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2h:
  "combine_blocks comms (InBlock ch v # blks2) [] blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim2i:
  "combine_blocks comms (OutBlock ch v # blks2) [] blks \<Longrightarrow> ch \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)


text \<open>IO cases, unpaired\<close>
lemma combine_blocks_elim3:
  "combine_blocks comms (InBlock ch1 v # blks1) (OutBlock ch2 w # blks2) blks \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>blks'. blks = InBlock ch1 v # blks' \<Longrightarrow> combine_blocks comms blks1 (OutBlock ch2 w # blks2) blks' \<Longrightarrow> P) \<Longrightarrow>
   (\<And>blks'. blks = OutBlock ch2 w # blks' \<Longrightarrow> combine_blocks comms (InBlock ch1 v # blks1) blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim3a:
  "combine_blocks comms (InBlock ch1 v # blks1) [] blks \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   (\<And>blks'. blks = InBlock ch1 v # blks' \<Longrightarrow> combine_blocks comms blks1 [] blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim3b:
  "combine_blocks comms [] (OutBlock ch2 w # blks2) blks \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>blks'. blks = OutBlock ch2 w # blks' \<Longrightarrow> combine_blocks comms [] blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

text \<open>Wait cases\<close>
lemma combine_blocks_elim4:
  "combine_blocks comms (WaitBlock d p1 rdy1 # blks1) (WaitBlock d p2 rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>blks'. blks = WaitBlock d (\<lambda>t\<in>{0..d}. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # blks' \<Longrightarrow>
            combine_blocks comms blks1 blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim4a:
  "combine_blocks comms (WaitBlock d1 p1 rdy1 # blks1) (WaitBlock d2 p2 rdy2 # blks2) blks \<Longrightarrow>
   \<not>compat_rdy rdy1 rdy2 \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim4b:
  "combine_blocks comms (WaitBlock d1 p1 rdy1 # blks1) [] blks \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim4c:
  "combine_blocks comms [] (WaitBlock d1 p1 rdy1 # blks1) blks \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim4d:
  "combine_blocks comms (WaitBlock d1 p1 rdy1 # blks1) (WaitBlock d2 p2 rdy2 # blks2) blks \<Longrightarrow>
   d1 < d2 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>blks'. blks = WaitBlock d1 (\<lambda>t\<in>{0..d1}. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # blks' \<Longrightarrow>
            combine_blocks comms blks1 (WaitBlock (d2 - d1) (\<lambda>t\<in>{0..d2-d1}. p2 (t + d1)) rdy2 # blks2) blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_elim4e:
  "combine_blocks comms (WaitBlock d1 p1 rdy1 # blks1) (WaitBlock d2 p2 rdy2 # blks2) blks \<Longrightarrow>
   d1 > d2 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>blks'. blks = WaitBlock d2 (\<lambda>t\<in>{0..d2}. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # blks' \<Longrightarrow>
            combine_blocks comms (WaitBlock (d1 - d2) (\<lambda>t\<in>{0..d1-d2}. p1 (t + d2)) rdy1 # blks1) blks2 blks' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)


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

definition ParValid :: "gs_assn \<Rightarrow> pproc \<Rightarrow> gassn \<Rightarrow> bool" where
  "ParValid P c Q \<longleftrightarrow> (\<forall>s1 s2 tr2. P s1 \<longrightarrow> par_big_step c s1 tr2 s2 \<longrightarrow> Q s2 tr2)"


inductive_cases SingleE: "par_big_step (Single p) s1 tr s2"
thm SingleE

inductive_cases ParallelE: "par_big_step (Parallel p1 ch p2) s1 tr s2"
thm ParallelE

lemma ParValid_Single:
  assumes "Valid (\<lambda>s tr. P s \<and> tr = []) c Q"
  shows "ParValid (sing_assn P) (Single c) (sing_gassn Q)"
  using assms unfolding ParValid_def Valid_def
  by (metis SingleE append_Nil gstate.inject(1) sing_assn.elims(2) sing_gassn.simps(1))

lemma ParValid_Parallel:
  assumes "ParValid P1 p1 Q1"
    and "ParValid P2 p2 Q2"
  shows "ParValid (par_assn P1 P2) (Parallel p1 chs p2) (sync_gassn chs Q1 Q2)"
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
  assumes "ParValid P c Q"
    and "\<And>s. P' s \<Longrightarrow> P s"
    and "\<And>s tr. Q s tr \<Longrightarrow> Q' s tr"
  shows "ParValid P' c Q'"
  using assms unfolding ParValid_def by blast


subsection \<open>Combining standard assertions\<close>

lemma combine_assn_elim2:
  "combine_blocks comms tr1 tr2 tr \<Longrightarrow>
   Out\<^sub>A s1 ch v tr1 \<Longrightarrow>
   In\<^sub>A s2 ch w tr2 \<Longrightarrow>
   ch \<in> comms \<Longrightarrow>
   (w = v \<Longrightarrow> tr = [IOBlock ch v] \<Longrightarrow> P) \<Longrightarrow> P"
  apply (simp only: out_assn.simps in_assn.simps)
  apply (auto elim!: combine_blocks_elim1 combine_blocks_elim2a combine_blocks_elim2b
                     combine_blocks_elim2e combine_blocks_elim4a )
  by (simp add: combine_blocks_elim1)

lemma combine_assn_elim2a:
  "combine_blocks comms (tr1 @ tr1') (tr2 @ tr2') tr \<Longrightarrow>
   Out\<^sub>A s1 ch v tr1 \<Longrightarrow>
   In\<^sub>A s2 ch w tr2 \<Longrightarrow>
   ch \<in> comms \<Longrightarrow>
   (\<And>blks'. w = v \<Longrightarrow> tr = [IOBlock ch w] @ blks' \<Longrightarrow> combine_blocks comms tr1' tr2' blks' \<Longrightarrow> P) \<Longrightarrow> P"
  apply (simp only: out_assn.simps in_assn.simps)
  by (auto elim!: combine_blocks_elim1 combine_blocks_elim2a combine_blocks_elim2b
                  combine_blocks_elim2e combine_blocks_elim4a)

lemma combine_assn_elim2a':
  "combine_blocks comms (tr1 @ tr1') (tr2 @ tr2') tr \<Longrightarrow>
   In\<^sub>A s1 ch v tr1 \<Longrightarrow>
   Out\<^sub>A s2 ch w tr2 \<Longrightarrow>
   ch \<in> comms \<Longrightarrow>
   (\<And>blks'. w = v \<Longrightarrow> tr = [IOBlock ch w] @ blks' \<Longrightarrow> combine_blocks comms tr1' tr2' blks' \<Longrightarrow> P) \<Longrightarrow> P"
  apply (simp only: out_assn.simps in_assn.simps)
  by (auto elim!: combine_blocks_elim1 combine_blocks_elim2 combine_blocks_elim2c
                  combine_blocks_elim2d combine_blocks_elim4a)

lemma combine_assn_elim2b:
  "combine_blocks comms [] tr2 tr \<Longrightarrow> ch \<in> comms \<Longrightarrow> (In\<^sub>A s ch a @\<^sub>t Q) tr2 \<Longrightarrow> P"
  apply (simp only: in_assn.simps join_assn_def)
  by (auto elim!: combine_blocks_elim2f combine_blocks_elim4c)

lemma combine_assn_elim2c:
  "combine_blocks comms tr1 [] tr \<Longrightarrow> ch \<in> comms \<Longrightarrow> (Out\<^sub>A s ch a @\<^sub>t Q) tr1 \<Longrightarrow> P"
  apply (simp only: out_assn.simps join_assn_def)
  by (auto elim!: combine_blocks_elim2i combine_blocks_elim4b)


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
  "combine_assn chs emp\<^sub>A emp\<^sub>A = emp\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: emp_assn_def)
   apply (elim combine_blocks_elim1)
  by (rule combine_blocks_empty)

lemma combine_assn_emp_in:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>A (In\<^sub>A s ch v @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_assn.cases)
  by (auto elim!: combine_blocks_elim2f combine_blocks_elim4c)

lemma combine_assn_in_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (In\<^sub>A s ch v @\<^sub>t P) emp\<^sub>A = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_assn.cases)
  by (auto elim!: combine_blocks_elim2h combine_blocks_elim4b)

lemma combine_assn_emp_out:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>A (Out\<^sub>A s ch v @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_assn.cases)
  by (auto elim!: combine_blocks_elim2g combine_blocks_elim4c)

lemma combine_assn_out_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (Out\<^sub>A s ch v @\<^sub>t P) emp\<^sub>A = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_assn.cases)
  by (auto elim!: combine_blocks_elim2i combine_blocks_elim4b)

lemma combine_assn_out_in:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Out\<^sub>A s1 ch v @\<^sub>t P) (In\<^sub>A s2 ch w @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>A ch v @\<^sub>t combine_assn chs P Q))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_assn.simps)
   apply (auto elim!: combine_assn_elim2a) by auto

lemma combine_assn_out_in':
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Out\<^sub>A s1 ch v) (In\<^sub>A s2 ch w) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>A ch v))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_assn.simps)
  by (auto elim!: combine_assn_elim2)

lemma combine_assn_in_out:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (In\<^sub>A s1 ch v @\<^sub>t P) (Out\<^sub>A s2 ch w @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>A ch v @\<^sub>t combine_assn chs P Q))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_assn.simps)
   apply (auto elim!: combine_assn_elim2a') by auto

lemma combine_assn_wait_emp:
  "combine_assn chs (Wait\<^sub>A d p @\<^sub>t P) emp\<^sub>A \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def false_assn_def)
  by (auto elim!: combine_blocks_elim4b)

lemma combine_assn_emp_wait:
  "combine_assn chs emp\<^sub>A (Wait\<^sub>A d p @\<^sub>t P) \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def false_assn_def)
  by (auto elim!: combine_blocks_elim4c)

lemma combine_assn_wait:
  "combine_assn chs (Wait\<^sub>A d p @\<^sub>t P) (Wait\<^sub>A d q @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Wait\<^sub>A d (\<lambda>t. ParState (p t) (q t)) @\<^sub>t combine_assn chs P Q)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def wait_assn.simps)
  apply (auto elim!: combine_blocks_elim4) by auto

lemma combine_assn_wait_in:
  assumes "ch \<in> chs"
  shows "combine_assn chs (Wait\<^sub>A d p @\<^sub>t P) (In\<^sub>A s ch v @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Wait\<^sub>A d (\<lambda>t\<in>{0..d}. ParState (p t) (State s)) @\<^sub>t combine_assn chs P (In\<^sub>A s ch v @\<^sub>t Q))"
proof -
  have *: "\<exists>tr1. P tr1 \<and> (\<exists>tr2. (\<exists>tr1. In\<^sub>A s ch v tr1 \<and> (\<exists>tr2a. Q tr2a \<and> tr2 = tr1 @ tr2a)) \<and> combine_blocks chs tr1 tr2 (tl tr))"
       "tr = WaitBlock d (\<lambda>t\<in>{0..d}. ParState (p t) (State s)) ({}, {}) # tl tr"
    if "combine_blocks chs (WaitBlock d (restrict p {0..d}) ({}, {}) # tr1'') (tr2' @ tr2'') tr"
       "In\<^sub>A s ch v tr2'"
       "P tr1''"
       "Q tr2''" for tr tr2' tr1'' tr2''
  proof -
    show "\<exists>tr1. P tr1 \<and> (\<exists>tr2. (\<exists>tr1. In\<^sub>A s ch v tr1 \<and> (\<exists>tr2a. Q tr2a \<and> tr2 = tr1 @ tr2a)) \<and> combine_blocks chs tr1 tr2 (tl tr))"
      apply (rule exI[where x=tr1''])
      apply (auto simp add: that(3))
      sorry
    show "tr = WaitBlock d (\<lambda>t\<in>{0..d}. ParState (p t) (State s)) ({}, {}) # tl tr"
      sorry
  qed
  show ?thesis
    unfolding combine_assn_def
    apply (auto simp add: entails_tassn_def)
    subgoal for tr tr1 tr2
      apply (auto simp add: join_assn_def)
      subgoal for tr1' tr2' tr1'' tr2''
        apply (rule exI[where x="[WaitBlock d (\<lambda>t\<in>{0..d}. ParState (p t) (State s)) ({}, {})]"])
        apply (auto simp add: wait_assn.simps)[1]
        apply (rule exI[where x="tl tr"])
        using * by auto
      done
    done
qed

(*
  apply (auto simp add: entails_tassn_def join_assn_def wait_assn.simps in_assn.simps)
  using assms apply (auto elim!: combine_blocks_elim2e)
  subgoal for tr tr2 tr2' d'
    apply (rule exI[where x=tr2'])
    apply auto
     apply (rule exI[where x=tr2])
    apply auto
*)

end
