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
  apply (auto simp add: emp_assn_def)
   apply (elim combine_blocks_elim1)
  by (rule combine_blocks_empty)

lemma combine_assn_emp_in:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (In\<^sub>t s ch v @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_assn.cases)
  by (auto elim!: combine_blocks_elim2f combine_blocks_elim4c)

lemma combine_assn_in_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (In\<^sub>t s ch v @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_assn.cases)
  by (auto elim!: combine_blocks_elim2h combine_blocks_elim4b)

lemma combine_assn_emp_out:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (Out\<^sub>t s ch v @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_assn.cases)
  by (auto elim!: combine_blocks_elim2g combine_blocks_elim4c)

lemma combine_assn_out_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (Out\<^sub>t s ch v @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_assn.cases)
  by (auto elim!: combine_blocks_elim2i combine_blocks_elim4b)

lemma combine_assn_out_in:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Out\<^sub>t s1 ch v @\<^sub>t P) (In\<^sub>t s2 ch w @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_assn.simps
                        out_assn.simps in_assn.simps)
  by (auto elim!: combine_blocks_elim1 combine_blocks_elim2a combine_blocks_elim2b
                  combine_blocks_elim2e combine_blocks_elim4a)

lemma combine_assn_out_in':
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Out\<^sub>t s1 ch v) (In\<^sub>t s2 ch w) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def
                        io_assn.simps out_assn.simps in_assn.simps)
  by (auto elim!: combine_blocks_elim1 combine_blocks_elim2a combine_blocks_elim2b
                  combine_blocks_elim2e combine_blocks_elim4a)

lemma combine_assn_in_out:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (In\<^sub>t s1 ch v @\<^sub>t P) (Out\<^sub>t s2 ch w @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_assn.simps
                        out_assn.simps in_assn.simps)
  by (auto elim!: combine_blocks_elim1 combine_blocks_elim2 combine_blocks_elim2c
                  combine_blocks_elim2d combine_blocks_elim4a)

lemma combine_assn_wait_emp:
  "combine_assn chs (Wait\<^sub>t d p rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def false_assn_def)
  by (auto elim!: combine_blocks_elim4b)

lemma combine_assn_emp_wait:
  "combine_assn chs emp\<^sub>t (Wait\<^sub>t d p rdy @\<^sub>t P) \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def false_assn_def)
  by (auto elim!: combine_blocks_elim4c)

lemma combine_assn_wait:
  "compat_rdy rdy1 rdy2 \<Longrightarrow>
   combine_assn chs (Wait\<^sub>t d p rdy1 @\<^sub>t P) (Wait\<^sub>t d q rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Wait\<^sub>t d (\<lambda>t. ParState (p t) (q t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P Q)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def wait_assn.simps)
  apply (auto elim!: combine_blocks_elim4) by auto


lemma combine_assn_wait_in:
  assumes "ch \<in> chs"
    and "compat_rdy rdy1 ({}, {ch})"
    and "d > 0"
  shows "combine_assn chs (Wait\<^sub>t d p rdy1 @\<^sub>t P) (In\<^sub>t s ch v @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Wait\<^sub>t d (\<lambda>t. ParState (p t) (State s)) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q))"
proof -
  have *: "(Wait\<^sub>t d (\<lambda>t. ParState (p t) (State s)) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q)) tr"
    if "(Wait\<^sub>t d p rdy1 @\<^sub>t P) tr1" "(In\<^sub>t s ch v @\<^sub>t Q) tr2" "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "Wait\<^sub>t d p rdy1 tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "In\<^sub>t s ch v tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    have c: "tr11 = [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy1]"
      using a(1) wait_assn.cases by blast
    have d: "(Wait\<^sub>t d (\<lambda>t. ParState (p t) (State s)) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q)) tr"
      if "compat_rdy rdy1 ({}, {ch})" "0 < d2"
         "combine_blocks chs (WaitBlock d (restrict p {0..d}) rdy1 # tr12)
          (WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. State s) ({}, {ch}) # InBlock ch v # tr22) tr" for d2
    proof -
      have "d < d2 \<or> d = d2 \<or> d > d2" by auto
      then show ?thesis
      proof (elim disjE)
        assume d1: "d < d2"
        have rw: "WaitBlock (d2 - d) (\<lambda>t\<in>{0..d2 - d}. (\<lambda>\<tau>\<in>{0..d2}. State s) (t + d)) ({}, {ch}) =
                  WaitBlock (d2 - d) (\<lambda>t\<in>{0..d2 - d}. State s) ({}, {ch})"
          apply auto apply (rule ext) using assms(3) by auto
        show ?thesis
          using that(3)
          apply (elim combine_blocks_elim4d)
            apply (rule d1) using that(1) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlock d (\<lambda>t\<in>{0..d}. ParState (p t) (State s)) (merge_rdy rdy1 ({}, {ch}))]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal by (simp add: wait_assn.simps)
            apply (rule conjI)
             prefer 2 subgoal using d1 by auto
            unfolding combine_assn_def
            apply (rule exI[where x=tr12])
            apply (rule exI[where x="WaitBlock (d2 - d) (\<lambda>t\<in>{0..d2 - d}. State s) ({}, {ch}) # InBlock ch v # tr22"])
            apply (rule conjI)
            subgoal by (rule a(2))
            apply (rule conjI)
             prefer 2 subgoal unfolding rw by auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlock (d2 - d) (\<lambda>t\<in>{0..d2 - d}. State s) ({}, {ch}), InBlock ch v]"])
            apply (rule exI[where x=tr22])
            using b(2) d1 by (auto intro: in_assn.intros)
          done
      next
        assume d2: "d = d2"
        show ?thesis
          using that(3) unfolding d2[symmetric]
          apply (elim combine_blocks_elim4)
          using that(1) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlock d (\<lambda>t\<in>{0..d}. ParState (p t) (State s)) (merge_rdy rdy1 ({}, {ch}))]"])
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
        show ?thesis
          using that(3)
          apply (elim combine_blocks_elim4e)
          apply (rule d3)
           using that(1) apply simp
          apply (elim combine_blocks_elim2e)
          using assms by auto
      qed
    qed
    show ?thesis
      using b(1) apply (cases rule: in_assn.cases)
      subgoal
        by (metis Cons_eq_appendI a(3) assms(1) b(3) c combine_blocks_elim2e that(3))
      subgoal for d2
        using that(3) unfolding a(3) b(3) c
        using d assms(2) by auto
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
    have c: "tr21 = [WaitBlock d2 (\<lambda>\<tau>\<in>{0..d2}. p2 \<tau>) rdy2]"
      using b(1) wait_assn.cases by blast
    have d: "(\<up> (d2 \<le> d) \<and>\<^sub>t
             Wait\<^sub>t d2 (\<lambda>t. ParState (State (p t)) (p2 t)) (merge_rdy rdy rdy2) @\<^sub>t
             combine_assn chs (WaitOut\<^sub>t (d - d2) (\<lambda>t. p (t + d2)) ch e rdy @\<^sub>t P) Q) tr"
      if "0 < d"
         "combine_blocks chs (WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) rdy # OutBlock ch (e (p d)) # tr12)
                             (WaitBlock d2 (restrict p2 {0..d2}) rdy2 # tr22) tr"
    proof -
      have "d < d2 \<or> d = d2 \<or> d > d2" by auto
      then show ?thesis
      proof (elim disjE)
        assume d1: "d < d2"
        show ?thesis
          using that(2)
          apply (elim combine_blocks_elim4d)
            apply (rule d1) apply (rule assms(2))
          using assms(1) combine_blocks_elim2b by blast
      next
        assume d2: "d = d2"
        have rw: "WaitBlock d (\<lambda>t\<in>{0..d}. ParState ((\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) t) (restrict p2 {0..d} t)) (merge_rdy rdy rdy2) =
                  WaitBlock d (\<lambda>t\<in>{0..d}. ParState (State (p t)) (p2 t)) (merge_rdy rdy rdy2)"
          by auto
        show ?thesis
          using that(2)
          unfolding d2[symmetric]
          apply (elim combine_blocks_elim4)
           apply (rule assms(2))
          subgoal for blks'
            unfolding pure_assn_def conj_assn_def
            apply (rule conjI)
            subgoal by auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlock d (\<lambda>t\<in>{0..d}. ParState (State (p t)) (p2 t)) (merge_rdy rdy rdy2)]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal by (auto intro: wait_assn.intros)
            apply (rule conjI)
             prefer 2 subgoal unfolding rw by auto
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
        have rw: "WaitBlock (d - d2) (\<lambda>t\<in>{0..d - d2}. (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>)) (t + d2)) rdy =
                  WaitBlock (d - d2) (\<lambda>t\<in>{0..d - d2}. State (p (t + d2))) rdy"
          apply auto apply (rule ext) using d3 that(1) assms(3) by auto
        show ?thesis
          using that(2)
          apply (elim combine_blocks_elim4e)
            apply (rule d3) apply (rule assms(2))
          subgoal for blks'
            unfolding pure_assn_def conj_assn_def
            apply (rule conjI)
            subgoal using d3 by auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlock d2 (\<lambda>t\<in>{0..d2}. ParState (State (p t)) (p2 t)) (merge_rdy rdy rdy2)]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal by (auto intro: wait_assn.intros)
            apply (rule conjI)
             prefer 2 subgoal apply auto apply (rule ext) using d3 by auto
            unfolding combine_assn_def
            apply (rule exI[where x="WaitBlock (d - d2) (\<lambda>t\<in>{0..d - d2}. State (p (t + d2))) rdy # OutBlock ch (e (p d)) # tr12"])
            apply (rule exI[where x=tr22])
            apply (rule conjI)
             prefer 2 subgoal apply (rule conjI)
               apply (rule b(2)) unfolding rw by auto
            unfolding join_assn_def
            apply (rule exI[where x="[WaitBlock (d - d2) (\<lambda>t\<in>{0..d - d2}. State (p (t + d2))) rdy, OutBlock ch (e (p d))]"])
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
        using assms combine_blocks_elim2b by blast
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
          apply (elim combine_blocks_elim2a)
          apply (rule assms(1))
          apply (auto simp add: conj_assn_def pure_assn_def join_assn_def)
          apply (rule exI[where x="[IOBlock ch (e (p 0))]"])
          apply (auto intro: io_assn.intros)
          unfolding combine_assn_def using a(2) b(2) by auto
        using that(3) unfolding a(3) b(3) apply auto
        apply (elim combine_blocks_elim2b) by (rule assms)
      using b(1) apply (cases rule: in_assn.cases)
      using that(3) unfolding a(3) b(3) apply auto
       apply (elim combine_blocks_elim2e) apply (rule assms)
      apply (elim combine_blocks_elim4a)
      using assms(2) apply (cases rdy) by auto
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
  using assms by (auto elim!: combine_blocks_elim2i combine_blocks_elim4b)

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

end
