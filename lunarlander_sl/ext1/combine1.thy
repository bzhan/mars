theory combine1
  imports sch
begin


lemma combine_assn_wait_emp':
  "combine_assn chs (Wait\<^sub>t d p rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t combine_assn chs P emp\<^sub>t "
  unfolding combine_assn_def entails_tassn_def
  apply (auto)
  apply (simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def)
  by (auto elim!: sync_elims)

lemma combine_assn_emp_wait':
  "combine_assn chs emp\<^sub>t (Wait\<^sub>t d p rdy @\<^sub>t P) \<Longrightarrow>\<^sub>t combine_assn chs emp\<^sub>t P"
  unfolding combine_assn_def entails_tassn_def
  apply (auto )
  apply (simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def)
  by (auto elim!: sync_elims)

lemma combine_or_right:
"combine_assn chs p q1 \<Longrightarrow>\<^sub>t R \<Longrightarrow> combine_assn chs p q2 \<Longrightarrow>\<^sub>t R \<Longrightarrow> combine_assn chs (p) (q1 \<or>\<^sub>t q2) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def disj_assn_def entails_tassn_def
  apply auto
  by blast

lemma combine_or_left:
"combine_assn chs p1 q \<Longrightarrow>\<^sub>t R \<Longrightarrow> combine_assn chs p2 q \<Longrightarrow>\<^sub>t R \<Longrightarrow> combine_assn chs (p1 \<or>\<^sub>t p2) q \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def disj_assn_def entails_tassn_def
  apply auto
  by blast


lemma combine_assn_ex_pre_left':
  assumes "\<And>x. combine_assn chs (P x) Q \<Longrightarrow>\<^sub>t R"
  shows "combine_assn chs (\<exists>\<^sub>t x. P x) Q \<Longrightarrow>\<^sub>t R"
  using assms by (auto simp add: ex_assn_def combine_assn_def entails_tassn_def)

lemma combine_assn_ex_pre_right':
  assumes "\<And>x. combine_assn chs P (Q x) \<Longrightarrow>\<^sub>t R"
  shows "combine_assn chs P (\<exists>\<^sub>t x. Q x) \<Longrightarrow>\<^sub>t R"
  using assms by (auto simp add: ex_assn_def combine_assn_def entails_tassn_def)

lemma combine_assn_pure_pre_left':
  assumes "b \<Longrightarrow> combine_assn chs P Q \<Longrightarrow>\<^sub>t R"
  shows "combine_assn chs (\<up>b \<and>\<^sub>t P) (Q) \<Longrightarrow>\<^sub>t R"
  using assms by (auto simp add: pure_assn_def combine_assn_def entails_tassn_def conj_assn_def)


lemma combine_assn_pure_pre_right':
  assumes "b \<Longrightarrow> combine_assn chs P (Q) \<Longrightarrow>\<^sub>t R"
  shows "combine_assn chs P (\<up>b \<and>\<^sub>t Q) \<Longrightarrow>\<^sub>t R"
  using assms by (auto simp add: pure_assn_def combine_assn_def entails_tassn_def conj_assn_def)


lemma combine_assn_emp_waitin:
  assumes "ch \<in> chs"
  shows "combine_assn chs emp\<^sub>t (Waitin\<^sub>t d p ch v rdy @\<^sub>t P)\<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def waitin_assn.simps)
  using assms by (auto elim: sync_elims)


lemma combine_assn_inrdy_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (Inrdy\<^sub>t s ch v rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def inrdy_assn.simps)
  using assms by (auto elim: sync_elims)


lemma combine_assn_inrdy_emp':
  assumes "ch \<notin> chs"
  shows "combine_assn chs (Inrdy\<^sub>t s ch v rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t In0\<^sub>t ch v @\<^sub>t (combine_assn chs P emp\<^sub>t)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def inrdy_assn.simps)
  using assms apply (auto elim!: sync_elims)
  apply(rule exI[where x="[InBlock ch v]"])
  apply auto
  apply(rule )
  done

fun combine1 :: "nat \<Rightarrow> nat \<Rightarrow> estate ext_state \<Rightarrow> estate ext_state \<Rightarrow> estate tassn" where
  "combine1 0 0 (Sch p rn rp,ss) (Task st ent tp,ts) = (emp\<^sub>t)"
| "combine1 0 (Suc k) (Sch p rn rp,ss) (Task WAIT ent tp,ts) = 
   (combine1 0 k (Sch p rn rp,ss) (Task READY ezero tp,ts(T := 0))) "
| "combine1 0 (Suc k) (Sch p rn rp,ss) (Task READY ent tp,ts) = false\<^sub>A"
| "combine1 0 (Suc k) (Sch p rn rp,ss) (Task RUNNING ent tp,ts) = false\<^sub>A"
| "combine1 (Suc k) 0 (Sch p rn rp,ss) (Task st ent tp,ts) = (
    In0\<^sub>t (req_ch 2) 1 @\<^sub>t emp\<^sub>t
    )"

definition propc :: "nat \<Rightarrow> estate \<Rightarrow> estate \<Rightarrow> bool" where
"propc k schs task_es = (k>0 \<longrightarrow>(status task_es = RUNNING \<longleftrightarrow> run_now schs = 1))"


lemma combine_SCH_T1:
"propc ns (Sch p rn rp) (Task st ent 2) \<Longrightarrow>
   proper schs \<Longrightarrow>
 combine_assn {req_ch 1, preempt_ch 1, run_ch 1, free_ch 1, exit_ch 1} 
 (SCH_tr nt (Sch p rn rp,ts)) (T1_tr ns (Task st ent 2,ss)) \<Longrightarrow>\<^sub>t
 combine1 nt ns (Sch p rn rp,ts) (Task st ent 2,ss) "
proof(induction " nt+ns"  arbitrary: nt ns p rn rp ts st ent ss rule: less_induct)
  case less
  then show ?case 
    apply(cases nt)
    subgoal
      apply(cases ns)
      subgoal
        by auto
      subgoal for ns'
        apply(cases st)
        apply auto
        subgoal premises pre
          apply(rule entails_tassn_trans)
           apply(rule combine_assn_emp_wait')
          using pre(1)[of 0 ns' p rn rp READY ezero ts "ss(T := 0)"]
          apply(subgoal_tac "propc ns' (Sch p rn rp) (Task READY ezero 2)")
          subgoal by auto
          subgoal unfolding propc_def 
            apply(cases ns') subgoal by auto
            by (metis estate.sel(4) less.prems(1) pre(5) pre(6) propc_def status.distinct(3) status.distinct(5) zero_less_Suc)
          done
        subgoal
          apply(rule combine_or_right)
          subgoal
            apply(rule combine_assn_ex_pre_right')+
            apply(rule combine_assn_pure_pre_right')
            by(simp add: combine_assn_emp_out)
          subgoal
            by(simp add: combine_assn_emp_out)
          done
        subgoal
          apply(rule combine_or_right)
          subgoal
            apply(rule combine_assn_ex_pre_right')+
            apply(rule combine_assn_pure_pre_right')
            apply(rule combine_assn_emp_waitin)
            by auto
          subgoal
            apply(rule entails_tassn_trans)
            apply(simp only:join_assoc)
             apply(rule combine_assn_emp_wait')
            by(simp add: combine_assn_emp_out)
          done
        done
      done
    subgoal for nt'
      apply(cases ns)
      subgoal
        apply (simp only: SCH_tr.simps T1_tr.simps)
        apply(rule combine_or_left)
        subgoal
          apply(rule entails_tassn_trans)
           apply(rule combine_assn_inrdy_emp)
          by(auto simp add:false_assn_def)
        apply(rule combine_or_left)
        subgoal
          apply(rule combine_assn_ex_pre_left')+
          apply(rule combine_assn_pure_pre_left')
          apply(rule entails_tassn_trans)
           apply(rule combine_assn_inrdy_emp)
          by(auto simp add:false_assn_def)
        apply(rule combine_or_left)
        subgoal
          apply(simp only:combine1.simps)
          apply(rule entails_tassn_trans)
           apply(rule combine_assn_inrdy_emp')
          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
          apply(rule entails_tassn_cancel_left)

          
qed




end