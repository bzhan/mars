theory combine1
  imports sch
begin


lemma entails_tassn_disjI1:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> P \<Longrightarrow>\<^sub>t (Q \<or>\<^sub>t R)"
  by (auto simp add: entails_tassn_def disj_assn_def)

lemma entails_tassn_disjI2:
  "P \<Longrightarrow>\<^sub>t R \<Longrightarrow> P \<Longrightarrow>\<^sub>t (Q \<or>\<^sub>t R)"
  by (auto simp add: entails_tassn_def disj_assn_def)

lemma entails_tassn_disjE:
  "P \<Longrightarrow>\<^sub>t R \<Longrightarrow> Q \<Longrightarrow>\<^sub>t R \<Longrightarrow> (P \<or>\<^sub>t Q) \<Longrightarrow>\<^sub>t R"
  by (auto simp add: entails_tassn_def disj_assn_def)


lemma combine_assn_left_tran:
"P1 \<Longrightarrow>\<^sub>t Q1 \<Longrightarrow>  combine_assn chs P1 R \<Longrightarrow>\<^sub>t combine_assn chs Q1 R"
  unfolding entails_tassn_def combine_assn_def
  by auto

lemma combine_assn_right_tran:
"P2 \<Longrightarrow>\<^sub>t Q2 \<Longrightarrow>  combine_assn chs R P2 \<Longrightarrow>\<^sub>t combine_assn chs R Q2"
  unfolding entails_tassn_def combine_assn_def
  by auto

lemma combine_assn_both_tran:
"P1 \<Longrightarrow>\<^sub>t Q1 \<Longrightarrow> P2 \<Longrightarrow>\<^sub>t Q2 \<Longrightarrow> combine_assn chs P1 P2 \<Longrightarrow>\<^sub>t combine_assn chs Q1 Q2"
  unfolding entails_tassn_def combine_assn_def
  by auto

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

lemma combine_assn_out0_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (Out0\<^sub>t ch v @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def out_0assn.simps)
  using assms by (auto elim: sync_elims)

lemma combine_assn_out0_emp':
  assumes "ch \<notin> chs"
  shows "combine_assn chs (Out0\<^sub>t ch v @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t Out0\<^sub>t ch v @\<^sub>t (combine_assn chs P emp\<^sub>t)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def out_0assn.simps)
  using assms by (auto elim!: sync_elims)


lemma combine_assn_waitp_emp:
 "combine_assn chs (wait_passn p rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def wait_passn.simps)
  by (auto elim: sync_elims)


lemma combine_assn_inrdy_wait:
  assumes "ch \<in> chs \<and> compat_rdy rdy1 rdy2"
  shows "combine_assn chs (Inrdy\<^sub>t s ch v rdy1 @\<^sub>t P)(Wait\<^sub>t d p rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t Wait\<^sub>t d (\<lambda> t. ParState (EState s) (p t)) (merge_rdy rdy1 rdy2) @\<^sub>t (combine_assn chs (Inrdy\<^sub>t s ch v rdy1 @\<^sub>t P) Q)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def)
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: inrdy_assn.cases[of s ch v rdy1 tr1a])
      apply auto
    subgoal
      apply(cases rule: wait_assn.cases[of d p rdy2 tr1b])
        apply auto
      subgoal using assms
        by (auto elim!: sync_elims)
      subgoal using assms
        apply (auto elim: sync_elims)
        unfolding emp_assn_def
        apply auto
        apply(rule exI[where x="(InBlock ch v # tr2a)"])
        by auto
      done
    subgoal for dd
      apply(cases rule: wait_assn.cases[of d p rdy2 tr1b])
        apply auto
      subgoal using assms
        apply(cases "d<dd")
        subgoal
          apply (auto elim!: combine_blocks_waitE4)
          apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (EState s) (p t)) (merge_rdy rdy1 rdy2)]"])
          apply auto
          subgoal apply rule by auto
          apply(rule exI[where x="WaitBlk (dd - d) (\<lambda>t. EState s) rdy1 # InBlock ch v # tr2a"])
          apply auto
          apply(rule exI[where x="WaitBlk (dd - d) (\<lambda>t. EState s) rdy1 # [InBlock ch v]"])
          apply auto
          apply(rule )
          by auto
        apply(cases "d>dd")
        subgoal
          apply (auto elim!: combine_blocks_waitE3)
          by (auto elim:combine_blocks_pairE2)
        apply(cases "d=dd")
        subgoal
          apply (auto elim!: combine_blocks_waitE2)
          apply(rule exI[where x="[WaitBlk dd (\<lambda>t. ParState (EState s) (p t)) (merge_rdy rdy1 rdy2)]"])
          apply auto
          subgoal apply(rule) by auto
          apply(rule exI[where x="(InBlock ch v # tr2a)"])
          apply auto
          apply(rule exI[where x="[InBlock ch v]"])
          apply auto
          apply(rule)
          done
        by auto
      subgoal
        apply(auto simp add:emp_assn_def)
        apply(rule exI[where x="(WaitBlk dd (\<lambda>_. EState s) rdy1 # InBlock ch v # tr2a)"])
        by auto
      done
    done
  done


lemma combine_assn_inrdy_wait':
  assumes "ch \<notin> chs \<and> compat_rdy rdy1 rdy2"
  shows "combine_assn chs (Inrdy\<^sub>t s ch v rdy1 @\<^sub>t P)(Wait\<^sub>t d p rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
   (Wait\<^sub>t d (\<lambda> t. ParState (EState s) (p t)) (merge_rdy rdy1 rdy2) @\<^sub>t (combine_assn chs (Inrdy\<^sub>t s ch v rdy1 @\<^sub>t P) Q))
\<or>\<^sub>t (\<exists>\<^sub>ttt. \<up>(0 \<le> tt \<and> tt < d) \<and>\<^sub>t Waitin\<^sub>t tt (\<lambda> t. ParState (EState s) (p t)) ch v (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P (Wait\<^sub>t (d-tt) (\<lambda> t. p(t+tt)) rdy2 @\<^sub>t Q))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def)
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule: inrdy_assn.cases[of s ch v rdy1 tr1a])
      apply auto
    subgoal
      apply(cases rule:wait_assn.cases[of d p rdy2 tr1b])
        apply auto
      subgoal using assms
        apply (auto elim!: combine_blocks_unpairE3)
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(auto simp add:ex_assn_def)
        apply(rule exI[where x=0])
        apply auto
        apply(rule exI[where x="[InBlock ch v]"])
        apply auto
        subgoal apply rule by auto
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(WaitBlk d p rdy2 # tr2b)"])
        by auto
      subgoal unfolding disj_assn_def
        apply(rule disjI1)
        apply(auto simp add:emp_assn_def)
        apply(rule exI[where x="(InBlock ch v # tr2a)"])
        by auto
      done
    subgoal for dd
      apply(cases rule:wait_assn.cases[of d p rdy2 tr1b])
        apply auto
      subgoal
        apply(cases "d<dd")
        subgoal
          using assms
          apply (auto elim!: combine_blocks_waitE4)
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (EState s) (p t)) (merge_rdy rdy1 rdy2)]"])
          apply auto
          subgoal
            apply(rule) by auto 
          apply(rule exI[where x="(WaitBlk (dd - d) (\<lambda>t. EState s) rdy1 # InBlock ch v # tr2a)"])
          apply auto
          apply(rule exI[where x="WaitBlk (dd - d) (\<lambda>t. EState s) rdy1 # [InBlock ch v]"])
          apply auto
          apply(rule ) by auto
        apply(cases "d>dd")
        subgoal
          using assms
          apply (auto elim!: combine_blocks_waitE3 combine_blocks_unpairE3)
          unfolding disj_assn_def
          apply(rule disjI2)
          unfolding ex_assn_def
          apply(rule exI[where x=dd])
          apply auto
          apply(rule exI[where x="WaitBlk dd (\<lambda>t. ParState (EState s) (p t)) (merge_rdy rdy1 rdy2) # [InBlock ch v]"])
          apply auto
          subgoal apply rule by auto
          apply(rule exI[where x= tr2a])
          apply auto
          apply(rule exI[where x="(WaitBlk (d - dd) (\<lambda>t. p (t + dd)) rdy2 # tr2b)"])
          apply auto
          apply(rule exI[where x="[WaitBlk (d - dd) (\<lambda>t. p (t + dd)) rdy2]"])
          apply auto
          apply rule by auto
        apply(cases "d=dd")
        subgoal
          using assms
          apply (auto elim!: combine_blocks_waitE2)
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (EState s) (p t)) (merge_rdy rdy1 rdy2)]"])
          apply auto
          subgoal
            apply(rule) by auto 
          apply(rule exI[where x="(InBlock ch v # tr2a)"])
          apply auto
          apply(rule exI[where x="[InBlock ch v]"])
          apply auto
          apply(rule ) 
          done
        by auto
      subgoal unfolding disj_assn_def
        apply(rule disjI1)
        apply (auto simp add:emp_assn_def)
        apply(rule exI[where x="(WaitBlk dd (\<lambda>_. EState s) rdy1 # InBlock ch v # tr2a)"])
        by auto
      done
    done
  done
 

fun combine1 :: "nat \<Rightarrow> nat \<Rightarrow> estate ext_state \<Rightarrow> estate ext_state \<Rightarrow> estate tassn" where
  "combine1 0 0 (Sch p rn rp,ss) (Task st ent tp,ts) = (emp\<^sub>t)"
| "combine1 0 (Suc k) (Sch p rn rp,ss) (Task WAIT ent tp,ts) = 
   (combine1 0 k (Sch p rn rp,ss) (Task READY ezero tp,ts(T := 0))) "
| "combine1 0 (Suc k) (Sch p rn rp,ss) (Task READY ent tp,ts) = false\<^sub>A"
| "combine1 0 (Suc k) (Sch p rn rp,ss) (Task RUNNING ent tp,ts) = false\<^sub>A"
| "combine1 (Suc k) 0 (Sch p rn rp,ss) (Task st ent tp,ts) = (
    (In0\<^sub>t (req_ch 2) 1 @\<^sub>t (if 1\<le>rp then combine1 k 0 (Sch (p@[(1,2)]) rn rp,ss(Pr:=1)) (Task st ent tp,ts)
                                  else \<up>(rn \<noteq> 1) \<and>\<^sub>t Out0\<^sub>t (run_ch 2) 0 @\<^sub>t combine1 k 0 (Sch p 2 1, ss(Pr := 1)) (Task st ent tp,ts)))
 \<or>\<^sub>t (\<exists>\<^sub>t v. \<up> (v \<noteq> 1) \<and>\<^sub>t In0\<^sub>t (req_ch 2) v @\<^sub>t true\<^sub>A )
 \<or>\<^sub>t (\<exists>\<^sub>t v. In0\<^sub>t (free_ch 2) v @\<^sub>t (if length p > 0 then Out0\<^sub>t (run_ch 2) 0 @\<^sub>t combine1 k 0 (sched_get_max'(Sch p rn rp),ss(G:=v)) (Task st ent tp,ts) else 
                                   combine1 k 0 (Sch [] (-1) (-1),ss(G:=v)) (Task st ent tp,ts)))   
 \<or>\<^sub>t (\<exists>\<^sub>t v. In0\<^sub>t (exit_ch 2) v @\<^sub>t combine1 k 0 (Sch (del_proc p 2) rn rp,ss(G:=v)) (Task st ent tp,ts))
)"
| "combine1 (Suc sk) (Suc tk) (Sch p rn rp,ss) (Task WAIT ent tp,ts) = (
     (Wait\<^sub>t (9 / 200 - ts T) (\<lambda>t. ParState (EState (Sch p rn rp, ss)) (EState (Task WAIT ent tp, ts(T:= ts T + t)))) ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t
      combine1 (Suc sk) tk (Sch p rn rp,ss) (Task READY ezero tp,ts(T:=0)))
    \<or>\<^sub>t   (\<exists>\<^sub>ttt. \<up> (0 \<le> tt \<and> tt < 9 / 200 - ts T) \<and>\<^sub>t
        Waitin\<^sub>t tt (\<lambda>t. ParState (EState (Sch p rn rp, ss)) (EState (Task WAIT ent 2, ts(T:= ts T + t))))
         (req_ch 2) 1 ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})
       @\<^sub>t (if 1\<le>rp then combine1 sk (Suc tk) (Sch (p@[(1,2)]) rn rp,ss(Pr:=1)) (Task WAIT ent 2,ts(T:= ts T + tt)) else emp\<^sub>t))
)"

definition propc :: "nat \<Rightarrow> estate \<Rightarrow> estate \<Rightarrow> bool" where
"propc k schs task_es = (k>0 \<longrightarrow>(status task_es = RUNNING \<longleftrightarrow> run_now schs = 1))"


lemma combine_SCH_T1:
"propc ns (Sch p rn rp) (Task st ent 2) \<Longrightarrow>
   proper (Sch p rn rp) \<Longrightarrow>
 combine_assn {req_ch 1, preempt_ch 1, run_ch 1, free_ch 1, exit_ch 1} 
 (SCH_tr nt (Sch p rn rp,ss)) (T1_tr ns (Task st ent 2,ts)) \<Longrightarrow>\<^sub>t
 combine1 nt ns (Sch p rn rp,ss) (Task st ent 2,ts) "
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
          using pre(1)[of 0 ns' p rn rp READY ezero ss "ts(T := 0)"] pre(2,3)
          apply(subgoal_tac "propc ns' (Sch p rn rp) (Task READY ezero 2)")
          subgoal unfolding proper_def by auto
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
        subgoal premises pre
          apply(simp only:combine1.simps)
          apply(rule entails_tassn_disjI1)
          apply(rule entails_tassn_trans)
           apply(rule combine_assn_inrdy_emp')
          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
          apply(rule entails_tassn_cancel_left)
          apply(cases "1\<le>rp")
          subgoal apply simp
            using pre(1)[of nt' 0 "(p @ [(1, 2)])" rn rp st ent "ss(Pr := 1)" ts] pre(2,3) properl_p1[of p 1 2]
            by(auto simp add:propc_def proper_def properp_def)
          apply(cases "rn = 1")
          subgoal apply simp
            apply(rule combine_or_left)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_out0_emp)
              by auto
            apply(rule combine_or_left)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_waitp_emp)
              by auto
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_out0_emp)
              by auto
            done
          apply simp
          apply(rule combine_or_left)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_out0_emp')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              apply(rule entails_tassn_cancel_left)
              using pre(1)[of nt' 0 p 2 1 st ent "ss(Pr := 1)" ts] pre(2,3)
              by (auto simp add:propc_def proper_def properp_def)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_waitp_emp)
              by auto
            done
          apply(rule combine_or_left)
          subgoal premises pre
            apply(simp only:combine1.simps)
            apply(rule entails_tassn_disjI2)
            apply(rule entails_tassn_disjI1)
            apply(rule combine_assn_ex_pre_left')
            subgoal for v
            apply(rule combine_assn_pure_pre_left')
              apply(rule entails_tassn_exI[where x=v])
              apply simp
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_emp')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              apply(rule entails_tassn_cancel_left)
              by(auto simp add: entails_tassn_def true_assn_def)
            done
          apply(rule combine_or_left)
          subgoal
            apply(rule combine_assn_ex_pre_left')
            apply(rule entails_tassn_trans)
             apply(rule combine_assn_inrdy_emp)
            by auto
          apply(rule combine_or_left)
          subgoal premises pre
            apply(simp only:combine1.simps)
            apply(rule entails_tassn_disjI2)
            apply(rule entails_tassn_disjI2)
            apply(rule entails_tassn_disjI1)
            apply(rule combine_assn_ex_pre_left')
            subgoal for v
              apply(rule entails_tassn_exI[where x=v])
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_emp')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              apply(rule entails_tassn_cancel_left)
              apply(cases "length p > 0")
              subgoal 
                apply(subgoal_tac"get_max p = (1, 2)")
                 prefer 2
                 subgoal using pre(3) properl_p5[of p]
                  apply auto
                  apply(cases "get_max p")
                  by (auto simp add: proper_def properp_def)
                apply simp
                apply(rule combine_or_left)
                subgoal
                 apply(rule entails_tassn_trans)
                  apply(rule combine_assn_out0_emp')
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply(rule entails_tassn_cancel_left)
                using pre(1)[of nt' 0 "(del_proc p 2)" 2 1 st ent "ss(G := v)" ts] pre(2,3) properl_p4[of p 2]
                by(auto simp add:propc_def proper_def properp_def)
              subgoal
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_waitp_emp)
                by auto
              done
            subgoal
              apply simp
              using pre(1)[of nt' 0 "[]" "-1" "-1" st ent "ss(G := v)" ts] pre(2,3) properl_p4[of p 2]
              by(auto simp add:propc_def proper_def properp_def)
            done
          done
        apply(rule combine_or_left)
        subgoal
          apply(rule combine_assn_ex_pre_left')
            apply(rule entails_tassn_trans)
             apply(rule combine_assn_inrdy_emp)
          by auto
        subgoal premises pre
            apply(simp only:combine1.simps)
            apply(rule entails_tassn_disjI2)
          apply(rule entails_tassn_disjI2)
          apply(rule entails_tassn_disjI2)
            apply(rule combine_assn_ex_pre_left')
            subgoal for v
              apply(rule entails_tassn_exI[where x=v])
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_emp')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              apply(rule entails_tassn_cancel_left)
              using pre(1)[of nt' 0 "(del_proc p 2)" rn rp st ent "ss(G := v)" ts] pre(2,3) properl_p4[of p 2]
              by(auto simp add:propc_def proper_def properp_def)
            done
          done
        subgoal for ns'
          apply(cases st)
            apply (simp only: SCH_tr.simps T1_tr.simps)
          subgoal premises pre
            apply(rule combine_or_left)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_wait)
              subgoal by auto
              apply(auto simp only: merge_rdy.simps)
              unfolding combine1.simps
              apply(rule entails_tassn_disjI1)
              apply(rule entails_tassn_cancel_both)
              subgoal by auto
              thm pre
              apply(rule entails_tassn_trans)
               prefer 2
               apply(rule pre)
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) by auto
              apply(rule combine_assn_left_tran)
              apply(simp only: SCH_tr.simps)
              apply(rule entails_tassn_disjI1)
              by auto
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule combine_assn_pure_pre_left')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_wait)
              subgoal by auto
              apply(auto simp only: merge_rdy.simps)
              unfolding combine1.simps
              apply(rule entails_tassn_disjI1)
              apply(rule entails_tassn_cancel_both)
              subgoal by auto
              thm pre
              apply(rule entails_tassn_trans)
               prefer 2
               apply(rule pre)
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) by auto
              apply(rule combine_assn_left_tran)
              apply(simp only: SCH_tr.simps)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI1)
              subgoal for v
                apply(rule entails_tassn_exI[where x= v])
                by simp
              done
            apply(rule combine_or_left)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_wait')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              apply(rule entails_tassn_disjE)
              subgoal
                unfolding combine1.simps
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_cancel_both)
                subgoal by auto
                thm pre
                apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre)
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) by auto
                apply(rule combine_assn_left_tran)
                apply(simp only: SCH_tr.simps)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                by auto
              subgoal
                apply(cases "1\<le>rp")
                subgoal apply simp
                  apply(rule entails_tassn_disjI2)
                  apply(rule ex_tran)
                  apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre)
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(2,3) properl_p1[of p 1 2] unfolding proper_def properp_def
                    by auto
                  apply(rule combine_assn_right_tran)
                  apply simp


                  
              


                  
                  

            
            


          
qed




end