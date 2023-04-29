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

lemma entails_tassn_conj:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> P \<Longrightarrow>\<^sub>t R \<Longrightarrow> P \<Longrightarrow>\<^sub>t Q \<and>\<^sub>t R"
  by (auto simp add: entails_tassn_def conj_assn_def)

lemma waitin_assn_decomp:
  "waitin_assn d p ch v rdy = wait_assn d p rdy @\<^sub>t in_0assn ch v"
  apply(auto simp add: join_assn_def)
  apply(rule ext)
  apply auto
  subgoal for tr
    apply(cases rule:waitin_assn.cases[of d p ch v rdy tr])
      apply auto
    subgoal
     apply(rule exI[where x="[WaitBlk d p rdy]"])
      apply auto
       apply rule apply auto
      apply rule done
    apply(auto simp add:emp_assn_def)
    apply(rule) done
  subgoal for tr1 tr2
    apply(cases rule:in_0assn.cases[of ch v tr2])
     apply auto
    apply(cases rule:wait_assn.cases[of d p rdy tr1])
      apply auto
     apply rule apply auto
    apply rule by auto
  done


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

lemma combine_assn_left_disj:
"combine_assn chs (P1) Q \<Longrightarrow>\<^sub>t R \<Longrightarrow> combine_assn chs (P2) Q \<Longrightarrow>\<^sub>t R \<Longrightarrow>  combine_assn chs (P1 \<or>\<^sub>t P2) Q \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def disj_assn_def
  by blast

lemma combine_assn_wait_emp':
  "combine_assn chs (Wait\<^sub>t d p rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t combine_assn chs P emp\<^sub>t "
  unfolding combine_assn_def entails_tassn_def
  apply (auto)
  apply (simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def)
  by (auto elim!: sync_elims)

lemma combine_assn_wait_emp'':
  "combine_assn chs (Wait\<^sub>t d p rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t \<up>(d\<le>0) \<and>\<^sub>t combine_assn chs P emp\<^sub>t "
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

lemma combine_assn_emp_wait'':
  "combine_assn chs emp\<^sub>t (Wait\<^sub>t d p rdy @\<^sub>t P) \<Longrightarrow>\<^sub>t \<up>(d\<le>0) \<and>\<^sub>t combine_assn chs emp\<^sub>t P"
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
  shows "combine_assn chs emp\<^sub>t (Waitin\<^sub>t d p ch v rdy @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def false_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def waitin_assn.simps)
  using assms 
  by(auto elim!: sync_elims)

lemma combine_assn_waitin_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (Waitin\<^sub>t d p ch v rdy @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def false_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def waitin_assn.simps)
  using assms 
  by(auto elim!: sync_elims)


lemma combine_assn_inrdy_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (Inrdy\<^sub>t s ch v rdy @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def false_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def inrdy_assn.simps)
  using assms by (auto elim!: sync_elims)


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


lemma combine_assn_emp_outrdy:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (Outrdy\<^sub>t s ch v rdy @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: outrdy_assn.cases)
  by (auto elim: sync_elims)


lemma combine_assn_emp_inrdy:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (Inrdy\<^sub>t s ch v rdy @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: inrdy_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_out0_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (Out0\<^sub>t ch v @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def false_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def out_0assn.simps)
  using assms by (auto elim: sync_elims)

lemma combine_assn_out0_emp':
  assumes "ch \<notin> chs"
  shows "combine_assn chs (Out0\<^sub>t ch v @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t Out0\<^sub>t ch v @\<^sub>t (combine_assn chs P emp\<^sub>t)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def out_0assn.simps)
  using assms by (auto elim!: sync_elims)


lemma combine_assn_waitp_emp:
 "combine_assn chs (wait_passn rdy @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def false_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def wait_passn.simps)
  by (auto elim!: sync_elims)


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


lemma combine_assn_out0_wait:
  assumes "ch\<in>chs \<and> d>0"
  shows "combine_assn chs (out_0assn ch v @\<^sub>t P) (wait_assn d p rdy @\<^sub>t Q) 
          \<Longrightarrow>\<^sub>t R"
  unfolding Valid_def combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch v tr1a])
     apply auto
    apply(cases rule:wait_assn.cases[of d p rdy tr1b])
      apply auto
    apply(elim combine_blocks_pairE2)
    apply auto
    done
  done
lemma combine_assn_out0_wait'':
  "ch \<in> chs \<Longrightarrow> combine_assn chs (out_0assn ch v @\<^sub>t P) (wait_assn d p rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   \<up>(d\<le>0) \<and>\<^sub>t combine_assn chs (out_0assn ch v @\<^sub>t P) Q"
unfolding Valid_def combine_assn_def entails_tassn_def join_assn_def
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch v tr1a])
     apply auto
    apply(cases rule:wait_assn.cases[of d p rdy tr1b])
      apply auto
    apply(elim combine_blocks_pairE2)
     apply auto
    apply(rule exI[where x="(OutBlock ch v # tr2a)"])
    by auto
  done

lemma combine_assn_out0_wait':
  assumes "ch\<notin>chs \<and> d>0"
  shows "combine_assn chs (out_0assn ch v @\<^sub>t P) (wait_assn d p rdy @\<^sub>t Q) 
          \<Longrightarrow>\<^sub>t out_0assn ch v @\<^sub>t (combine_assn chs P (wait_assn d p rdy @\<^sub>t Q))"
  unfolding Valid_def combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch v tr1a])
     apply auto
    apply(cases rule:wait_assn.cases[of d p rdy tr1b])
      apply auto
    apply(elim combine_blocks_unpairE3)
    apply auto
    apply(rule exI[where x="[OutBlock ch v]"])
    apply auto
    apply(rule exI[where x="tr2a"])
    apply auto
    apply(rule exI[where x="(WaitBlk d p rdy # tr2b)"])
    apply auto
    done
  done


lemma combine_assn_waitp_wait:
  assumes "compat_rdy rdy1 rdy2 \<and> d > 0"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P) (wait_assn d p2 rdy2 @\<^sub>t Q)
      \<Longrightarrow>\<^sub>t wait_passn (merge_rdy rdy1 rdy2) @\<^sub>t true\<^sub>A"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    apply(cases rule:wait_assn.cases[of d p2 rdy2 tr1b])
      apply auto
    subgoal for dd p1
      apply(cases "dd < d")
      subgoal 
        apply(elim combine_blocks_waitE3)
           apply auto
        apply(rule exI[where x="[WaitBlk dd (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd>d")
      subgoal
       apply(elim combine_blocks_waitE4)
           apply auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd= d")
      subgoal
        apply simp
       apply(elim combine_blocks_waitE2)
           apply auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      by auto
    done
  done

lemma combine_assn_waitp_wait':
  assumes "\<not>compat_rdy rdy1 rdy2 \<and> d > 0"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P) (wait_assn d p2 rdy2 @\<^sub>t Q)
      \<Longrightarrow>\<^sub>t R "
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    apply(cases rule:wait_assn.cases[of d p2 rdy2 tr1b])
      apply auto
    subgoal for dd p1
      apply(elim combine_blocks_waitE1)
           apply auto
      done
    done
  done

lemma combine_assn_waitp_wait'':
  assumes "\<not>compat_rdy rdy1 rdy2"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P) (wait_assn d p2 rdy2 @\<^sub>t Q)
      \<Longrightarrow>\<^sub>t \<up>(d \<le> 0) \<and>\<^sub>t combine_assn chs (wait_passn rdy1 @\<^sub>t P) Q "
  apply(cases "d\<le>0")
   apply auto
  apply(rule combine_assn_waitp_wait')
  using assms by auto
  

lemma combine_assn_out0_waitin:
  assumes "ch\<in>chs"
  shows "combine_assn chs (out_0assn ch v2 @\<^sub>t P) (waitin_assn d p ch v1 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
            \<up>(v1 = v2 \<and> d \<le> 0) \<and>\<^sub>t  combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch v2 tr1a])
     apply auto
    apply(cases rule:waitin_assn.cases[of d p ch v1 rdy tr1b])
      apply auto
    subgoal
      by(auto elim!:combine_blocks_pairE2)
    subgoal
      apply(auto elim!:combine_blocks_pairE)
      by blast
    done
  done

lemma combine_assn_out0_waitin':
  assumes "ch1\<in>chs \<and> ch2\<notin>chs"
  shows "combine_assn chs (out_0assn ch2 v2 @\<^sub>t P) (waitin_assn d p ch1 v1 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
            out_0assn ch2 v2 @\<^sub>t combine_assn chs P (waitin_assn d p ch1 v1 rdy @\<^sub>t Q)"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch2 v2 tr1a])
     apply auto
    apply(cases rule:waitin_assn.cases[of d p ch1 v1 rdy tr1b])
      apply auto
    subgoal
      apply(auto elim!:combine_blocks_unpairE3)
      apply(rule exI[where x="[OutBlock ch2 v2]"])
      apply auto
      apply(rule exI[where x=tr2a])
      apply auto
      apply(rule exI[where x="(WaitBlk d p rdy # InBlock ch1 v1 # tr2b)"])
      by auto
    subgoal
      apply(auto elim!:combine_blocks_unpairE1)
      apply(rule exI[where x="[OutBlock ch2 v2]"])
      apply auto
      apply(rule exI[where x=tr2a])
      apply auto
      apply(rule exI[where x="(InBlock ch1 v1 # tr2b)"])
      by auto
    done
  done


lemma combine_assn_waitp_waitin:
  assumes "ch\<in>chs \<and> compat_rdy rdy1 rdy2"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P) (waitin_assn d p2 ch v rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
           wait_passn  (merge_rdy rdy1 rdy2) @\<^sub>t true\<^sub>A"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    apply(cases rule:waitin_assn.cases[of d p2 ch v rdy2 tr1b])
      apply auto
    subgoal for dd p1
      apply(cases "dd < d")
      subgoal 
        apply(elim combine_blocks_waitE3)
           apply auto
        apply(rule exI[where x="[WaitBlk dd (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd>d")
      subgoal
       apply(elim combine_blocks_waitE4)
           apply auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd= d")
      subgoal
        apply simp
       apply(elim combine_blocks_waitE2)
           apply auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      by auto
    subgoal for dd
      apply(auto elim: combine_blocks_pairE2')
      done
    done
  done

lemma combine_assn_waitp_waitin':
  assumes "ch\<in>chs \<and> \<not> compat_rdy rdy1 rdy2"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P) (waitin_assn d p2 ch v rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
           R"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    apply(cases rule:waitin_assn.cases[of d p2 ch v rdy2 tr1b])
      apply auto
    subgoal for dd p1
      by(auto elim!: combine_blocks_waitE1)
    subgoal for dd
      apply(auto elim: combine_blocks_pairE2')
      done
    done
  done

lemma combine_assn_inrdy_out:
  assumes "ch\<in>chs \<and> ch \<in> snd rdy"
  shows "combine_assn chs (inrdy_assn s ch v rdy @\<^sub>t P) (out_assn s' ch v' @\<^sub>t Q) \<Longrightarrow>\<^sub>t
           \<up>(v=v') \<and>\<^sub>t combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s ch v rdy tr1a])
      apply auto
    subgoal
      apply(cases rule:out_assn.cases[of s' ch v' tr1b])
        apply auto
      subgoal
        apply (auto elim!: combine_blocks_pairE)
        by blast
      subgoal for d
        by(auto elim:combine_blocks_pairE2)
      done
    subgoal for d'
      apply(cases rule:out_assn.cases[of s' ch v' tr1b])
      apply auto
      subgoal
        by(auto elim:combine_blocks_pairE2')
      subgoal for d
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        by auto
      done
    done
  done


lemma combine_assn_inrdy_out':
  assumes "ch\<in>chs \<and> ch \<in> snd rdy \<and> ch'\<notin> chs"
  shows "combine_assn chs (inrdy_assn s ch' v rdy @\<^sub>t P) (out_assn s' ch v' @\<^sub>t Q) \<Longrightarrow>\<^sub>t
           in_0assn ch' v @\<^sub>t combine_assn chs P (out_assn s' ch v' @\<^sub>t Q)"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s ch' v rdy tr1a])
      apply auto
    subgoal
      apply(cases rule:out_assn.cases[of s' ch v' tr1b])
        apply auto
      subgoal
        apply(auto elim!:combine_blocks_unpairE1)
        apply(rule exI[where x="[InBlock ch' v]"])
        apply auto
        subgoal apply rule done
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(OutBlock ch v' # tr2b)"])
        apply auto
        done
      subgoal for d
        apply(auto elim!:combine_blocks_unpairE3)
        apply(rule exI[where x="[InBlock ch' v]"])
        apply auto
        subgoal apply rule done
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(WaitBlk d (\<lambda>_. s') ({ch}, {}) # OutBlock ch v' # tr2b)"])
        by auto
      done
    subgoal for dd
      apply(cases rule:out_assn.cases[of s' ch v' tr1b])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d
        apply (auto elim!: combine_blocks_waitE1)
        apply(cases rdy)
        by auto
      done
    done
  done

lemma combine_assn_inrdy_out'':
  assumes "ch1\<in>chs \<and> ch2\<in>chs \<and> ch1\<noteq>ch2"
  shows "combine_assn chs (inrdy_assn s ch1 v rdy @\<^sub>t P) (out_assn s' ch2 v' @\<^sub>t Q) \<Longrightarrow>\<^sub>t
           R"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s ch1 v rdy tr1a])
      apply auto
    subgoal
      apply(cases rule:out_assn.cases[of s' ch2 v' tr1b])
        apply auto
        subgoal
          by (auto elim!: combine_blocks_pairE)
        subgoal
          by (auto elim!: sync_elims)
        done
      subgoal for d1
        apply(cases rule:out_assn.cases[of s' ch2 v' tr1b])
        apply auto
        subgoal
          by (auto elim!: sync_elims)
        subgoal for d2
          apply(cases "\<not> compat_rdy rdy ({ch2}, {})")
          subgoal by (auto elim!: sync_elims)
          apply(cases "d1<d2")
          subgoal
            apply(elim combine_blocks_waitE3)
            by (auto elim!: sync_elims)
          apply(cases "d1>d2")
          subgoal
            apply(elim combine_blocks_waitE4)
            by (auto elim!: sync_elims)
          apply auto
          apply(elim combine_blocks_waitE2)
          by (auto elim!: combine_blocks_pairE)
        done
      done
    done


lemma combine_assn_inrdy_outrdy':
  assumes "ch\<in>chs \<and> \<not>compat_rdy rdy1 rdy2 \<and> ch'\<notin> chs"
  shows "combine_assn chs (inrdy_assn s ch' v rdy1 @\<^sub>t P) (outrdy_assn s' ch v' rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
           in_0assn ch' v @\<^sub>t combine_assn chs P (outrdy_assn s' ch v' rdy2 @\<^sub>t Q)"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s ch' v rdy1 tr1a])
      apply auto
    subgoal
      apply(cases rule:outrdy_assn.cases[of s' ch v' rdy2 tr1b])
        apply auto
      subgoal
        apply(auto elim!:combine_blocks_unpairE1)
        apply(rule exI[where x="[InBlock ch' v]"])
        apply auto
        subgoal apply rule done
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(OutBlock ch v' # tr2b)"])
        apply auto
        done
      subgoal for d
        apply(auto elim!:combine_blocks_unpairE3)
        apply(rule exI[where x="[InBlock ch' v]"])
        apply auto
        subgoal apply rule done
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(WaitBlk d (\<lambda>_. EState s') rdy2 # OutBlock ch v' # tr2b)"])
        by auto
      done
    subgoal for dd
      apply(cases rule:outrdy_assn.cases[of s' ch v' rdy2 tr1b])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d
        apply (auto elim!: combine_blocks_waitE1)
        done
      done
    done
  done

lemma combine_assn_inrdy_outrdy'':
  assumes "ch1\<in>chs \<and> ch2\<in>chs \<and> ch1\<noteq>ch2"
  shows "combine_assn chs (inrdy_assn s ch1 v rdy1 @\<^sub>t P) (outrdy_assn s' ch2 v' rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
           R"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s ch1 v rdy1 tr1a])
      apply auto
    subgoal
      apply(cases rule:outrdy_assn.cases[of s' ch2 v' rdy2 tr1b])
        apply auto
        subgoal
          by (auto elim!: combine_blocks_pairE)
        subgoal
          by (auto elim!: sync_elims)
        done
      subgoal for d1
        apply(cases rule:outrdy_assn.cases[of s' ch2 v' rdy2 tr1b])
        apply auto
        subgoal
          by (auto elim!: sync_elims)
        subgoal for d2
          apply(cases "\<not> compat_rdy rdy1 rdy2")
          subgoal by (auto elim!: sync_elims)
          apply(cases "d1<d2")
          subgoal
            apply(elim combine_blocks_waitE3)
            by (auto elim!: sync_elims)
          apply(cases "d1>d2")
          subgoal
            apply(elim combine_blocks_waitE4)
            by (auto elim!: sync_elims)
          apply auto
          apply(elim combine_blocks_waitE2)
          by (auto elim!: combine_blocks_pairE)
        done
      done
    done


lemma combine_assn_out0_outrdy1:
  assumes "ch2\<in>chs \<and> ch1\<in>chs"
  shows "combine_assn chs (out_0assn ch2 v2 @\<^sub>t P)(outrdy_assn s ch1 v1 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         R"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch2 v2 tr1a])
     apply auto
    apply(cases rule:outrdy_assn.cases[of s ch1 v1 rdy tr1b])
      apply auto
    subgoal
      by(auto elim!: combine_blocks_pairE)
    subgoal for d
      by(auto elim!: combine_blocks_pairE2)
    done
  done

lemma combine_assn_out0_outrdy2:
  assumes "ch2\<notin>chs \<and> ch1\<in>chs"
  shows "combine_assn chs (out_0assn ch2 v2 @\<^sub>t P)(outrdy_assn s ch1 v1 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         out_0assn ch2 v2 @\<^sub>t combine_assn chs P (outrdy_assn s ch1 v1 rdy @\<^sub>t Q)"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch2 v2 tr1a])
     apply auto
    apply(cases rule:outrdy_assn.cases[of s ch1 v1 rdy tr1b])
      apply auto
    subgoal
      apply(auto elim!: combine_blocks_unpairE1)
      apply(rule exI[where x="[OutBlock ch2 v2]"])
      apply auto
      apply(rule exI[where x= tr2a])
      apply auto
      apply(rule exI[where x= "(OutBlock ch1 v1 # tr2b)"])
      apply auto
      done
    subgoal for d
      apply(auto elim!: combine_blocks_unpairE3)
      apply(rule exI[where x="[OutBlock ch2 v2]"])
      apply auto
      apply(rule exI[where x= tr2a])
      apply auto
      apply(rule exI[where x= "(WaitBlk d (\<lambda>_. EState s) rdy # OutBlock ch1 v1 # tr2b)"])
      apply auto
      done
    done
  done

lemma combine_assn_out0_out1:
  assumes "ch2\<in>chs \<and> ch1\<in>chs"
  shows "combine_assn chs (out_0assn ch2 v2 @\<^sub>t P)(out_assn s ch1 v1 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         R"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch2 v2 tr1a])
     apply auto
    apply(cases rule:out_assn.cases[of s ch1 v1 tr1b])
      apply auto
    subgoal
      by(auto elim!: combine_blocks_pairE)
    subgoal for d
      by(auto elim!: combine_blocks_pairE2)
    done
  done

lemma combine_assn_out0_out2:
  assumes "ch2\<notin>chs \<and> ch1\<in>chs"
  shows "combine_assn chs (out_0assn ch2 v2 @\<^sub>t P)(out_assn s ch1 v1 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         out_0assn ch2 v2 @\<^sub>t combine_assn chs P (out_assn s ch1 v1 @\<^sub>t Q)"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch2 v2 tr1a])
     apply auto
    apply(cases rule:out_assn.cases[of s ch1 v1 tr1b])
      apply auto
    subgoal
      apply(auto elim!: combine_blocks_unpairE1)
      apply(rule exI[where x="[OutBlock ch2 v2]"])
      apply auto
      apply(rule exI[where x= tr2a])
      apply auto
      apply(rule exI[where x= "(OutBlock ch1 v1 # tr2b)"])
      apply auto
      done
    subgoal for d
      apply(auto elim!: combine_blocks_unpairE3)
      apply(rule exI[where x="[OutBlock ch2 v2]"])
      apply auto
      apply(rule exI[where x= tr2a])
      apply auto
      apply(rule exI[where x= "(WaitBlk d (\<lambda>_. s) ({ch1}, {}) # OutBlock ch1 v1 # tr2b)"])
      apply auto
      done
    done
  done


lemma combine_assn_out0_inrdy1:
  assumes "ch2\<in>chs \<and> ch1\<in>chs"
  shows "combine_assn chs (out_0assn ch2 v2 @\<^sub>t P)(inrdy_assn s ch1 v1 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         \<up>(ch1 = ch2 \<and> v1 = v2) \<and>\<^sub>t combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch2 v2 tr1a])
     apply auto
    apply(cases rule:inrdy_assn.cases[of s ch1 v1 rdy tr1b])
      apply auto
    subgoal
      apply(auto elim!: combine_blocks_pairE)
      by blast
    subgoal for d
      by(auto elim!: combine_blocks_pairE2)
    done
  done


lemma combine_assn_out0_inrdy2:
  assumes "ch2\<notin>chs \<and> ch1\<in>chs"
  shows "combine_assn chs (out_0assn ch2 v2 @\<^sub>t P)(inrdy_assn s ch1 v1 rdy @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         out_0assn ch2 v2 @\<^sub>t combine_assn chs P (inrdy_assn s ch1 v1 rdy @\<^sub>t Q)"
  unfolding combine_assn_def entails_tassn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:out_0assn.cases[of ch2 v2 tr1a])
     apply auto
    apply(cases rule:inrdy_assn.cases[of s ch1 v1 rdy tr1b])
      apply auto
    subgoal
      apply(auto elim!: combine_blocks_unpairE1)
      apply(rule exI[where x="[OutBlock ch2 v2]"])
      apply auto
      apply(rule exI[where x= tr2a])
      apply auto
      apply(rule exI[where x= "(InBlock ch1 v1 # tr2b)"])
      apply auto
      done
    subgoal for d
      apply(auto elim!: combine_blocks_unpairE3)
      apply(rule exI[where x="[OutBlock ch2 v2]"])
      apply auto
      apply(rule exI[where x= tr2a])
      apply auto
      apply(rule exI[where x= "(WaitBlk d (\<lambda>_. EState s) rdy # InBlock ch1 v1 # tr2b)"])
      apply auto
      done
    done
  done


lemma combine_assn_waitp_outrdy:
  assumes "ch1\<in>chs \<and> compat_rdy rdy1 rdy2"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P)(outrdy_assn s ch1 v1 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         wait_passn (merge_rdy rdy1 rdy2) @\<^sub>t true\<^sub>A"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    subgoal for dd p
      apply(cases rule:outrdy_assn.cases[of s ch1 v1 rdy2 tr1b])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d
        apply(cases "dd < d")
      subgoal 
        apply(elim combine_blocks_waitE3)
           apply auto
        apply(rule exI[where x="[WaitBlk dd (\<lambda>t. ParState (p t) (EState s)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd>d")
      subgoal
       apply(elim combine_blocks_waitE4)
           apply auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) (EState s)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd= d")
      subgoal
        apply simp
       apply(elim combine_blocks_waitE2)
           apply auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) (EState s)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      by auto
    done
  done
  done


lemma combine_assn_waitp_outrdy':
  assumes "ch1\<in>chs \<and> \<not> compat_rdy rdy1 rdy2"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P)(outrdy_assn s ch1 v1 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         R"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    subgoal for dd p
      apply(cases rule:outrdy_assn.cases[of s ch1 v1 rdy2 tr1b])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d
        apply(elim combine_blocks_waitE1)
           by auto
         done
       done
     done

lemma combine_assn_waitp_out:
  assumes "ch1\<in>chs \<and> ch1 \<notin> snd rdy1"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P)(out_assn s ch1 v1 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         wait_passn (merge_rdy rdy1 ({ch1}, {})) @\<^sub>t true\<^sub>A"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    subgoal for dd p
      apply(cases rule:out_assn.cases[of s ch1 v1 tr1b])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d
        apply(cases "dd < d")
      subgoal 
        apply(elim combine_blocks_waitE3)
           apply auto
        subgoal apply(cases rdy1)
          by auto
        apply(rule exI[where x="[WaitBlk dd (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({ch1}, {}))]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd>d")
      subgoal
       apply(elim combine_blocks_waitE4)
           apply auto
        subgoal apply(cases rdy1)
          by auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({ch1}, {}))]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd= d")
      subgoal
        apply simp
       apply(elim combine_blocks_waitE2)
         apply auto
        subgoal apply(cases rdy1)
          by auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({ch1}, {}))]"])
        apply auto
        apply(rule) by auto
      by auto
    done
  done
  done


lemma combine_assn_waitp_out':
  assumes "ch1\<in>chs \<and> ch1 \<in> snd rdy1"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P)(out_assn s ch1 v1 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         R"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    subgoal for dd p
      apply(cases rule:out_assn.cases[of s ch1 v1 tr1b])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d
        apply(elim combine_blocks_waitE1)
        apply(cases rdy1)
           by auto
         done
       done
  done


lemma combine_assn_waitp_inrdy:
  assumes "ch1\<in>chs \<and> compat_rdy rdy1 rdy2"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P)(inrdy_assn s ch1 v1 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         wait_passn (merge_rdy rdy1 rdy2) @\<^sub>t true\<^sub>A"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    subgoal for dd p
      apply(cases rule:inrdy_assn.cases[of s ch1 v1 rdy2 tr1b])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d
        apply(cases "dd < d")
      subgoal 
        apply(elim combine_blocks_waitE3)
           apply auto
        apply(rule exI[where x="[WaitBlk dd (\<lambda>t. ParState (p t) (EState s)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd>d")
      subgoal
       apply(elim combine_blocks_waitE4)
           apply auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) (EState s)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      apply(cases "dd= d")
      subgoal
        apply simp
       apply(elim combine_blocks_waitE2)
           apply auto
        apply(rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) (EState s)) (merge_rdy rdy1 rdy2)]"])
        apply auto
        apply(rule) by auto
      by auto
    done
  done
  done

lemma combine_assn_waitp_inrdy':
  assumes "ch1\<in>chs \<and> \<not>compat_rdy rdy1 rdy2"
  shows "combine_assn chs (wait_passn rdy1 @\<^sub>t P)(inrdy_assn s ch1 v1 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
         R"
  unfolding combine_assn_def entails_tassn_def join_assn_def true_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:wait_passn.cases[of rdy1 tr1a])
     apply auto
    subgoal for dd p
      apply(cases rule:inrdy_assn.cases[of s ch1 v1 rdy2 tr1b])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d
        apply(elim combine_blocks_waitE1)
           by auto
    done
  done
  done


lemma combine_assn_inrdy_waitin:
  assumes "ch1\<in>chs \<and> ch2\<in>chs"
  shows "combine_assn chs (Inrdy\<^sub>t s ch1 v1 rdy1 @\<^sub>t P) (Waitin\<^sub>t d p ch2 v2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s ch1 v1 rdy1])
      apply auto
    subgoal
      apply(cases rule:waitin_assn.cases[of d p ch2 v2 rdy2 tr1b])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      done
    subgoal for dd
      apply(cases rule:waitin_assn.cases[of d p ch2 v2 rdy2 tr1b])
        apply auto
      subgoal
        apply(cases "\<not> compat_rdy rdy1 rdy2")
        subgoal by (auto elim!: sync_elims)
        apply(cases "dd<d")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "dd>d")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          by (auto elim!: sync_elims)
        apply auto
        apply(elim combine_blocks_waitE2)
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        by (auto elim!: sync_elims)
      done
    done
  done


lemma combine_assn_inrdy_waitin':
  assumes "ch1\<notin>chs \<and> ch2\<in>chs \<and> compat_rdy rdy1 rdy2 \<and> d\<ge>0"
  shows "combine_assn chs (Inrdy\<^sub>t s ch1 v1 rdy1 @\<^sub>t P) (Waitin\<^sub>t d p ch2 v2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
          (\<exists>\<^sub>ttt. \<up>(0 \<le> tt \<and> tt \<le> d) \<and>\<^sub>t Waitin\<^sub>t tt (\<lambda> t. ParState (EState s) (p t)) ch1 v1 (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P (Waitin\<^sub>t (d-tt) (\<lambda> t. p(t+tt)) ch2 v2 rdy2 @\<^sub>t Q))"
  unfolding entails_tassn_def combine_assn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s ch1 v1 rdy1])
      apply auto
    subgoal
      apply(cases rule:waitin_assn.cases[of d p ch2 v2 rdy2 tr1b])
        apply auto
      subgoal
        apply (elim combine_blocks_unpairE3)
         apply (auto simp add: ex_assn_def pure_assn_def conj_assn_def)
        apply(rule exI[where x= 0])
        apply auto
        apply(rule exI[where x="[InBlock ch1 v1]"])
        apply auto
        subgoal apply rule by auto
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(WaitBlk d p rdy2 # InBlock ch2 v2 # tr2b)"])
        by auto
      subgoal
        apply(elim combine_blocks_unpairE1)
          apply (auto simp add: ex_assn_def pure_assn_def conj_assn_def)
        apply(rule exI[where x= 0])
        apply auto
        apply(rule exI[where x="[InBlock ch1 v1]"])
        apply auto
        subgoal apply rule by auto
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(InBlock ch2 v2 # tr2b)"])
        by auto
      done
    subgoal for dd
      apply(cases rule:waitin_assn.cases[of d p ch2 v2 rdy2 tr1b])
        apply auto
      subgoal
        apply(cases "dd<d")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          apply(elim combine_blocks_unpairE3)
           apply (auto simp add: ex_assn_def pure_assn_def conj_assn_def)
          apply(rule exI[where x=dd])
          apply auto
          apply(rule exI[where x="WaitBlk dd (\<lambda>t. ParState (EState s) (p t)) (merge_rdy rdy1 rdy2) #[InBlock ch1 v1]"])
          apply auto
          subgoal apply rule by auto
          apply(rule exI[where x= tr2a])
          apply auto
          apply(rule exI[where x="(WaitBlk (d - dd) (\<lambda>t. p (t + dd)) rdy2 # InBlock ch2 v2 # tr2b)"])
          apply auto
          apply(rule exI[where x = "WaitBlk (d - dd) (\<lambda>t. p (t + dd)) rdy2 # [InBlock ch2 v2]"])
          apply auto
          apply rule by auto
        apply(cases "dd>d")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          by (auto elim!: sync_elims)
        apply auto
        apply(elim combine_blocks_waitE2)
        apply auto
        apply(elim combine_blocks_unpairE1)
          apply (auto simp add: ex_assn_def pure_assn_def conj_assn_def)
        apply(rule exI[where x= d])
        apply auto
        apply(rule exI[where x="WaitBlk d (\<lambda>t. ParState (EState s) (p t)) (merge_rdy rdy1 rdy2) # [InBlock ch1 v1]"])
        apply auto
        subgoal apply rule by auto
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(InBlock ch2 v2 # tr2b)"])
        apply auto
        apply(rule exI[where x="[InBlock ch2 v2]"])
        apply auto
        apply rule
        by auto
      subgoal by (auto elim!: sync_elims)
      done
    done
  done


lemma combine_assn_inrdy_inrdy:
  assumes "ch1\<in>chs \<and> ch2\<in>chs"
  shows "combine_assn chs (Inrdy\<^sub>t s ch1 v1 rdy1 @\<^sub>t P) (Inrdy\<^sub>t s' ch2 v2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s ch1 v1 rdy1])
      apply auto
    subgoal
      apply(cases rule:inrdy_assn.cases[of s' ch2 v2 rdy2])
        apply auto
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        by (auto elim!: sync_elims)
      done
    subgoal for dd
      apply(cases rule:inrdy_assn.cases[of s' ch2 v2 rdy2])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d
        apply(cases "\<not> compat_rdy rdy1 rdy2")
        subgoal by (auto elim!: sync_elims)
        apply(cases "dd<d")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "dd>d")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          by (auto elim!: sync_elims)
        apply auto
        apply(elim combine_blocks_waitE2)
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      done
    done
  done



lemma combine_assn_inrdy_inrdy':
  assumes "ch1\<notin>chs \<and> ch2\<in>chs \<and> \<not> compat_rdy rdy1 rdy2"
  shows "combine_assn chs (Inrdy\<^sub>t s ch1 v1 rdy1 @\<^sub>t P) (Inrdy\<^sub>t s' ch2 v2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         In0\<^sub>t ch1 v1 @\<^sub>t combine_assn chs P (Inrdy\<^sub>t s' ch2 v2 rdy2 @\<^sub>t Q)"
  unfolding entails_tassn_def combine_assn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s ch1 v1 rdy1])
      apply auto
    subgoal
      apply(cases rule:inrdy_assn.cases[of s' ch2 v2 rdy2])
        apply auto
      subgoal
        apply(elim combine_blocks_unpairE1)
          apply auto
        apply(rule exI[where x="[InBlock ch1 v1]"])
        apply auto
        subgoal apply rule done
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(InBlock ch2 v2 # tr2b)"])
        by auto
      subgoal for d2
        apply(elim combine_blocks_unpairE3)
         apply auto
        apply(rule exI[where x="[InBlock ch1 v1]"])
        apply auto
        subgoal apply rule done
        apply(rule exI[where x=tr2a])
        apply auto
        apply(rule exI[where x="(WaitBlk d2 (\<lambda>_. EState s') rdy2 # InBlock ch2 v2 # tr2b)"])
        by auto
      done
    subgoal for d1
      apply(cases rule:inrdy_assn.cases[of s' ch2 v2 rdy2])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal for d2
        by (auto elim!: sync_elims)
      done
    done
  done


lemma combine_assn_inrdy_outrdy:
  assumes "ch1\<in>chs \<and> ch2\<in>chs \<and> \<not>compat_rdy rdy1 rdy2"
  shows "combine_assn chs (inrdy_assn s1 ch1 v1 rdy1 @\<^sub>t P)(outrdy_assn s2 ch2 v2 rdy2 @\<^sub>t Q)
         \<Longrightarrow>\<^sub>t \<up>(ch1 = ch2 \<and> v1= v2) \<and>\<^sub>t combine_assn chs P Q"
  unfolding entails_tassn_def combine_assn_def join_assn_def
  using assms
  apply auto
  subgoal for tr tr1a tr2a tr1b tr2b
    apply(cases rule:inrdy_assn.cases[of s1 ch1 v1 rdy1 tr1a])
      apply auto
    subgoal
      apply(cases rule:outrdy_assn.cases[of s2 ch2 v2 rdy2 tr1b])
        apply auto
      subgoal
        apply(auto elim!: combine_blocks_pairE)
        by blast
      by (auto elim!: sync_elims)
    subgoal
      apply(cases rule:outrdy_assn.cases[of s2 ch2 v2 rdy2 tr1b])
        apply auto
      by (auto elim!: sync_elims)
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
        Waitin\<^sub>t tt (\<lambda>t. ParState (EState (Sch p rn rp, ss)) (EState (Task WAIT ent tp, ts(T:= ts T + t))))
         (req_ch 2) 1 ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})
       @\<^sub>t (if 1\<le>rp then combine1 sk (Suc tk) (Sch (p@[(1,2)]) rn rp,ss(Pr:=1)) (Task WAIT ent tp,ts(T:= ts T + tt)) 
                   else (Out0\<^sub>t (run_ch 2) 0 @\<^sub>t combine1 sk (Suc tk) (Sch p 2 1,ss(Pr:=1)) (Task WAIT ent tp,ts(T:= ts T + tt))
                        \<or>\<^sub>t Waitp\<^sub>t ({run_ch 2},{}) @\<^sub>t true\<^sub>A)))
    \<or>\<^sub>t  (\<exists>\<^sub>ttt v.\<up> (0 \<le> tt \<and> tt < 9 / 200 - ts T \<and> v\<noteq>1) \<and>\<^sub>t
        Waitin\<^sub>t tt (\<lambda>t. ParState (EState (Sch p rn rp, ss)) (EState (Task WAIT ent tp, ts(T := ts T + t))))
         (req_ch 2) v ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t true\<^sub>A)
    \<or>\<^sub>t  (\<exists>\<^sub>ttt v.\<up> (0 \<le> tt \<and> tt < 9 / 200 - ts T) \<and>\<^sub>t 
        Waitin\<^sub>t tt (\<lambda>t. ParState (EState (Sch p rn rp, ss)) (EState (Task WAIT ent tp, ts(T := ts T + t))))
         (free_ch 2) v ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})
          @\<^sub>t (if length p > 0 then (Out0\<^sub>t (run_ch 2) 0 @\<^sub>t combine1 sk (Suc tk) (Sch (del_proc p 2) 2 1,ss(G:=v)) (Task WAIT ent tp,ts(T:= ts T + tt))
                                     \<or>\<^sub>t Waitp\<^sub>t  ({run_ch 2},{}) @\<^sub>t true\<^sub>A ) 
              else combine1 sk (Suc tk) (Sch [] (-1) (-1),ss(G:=v)) (Task WAIT ent tp,ts(T:= ts T + tt))))
    \<or>\<^sub>t  (\<exists>\<^sub>ttt v.\<up> (0 \<le> tt \<and> tt < 9 / 200 - ts T) \<and>\<^sub>t
        Waitin\<^sub>t tt(\<lambda>t. ParState (EState (Sch p rn rp, ss))(EState (Task WAIT ent tp, ts(T := ts T + t))))
         (exit_ch 2) v ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})
            @\<^sub>t combine1 sk (Suc tk) (Sch (del_proc p 2) rn rp,ss(G:=v)) (Task WAIT ent tp,ts(T:= ts T + tt)))
)"
| "combine1 (Suc sk) (Suc tk) (Sch p rn rp,ss) (Task READY ent tp,ts) = (
   (if rn = 2 then Out0\<^sub>t (preempt_ch 2) 0 @\<^sub>t combine1 sk tk (Sch p 1 2,ss(Pr:=2)) (Task RUNNING ent tp,ts(F:=0))
                \<or>\<^sub>t  Waitp\<^sub>t ({preempt_ch 2}, {run_ch 1}) @\<^sub>t true\<^sub>A 
                \<or>\<^sub>t  Waitp\<^sub>t ({exit_ch 1, preempt_ch 2}, {run_ch 1}) @\<^sub>t true\<^sub>A 
              else combine1 sk tk (Sch p 1 2,ss(Pr:=2)) (Task RUNNING ent tp,ts(F:=0)))
 \<or>\<^sub>t (In0\<^sub>t (req_ch 2) 1 @\<^sub>t (if 1\<le>rp then combine1 sk (Suc tk) (Sch (p @ [(1, 2)]) rn rp, ss(Pr := 1)) (Task READY ent tp,ts) 
                                   else (Out0\<^sub>t (run_ch 2) 0  @\<^sub>t combine1 sk (Suc tk) (Sch p 2 1, ss(Pr := 1)) (Task READY ent tp,ts)
                                        \<or>\<^sub>t  Waitp\<^sub>t ({req_ch 1, run_ch 2},{}) @\<^sub>t true\<^sub>A)))
 \<or>\<^sub>t (\<exists>\<^sub>tv. \<up> (v \<noteq> 1) \<and>\<^sub>t In0\<^sub>t (req_ch 2) v @\<^sub>t true\<^sub>A)
 \<or>\<^sub>t (\<exists>\<^sub>tv. In0\<^sub>t (free_ch 2) v @\<^sub>t (if length p > 0 then (Out0\<^sub>t (run_ch 2) 0  @\<^sub>t combine1 sk (Suc tk) (Sch (del_proc p 2) 2 1, ss(G := v)) (Task READY ent tp,ts)
                                        \<or>\<^sub>t  Waitp\<^sub>t ({req_ch 1, run_ch 2},{}) @\<^sub>t true\<^sub>A) 
                                 else combine1 sk (Suc tk) (Sch [] (- 1) (- 1), ss(G := v)) (Task READY ent tp,ts)))
 \<or>\<^sub>t (\<exists>\<^sub>tv. In0\<^sub>t (exit_ch 2) v @\<^sub>t combine1 sk (Suc tk) (Sch (del_proc p 2) rn rp, ss(G := v)) (Task READY ent tp,ts))
)"
| "combine1 (Suc sk) (Suc tk) (Sch p rn rp,ss) (Task RUNNING ent tp,ts) = (
  (Wait\<^sub>t (min (45 / 10 ^ 3 - ts T) (1 / 10\<^sup>2 - C_upd ent (ts C)))
     (\<lambda>t. ParState (EState (Sch p rn rp, ss))
           (EState (Task RUNNING eone tp, ts(T := ts T + t, C := C_upd ent (ts C) + t))))
     ({}, {preempt_ch 1, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t 
     (if length p > 0 then out_0assn (run_ch 2) 0 @\<^sub>t combine1 sk tk (Sch (del_proc p 2) 2 1,ss(G:=0)) (Task WAIT eone tp, ts(T:=ts T + min(0.045-ts T)(0.01-C_upd ent (ts C)),C:=C_upd ent (ts C) + min(0.045-ts T)(0.01-C_upd ent (ts C))))
                           \<or>\<^sub>t Waitp\<^sub>t ({run_ch 2}, {}) @\<^sub>t true\<^sub>A \<or>\<^sub>t Waitp\<^sub>t ({req_ch 1, run_ch 2}, {}) @\<^sub>t true\<^sub>A
                      else combine1 sk tk (Sch [] (-1) (-1),ss(G:=0)) (Task WAIT eone tp, ts(T:=ts T + min(0.045-ts T)(0.01-C_upd ent (ts C)),C:=C_upd ent (ts C) + min(0.045-ts T)(0.01-C_upd ent (ts C))))))
\<or>\<^sub>t  (\<exists>\<^sub>t t. \<up> (0 \<le> t \<and> t \<le> min (45 / 10 ^ 3 - ts T) (1 / 10\<^sup>2 - C_upd ent (ts C))) \<and>\<^sub>t
           Waitin\<^sub>t t (\<lambda>t. ParState (EState (Sch p rn rp, ss))
                  (EState (Task RUNNING eone 2, ts
                     (T := ts T + t,
                      C := C_upd ent (ts C) + t))))
            (req_ch 2) 1 ({}, {preempt_ch 1, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})
               @\<^sub>t combine1 sk (Suc tk) (Sch (p@[(1,2)]) 1 2,ss(Pr:=1)) (Task RUNNING eone tp,ts
                 (T := ts T + t,
                  C := C_upd ent (ts C) + t)))
\<or>\<^sub>t  (\<exists>\<^sub>t t v. \<up> (0 \<le> t \<and> t \<le> min (45 / 10 ^ 3 - ts T) (1 / 10\<^sup>2 - C_upd ent (ts C)) \<and> v \<noteq> 1) \<and>\<^sub>t
           Waitin\<^sub>t t (\<lambda>t. ParState (EState (Sch p rn rp, ss))
                  (EState (Task RUNNING eone 2, ts
                     (T := ts T + t,
                      C := C_upd ent (ts C) + t))))
            (req_ch 2) v ({}, {preempt_ch 1, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})
               @\<^sub>t true\<^sub>A)
\<or>\<^sub>t  (\<exists>\<^sub>t t v. \<up> (0 \<le> t \<and> t \<le> min (45 / 10 ^ 3 - ts T) (1 / 10\<^sup>2 - C_upd ent (ts C))) \<and>\<^sub>t
           Waitin\<^sub>t t (\<lambda>t. ParState (EState (Sch p rn rp, ss))
                  (EState (Task RUNNING eone 2, ts
                     (T := ts T + t,
                      C := C_upd ent (ts C) + t))))
            (free_ch 2) v ({}, {preempt_ch 1, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})
               @\<^sub>t true\<^sub>A)
\<or>\<^sub>t  (\<exists>\<^sub>t t v. \<up> (0 \<le> t \<and> t \<le> min (45 / 10 ^ 3 - ts T) (1 / 10\<^sup>2 - C_upd ent (ts C))) \<and>\<^sub>t
           Waitin\<^sub>t t (\<lambda>t. ParState (EState (Sch p rn rp, ss))
                  (EState (Task RUNNING eone 2, ts
                     (T := ts T + t,
                      C := C_upd ent (ts C) + t))))
            (exit_ch 2) v ({}, {preempt_ch 1, req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})
               @\<^sub>t combine1 sk (Suc tk) (Sch (del_proc p 2) 1 2,ss(G := v)) (Task RUNNING eone tp,ts
                 (T := ts T + t,
                  C := C_upd ent (ts C) + t)))

)"



definition propc :: "nat \<Rightarrow> estate \<Rightarrow> estate \<Rightarrow> bool" where
"propc k schs task_es = (k>0 \<longrightarrow>(status task_es = RUNNING \<longleftrightarrow> run_now schs = 1))"


lemma combine_SCH_T1:
"propc nt (Sch p rn rp) (Task st ent 2) \<Longrightarrow>
   proper (Sch p rn rp) \<Longrightarrow>
   inv_s ts \<Longrightarrow>
 combine_assn {req_ch 1, preempt_ch 1, run_ch 1, free_ch 1, exit_ch 1} 
 (SCH_tr ns (Sch p rn rp,ss)) (T1_tr nt (Task st ent 2,ts)) \<Longrightarrow>\<^sub>t
 combine1 ns nt (Sch p rn rp,ss) (Task st ent 2,ts) "
proof(induction " nt+ns"  arbitrary: nt ns p rn rp ts st ent ss rule: less_induct)
  case less
  then show ?case 
    apply(cases ns)
    subgoal
      apply(cases nt)
      subgoal
        by auto
      subgoal for nt'
        apply(cases st)
        apply auto
        subgoal premises pre
          apply(rule entails_tassn_trans)
           apply(rule combine_assn_emp_wait')
          using pre(1)[of nt' 0 p rn rp READY ezero "ts(T := 0)" ss] pre(2,3,4)
          apply(subgoal_tac "propc nt' (Sch p rn rp) (Task READY ezero 2)")
          subgoal unfolding proper_def inv_s_def by auto
          subgoal unfolding propc_def 
            apply(cases nt') subgoal by auto
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
            apply(simp add: combine_assn_emp_waitin)
            done
          subgoal
            apply(rule entails_tassn_trans)
             apply(rule combine_assn_emp_wait')
            apply(rule combine_or_right)
            subgoal by(simp add: combine_assn_emp_outrdy)
            subgoal apply(rule combine_assn_ex_pre_right')
              by(simp add: combine_assn_emp_inrdy)
            done
          done
        done
      done
    subgoal for ns'
      apply(cases nt)
      subgoal
        apply (simp only: SCH_tr.simps T1_tr.simps)
        apply(rule combine_or_left)
        subgoal
          apply(simp add: combine_assn_inrdy_emp)
          done
        apply(rule combine_or_left)
        subgoal
          apply(rule combine_assn_ex_pre_left')+
          apply(rule combine_assn_pure_pre_left')
          apply(simp add: combine_assn_inrdy_emp)
          done
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
            using pre(1)[of 0 ns' "(p @ [(1, 2)])" rn rp st ent ts "ss(Pr := 1)"] pre(2,3,4) properl_p1[of p 1 2]
            by(auto simp add:propc_def proper_def properp_def inv_s_def)
          apply(cases "rn = 1")
          subgoal apply simp
            apply(rule combine_or_left)
            subgoal
              apply(simp add: combine_assn_out0_emp)
              done
            apply(rule combine_or_left)
            subgoal
              apply(simp add: combine_assn_waitp_emp)
              done
            subgoal
              apply(simp add: combine_assn_out0_emp)
              done
            done
          apply simp
          apply(rule combine_or_left)
            subgoal
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_out0_emp')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              apply(rule entails_tassn_cancel_left)
              using pre(1)[of 0 ns' p 2 1 st ent ts "ss(Pr := 1)" ] pre(2,3,4)
              by (auto simp add:propc_def proper_def properp_def)
            subgoal
              apply(simp add: combine_assn_waitp_emp)
              done
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
            apply(simp add: combine_assn_inrdy_emp)
            done
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
                using pre(1)[of 0 ns' "(del_proc p 2)" 2 1 st ent ts "ss(G := v)"] pre(2,3,4) properl_p4[of p 2]
                by(auto simp add:propc_def proper_def properp_def)
              subgoal
                apply(simp add: combine_assn_waitp_emp)
                done
              done
            subgoal
              apply simp
              using pre(1)[of 0 ns' "[]" "-1" "-1" st ent ts "ss(G := v)"] pre(2,3,4) properl_p4[of p 2]
              by(auto simp add:propc_def proper_def properp_def)
            done
          done
        apply(rule combine_or_left)
        subgoal
          apply(rule combine_assn_ex_pre_left')
            apply(simp add: combine_assn_inrdy_emp)
          done
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
              using pre(1)[of 0 ns' "(del_proc p 2)" rn rp st ent ts "ss(G := v)"] pre(2,3,4) properl_p4[of p 2]
              by(auto simp add:propc_def proper_def properp_def)
            done
          done
        subgoal for nt'






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
              subgoal using pre(4) unfolding inv_s_def by auto
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
              subgoal using pre(4) unfolding inv_s_def by auto
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
                subgoal using pre(4) unfolding inv_s_def by auto
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
                  apply(rule entails_tassn_disjI1)
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
                  subgoal using pre(4) unfolding inv_s_def C_def T_def by auto
                  apply(rule combine_assn_right_tran)
                  apply simp
                  thm pre
                  subgoal premises pre' for tt
                  proof-
                    have 1:"(9 / 200 - (ts T + tt)) = (9 / 200 - ts T - tt)"
                      by auto
                    have 2:"(\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + tt + t))) = (\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + (t + tt))))"
                      apply(rule ext)
                      by auto
                    show ?thesis
                      by(auto simp add:1 2)
                  qed
                  done
                subgoal 
                  apply(subgoal_tac"rn\<noteq>1")
                   prefer 2
                  subgoal using pre(2) unfolding propc_def by auto
                  apply simp
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI1)
                  apply(rule ex_tran)
                  apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule combine_assn_left_disj)
                  subgoal for tt
                    apply(rule entails_tassn_disjI1)
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_out0_wait')
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                    apply(rule entails_tassn_trans)
                     prefer 2
                     apply(rule pre)
                    subgoal by auto
                    subgoal using pre(2) unfolding propc_def by auto
                    subgoal using pre(2,3) properl_p1[of p 1 2] unfolding proper_def properp_def
                      by auto
                    subgoal using pre(4) unfolding inv_s_def C_def T_def  by auto
                    apply(rule combine_assn_right_tran)
                    apply simp
                    thm pre
                    subgoal premises pre'
                    proof-
                      have 1:"(9 / 200 - (ts T + tt)) = (9 / 200 - ts T - tt)"
                        by auto
                      have 2:"(\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + tt + t))) = (\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + (t + tt))))"
                        apply(rule ext)
                        by auto
                      show ?thesis
                        by(auto simp add:1 2)
                    qed
                    done
                  subgoal for tt
                    apply(rule entails_tassn_disjI2)
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_waitp_wait)
                    subgoal by auto
                    by auto
                  done
                done
              done
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule combine_assn_pure_pre_left')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_wait')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              apply(rule entails_tassn_disjE)
              subgoal for v
                apply simp
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_cancel_left)
                apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre)
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) by auto
                subgoal using pre(4) unfolding inv_s_def by auto
                apply(rule combine_assn_left_tran)
                unfolding SCH_tr.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_exI[where x= v])
                by auto
              subgoal for v
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                apply(rule ex_tran)
                apply auto
                apply(rule entails_tassn_exI[where x= v])
                apply auto
                apply(rule entails_tassn_cancel_left)
                unfolding entails_tassn_def true_assn_def
                by auto
              done
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule entails_tassn_trans)
              apply(rule combine_assn_inrdy_wait)
              subgoal by auto
              unfolding combine1.simps
              apply(rule entails_tassn_disjI1)
              apply(rule entails_tassn_cancel_both)
              subgoal by auto
              apply(rule entails_tassn_trans)
                prefer 2
                apply(rule pre)
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) by auto
              subgoal using pre(4) unfolding inv_s_def by auto
              apply(rule combine_assn_left_tran)
              unfolding SCH_tr.simps
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI1)
              subgoal for v
                apply(rule entails_tassn_exI[where x= v])
                by auto
              done
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_wait')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              apply(rule entails_tassn_disjE)
              subgoal for v
                unfolding combine1.simps
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_cancel_both)
                subgoal by auto
                apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre)
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) by auto
                subgoal using pre(4) unfolding inv_s_def by auto
                apply(rule combine_assn_left_tran)
                unfolding SCH_tr.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_exI[where x= v])
                by auto
              subgoal for v
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                apply(rule ex_tran)
                apply(cases "length p > 0")
                subgoal for tt
                  apply(subgoal_tac"get_max p = (1, 2)")
                   prefer 2
                  subgoal using pre(3) properl_p5[of p]
                  apply auto
                  apply(cases "get_max p")
                    by (auto simp add: proper_def properp_def)
                  apply auto
                  apply(rule entails_tassn_exI[where x= v])
                  apply(rule entails_tassn_cancel_left)
                  apply(rule combine_assn_left_disj)
                  subgoal
                    apply(rule entails_tassn_disjI1)
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_out0_wait')
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                    apply(rule entails_tassn_trans)
                     prefer 2
                     apply(rule pre)
                    subgoal by auto
                    subgoal using pre(2) unfolding propc_def by auto
                    subgoal using pre(2,3) properl_p4[of p 2] unfolding proper_def properp_def
                      by auto
                    subgoal using pre(4) unfolding inv_s_def C_def T_def by auto
                    apply(rule combine_assn_right_tran)
                    unfolding T1_tr.simps
                    apply simp
                    thm pre
                    subgoal premises pre'
                    proof-
                      have 1:"(9 / 200 - (ts T + tt)) = (9 / 200 - ts T - tt)"
                        by auto
                      have 2:"(\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + tt + t))) = (\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + (t + tt))))"
                        apply(rule ext)
                        by auto
                      show ?thesis
                        by(auto simp add:1 2)
                    qed
                    done
                  subgoal 
                    apply(rule entails_tassn_disjI2)
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_waitp_wait)
                    subgoal by auto
                    by auto
                  done
                subgoal for tt
                  apply auto
                  apply(rule entails_tassn_exI[where x= v])
                  apply(rule entails_tassn_cancel_left)
                    apply(rule entails_tassn_trans)
                     prefer 2
                     apply(rule pre)
                    subgoal by auto
                    subgoal using pre(2) unfolding propc_def by auto
                    subgoal using pre(2,3) properl_p4[of p 2] unfolding proper_def properp_def
                      by auto
                    subgoal using pre(4) unfolding inv_s_def C_def T_def by auto
                    apply(rule combine_assn_right_tran)
                    unfolding T1_tr.simps
                    apply simp
                    thm pre
                    subgoal premises pre'
                    proof-
                      have 1:"(9 / 200 - (ts T + tt)) = (9 / 200 - ts T - tt)"
                        by auto
                      have 2:"(\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + tt + t))) = (\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + (t + tt))))"
                        apply(rule ext)
                        by auto
                      show ?thesis
                        by(auto simp add:1 2)
                    qed
                    done
                  done
                done
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule entails_tassn_trans)
              apply(rule combine_assn_inrdy_wait)
              subgoal by auto
              unfolding combine1.simps
              apply(rule entails_tassn_disjI1)
              apply(rule entails_tassn_cancel_both)
              subgoal by auto
              apply(rule entails_tassn_trans)
                prefer 2
                apply(rule pre)
              subgoal by auto
              subgoal using pre(2) unfolding propc_def by auto
              subgoal using pre(3) by auto
              subgoal using pre(4) unfolding inv_s_def by auto
              apply(rule combine_assn_left_tran)
              unfolding SCH_tr.simps
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI1)
              subgoal for v
                apply(rule entails_tassn_exI[where x= v])
                by auto
              done
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_wait')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              unfolding combine1.simps
              apply(rule entails_tassn_disjE)
              subgoal for v
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_cancel_both)
                subgoal by auto
                apply(rule entails_tassn_trans)
                prefer 2
                apply(rule pre)
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(2,3) properl_p4[of p 2] unfolding proper_def properp_def
                  by auto
                subgoal using pre(4) unfolding inv_s_def by auto
                apply(rule combine_assn_left_tran)
                unfolding SCH_tr.simps
                apply(rule entails_tassn_disjI2)+
                apply(rule entails_tassn_exI[where x= v])
                by auto
              subgoal for v
                apply(rule entails_tassn_disjI2)+
                apply(rule ex_tran)
                subgoal for tt
                  apply(rule entails_tassn_exI[where x= v])
                  apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                     prefer 2
                     apply(rule pre)
                    subgoal by auto
                    subgoal using pre(2) unfolding propc_def by auto
                    subgoal using pre(2,3) properl_p4[of p 2] unfolding proper_def properp_def
                      by auto
                    subgoal using pre(4) unfolding inv_s_def C_def T_def by auto
                    apply(rule combine_assn_right_tran)
                    unfolding T1_tr.simps
                    apply simp
                    thm pre
                    subgoal premises pre'
                    proof-
                      have 1:"(9 / 200 - (ts T + tt)) = (9 / 200 - ts T - tt)"
                        by auto
                      have 2:"(\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + tt + t))) = (\<lambda>t. EState (Task WAIT ent 2, ts(T := ts T + (t + tt))))"
                        apply(rule ext)
                        by auto
                      show ?thesis
                        by(auto simp add:1 2)
                    qed
                    done
                  done
                done
              done




          apply (simp only: SCH_tr.simps T1_tr.simps)
          subgoal premises pre
            apply(rule combine_or_left)
            subgoal 
              unfolding combine1.simps
              apply(rule entails_tassn_disjI1)
              apply(rule combine_or_right)
              subgoal
               apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                subgoal for v tt
                  apply(rule entails_tassn_trans)
                  apply(rule combine_assn_inrdy_out)
                  subgoal by auto
                  apply(subgoal_tac"rp<2")
                   prefer 2
                  subgoal premises pre'
                  proof-
                    have 1:"rn \<noteq> 1"
                      using pre(2,3) unfolding propc_def by auto
                    have 2:"rp \<noteq> 2"
                      using pre(2,3) unfolding propc_def proper_def properp_def  by auto
                    then show ?thesis
                      using pre(2,3) unfolding propc_def proper_def properp_def by auto
                  qed
                  apply(cases "rn = 2")
                   apply auto
                  subgoal
                    apply(rule combine_or_left)
                    subgoal
                      apply(rule entails_tassn_disjI1)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_out0_waitin')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      apply(rule entails_tassn_cancel_left)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_out0_waitin)
                      subgoal by auto
                      apply auto
                      apply(rule entails_tassn_trans)
                       prefer 2
                       apply(rule pre(1))
                      subgoal by auto
                      subgoal unfolding propc_def by auto
                      subgoal using pre(3) unfolding proper_def properp_def by auto
                      subgoal using pre(4) unfolding inv_s_def by auto
                      by auto
                    apply(rule combine_or_left)
                    subgoal
                      apply(rule entails_tassn_disjI2)
                      apply(rule entails_tassn_disjI1)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitp_waitin)
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      by auto
                    subgoal
                      apply(rule entails_tassn_disjI1)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_out0_waitin')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      apply(rule entails_tassn_cancel_left)
                      apply(rule combine_assn_waitp_waitin')
                      by auto
                    done
                  apply(rule combine_or_left)
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_out0_waitin)
                    subgoal by auto
                    apply(rule entails_tassn_trans)
                    prefer 2
                     apply(rule pre(1))
                    subgoal by auto
                    subgoal unfolding propc_def by auto
                    subgoal using pre(3) unfolding proper_def properp_def by auto
                    subgoal using pre(4) unfolding inv_s_def by auto
                    by auto
                  subgoal
                    apply(rule combine_assn_waitp_waitin')
                    by auto
                  done
                done
              subgoal 
                apply(rule entails_tassn_trans)
                apply(rule combine_assn_inrdy_out)
                subgoal by auto
                apply(subgoal_tac"rp<2")
                 prefer 2
                subgoal premises pre'
                  proof-
                  have 1:"rn \<noteq> 1"
                      using pre(2,3) unfolding propc_def by auto
                    have 2:"rp \<noteq> 2"
                      using pre(2,3) unfolding propc_def proper_def properp_def  by auto
                    then show ?thesis
                      using pre(2,3) unfolding propc_def proper_def properp_def by auto
                  qed
               apply(cases "rn = 2")
                 apply auto
                  subgoal
                    apply(cases "(9 / 200 - ts T) \<le> 0")
                    subgoal apply simp
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_or_right)
                        subgoal
                          apply(rule entails_tassn_disjI1)
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_out0_outrdy2)
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule combine_assn_out0_outrdy1)
                          by auto
                        subgoal
                          apply(rule combine_assn_ex_pre_right')
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_out0_inrdy2)
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          apply(rule entails_tassn_disjI1)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_out0_inrdy1)
                          subgoal by auto
                          using pre(4) unfolding inv_s_def
                          apply auto
                          apply(subgoal_tac "ts(F := 0) = ts(T := 9 / 200, F := 0)")
                           prefer 2
                          subgoal
                            by(auto simp add:T_def F_def)
                          apply simp
                          apply(rule entails_tassn_trans)
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) unfolding proper_def properp_def by auto
                          subgoal using pre(4) unfolding inv_s_def by auto
                          by auto
                        done
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_or_right)
                        subgoal apply(rule entails_tassn_disjI2)+
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_waitp_outrdy)
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          by auto
                        subgoal apply(rule entails_tassn_disjI2)+
                          apply(rule combine_assn_ex_pre_right')
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_waitp_inrdy)
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          by auto
                        done
                      subgoal
                        apply(rule combine_or_right)
                        subgoal
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_out0_outrdy2)
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          apply(rule entails_tassn_disjI1)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule combine_assn_waitp_outrdy')
                          by auto
                        subgoal
                          apply(rule entails_tassn_disjI1)
                          apply(rule combine_assn_ex_pre_right')
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_out0_inrdy2)
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule combine_assn_waitp_inrdy')
                          by auto
                        done
                      done
                    apply(rule combine_or_left)
                    subgoal
                      apply(rule entails_tassn_disjI1)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_out0_wait')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      apply(rule entails_tassn_cancel_left)
                      apply(rule combine_assn_out0_wait)
                      by auto
                    apply(rule combine_or_left)
                    subgoal
                      apply(rule entails_tassn_disjI2)
                      apply(rule entails_tassn_disjI1)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_waitp_wait)
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      by auto
                    subgoal
                      apply(rule entails_tassn_disjI1)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_out0_wait')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      apply(rule entails_tassn_cancel_left)
                      apply(rule combine_assn_waitp_wait')
                      by auto
                    done
                  apply(cases "(9 / 200 - ts T) \<le> 0")
                    subgoal apply simp
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_or_right)
                        subgoal
                          apply(rule combine_assn_out0_outrdy1)
                          by auto
                        subgoal
                          apply(rule combine_assn_ex_pre_right')
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_out0_inrdy1)
                          subgoal by auto
                          apply auto
                          using pre(4) unfolding inv_s_def
                          apply auto
                          apply(subgoal_tac "ts(F := 0) = ts(T := 9 / 200, F := 0)")
                           prefer 2
                          subgoal
                            by(auto simp add:T_def F_def)
                          apply simp
                          apply(rule entails_tassn_trans)
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) unfolding proper_def properp_def by auto
                          subgoal using pre(4) unfolding inv_s_def T_def C_def by auto
                          by auto
                        done
                      subgoal
                      apply(rule combine_or_right)
                        subgoal
                          apply(rule combine_assn_waitp_outrdy')
                          by auto
                        subgoal
                          apply(rule combine_assn_ex_pre_right')
                          apply(rule combine_assn_waitp_inrdy')
                          by auto
                        done
                      done
                    subgoal
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule combine_assn_out0_wait)
                        by auto
                      subgoal
                        apply(rule combine_assn_waitp_wait')
                        by auto
                      done
                    done
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_left')
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_inrdy_out)
                    subgoal by auto
                    by auto
                  subgoal
                    apply(rule combine_assn_ex_pre_left')
                    apply(rule combine_assn_pure_pre_left')
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_inrdy_out)
                    subgoal by auto
                    by auto
                  done
                apply(rule combine_or_left)
                subgoal
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI1)
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')+
                    apply(rule combine_assn_pure_pre_right')
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_inrdy_out')
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                    apply(cases "1\<le>rp")
                    subgoal for v tt
                      apply simp
                      apply(rule entails_tassn_trans)
                       prefer 2
                       apply(rule pre(1))
                      subgoal by auto
                      subgoal using pre(2) unfolding propc_def by auto
                      subgoal using pre(3) properl_p1[of p 1 2] unfolding proper_def properp_def by auto
                      subgoal using pre(4) by auto
                      apply(rule combine_assn_right_tran)
                      unfolding T1_tr.simps
                      apply(rule entails_tassn_disjI1)
                      apply(rule entails_tassn_exI[where x=v])
                      apply(rule entails_tassn_exI[where x=tt])
                      by auto
                    subgoal for v tt
                      apply(subgoal_tac"rn\<noteq>1")
                       prefer 2
                      subgoal using pre(2) unfolding propc_def by auto
                      apply simp
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule entails_tassn_disjI1)
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_out0_out2)
                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        apply(rule entails_tassn_cancel_left)
                        apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                        subgoal by auto
                        subgoal using pre(2) unfolding propc_def by auto
                        subgoal using pre(3) unfolding proper_def properp_def by auto
                        subgoal using pre(4) by auto
                        apply(rule combine_assn_right_tran)
                        unfolding T1_tr.simps
                        apply(rule entails_tassn_disjI1)
                        apply(rule entails_tassn_exI[where x=v])
                        apply(rule entails_tassn_exI[where x=tt])
                        by auto 
                      subgoal
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitp_out)
                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        by auto
                      done
                    done
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_inrdy_out')
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                    apply(cases "1\<le>rp")
                    subgoal 
                      apply simp
                      apply(rule entails_tassn_trans)
                       prefer 2
                       apply(rule pre(1))
                      subgoal by auto
                      subgoal using pre(2) unfolding propc_def by auto
                      subgoal using pre(3) properl_p1[of p 1 2] unfolding proper_def properp_def by auto
                      subgoal using pre(4) by auto
                      apply(rule combine_assn_right_tran)
                      unfolding T1_tr.simps
                      apply(rule entails_tassn_disjI2)
                      by auto
                    subgoal 
                      apply(subgoal_tac"rn\<noteq>1")
                       prefer 2
                      subgoal using pre(2) unfolding propc_def by auto
                      apply simp
                      apply(rule combine_or_left)
                      subgoal
                        apply(rule entails_tassn_disjI1)
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_out0_out2)
                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        apply(rule entails_tassn_cancel_left)
                        apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                        subgoal by auto
                        subgoal using pre(2) unfolding propc_def by auto
                        subgoal using pre(3) unfolding proper_def properp_def by auto
                        subgoal using pre(4) by auto
                        apply(rule combine_assn_right_tran)
                        unfolding T1_tr.simps
                        apply(rule entails_tassn_disjI2)
                        by auto 
                      subgoal
                        apply(rule entails_tassn_disjI2)
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitp_out)
                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        by auto
                      done
                    done
                  done
                apply(rule combine_or_left)
                subgoal
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI1)
                  apply(rule combine_assn_ex_pre_left')
                  apply(rule combine_assn_pure_pre_left')
                  subgoal for v
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_inrdy_out')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      subgoal for vv tt
                        apply(rule entails_tassn_exI[where x=v])
                        apply auto
                        apply(rule entails_tassn_cancel_left)
                        by(auto simp add:true_assn_def entails_tassn_def)
                      done
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_inrdy_out')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      subgoal 
                        apply(rule entails_tassn_exI[where x=v])
                        apply auto
                        apply(rule entails_tassn_cancel_left)
                        by(auto simp add:true_assn_def entails_tassn_def)
                      done
                    done
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')
                  subgoal for v
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_inrdy_out'')
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule combine_assn_inrdy_out'')
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    done
                  done
                apply(rule combine_or_left)
                subgoal
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI1)
                  apply(rule combine_assn_ex_pre_left')
                  subgoal for v
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_inrdy_out')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      subgoal for vv tt
                        apply(cases "0<length p")
                        subgoal
                          apply(subgoal_tac"get_max p = (1,2)")
                          prefer 2
                          subgoal using pre(3) properl_p5[of p]
                            apply auto
                             apply(cases "get_max p")
                            by (auto simp add: proper_def properp_def)
                          apply simp
                          apply(rule entails_tassn_exI[where x= v])
                          apply(rule entails_tassn_cancel_left)
                          apply(rule combine_or_left)
                          subgoal
                            apply(rule entails_tassn_trans)
                             apply(rule combine_assn_out0_out2)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                            apply(rule entails_tassn_disjI1)
                            apply(rule entails_tassn_cancel_left)
                            apply(rule entails_tassn_trans)
                             prefer 2
                             apply(rule pre(1))
                            subgoal by auto
                            subgoal using pre(2) unfolding propc_def by auto
                            subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                            subgoal using pre(4) by auto
                            apply(rule combine_assn_right_tran)
                            unfolding T1_tr.simps
                            apply(rule entails_tassn_disjI1)
                            apply(rule entails_tassn_exI[where x=vv])
                            apply(rule entails_tassn_exI[where x=tt])
                            by auto 
                          subgoal
                            apply(rule entails_tassn_trans)
                             apply(rule combine_assn_waitp_out)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                            apply(rule entails_tassn_disjI2)
                            by auto
                          done
                        subgoal
                          apply simp
                          apply(rule entails_tassn_exI[where x=v])
                          apply(rule entails_tassn_cancel_left)
                          apply(rule entails_tassn_trans)
                          prefer 2
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                          subgoal using pre(4) by auto
                          apply(rule combine_assn_right_tran)
                          unfolding T1_tr.simps
                          apply(rule entails_tassn_disjI1)
                          apply(rule entails_tassn_exI[where x=vv])
                          apply(rule entails_tassn_exI[where x=tt])
                          by auto 
                        done
                      done
                    subgoal
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_inrdy_out')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      subgoal 
                        apply(cases "0<length p")
                        subgoal
                          apply(subgoal_tac"get_max p = (1,2)")
                          prefer 2
                          subgoal using pre(3) properl_p5[of p]
                            apply auto
                             apply(cases "get_max p")
                            by (auto simp add: proper_def properp_def)
                          apply simp
                          apply(rule entails_tassn_exI[where x= v])
                          apply(rule entails_tassn_cancel_left)
                          apply(rule combine_or_left)
                          subgoal
                            apply(rule entails_tassn_trans)
                             apply(rule combine_assn_out0_out2)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                            apply(rule entails_tassn_disjI1)
                            apply(rule entails_tassn_cancel_left)
                            apply(rule entails_tassn_trans)
                             prefer 2
                             apply(rule pre(1))
                            subgoal by auto
                            subgoal using pre(2) unfolding propc_def by auto
                            subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                            subgoal using pre(4) by auto
                            apply(rule combine_assn_right_tran)
                            unfolding T1_tr.simps
                            apply(rule entails_tassn_disjI2)                            
                            by auto 
                          subgoal
                            apply(rule entails_tassn_trans)
                             apply(rule combine_assn_waitp_out)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                            apply(rule entails_tassn_disjI2)
                            by auto
                          done
                        subgoal
                          apply simp
                          apply(rule entails_tassn_exI[where x=v])
                          apply(rule entails_tassn_cancel_left)
                          apply(rule entails_tassn_trans)
                          prefer 2
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                          subgoal using pre(4) by auto
                          apply(rule combine_assn_right_tran)
                          unfolding T1_tr.simps
                          apply(rule entails_tassn_disjI2)                         
                          by auto 
                        done
                      done
                    done
                  done
                apply(rule combine_or_left)
                subgoal
                  apply(rule combine_assn_ex_pre_left')
                  subgoal for v
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule combine_assn_inrdy_out'')
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    subgoal
                      apply(rule combine_assn_inrdy_out'')
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    done
                  done
                subgoal
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI2)
                  apply(rule combine_assn_ex_pre_left')
                  subgoal for v
                    apply(rule combine_or_right)
                    subgoal
                      apply(rule combine_assn_ex_pre_right')+
                      apply(rule combine_assn_pure_pre_right')
                      apply(rule entails_tassn_trans)
                       apply(rule combine_assn_inrdy_out')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      subgoal for vv tt
                        apply(rule entails_tassn_exI[where x = v])
                        apply(rule entails_tassn_cancel_left)
                        apply(rule entails_tassn_trans)
                          prefer 2
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                          subgoal using pre(4) by auto
                          apply simp
                          apply(rule combine_assn_right_tran)
                          unfolding T1_tr.simps
                          apply(rule entails_tassn_disjI1)
                          apply(rule entails_tassn_exI[where x=vv])
                          apply(rule entails_tassn_exI[where x=tt])
                          by auto 
                        done
                    subgoal
                       apply(rule entails_tassn_trans)
                       apply(rule combine_assn_inrdy_out')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                      subgoal 
                        apply(rule entails_tassn_exI[where x = v])
                        apply(rule entails_tassn_cancel_left)
                        apply(rule entails_tassn_trans)
                          prefer 2
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                          subgoal using pre(4) by auto
                          apply simp
                          apply(rule combine_assn_right_tran)
                          unfolding T1_tr.simps
                          apply(rule entails_tassn_disjI2)                       
                          by auto 
                        done
                      done
                    done
                  done






        apply (simp only: SCH_tr.simps T1_tr.simps)
          subgoal premises pre
            apply(rule combine_or_left)
            subgoal 
              apply(rule combine_or_right)
              subgoal
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                apply(rule combine_assn_inrdy_waitin)
                by auto
              subgoal
                unfolding combine1.simps
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_wait)
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply(rule entails_tassn_cancel_both)
                subgoal by auto
                apply(rule combine_or_right)
                subgoal
                  apply(rule combine_assn_inrdy_outrdy'')
                  subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  done
                subgoal
                  apply(rule combine_assn_ex_pre_right')
                  apply(rule combine_assn_inrdy_inrdy)
                  subgoal by auto
                  done
                done
              done
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule combine_assn_pure_pre_left')
              apply(rule combine_or_right)
              subgoal for v
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                apply(rule combine_assn_inrdy_waitin)
                by auto
              subgoal for v
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_wait)
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                unfolding combine1.simps
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_cancel_both)
                subgoal by auto
                apply(rule combine_or_right)
                subgoal
                  apply(rule combine_assn_inrdy_outrdy'')
                  subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  done
                subgoal
                  apply(rule combine_assn_ex_pre_right')
                  apply(rule combine_assn_inrdy_inrdy)
                  by auto
                done
              done
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_or_right)
              subgoal
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_waitin')
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                apply(rule ex_tran)
                apply(subgoal_tac"rp = 2 \<and> rn = 1")
                 prefer 2
                subgoal using pre(2,3)
                  unfolding propc_def proper_def properp_def 
                  by auto
                apply (auto simp add:T_def C_def)
                apply(rule entails_tassn_cancel_left)
                apply(rule entails_tassn_trans)
                 prefer 2
                 apply(rule pre(1))
                subgoal by auto
                subgoal using pre(2) unfolding propc_def by auto
                subgoal using pre(3) properl_p1[of p 1 2] unfolding proper_def properp_def by auto
                subgoal using pre(4) unfolding inv_s_def T_def C_def by auto
                apply(rule combine_assn_right_tran)
                unfolding T1_tr.simps
                subgoal for v tt tta
                  apply(rule entails_tassn_disjI1)
                  apply(rule entails_tassn_exI[where x=v])
                  apply(rule entails_tassn_exI[where x="tt-tta"])
                  apply(auto simp add:C_def T_def C_upd_def)
                  subgoal
                    apply(rule entails_tassn_cancel_right)
                    subgoal premises pre'
                    proof-
                      have "(\<lambda>t. EState
                          (Task RUNNING eone 2, ts
                          (CHR ''t'' := ts CHR ''t'' + tta + t, CHR ''c'' := tta + t)))
                          = (\<lambda>t. EState
                          (Task RUNNING eone 2, ts
                          (CHR ''t'' := ts CHR ''t'' + (t + tta), CHR ''c'' := t + tta)))"
                        apply(rule ext)
                        by auto
                      then show ?thesis
                        by auto
                    qed
                    done
                  subgoal
                    apply(rule entails_tassn_cancel_right)
                    subgoal premises pre'
                    proof-
                      have "(\<lambda>t. EState
           (Task RUNNING eone 2, ts
            (CHR ''t'' := ts CHR ''t'' + tta + t, CHR ''c'' := ts CHR ''c'' + tta + t)))
                          = (\<lambda>t. EState
           (Task RUNNING eone 2, ts
            (CHR ''t'' := ts CHR ''t'' + (t + tta),CHR ''c'' := ts CHR ''c'' + (t + tta))))"
                        apply(rule ext)
                        by auto
                      then show ?thesis
                        by auto
                    qed
                    done
                  done
                done
              subgoal
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_wait')
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply(rule entails_tassn_disjE)
                subgoal
                  apply(subgoal_tac"rp = 2 \<and> rn = 1")
                   prefer 2
                  subgoal using pre(2,3)
                  unfolding propc_def proper_def properp_def 
                  by auto
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_exI[where x="min (9 / 200 - ts T) (1 / 100 - C_upd ent (ts C))"])
                apply auto
                apply(subgoal_tac"ts T * 200 \<le> 9 \<and> C_upd ent (ts C) * 100 \<le> 1")
                 prefer 2
                subgoal using pre(4) unfolding inv_s_def C_upd_def by auto
                apply auto
                apply(simp add:waitin_assn_decomp join_assoc)
                  apply(rule entails_tassn_cancel_left)
                apply(rule combine_or_right)
                subgoal
                  apply(rule entails_tassn_trans)
                  apply(rule combine_assn_inrdy_outrdy')
                  subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) properl_p1[of p 1 2] unfolding proper_def properp_def by auto
                  subgoal using pre(4) unfolding inv_s_def 
                    apply(cases "(9 / 200 - ts T) \<le> (1 / 100 - C_upd ent (ts C))")
                    subgoal by(auto simp add:T_def C_def)
                    subgoal by(auto simp add:T_def C_def)
                    done
                  apply(rule combine_assn_right_tran)
                  unfolding T1_tr.simps
                  apply(rule entails_tassn_disjI2)
                  apply(cases "(9 / 200 - ts T) \<le> (1 / 100 - C_upd ent (ts C))")
                  subgoal apply (auto simp add:T_def C_def C_upd_def)
                    subgoal apply(rule entails_tassn_disjI1) by auto
                    subgoal apply(rule entails_tassn_disjI1) by auto
                    done
                  subgoal apply (auto simp add:T_def C_def C_upd_def)
                    subgoal apply(rule entails_tassn_disjI1) by auto
                    subgoal apply(rule entails_tassn_disjI1) by auto
                    done
                  done
                apply(rule combine_assn_ex_pre_right')
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_inrdy')
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) properl_p1[of p 1 2] unfolding proper_def properp_def by auto
                  subgoal using pre(4) unfolding inv_s_def 
                    apply(cases "(9 / 200 - ts T) \<le> (1 / 100 - C_upd ent (ts C))")
                    subgoal by(auto simp add:T_def C_def)
                    subgoal by(auto simp add:T_def C_def)
                    done
                  apply(rule combine_assn_right_tran)
                  unfolding T1_tr.simps
                  apply(rule entails_tassn_disjI2)
                  apply(cases "(9 / 200 - ts T) \<le> (1 / 100 - C_upd ent (ts C))")
                  subgoal for v apply (auto simp add:T_def C_def C_upd_def)
                    subgoal apply(rule entails_tassn_disjI2) apply(rule entails_tassn_exI[where x= v]) by auto
                    subgoal apply(rule entails_tassn_disjI2) apply(rule entails_tassn_exI[where x= v]) by auto
                    done
                  subgoal for v apply (auto simp add:T_def C_def C_upd_def)
                    subgoal apply(rule entails_tassn_disjI2) apply(rule entails_tassn_exI[where x= v]) by auto
                    subgoal apply(rule entails_tassn_disjI2) apply(rule entails_tassn_exI[where x= v]) by auto
                    done
                  done
                subgoal
                  unfolding combine1.simps
                  apply(rule entails_tassn_disjI2)
                  apply(rule entails_tassn_disjI1)
                  apply(rule ex_tran)
                  apply(subgoal_tac"rp = 2 \<and> rn = 1")
                   prefer 2
                  subgoal using pre(2,3)
                  unfolding propc_def proper_def properp_def 
                  by auto
                  apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) properl_p1[of p 1 2] unfolding proper_def properp_def by auto
                  subgoal using pre(4) unfolding inv_s_def C_def T_def by auto
                  apply(rule combine_assn_right_tran)
                  unfolding T1_tr.simps
                  apply(rule entails_tassn_disjI2)
                  apply (auto simp add:T_def C_def)
                  apply(rule entails_tassn_cancel_both) 
                  subgoal premises pre' for tt
                  proof-
                    have 1:"(min (9 / 200 - (ts CHR ''t'' + tt))
                      (1 / 100 - (C_upd ent (ts CHR ''c'') + tt))) = 
                    (min (9 / 200 - ts CHR ''t'') (1 / 100 - C_upd ent (ts CHR ''c'')) - tt)"
                      by(auto simp add: C_upd_def)
                    have 2:"(\<lambda>\<tau>. EState
           (Task RUNNING eone 2, ts
            (CHR ''t'' := ts CHR ''t'' + tt + \<tau>,
             CHR ''c'' := (C_upd ent (ts CHR ''c'') + tt) + \<tau>))) = 
                            (\<lambda>t. EState
           (Task RUNNING eone 2, ts
            (CHR ''t'' := ts CHR ''t'' + (t + tt),
             CHR ''c'' := C_upd ent (ts CHR ''c'') + (t + tt))))"
                      apply(rule ext)
                      by(auto simp add: C_upd_def)
                    show ?thesis
                      by(simp add:1 2)
                  qed
                  apply(rule entails_tassn_disjE)
                  subgoal for tt
                    apply(rule entails_tassn_disjI1)
                    subgoal premises pre'
                    proof-
                      have "ts
       (CHR ''t'' :=
         ts CHR ''t'' +
         min (9 / 200 - ts CHR ''t'') (1 / 100 - C_upd ent (ts CHR ''c'')),
       CHR ''c'' :=
         C_upd ent (ts CHR ''c'') +
         min (9 / 200 - ts CHR ''t'') (1 / 100 - C_upd ent (ts CHR ''c'')))
                    =     ts
      (CHR ''t'' :=
         ts CHR ''t'' + tt +
         min (9 / 200 - (ts CHR ''t'' + tt)) (1 / 100 - (C_upd ent (ts CHR ''c'') + tt)),
       CHR ''c'' :=
         C_upd ent (ts CHR ''c'') + tt +
         min (9 / 200 - (ts CHR ''t'' + tt))
          (1 / 100 - (C_upd ent (ts CHR ''c'') + tt))) "
                        apply(rule ext)
                        by auto
                      then show ?thesis by auto
                    qed
                    done
                  apply(rule entails_tassn_disjI2)
                  apply(rule ex_tran)
                  subgoal premises pre' for tt v
                  proof-
                    have "ts (CHR ''t'' :=
         ts CHR ''t'' +
         min (9 / 200 - ts CHR ''t'') (1 / 100 - C_upd ent (ts CHR ''c'')),
       CHR ''c'' :=
         C_upd ent (ts CHR ''c'') +
         min (9 / 200 - ts CHR ''t'') (1 / 100 - C_upd ent (ts CHR ''c''))) = 
                          ts (CHR ''t'' :=
         ts CHR ''t'' + tt +
         min (9 / 200 - (ts CHR ''t'' + tt)) (1 / 100 - (C_upd ent (ts CHR ''c'') + tt)),
       CHR ''c'' :=
         C_upd ent (ts CHR ''c'') + tt +
         min (9 / 200 - (ts CHR ''t'' + tt))
          (1 / 100 - (C_upd ent (ts CHR ''c'') + tt)))"
                      apply(rule ext)
                      apply auto
                      done
                    then show ?thesis
                      by(auto simp add: F_def)
                  qed
                  done
                done
              done
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule combine_assn_pure_pre_left')
              apply(rule combine_or_right)
              subgoal for v
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_waitin')
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                apply(rule ex_tran)
                apply(rule entails_tassn_exI[where x=v])
                apply auto
                apply(rule entails_tassn_cancel_left)
                by(auto simp add:entails_tassn_def true_assn_def)
              subgoal for v
                unfolding combine1.simps
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI2)
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_wait')
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply(rule entails_tassn_disjE)
                subgoal
                  apply(rule entails_tassn_exI[where x="min (45 / 10 ^ 3 - ts T) (1 / 10\<^sup>2 - C_upd ent (ts C))"])
                  apply(rule entails_tassn_exI[where x=v])
                  apply auto
                  apply(subgoal_tac"ts T * 200 \<le> 9 \<and> C_upd ent (ts C) * 100 \<le> 1")
                   prefer 2
                  subgoal using pre(4) unfolding inv_s_def
                    apply auto
                    apply(cases ent)
                    by(auto simp add:C_upd_def)
                  apply auto
                  apply(simp add: waitin_assn_decomp join_assoc)
                  apply(rule entails_tassn_cancel_left)
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_inrdy_outrdy')
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                    by(auto simp add:entails_tassn_def true_assn_def)
                  subgoal
                    apply(rule combine_assn_ex_pre_right')
                    apply(rule entails_tassn_trans)
                    apply(rule combine_assn_inrdy_inrdy')
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                    by(auto simp add:entails_tassn_def true_assn_def)
                  done
                subgoal
                  apply(rule ex_tran)
                  apply(rule entails_tassn_exI[where x=v])
                  apply auto
                  apply(rule entails_tassn_cancel_left)
                  by(auto simp add:entails_tassn_def true_assn_def)
                done
              done
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule combine_or_right)
              subgoal for v
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                apply(rule combine_assn_inrdy_waitin)
                by auto
              subgoal for v
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_wait)
                subgoal by auto
                unfolding combine1.simps
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_cancel_both)
                subgoal by auto
                apply(rule combine_or_right)
                subgoal
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_inrdy_outrdy)
                  subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  apply(cases "length p > 0")
                  subgoal
                    apply(subgoal_tac"get_max p =(1,2)")
                     prefer 2
                    subgoal using pre(3) properl_p5[of p]
                      unfolding propc_def proper_def properp_def
                      by (metis estate.sel(1) insert_iff less_minus_one_simps(3) prod.exhaust_sel singletonD)
                    apply auto
                    apply(rule combine_or_left)
                    subgoal
                      apply(rule entails_tassn_disjI1)
                      apply(cases nt')
                      subgoal apply auto
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_out0_emp')
                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                        apply(rule entails_tassn_cancel_left)
                        apply(rule entails_tassn_trans)
                         prefer 2
                         apply(rule pre(1))
                        subgoal by auto
                        subgoal using pre(2) unfolding propc_def by auto
                        subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                        subgoal using pre(4) unfolding inv_s_def C_def T_def 
                          apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                          by auto
                        by auto
                      subgoal for nt''
                        apply(simp only:T1_tr.simps)
                        apply(cases "(9 / 200 -
        (ts(T := ts T + min (9 / 200 - ts T) (1 / 100 - C_upd ent (ts C)),
            C := C_upd ent (ts C) + min (9 / 200 - ts T) (1 / 100 - C_upd ent (ts C))))
         T) > 0")
                        subgoal
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_out0_wait')
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule entails_tassn_trans)
                           prefer 2
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                          subgoal using pre(4) unfolding inv_s_def C_def T_def 
                          apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                            by auto
                          by auto
                        apply (auto simp add:T_def C_def)
                        apply(cases nt'')
                        subgoal
                          apply simp
                          apply(rule entails_tassn_trans)
                           apply(rule combine_assn_out0_emp')
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule entails_tassn_trans)
                           prefer 2
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                          subgoal using pre(4) unfolding inv_s_def C_def T_def 
                            apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                            by auto
                          apply(rule combine_assn_right_tran)
                          unfolding T1_tr.simps
                          by (auto simp add:C_def T_def)
                        subgoal for nt'''
                          apply(simp only:T1_tr.simps)
                          apply(rule combine_or_right)
                          subgoal
                            apply(rule combine_assn_ex_pre_right')+
                            apply(rule combine_assn_pure_pre_right')
                            apply(rule entails_tassn_trans)
                             apply(rule combine_assn_out0_out2)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule entails_tassn_trans)
                           prefer 2
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                          subgoal using pre(4) unfolding inv_s_def C_def T_def 
                            apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                            by auto
                          apply(rule combine_assn_right_tran)
                          unfolding T1_tr.simps
                          apply (auto simp add:C_def T_def)
                          apply(rule entails_tassn_disjI1)
                          subgoal for vv tt
                            apply(rule entails_tassn_exI[where x=vv])
                            apply(rule entails_tassn_exI[where x=tt])
                            by auto
                          done
                        subgoal
                          apply(rule entails_tassn_trans)
                             apply(rule combine_assn_out0_out2)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                          apply(rule entails_tassn_cancel_left)
                          apply(rule entails_tassn_trans)
                           prefer 2
                           apply(rule pre(1))
                          subgoal by auto
                          subgoal using pre(2) unfolding propc_def by auto
                          subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                          subgoal using pre(4) unfolding inv_s_def C_def T_def 
                            apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                            by auto
                          apply(rule combine_assn_right_tran)
                          unfolding T1_tr.simps
                          apply (auto simp add:C_def T_def)
                          apply(rule entails_tassn_disjI2)
                          by auto
                        done
                      done
                    done
                  subgoal
                    apply(rule entails_tassn_disjI2)
                    apply(cases nt')
                    subgoal
                      apply simp
                      apply(simp add: combine_assn_waitp_emp)
                      done
                    subgoal for nt''
                      apply (simp only:T1_tr.simps)
                      apply(cases "(9 / 200 -
        (ts(T := ts T + min (9 / 200 - ts T) (1 / 100 - C_upd ent (ts C)),
            C := C_upd ent (ts C) + min (9 / 200 - ts T) (1 / 100 - C_upd ent (ts C))))
         T) > 0")
                      subgoal
                        apply (simp add:T_def C_def)
                        apply(rule entails_tassn_trans)
                         apply(rule combine_assn_waitp_wait)
                        subgoal by auto
                        apply(rule entails_tassn_disjI1)
                        by auto
                      subgoal
                        apply (simp add:T_def C_def)
                        apply(cases nt'')
                        subgoal
                          apply simp
                          apply(simp add: combine_assn_waitp_emp)
                          done
                        subgoal for nt'''
                          apply(simp only:T1_tr.simps)
                          apply(rule combine_or_right)
                          subgoal
                            apply(rule combine_assn_ex_pre_right')+
                            apply(rule combine_assn_pure_pre_right')
                            apply(rule entails_tassn_trans)
                             apply(rule combine_assn_waitp_out)
                            subgoal by auto
                            apply(rule entails_tassn_disjI2)
                            by auto
                          subgoal
                            apply(rule entails_tassn_trans)
                            apply(rule combine_assn_waitp_out)
                            subgoal by auto
                            apply(rule entails_tassn_disjI2)
                            by auto
                          done
                        done
                      done
                    done
                  done
                subgoal
                  apply auto
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                  subgoal using pre(4) unfolding inv_s_def C_def T_def 
                    apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                    by auto
                  by auto
                done
              subgoal
                apply(rule combine_assn_ex_pre_right')
                apply(rule combine_assn_inrdy_inrdy)
                by auto
              done
            done
          apply(rule combine_or_left)
          subgoal
            unfolding combine1.simps
            apply(rule entails_tassn_disjI2)
            apply(rule entails_tassn_disjI2)
            apply(rule entails_tassn_disjI2)
            apply(rule entails_tassn_disjI1)
            apply(rule combine_assn_ex_pre_left')
            apply(rule combine_or_right)
            subgoal for v
              apply(rule combine_assn_ex_pre_right')+
              apply(rule combine_assn_pure_pre_right')
              apply(rule entails_tassn_trans)
               apply(rule combine_assn_inrdy_waitin')
              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
              apply(rule ex_tran)
              apply(rule entails_tassn_exI[where x= v])
              apply auto
                subgoal
                  apply(rule entails_tassn_cancel_left) 
                  by(auto simp add:true_assn_def entails_tassn_def)
                subgoal
                  apply(rule entails_tassn_cancel_left) 
                  by(auto simp add:true_assn_def entails_tassn_def)
                subgoal
                  apply(rule entails_tassn_cancel_left) 
                  by(auto simp add:true_assn_def entails_tassn_def)
                done
              subgoal for v
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_wait')
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply(rule entails_tassn_disjE)
                subgoal
                  apply(rule entails_tassn_exI[where x= "(min (45 / 10 ^ 3 - ts T) (1 / 10\<^sup>2 - C_upd ent (ts C)))"])
                  apply(rule entails_tassn_exI[where x= v])
                  apply(rule entails_tassn_conj)
                  subgoal
                    using pre(4)
                    unfolding inv_s_def entails_tassn_def pure_assn_def C_upd_def
                    apply(cases ent)
                    by auto
                  apply(simp only:waitin_assn_decomp join_assoc)
                  apply(rule entails_tassn_cancel_both)
                  subgoal by auto
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_inrdy_outrdy')
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                    by(auto simp add:entails_tassn_def true_assn_def)
                  apply(rule combine_assn_ex_pre_right')
                  apply(rule entails_tassn_trans)
                   apply(rule combine_assn_inrdy_inrdy')
                  subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                  by(auto simp add:entails_tassn_def true_assn_def)
                subgoal
                  apply(rule ex_tran)
                  apply(rule entails_tassn_exI[where x=v])
                  apply(rule entails_tassn_conj)
                  subgoal by auto
                  apply(simp only:pure_assn_entails)
                  apply(rule impI)
                  apply(rule entails_tassn_cancel_both) 
                  subgoal by auto
                  by auto
                done
              done
            apply(rule combine_or_left)
            subgoal
              apply(rule combine_assn_ex_pre_left')
              apply(rule combine_or_right)
              subgoal for v
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                apply(rule combine_assn_inrdy_waitin)
                subgoal by auto
                done
              subgoal for v
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_wait)
                subgoal by auto
                unfolding combine1.simps
                apply(rule entails_tassn_disjI1)
                apply(rule entails_tassn_cancel_both)
                subgoal by auto
                apply(rule combine_or_right)
                subgoal
                  apply(rule combine_assn_inrdy_outrdy'')
                  subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                  done
                subgoal
                  apply(rule combine_assn_ex_pre_right')
                  apply(rule combine_assn_inrdy_inrdy)
                  by auto
                done
              done
            subgoal
              unfolding combine1.simps
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule entails_tassn_disjI2)
              apply(rule combine_assn_ex_pre_left')
              apply(rule combine_or_right)
              subgoal for v
                apply(rule combine_assn_ex_pre_right')+
                apply(rule combine_assn_pure_pre_right')
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_waitin')
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply(rule ex_tran)
                apply(rule entails_tassn_exI[where x=v])
                apply auto
                apply(rule entails_tassn_cancel_left)
                apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                  subgoal using pre(4) unfolding inv_s_def C_def T_def 
                    apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                    by auto
                  apply(subgoal_tac"rp = 2 \<and> rn = 1")
                   prefer 2
                  subgoal using pre(2,3)
                  unfolding propc_def proper_def properp_def 
                  by auto
                  apply(simp add:T_def C_def)
                apply(rule combine_assn_right_tran)
                apply(rule entails_tassn_disjI1)
                subgoal for v tt tta
                  apply(rule entails_tassn_exI[where x= v])
                  apply(rule entails_tassn_exI[where x= "tt-tta"])
                  apply auto
                  subgoal premises pre'
                  proof-
                    have "(\<lambda>t. EState
           (Task RUNNING eone 2, ts
            (CHR ''t'' := ts CHR ''t'' + tta + t,
             CHR ''c'' := C_upd ent (ts CHR ''c'') + tta + t))) = 
                          (\<lambda>t. EState
           (Task RUNNING eone 2, ts
            (CHR ''t'' := ts CHR ''t'' + (t + tta),
             CHR ''c'' := C_upd ent (ts CHR ''c'') + (t + tta))))"
                      apply (rule ext)
                      by auto
                    then show ?thesis
                      by auto
                  qed
                  done
                done
              subgoal for v
                apply(rule entails_tassn_trans)
                 apply(rule combine_assn_inrdy_wait')
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply auto
                apply(rule entails_tassn_disjE)
                subgoal
                  apply(rule entails_tassn_exI[where x="(min (9 / 200 - ts T) (1 / 100 - C_upd ent (ts C)))"])
                  apply(rule entails_tassn_exI[where x=v])
                  apply auto
                  apply(subgoal_tac"ts T * 200 \<le> 9 \<and> C_upd ent (ts C) * 100 \<le> 1")
                   prefer 2
                  subgoal using pre(4) unfolding inv_s_def C_upd_def
                    apply(cases ent)
                    by auto
                  apply(simp add:waitin_assn_decomp join_assoc)
                  apply(rule entails_tassn_cancel_left)
                  apply(rule combine_or_right)
                  subgoal
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_inrdy_outrdy')
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                    apply(rule entails_tassn_trans)
                     prefer 2
                     apply(rule pre(1))
                    subgoal by auto
                    subgoal using pre(2) unfolding propc_def by auto
                    subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                    subgoal using pre(4) unfolding inv_s_def C_def T_def 
                      apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                      by auto
                    apply(subgoal_tac"rp = 2 \<and> rn = 1")
                     prefer 2
                    subgoal using pre(2,3)
                      unfolding propc_def proper_def properp_def 
                      by auto
                    apply(simp add:T_def C_def)
                    apply(rule combine_assn_right_tran)
                    apply(rule entails_tassn_disjI2)
                    apply(rule entails_tassn_disjI1)
                    apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                    by auto
                  subgoal
                    apply(rule combine_assn_ex_pre_right')
                    apply(rule entails_tassn_trans)
                     apply(rule combine_assn_inrdy_inrdy')
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                    apply(rule entails_tassn_cancel_left)
                    apply(rule entails_tassn_trans)
                     prefer 2
                     apply(rule pre(1))
                    subgoal by auto
                    subgoal using pre(2) unfolding propc_def by auto
                    subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                    subgoal using pre(4) unfolding inv_s_def C_def T_def 
                      apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                      by auto
                    apply(subgoal_tac"rp = 2 \<and> rn = 1")
                     prefer 2
                    subgoal using pre(2,3)
                      unfolding propc_def proper_def properp_def 
                      by auto
                    apply(simp add:T_def C_def)
                    apply(rule combine_assn_right_tran)
                    apply(rule entails_tassn_disjI2)
                    apply(rule entails_tassn_disjI2)
                    subgoal for vv
                      apply(rule entails_tassn_exI[where x=vv])
                      apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                      by auto
                    done
                  done
                subgoal
                  apply(rule ex_tran)
                  apply(rule entails_tassn_exI[where x=v])
                  apply auto
                  apply(rule entails_tassn_cancel_left)
                  apply(rule entails_tassn_trans)
                   prefer 2
                   apply(rule pre(1))
                  subgoal by auto
                  subgoal using pre(2) unfolding propc_def by auto
                  subgoal using pre(3) properl_p4[of p 2] unfolding proper_def properp_def by auto
                    subgoal using pre(4) unfolding inv_s_def C_def T_def 
                      apply(cases "(9 / 200 - ts CHR ''t'') \<le> (1 / 100 - C_upd ent (ts CHR ''c''))")
                      by auto
                    apply(subgoal_tac"rp = 2 \<and> rn = 1")
                     prefer 2
                    subgoal using pre(2,3)
                      unfolding propc_def proper_def properp_def 
                      by auto
                    apply(simp add:T_def C_def)
                    apply(rule combine_assn_right_tran)
                    apply(rule entails_tassn_disjI2)
                    apply auto
                    apply(rule entails_tassn_cancel_both)
                    subgoal premises pre' for tt
                    proof-
                      have 1:"(\<lambda>\<tau>. EState
           (Task RUNNING eone 2, ts
            (CHR ''t'' := ts CHR ''t'' + tt + \<tau>,
             CHR ''c'' := C_upd ent (ts CHR ''c'') + tt + \<tau>))) =
                            (\<lambda>t. EState
           (Task RUNNING eone 2, ts
            (CHR ''t'' := ts CHR ''t'' + (t + tt),
             CHR ''c'' := C_upd ent (ts CHR ''c'') + (t + tt))))"
                        apply (rule ext)
                        by auto
                      have 2:"(min (9 / 200 - (ts CHR ''t'' + tt))
             (1 / 100 - (C_upd ent (ts CHR ''c'') + tt))) =
              (min (9 / 200 - ts CHR ''t'') (1 / 100 - C_upd ent (ts CHR ''c'')) - tt)"
                        by auto
                      show ?thesis
                        using 1 2 
                        by auto
                    qed
                    subgoal premises pre' for tt
                    proof-
                      have "ts
             (CHR ''t'' :=
                ts CHR ''t'' + tt +
                min (9 / 200 - (ts CHR ''t'' + tt))
                 (1 / 100 - (C_upd ent (ts CHR ''c'') + tt)),
              CHR ''c'' :=
                C_upd ent (ts CHR ''c'') + tt +
                min (9 / 200 - (ts CHR ''t'' + tt))
                 (1 / 100 - (C_upd ent (ts CHR ''c'') + tt))) = ts
       (CHR ''t'' :=
          ts CHR ''t'' +
          min (9 / 200 - ts CHR ''t'') (1 / 100 - C_upd ent (ts CHR ''c'')),
        CHR ''c'' :=
          C_upd ent (ts CHR ''c'') +
          min (9 / 200 - ts CHR ''t'') (1 / 100 - C_upd ent (ts CHR ''c'')))"
                        apply(rule ext)
                        by auto
                      then show ?thesis
                        by simp
                    qed
                    done
                  done
                done
              done
            done
          done
        done
    qed





end