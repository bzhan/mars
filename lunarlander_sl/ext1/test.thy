theory test
  imports AssumeGuarantee
begin


inductive out_tassn :: "cname \<Rightarrow> real \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> (out_tassn ch v P) (OutBlock ch v # tr)"

inductive in_tassn :: "cname \<Rightarrow> real \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn " where
  "P tr \<Longrightarrow> (in_tassn ch v P) (InBlock ch v # tr)"

inductive in_assm_tassn :: "cname \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> 'a tassn)\<Rightarrow> 'a tassn " where
  "P v tr \<Longrightarrow> v\<in>V \<Longrightarrow> (in_assm_tassn ch V P) (InBlock ch v # tr)"
| "v \<notin> V \<Longrightarrow> (in_assm_tassn ch V P) (InBlock ch v # tr)"

inductive wait_tassn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> d \<le> 0 \<Longrightarrow> (wait_tassn d p rdy P) tr"
| "P tr \<Longrightarrow> d > 0 \<Longrightarrow> (wait_tassn d p rdy P) (WaitBlk d p rdy # tr)"

inductive wait_guar_tassn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> (real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "P 0 tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (wait_guar_tassn S p rdy P) tr"
| "P d tr \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (wait_guar_tassn S p rdy P) (WaitBlk d p rdy # tr)"


inductive waitin_assm_tassn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "v \<in> V \<Longrightarrow> 0 \<in> S \<Longrightarrow> (P 0 v) tr \<Longrightarrow> (waitin_assm_tassn S p rdy ch V P) (InBlock ch v # tr)"
| "v \<in> V \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (P d v) tr \<Longrightarrow> (waitin_assm_tassn S p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch v # tr)"
| "0 \<notin> S \<or> w \<notin> V \<Longrightarrow> (waitin_assm_tassn S p rdy ch V P) (InBlock ch w # tr)"
| "d \<notin> S \<or> w \<notin> V \<Longrightarrow> d > 0 \<Longrightarrow> (waitin_assm_tassn S p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch w # tr)"

lemma g:"waitin_assm_tassn S p rdy ch V P = ((wait_guar_tassn S p rdy (\<lambda> t. in_assm_tassn ch V (\<lambda> v. P t v))) \<or>\<^sub>t (wait_guar_tassn ({0..} - S) p rdy (\<lambda> t. in_assm_tassn ch UNIV (\<lambda> v. true\<^sub>A))))"
  apply(rule ext)
  apply auto
  subgoal for tr
    apply(cases rule:waitin_assm_tassn.cases[of S p rdy ch V P tr])
        apply auto
    subgoal for v tr'
      unfolding disj_assn_def
      apply(rule disjI1)
      apply(rule wait_guar_tassn.intros(1))
       apply(rule in_assm_tassn.intros(1))
      by auto
    subgoal for v d tr'
      unfolding disj_assn_def
      apply(rule disjI1)
      apply(rule wait_guar_tassn.intros(2))
       apply(rule in_assm_tassn.intros(1))
      by auto
    subgoal for v tr'
      unfolding disj_assn_def
      apply(rule disjI2)
      apply(rule wait_guar_tassn.intros(1))
       apply(rule in_assm_tassn.intros(1))
      by (auto simp add:true_assn_def)
    subgoal for v tr'
      unfolding disj_assn_def
      apply(cases "0\<in>S")
      subgoal
      apply(rule disjI1)
      apply(rule wait_guar_tassn.intros(1))
       apply(rule in_assm_tassn.intros(2))
        by auto    
      subgoal
      apply(rule disjI2)
      apply(rule wait_guar_tassn.intros(1))
       apply(rule in_assm_tassn.intros(1))
        by (auto simp add:true_assn_def)
      done
    subgoal for d v tr'
      unfolding disj_assn_def
      apply(rule disjI2)
      apply(rule wait_guar_tassn.intros(2))
       apply(rule in_assm_tassn.intros(1))
      by (auto simp add:true_assn_def)
    subgoal for d v tr'
      unfolding disj_assn_def
      apply(cases "d\<in>S")
      subgoal
      apply(rule disjI1)
      apply(rule wait_guar_tassn.intros(2))
       apply(rule in_assm_tassn.intros(2))
        by (auto simp add:true_assn_def)    
      subgoal
      apply(rule disjI2)
      apply(rule wait_guar_tassn.intros(2))
       apply(rule in_assm_tassn.intros(1))
        by (auto simp add:true_assn_def)
      done
    done
  subgoal for tr
    unfolding disj_assn_def
    apply(erule disjE)
    subgoal
      apply(cases rule: wait_guar_tassn.cases[of S p rdy "(\<lambda>t. in_assm_tassn ch V (P t))" tr])
        apply simp
      subgoal
        apply(cases rule:in_assm_tassn.cases[of ch V "(P 0)" tr])
          apply auto
        subgoal
          apply(rule waitin_assm_tassn.intros(1))
          by auto
        subgoal
          apply(rule waitin_assm_tassn.intros(3))
          by auto
        done
      subgoal for d tr'
        apply(cases rule:in_assm_tassn.cases[of ch V "(P d)" tr'])
          apply auto
        subgoal
          apply(rule waitin_assm_tassn.intros(2))
          by auto
        subgoal
          apply(rule waitin_assm_tassn.intros(4))
          by auto
        done
      done
    apply(cases rule: wait_guar_tassn.cases[of "({0..} - S)" p rdy "(\<lambda>t. in_assm_tassn ch UNIV (\<lambda>v. true\<^sub>A))" tr])
        apply simp
      subgoal
        apply(cases rule:in_assm_tassn.cases[of ch UNIV "(\<lambda>v. true\<^sub>A)" tr])
        apply auto
        apply(rule waitin_assm_tassn.intros(3))
        by auto
      subgoal for d tr'
        apply(cases rule:in_assm_tassn.cases[of ch UNIV "(\<lambda>v. true\<^sub>A)" tr'])
        apply auto
        apply(rule waitin_assm_tassn.intros(4))
        by auto
      done
    done





end