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
  "P tr \<Longrightarrow> d = 0 \<Longrightarrow> (wait_tassn d p rdy P) tr"
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

inductive waitout_assm_tassn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "P 0 tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (waitout_assm_tassn S p rdy ch f P) (OutBlock ch (f 0) # tr)"
| "P d tr \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (waitout_assm_tassn S p rdy ch f P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # OutBlock ch (f d) # tr)"
| "0 \<notin> S \<Longrightarrow> (waitout_assm_tassn S p rdy ch f P) (OutBlock ch (f 0) # tr)"
| "d \<notin> S \<Longrightarrow> d > 0 \<Longrightarrow> (waitout_assm_tassn S p rdy ch f P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # OutBlock ch (f d) # tr)"

inductive waitin'_assm_tassn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "v \<in> V \<Longrightarrow> 0 \<le> T \<Longrightarrow> (P 0 v) tr \<Longrightarrow> (waitin'_assm_tassn T p rdy ch V P) (InBlock ch v # tr)"
| "v \<in> V \<Longrightarrow> d \<le> T \<Longrightarrow> d > 0 \<Longrightarrow> (P d v) tr \<Longrightarrow> (waitin'_assm_tassn T p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch v # tr)"
| "w \<notin> V \<Longrightarrow> T \<ge> 0\<Longrightarrow> (waitin'_assm_tassn T p rdy ch V P) (InBlock ch w # tr)"
| "w \<notin> V \<Longrightarrow> d > 0 \<Longrightarrow> d \<le> T \<Longrightarrow> (waitin'_assm_tassn T p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch w # tr)"
| "d > T \<Longrightarrow> T \<ge> 0 \<Longrightarrow> (waitin'_assm_tassn T p rdy ch f P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # tr)"

inductive waitout'_assm_tassn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "P 0 tr \<Longrightarrow> 0 \<le> T \<Longrightarrow> (waitout'_assm_tassn T p rdy ch f P) (OutBlock ch (f 0) # tr)"
| "P d tr \<Longrightarrow> d \<le> T \<Longrightarrow> d > 0 \<Longrightarrow> (waitout'_assm_tassn T p rdy ch f P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # OutBlock ch (f d) # tr)"
| "d > T \<Longrightarrow> T \<ge> 0 \<Longrightarrow> (waitout'_assm_tassn T p rdy ch f P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # tr)"

lemma conj_join_pure_true [simp]:
  "(\<up>True \<and>\<^sub>t P) = P"
  by (auto simp add: pure_assn_def conj_assn_def join_assn_def)


lemma g1:"waitin_assm_tassn S p rdy ch V P = 
      ((wait_guar_tassn S p rdy (\<lambda> t. in_assm_tassn ch V (\<lambda> v. P t v))) 
    \<or>\<^sub>t (wait_guar_tassn ({0..} - S) p rdy (\<lambda> t. in_assm_tassn ch UNIV (\<lambda> v. true\<^sub>A))))"
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

lemma g2:"waitout_assm_tassn S p rdy ch f P = 
      ((wait_guar_tassn S p rdy (\<lambda> t. out_tassn ch (f t) (P t))) 
    \<or>\<^sub>t (wait_guar_tassn ({0..} - S) p rdy (\<lambda> t. out_tassn ch (f t) (true\<^sub>A))))"
  apply(rule ext)
  subgoal for tr
    apply auto
    subgoal
      apply(cases rule:waitout_assm_tassn.cases[of S p rdy ch f P tr])
          apply auto
      subgoal for tr'
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule wait_guar_tassn.intros(1))
         apply auto
        apply(rule out_tassn.intros)
        by auto
      subgoal for d tr'
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule wait_guar_tassn.intros(2))
         apply auto
        apply(rule out_tassn.intros)
        by auto
      subgoal for tr'
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule wait_guar_tassn.intros(1))
         apply auto
        apply(rule out_tassn.intros)
        by (auto simp add:true_assn_def)
      subgoal for d tr'
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule wait_guar_tassn.intros(2))
         apply auto
        apply(rule out_tassn.intros)
        by (auto simp add:true_assn_def)
      done
    unfolding disj_assn_def
    apply(erule disjE)
    subgoal
      apply(cases rule: wait_guar_tassn.cases[of S p rdy "(\<lambda>t. out_tassn ch (f t) (P t))" tr])
        apply auto
      subgoal
        apply(cases rule: out_tassn.cases[of ch "(f 0)" "(P 0)" tr])
         apply auto
        apply(rule waitout_assm_tassn.intros(1))
        by auto
      subgoal for d tr'
        apply(cases rule: out_tassn.cases[of ch "(f d)" "(P d)" tr'])
         apply auto
        apply(rule waitout_assm_tassn.intros(2))
        by auto
      done
    subgoal
      apply(cases rule: wait_guar_tassn.cases[of "({0..} - S)" p rdy "(\<lambda>t. out_tassn ch (f t) true\<^sub>A)" tr])
        apply auto
      subgoal
        apply(cases rule:out_tassn.cases[of ch "(f 0)" true\<^sub>A tr])
        apply auto
        apply(rule waitout_assm_tassn.intros(3))
        by auto
      subgoal for d tr'
        apply(cases rule:out_tassn.cases[of  ch "(f d)" true\<^sub>A tr'])
         apply auto
        apply(rule waitout_assm_tassn.intros(4))
        by auto
      done
      done
    done

lemma g3: "wait_guar_tassn S p rdy P = wait_guar_tassn (S \<inter> {0..}) p rdy P"
  unfolding entails_tassn_def false_assn_def
  apply (rule ext)
  apply auto
  subgoal for tr
    apply(cases rule: wait_guar_tassn.cases[of S p rdy P tr])
      apply auto
    subgoal
      apply(rule wait_guar_tassn.intros(1))
      by auto
    subgoal
      apply(rule wait_guar_tassn.intros(2))
      by auto
    done
  subgoal for tr
    apply(cases rule: wait_guar_tassn.cases[of "(S \<inter> {0..})" p rdy P tr])
      apply auto
    subgoal
      apply(rule wait_guar_tassn.intros(1))
      by auto
    subgoal
      apply(rule wait_guar_tassn.intros(2))
      by auto
    done
  done

lemma g4: "S = {} \<Longrightarrow> wait_guar_tassn S p rdy P = false\<^sub>A"
  unfolding entails_tassn_def false_assn_def
  apply (rule ext)
  apply auto
  subgoal for tr
    apply(cases rule: wait_guar_tassn.cases[of S p rdy P tr])
    by auto
  done

definition set_lesseq :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"set_lesseq S1 S2 = {x. x \<in> S1 \<inter> {0..} \<and> (\<exists> y \<in> S2 \<inter> {0..}. (x \<le> y))}"


definition set_minus :: "real set \<Rightarrow> real \<Rightarrow> real set" where
"set_minus S r = {x. x + r \<in> S \<inter> {0..}}"

lemma combine_wait_guar_wait_guar1:
"compat_rdy rdy1 rdy2 \<Longrightarrow>
combine_assn chs (wait_guar_tassn S1 p1 rdy1 P1) (wait_guar_tassn S2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
   wait_guar_tassn (set_lesseq S1 S2) (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) 
   (\<lambda> d. combine_assn chs (P1 d) (wait_guar_tassn (set_minus S2 d) (\<lambda> t. p2(t+d)) rdy2 (\<lambda> t. P2(t+d)))) 
\<or>\<^sub>t wait_guar_tassn (set_lesseq S2 S1) (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)
   (\<lambda> d. combine_assn chs (wait_guar_tassn (set_minus S1 d) (\<lambda> t. p1(t+d)) rdy1 (\<lambda> t. P1(t+d))) (P2 d))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_guar_tassn.cases[of S1 p1 rdy1 P1 tr1])
      apply auto
    subgoal
      apply(cases rule: wait_guar_tassn.cases[of S2 p2 rdy2 P2 tr2])
        apply auto
      subgoal
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule wait_guar_tassn.intros(1))
        unfolding set_lesseq_def
         apply auto
        apply(rule exI[where x="tr1"])
        apply auto
        apply(rule exI[where x="tr2"])
        apply auto
        apply(rule wait_guar_tassn.intros(1))
        unfolding set_minus_def
        by auto
      subgoal for d2 tr2'
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule wait_guar_tassn.intros(1))
        unfolding set_lesseq_def
         apply auto
        apply(rule exI[where x="tr1"])
        apply auto
        apply(rule exI[where x="tr2"])
        apply auto
        apply(rule wait_guar_tassn.intros(2))
        unfolding set_minus_def
        by auto
      done
    subgoal for d1 tr1'
      apply(cases rule: wait_guar_tassn.cases[of S2 p2 rdy2 P2 tr2])
        apply auto
      subgoal
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule wait_guar_tassn.intros(1))
        unfolding set_lesseq_def
         apply auto
        apply(rule exI[where x="tr1"])
        apply auto
        apply(rule wait_guar_tassn.intros(2))
        unfolding set_minus_def
        by auto
      subgoal for d2 tr2'
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(rule wait_guar_tassn.intros(2))
          unfolding set_lesseq_def
            apply auto
           apply(rule exI[where x= "tr1'"])
           apply auto
           apply(rule exI[where x="(WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2')"])
           apply auto
           apply(rule wait_guar_tassn.intros(2))
             apply auto
          unfolding set_minus_def
           apply auto
          by (metis Int_iff atLeast_iff inf.absorb4 inf_sup_ord(1) less_add_same_cancel1 pos_add_strict)
          apply(cases "d1=d2")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE2)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(rule wait_guar_tassn.intros(2))
          unfolding set_lesseq_def
            apply auto
           apply(rule exI[where x= "tr1'"])
           apply auto
           apply(rule exI[where x="tr2'"])
           apply auto
           apply(rule wait_guar_tassn.intros(1))
             apply auto
          unfolding set_minus_def
          by auto
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule wait_guar_tassn.intros(2))
          unfolding set_lesseq_def
            apply auto
           apply(rule exI[where x= "(WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1')"])
           apply auto
           apply(rule wait_guar_tassn.intros(2))
             apply auto
          unfolding set_minus_def
           apply auto
          by (metis Int_iff atLeast_iff inf.absorb4 inf_sup_ord(1) less_add_same_cancel1 pos_add_strict)
        by auto
      done
    done
  done


lemma combine_wait_guar_wait_guar1_int1:
"compat_rdy rdy1 rdy2 \<Longrightarrow>
combine_assn chs (wait_guar_tassn {0..d1} p1 rdy1 P1) (wait_guar_tassn {0..d2} p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
   wait_guar_tassn {0.. (min d1 d2)} (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) 
   (\<lambda> d. combine_assn chs (P1 d) (wait_guar_tassn {0..d2-d} (\<lambda> t. p2(t+d)) rdy2 (\<lambda> t. P2(t+d)))) 
\<or>\<^sub>t wait_guar_tassn {0.. (min d1 d2)} (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)
   (\<lambda> d. combine_assn chs (wait_guar_tassn {0..d1-d} (\<lambda> t. p1(t+d)) rdy1 (\<lambda> t. P1(t+d))) (P2 d))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_guar_tassn.cases[of "{0..d1}" p1 rdy1 P1 tr1])
      apply auto
    subgoal
      apply(cases rule: wait_guar_tassn.cases[of "{0..d2}" p2 rdy2 P2 tr2])
        apply auto
      subgoal
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule wait_guar_tassn.intros(1))
        by auto
      subgoal for d2 tr2'
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule wait_guar_tassn.intros(1))
        by auto
      done
    subgoal for d1 tr1'
      apply(cases rule: wait_guar_tassn.cases[of "{0..d2}" p2 rdy2 P2 tr2])
        apply auto
      subgoal
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule wait_guar_tassn.intros(1))
        by auto
      subgoal for d2 tr2'
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(rule wait_guar_tassn.intros(2))
          unfolding set_lesseq_def
            apply auto
           apply(rule exI[where x= "tr1'"])
           apply auto
           apply(rule exI[where x="(WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2')"])
           apply auto
           apply(rule wait_guar_tassn.intros(2))
          by auto
        apply(cases "d1=d2")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE2)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(rule wait_guar_tassn.intros(2))
          unfolding set_lesseq_def
            apply auto
           apply(rule exI[where x= "tr1'"])
           apply auto
           apply(rule exI[where x="tr2'"])
           apply auto
           apply(rule wait_guar_tassn.intros(1))
          by auto
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule wait_guar_tassn.intros(2))
          unfolding set_lesseq_def
            apply auto
           apply(rule exI[where x= "(WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1')"])
           apply auto
           apply(rule wait_guar_tassn.intros(2))
          by auto
        by auto
      done
    done
  done




lemma combine_wait_guar_wait_guar2:
"\<not> compat_rdy rdy1 rdy2 \<Longrightarrow>
combine_assn chs (wait_guar_tassn S1 p1 rdy1 P1) (wait_guar_tassn S2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
   (\<up>(0\<in>S1) \<and>\<^sub>t combine_assn chs (P1 0) (wait_guar_tassn S2 p2 rdy2 P2))
\<or>\<^sub>t (\<up>(0\<in>S2) \<and>\<^sub>t combine_assn chs (wait_guar_tassn S1 p1 rdy1 P1) (P2 0))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_guar_tassn.cases[of S1 p1 rdy1 P1 tr1])
      apply auto
    subgoal
      apply(cases rule: wait_guar_tassn.cases[of S2 p2 rdy2 P2 tr2])
        apply auto
      subgoal
        unfolding disj_assn_def
        apply(rule disjI1)
        by auto
      subgoal for d tr2'
        unfolding disj_assn_def
        apply(rule disjI1)
        by auto
      done
    subgoal for d tr1'
      apply(cases rule: wait_guar_tassn.cases[of S2 p2 rdy2 P2 tr2])
        apply auto
      subgoal
        unfolding disj_assn_def
        apply(rule disjI2)
        by auto
      subgoal for d' tr2'
        by (auto elim!: sync_elims)
      done
    done
  done

lemma combine_out_wait_guar1:
"ch\<in>chs \<Longrightarrow> combine_assn chs (out_tassn ch v P) (wait_guar_tassn S p rdy Q) \<Longrightarrow>\<^sub>t \<up>(0\<in>S) \<and>\<^sub>t combine_assn chs (out_tassn ch v P) (Q 0)"
 unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_tassn.cases[of ch v P tr1])
     apply auto
    subgoal for tr1'
      apply(cases rule: wait_guar_tassn.cases[of S p rdy Q tr2])
        apply auto
      subgoal for d tr2'
        by (auto elim!: sync_elims)
      done
    done
  done

lemma combine_out_wait_guar2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs (out_tassn ch v P) (wait_guar_tassn S p rdy Q) \<Longrightarrow>\<^sub>t 
    (out_tassn ch v (combine_assn chs P ((wait_guar_tassn (S-{0}) p rdy Q)))) 
\<or>\<^sub>t  (\<up>(0\<in>S) \<and>\<^sub>t combine_assn chs (out_tassn ch v P) (Q 0))"
 unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_tassn.cases[of ch v P tr1])
     apply auto
    subgoal for tr1'
      apply(cases rule: wait_guar_tassn.cases[of S p rdy Q tr2])
        apply auto
      subgoal
        unfolding disj_assn_def
        apply(rule disjI2)
        by auto
      subgoal for d tr2'
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(elim combine_blocks_unpairE3)
         apply auto
        apply(rule out_tassn.intros)
        apply(rule exI[where x="tr1'"])
        apply auto
        apply(rule exI[where x="tr2"])
        apply auto
        apply(rule wait_guar_tassn.intros(2))
        by auto
      done
    done
  done

lemma combine_left_disj:
"combine_assn chs (P \<or>\<^sub>t Q) R \<Longrightarrow>\<^sub>t (combine_assn chs P R) \<or>\<^sub>t (combine_assn chs Q R)"
unfolding combine_assn_def entails_tassn_def disj_assn_def
  by auto

lemma combine_right_disj:
"combine_assn chs R (P \<or>\<^sub>t Q) \<Longrightarrow>\<^sub>t (combine_assn chs R P) \<or>\<^sub>t (combine_assn chs R Q)"
unfolding combine_assn_def entails_tassn_def disj_assn_def
  by auto

lemma disj_tran:
"P1 \<Longrightarrow>\<^sub>t Q1 \<Longrightarrow> P2 \<Longrightarrow>\<^sub>t Q2 \<Longrightarrow> (P1 \<or>\<^sub>t P2) \<Longrightarrow>\<^sub>t (Q1 \<or>\<^sub>t Q2)"
unfolding entails_tassn_def disj_assn_def
  by auto

lemma wait_guar_tassn_tran:
  assumes"\<And>v. v \<in> s \<Longrightarrow> P v \<Longrightarrow>\<^sub>t Q v"
  shows "wait_guar_tassn s p rdy P \<Longrightarrow>\<^sub>t wait_guar_tassn s p rdy Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: wait_guar_tassn.cases[of s p rdy P tr])
      apply auto
    subgoal
      apply(rule wait_guar_tassn.intros(1))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal for d tr'
      apply(rule wait_guar_tassn.intros(2))
      using assms
      by(auto simp add:entails_tassn_def)
    done
  done

lemma combine_waitout_assm_wait2_1:
"ch\<notin>chs \<Longrightarrow> compat_rdy rdy1 rdy2 \<Longrightarrow> d1<d2 \<Longrightarrow> d1\<ge>0 \<Longrightarrow> combine_assn chs (waitout_assm_tassn {0..d1} p1 rdy1 ch f P1) (wait_tassn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
 wait_guar_tassn {0..d1} (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (\<lambda> d. out_tassn ch (f d) (combine_assn chs (P1 d) (wait_tassn (d2-d) (\<lambda> t. p2(t+d)) rdy2 P2)))
 \<or>\<^sub>t wait_guar_tassn {d1<..<d2} (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (\<lambda> d. out_tassn ch (f d) (combine_assn chs (true\<^sub>A) (wait_tassn (d2-d) (\<lambda> t. p2(t+d)) rdy2 P2)))
 \<or>\<^sub>t wait_tassn d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs (wait_guar_tassn {0..} (\<lambda> t. p1(t+d2)) rdy1 (\<lambda> d. out_tassn ch (f (d+d2)) (true\<^sub>A))) (P2))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_tassn.cases[of d2 p2 rdy2 P2 tr2])
      apply auto
    subgoal for tr2'
      apply(cases rule: waitout_assm_tassn.cases[of "{0..d1}" p1 rdy1 ch f P1 tr1])
          apply auto
      subgoal for tr1'
        apply (elim combine_blocks_unpairE3)
         apply auto
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule )
         apply(rule )
        by auto
      subgoal for d1' tr1'
        apply(elim combine_blocks_waitE3)
           apply auto
        apply (elim combine_blocks_unpairE3)
         apply auto
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule )
          apply(rule )
          apply auto
        apply(rule exI[where x="tr1'"])
        apply auto
        apply(rule exI[where x="(WaitBlk (d2 - d1') (\<lambda>t. p2 (t + d1')) rdy2 # tr2')"])
        apply auto
        apply(rule )
        by auto
      subgoal for d1' tr1'
        apply(cases "d1'<d2")
        subgoal
        apply(elim combine_blocks_waitE3)
           apply auto
        apply (elim combine_blocks_unpairE3)
         apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule disjI1)
          apply(rule)
          apply auto
          apply(rule)
          unfolding true_assn_def
          apply auto
          apply(rule exI[where x="tr1'"])
          apply(rule exI[where x="(WaitBlk (d2 - d1') (\<lambda>t. p2 (t + d1')) rdy2 # tr2')"])
          apply auto
          apply(rule )
          by auto
        apply(cases "d1'>d2")
        subgoal
        apply(elim combine_blocks_waitE4)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule)
           apply auto
          apply(rule exI[where x="(WaitBlk (d1' - d2) (\<lambda>t. p1 (t + d2)) rdy1 # OutBlock ch (f d1') # tr1')"])
          apply auto
          apply(rule )
            apply auto
          apply(rule)
          unfolding true_assn_def
          by auto
        apply auto
        apply(elim combine_blocks_waitE2)
         apply auto
        unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule)
         apply auto
        apply(rule exI[where x="(OutBlock ch (f d2) # tr1')"])
        apply auto
        apply(rule )
        apply auto
        apply(rule )
        unfolding true_assn_def
        by auto
      done
    done
  done

lemma combine_waitout_assm_wait2_2:
"ch\<notin>chs \<Longrightarrow> compat_rdy rdy1 rdy2 \<Longrightarrow> d1\<ge>d2 \<Longrightarrow> d2\<ge>0 \<Longrightarrow> combine_assn chs (waitout_assm_tassn {0..d1} p1 rdy1 ch f P1) (wait_tassn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
 wait_guar_tassn {0..<d2} (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (\<lambda> d. out_tassn ch (f d) (combine_assn chs (P1 d) (wait_tassn (d2-d) (\<lambda> t. p2(t+d)) rdy2 P2)))
 \<or>\<^sub>t wait_tassn d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs (waitout_assm_tassn {0..d1-d2} (\<lambda> t. p1(t+d2)) rdy1 ch (\<lambda> t. f(t+d2)) (\<lambda> d. P1(d+d2))) (P2))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_tassn.cases[of d2 p2 rdy2 P2 tr2])
      apply auto
    subgoal
      apply(cases rule: waitout_assm_tassn.cases[of "{0..d1}" p1 rdy1 ch f P1 tr1])
          apply auto
      subgoal for tr1'
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule)
        by auto
      subgoal for d1 tr1'
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule)
        by auto
      subgoal for d1' tr1'
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule)
        by auto
      done
    subgoal for tr2'
      apply(cases rule: waitout_assm_tassn.cases[of "{0..d1}" p1 rdy1 ch f P1 tr1])
          apply auto
      subgoal for tr1'
        apply (elim combine_blocks_unpairE3)
         apply auto
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule )
         apply(rule )
        by auto
      subgoal for d1' tr1'
        apply(cases "d1'<d2")
        subgoal
        apply(elim combine_blocks_waitE3)
             apply auto
          apply (elim combine_blocks_unpairE3)
          apply auto
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(rule )
          apply auto
          apply(rule )
          apply (rule exI[where x="tr1'"])
          apply auto
          apply(rule exI[where x="(WaitBlk (d2 - d1') (\<lambda>t. p2 (t + d1')) rdy2 # tr2')"])
          apply auto
          apply(rule )
          by auto
        apply(cases "d1'>d2")
        subgoal
        apply(elim combine_blocks_waitE4)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule )
           apply auto
          apply(rule exI[where x="(WaitBlk (d1' - d2) (\<lambda>t. p1 (t + d2)) rdy1 # OutBlock ch (f d1') # tr1')"])
          apply auto
          using waitout_assm_tassn.intros(2)[of "(\<lambda>d. P1 (d + d2))" "d1'-d2" tr1' "{0..d1 - d2}"  "(\<lambda>t. p1 (t + d2))" rdy1 ch "(\<lambda>t. f (t + d2))"]
          by auto
        apply auto
        apply(elim combine_blocks_waitE2)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule )
           apply auto
          apply(rule exI[where x="(OutBlock ch (f d2) # tr1')"])
          apply auto
          using waitout_assm_tassn.intros(1)[of "(\<lambda>d. P1 (d + d2))" tr1' "{0..d1 - d2}" "(\<lambda>t. p1 (t + d2))" rdy1 ch "(\<lambda>t. f (t + d2))"]
          by auto
        subgoal for d1' tr1'
          apply(elim combine_blocks_waitE4)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule )
           apply auto
          apply(rule exI[where x="(WaitBlk (d1' - d2) (\<lambda>t. p1 (t + d2)) rdy1 # OutBlock ch (f d1') # tr1')"])
          apply auto
          using waitout_assm_tassn.intros(4)[of "d1'-d2" "{0..d1 - d2}"  "(\<lambda>t. p1 (t + d2))" rdy1 ch "(\<lambda>t. f (t + d2))"]
          by auto
        done
      done
    done

lemma combine_waitout'_assm_wait2_1:
"ch\<notin>chs \<Longrightarrow> compat_rdy rdy1 rdy2 \<Longrightarrow> d1<d2 \<Longrightarrow> d1\<ge>0 \<Longrightarrow> combine_assn chs (waitout'_assm_tassn d1 p1 rdy1 ch f P1) (wait_tassn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
 waitout'_assm_tassn d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) ch f (\<lambda> d. (combine_assn chs (P1 d) (wait_tassn (d2-d) (\<lambda> t. p2(t+d)) rdy2 P2)))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_tassn.cases[of d2 p2 rdy2 P2 tr2])
      apply auto
    subgoal for tr2'
      apply(cases rule: waitout'_assm_tassn.cases[of d1 p1 rdy1 ch f P1 tr1])
          apply auto
      subgoal for tr1'
        apply (elim combine_blocks_unpairE3)
         apply auto
        unfolding disj_assn_def
        apply(rule )
         by auto
      subgoal for d1' tr1'
        apply(elim combine_blocks_waitE3)
           apply auto
        apply (elim combine_blocks_unpairE3)
         apply auto
        apply(rule waitout'_assm_tassn.intros(2))
          apply auto
        apply(rule exI[where x="tr1'"])
        apply auto
        apply(rule exI[where x="(WaitBlk (d2 - d1') (\<lambda>t. p2 (t + d1')) rdy2 # tr2')"])
        apply auto
        apply(rule )
        by auto
      subgoal for d1' tr1'
        apply(cases "d1'<d2")
        subgoal
        apply(elim combine_blocks_waitE3)
           apply auto
        apply(rule)
          by auto
        apply(cases "d1'>d2")
        subgoal
        apply(elim combine_blocks_waitE4)
             apply auto
          unfolding disj_assn_def
          apply(rule)
           by auto
        apply auto
        apply(elim combine_blocks_waitE2)
         apply auto
        apply(rule)
         by auto
      done
    done
  done

lemma combine_waitout'_assm_wait2_2:                                               
"ch\<notin>chs \<Longrightarrow> compat_rdy rdy1 rdy2 \<Longrightarrow> d1\<ge>d2 \<Longrightarrow> d2\<ge>0 \<Longrightarrow> combine_assn chs (waitout'_assm_tassn d1 p1 rdy1 ch f P1) (wait_tassn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
 wait_guar_tassn {0..<d2} (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (\<lambda> d. out_tassn ch (f d) (combine_assn chs (P1 d) (wait_tassn (d2-d) (\<lambda> t. p2(t+d)) rdy2 P2)))
 \<or>\<^sub>t wait_tassn d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs (waitout'_assm_tassn (d1-d2) (\<lambda> t. p1(t+d2)) rdy1 ch (\<lambda> t. f(t+d2)) (\<lambda> d. P1(d+d2))) (P2))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_tassn.cases[of d2 p2 rdy2 P2 tr2])
      apply auto
    subgoal
      apply(cases rule: waitout'_assm_tassn.cases[of "d1" p1 rdy1 ch f P1 tr1])
          apply auto
      subgoal for tr1'
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule)
        by auto
      subgoal for d1 tr1'
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule)
        by auto
      subgoal for d1' tr1'
        unfolding disj_assn_def
        apply(rule disjI2)
        apply(rule)
        by auto
      done
    subgoal for tr2'
      apply(cases rule: waitout'_assm_tassn.cases[of "d1" p1 rdy1 ch f P1 tr1])
          apply auto
      subgoal for tr1'
        apply (elim combine_blocks_unpairE3)
         apply auto
        unfolding disj_assn_def
        apply(rule disjI1)
        apply(rule )
         apply(rule )
        by auto
      subgoal for d1' tr1'
        apply(cases "d1'<d2")
        subgoal
        apply(elim combine_blocks_waitE3)
             apply auto
          apply (elim combine_blocks_unpairE3)
          apply auto
          unfolding disj_assn_def
          apply(rule disjI1)
          apply(rule )
          apply auto
          apply(rule )
          apply (rule exI[where x="tr1'"])
          apply auto
          apply(rule exI[where x="(WaitBlk (d2 - d1') (\<lambda>t. p2 (t + d1')) rdy2 # tr2')"])
          apply auto
          apply(rule )
          by auto
        apply(cases "d1'>d2")
        subgoal
        apply(elim combine_blocks_waitE4)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule )
           apply auto
          apply(rule exI[where x="(WaitBlk (d1' - d2) (\<lambda>t. p1 (t + d2)) rdy1 # OutBlock ch (f d1') # tr1')"])
          apply auto
          using waitout'_assm_tassn.intros(2)[of "(\<lambda>d. P1 (d + d2))" "d1'-d2" tr1' "d1-d2"  "(\<lambda>t. p1 (t + d2))" rdy1 ch "(\<lambda>t. f (t + d2))"]
          by auto
        apply auto
        apply(elim combine_blocks_waitE2)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule )
           apply auto
          apply(rule exI[where x="(OutBlock ch (f d2) # tr1')"])
          apply auto
          using waitout'_assm_tassn.intros(1)[of "(\<lambda>d. P1 (d + d2))" tr1' "d1 - d2" "(\<lambda>t. p1 (t + d2))" rdy1 ch "(\<lambda>t. f (t + d2))"]
          by auto
        subgoal for d1' tr1'
          apply(elim combine_blocks_waitE4)
             apply auto
          unfolding disj_assn_def
          apply(rule disjI2)
          apply(rule )
           apply auto
          apply(rule exI[where x="(WaitBlk (d1' - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1')"])
          apply auto
          using waitout'_assm_tassn.intros(3)[of  "d1 - d2" "d1'-d2" "(\<lambda>t. p1 (t + d2))" rdy1 ch "(\<lambda>t. f (t + d2))"]
          by auto
        done
      done
    done


inductive n_waitout_assm_tassn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "0 \<le> T \<Longrightarrow> P (tr @ [OutBlock ch (f 0)])\<Longrightarrow> 
   \<forall>d. (d \<le> T \<and> d > 0) \<longrightarrow> P (tr @ [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy , OutBlock ch (f d)])\<Longrightarrow>  
   \<forall>d tr'. d>T \<longrightarrow> P (tr @ [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy] @ tr')\<Longrightarrow> 
    (n_waitout_assm_tassn T p rdy ch f P) tr"

theorem send1:
  shows "\<Turnstile> {\<lambda>s t. (n_waitout_assm_tassn T (\<lambda>_. EState s) ({ch}, {}) ch (\<lambda>_ . e s) (P s)) t}
       Cm (ch[!]e)
    {\<lambda>s t. P s t}"
  unfolding Valid_def
  apply auto
  apply(elim sendE)
  subgoal for a b tr1 aa ba tr2
    apply(elim n_waitout_assm_tassn.cases)
    apply auto
    done
  subgoal for a b tr1 aa ba tr2 d
    apply(elim n_waitout_assm_tassn.cases)
    apply auto
    apply(cases "d\<le>T")
    apply auto
    done
  done


inductive n_waitin_assm_tassn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> (real set) \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "0 \<le> T \<Longrightarrow> P (tr @ [InBlock ch (f 0)])\<Longrightarrow> 
   \<forall>d. (d \<le> T \<and> d > 0) \<longrightarrow> P (tr @ [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy , OutBlock ch (f d)])\<Longrightarrow>  
   \<forall>d tr'. d>T \<longrightarrow> P (tr @ [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy] @ tr')\<Longrightarrow> 
    (n_waitin_assm_tassn T p rdy ch V P) tr"

end