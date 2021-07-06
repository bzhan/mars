theory newParallel
  imports ContinuousInv BigStepParallel Complementlemma

begin


inductive out_inv_assn :: "(gstate \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow>  bool) \<Rightarrow> cname \<Rightarrow> tassn" ("Outinv\<^sub>t") where
  "r s  \<Longrightarrow> g s v \<Longrightarrow> Outinv\<^sub>t r g ch [OutBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> r s  \<Longrightarrow> g s v \<Longrightarrow> Outinv\<^sub>t r g ch [WaitBlk (ereal d) (\<lambda>_. s) ({ch}, {}), OutBlock ch v]"
| "r s  \<Longrightarrow>Outinv\<^sub>t r g ch  [WaitBlk \<infinity> (\<lambda>_. s) ({ch}, {})]"

inductive in_inv_assn :: "(gstate \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> cname  \<Rightarrow> tassn" ("Ininv\<^sub>t") where
  "r s  \<Longrightarrow> g s v\<Longrightarrow> Ininv\<^sub>t r g ch [InBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> r s  \<Longrightarrow> g s v \<Longrightarrow> Ininv\<^sub>t r g ch [WaitBlk (ereal d) (\<lambda>_. s) ({}, {ch}), InBlock ch v]"
| "r s  \<Longrightarrow> Ininv\<^sub>t r g ch  [WaitBlk \<infinity> (\<lambda>_. s) ({}, {ch})]"

inductive io_inv_assn :: "(gstate \<Rightarrow>  bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> cname \<Rightarrow> tassn" ("IOinv\<^sub>t") where
  "r s  \<Longrightarrow> g s v \<Longrightarrow> IOinv\<^sub>t r g ch [IOBlock ch v]"

inductive wait_inv_assn :: "(gstate \<Rightarrow>  bool) \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Waitinv\<^sub>t") where
  " Waitinv\<^sub>t r rdy []"
| "d > 0 \<Longrightarrow> (\<forall>t\<in>{0..d}. r (p t)) \<Longrightarrow> Waitinv\<^sub>t r rdy [WaitBlk (ereal d) p rdy]" 


inductive s2gs1 :: "(state \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> bool)" where
 "p s \<Longrightarrow> s2gs1 p (State s)"

inductive s2gs2 :: "(state \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool)" where
 "p s v \<Longrightarrow> s2gs2 p (State s) v"

inductive pgs2gs1 :: "(gstate \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> bool)" where
 "r1 s \<Longrightarrow> r2 s' \<Longrightarrow> pgs2gs1 r1 r2 (ParState s s') "

inductive pgs2gs2 :: "(gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool)" where
 "r1 s v \<Longrightarrow> r2 s' v \<Longrightarrow> pgs2gs2 r1 r2 (ParState s s') v"

lemma combine_assn_emp_ininv:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (Ininv\<^sub>t r g ch @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_inv_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_emp_outinv:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (Outinv\<^sub>t r g ch @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_inv_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_ininv_outinv:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Ininv\<^sub>t r1 g1 ch @\<^sub>t P) (Outinv\<^sub>t r2 g2 ch @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (IOinv\<^sub>t (pgs2gs1 r1 r2) (pgs2gs2 g1 g2) ch @\<^sub>t combine_assn chs P Q)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_inv_assn.simps
                        out_inv_assn.simps in_inv_assn.simps pgs2gs1.simps pgs2gs2.simps)
  apply (auto elim: sync_elims)
  by (metis append_Cons append_self_conv2 combine_blocks_pairE)

lemma combine_assn_emp_waitinv:
  "combine_assn chs emp\<^sub>t (Waitinv\<^sub>t p rdy @\<^sub>t P) \<Longrightarrow>\<^sub>t combine_assn chs emp\<^sub>t P"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def wait_inv_assn.simps emp_assn_def join_assn_def false_assn_def)
  by (auto elim: sync_elims)


lemma combine_assn_wait_in:
  assumes "ch \<in> chs"
    and "compat_rdy rdy1 ({}, {ch})"
  shows "combine_assn chs (Waitinv\<^sub>t r1 rdy1 @\<^sub>t P) (Ininv\<^sub>t r2 g ch @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Waitinv\<^sub>t (pgs2gs1 r1 r2) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
    combine_assn chs P (Ininv\<^sub>t r2 g ch @\<^sub>t Q))"
proof-
  have *:"(Waitinv\<^sub>t (pgs2gs1 r1 r2) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
    combine_assn chs P (Ininv\<^sub>t r2 g ch @\<^sub>t Q)) tr" if
        "(Waitinv\<^sub>t r1 rdy1 @\<^sub>t P) tr1" "(Ininv\<^sub>t r2 g ch @\<^sub>t Q) tr2" 
        "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof-
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "Waitinv\<^sub>t r1 rdy1 tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "Ininv\<^sub>t r2 g ch tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    have d:"(Waitinv\<^sub>t (pgs2gs1 r1 r2) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
     combine_assn chs P (Ininv\<^sub>t r2 g ch @\<^sub>t Q)) tr" if 
        "0 < d2" "0<d"
        "combine_blocks chs (WaitBlk (ereal d) p rdy1 # tr12)
          (WaitBlk (ereal d2) (\<lambda>_. s) ({}, {ch}) # InBlock ch v # tr22) tr" 
        "\<forall>t\<in>{0..d}. r1 (p t)"
        "r2 s "  "g s v "
      for d p s v d2
    proof -
      have "d < d2 \<or> d = d2 \<or> d > d2" by auto
      then show ?thesis
      proof (elim disjE)
        assume d1: "d < d2"
        have d1': "ereal d < ereal d2"
          using d1 by auto
        show ?thesis
          using that(3)
          apply (elim combine_blocks_waitE3)
             apply (rule that(2)) apply (rule d1') using assms(2) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal 
              apply(auto simp add:wait_inv_assn.simps pgs2gs1.simps)
              apply(rule exI[where x="d"])
              apply(rule exI[where x="(\<lambda>t. ParState (p t) s)"])
              using that by auto
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
            using b(2) d1 that by (auto intro: in_inv_assn.intros)
          done
      next
        assume d2: "d = d2"
        show ?thesis
          using that(3) unfolding d2[symmetric]
          apply (elim combine_blocks_waitE2)
          using assms(2) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal using that apply (auto simp add: wait_inv_assn.simps pgs2gs1.simps)
              by blast
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
              by (auto intro: in_inv_assn.intros b(2) that)
            by auto
          done
      next
        assume d3: "d > d2"
        have d3': "ereal d > ereal d2"
          using d3  by auto
        show ?thesis
          using that(3)
          apply (elim combine_blocks_waitE4)
          apply (rule that(1)) apply (rule d3')
           using assms(2) apply simp
          apply (elim combine_blocks_pairE2')
          using assms by auto
      qed
        qed
      have e: "(Waitinv\<^sub>t (pgs2gs1 r1 r2) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
     combine_assn chs P (Ininv\<^sub>t r2 g ch @\<^sub>t Q)) tr" if 
        "combine_blocks chs (WaitBlk (ereal d) p rdy1 # tr12)
          (WaitBlk \<infinity> (\<lambda>_. s) ({}, {ch}) # tr22) tr" "0 < d " 
          "\<forall>t\<in>{0..d}. r1 (p t)" "r2 s" for d p s
      proof -
      have e1: "\<infinity> - ereal d = \<infinity>"
        by auto
      show ?thesis
        using that
        apply (elim combine_blocks_waitE3)
           apply auto using assms(2) apply simp
        subgoal for blks'
          apply (subst join_assn_def)
          apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
          apply (rule exI[where x=blks'])
          apply (rule conjI)
            subgoal apply(simp add: wait_inv_assn.simps pgs2gs1.simps) by blast
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
            using b(2) apply (auto intro: in_inv_assn.intros)
          done
        done
    qed
    show ?thesis
      using a(1) apply (cases rule: wait_inv_assn.cases)
      using b(1) apply (cases rule: in_inv_assn.cases)
      subgoal for s v
        apply(auto simp add: combine_assn_def join_assn_def)
        apply(rule exI[where x= "[]"])
        apply (auto simp add: wait_inv_assn.simps)
        apply(rule exI[where x= "tr12"])
        apply (auto simp add: a)
        apply(rule exI[where x= "tr2"])
        apply auto
         apply(rule exI[where x= "tr21"])
         apply auto
        using b apply auto
        using that a b by auto
 subgoal for d s v
        apply(auto simp add: combine_assn_def join_assn_def)
        apply(rule exI[where x= "[]"])
        apply (auto simp add: wait_inv_assn.simps)
        apply(rule exI[where x= "tr12"])
        apply (auto simp add: a)
        apply(rule exI[where x= "tr2"])
        apply auto
         apply(rule exI[where x= "tr21"])
         apply auto
        using b apply auto
        using that a b by auto
      subgoal for d 
        apply(auto simp add: combine_assn_def join_assn_def)
        apply(rule exI[where x= "[]"])
        apply (auto simp add: wait_inv_assn.simps)
        apply(rule exI[where x= "tr12"])
        apply (auto simp add: a)
        apply(rule exI[where x= "tr2"])
        apply auto
         apply(rule exI[where x= "tr21"])
         apply auto
        using b apply auto
        using that a b by auto
      using b(1) apply (cases rule: in_inv_assn.cases)
      subgoal for s v d p
        apply(auto simp add: combine_assn_def join_assn_def)
        by (metis Cons_eq_appendI a(3) assms(1) b(3)  combine_blocks_pairE2' that(3))
      subgoal for d p d2 s v
        apply(rule d[of d2 d p s v])
        using that a b by auto
      subgoal for d p s
        apply(rule e[of d p s])
        using that a b by auto
      done
  qed
show ?thesis
    apply (subst combine_assn_def)
    apply (auto simp add: entails_tassn_def)
  using * by auto
qed


        
 



end