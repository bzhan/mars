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

inductive wait_inv_assn :: "(gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> bool) \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Waitinv\<^sub>t") where
  "dp 0 \<Longrightarrow> Waitinv\<^sub>t r dp rdy []"
| "d > 0 \<Longrightarrow> dp d \<Longrightarrow> (\<forall>t\<in>{0..d}. r (p t) t) \<Longrightarrow> Waitinv\<^sub>t r dp rdy [WaitBlk (ereal d) p rdy]" 

inductive wait_out_inv_assn ::"(gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool) 
                                          \<Rightarrow> rdy_info \<Rightarrow> cname  \<Rightarrow> tassn" ("WaitOutinv\<^sub>t") where
  "dp 0 \<Longrightarrow> \<exists> s. r s 0 \<and> g s v \<Longrightarrow> WaitOutinv\<^sub>t r dp g rdy ch [OutBlock ch v]"
| "d > 0 \<Longrightarrow> dp d \<Longrightarrow> (\<forall>t\<in>{0..d}. r (p t) t) \<Longrightarrow> g (p d) v 
                \<Longrightarrow> WaitOutinv\<^sub>t r dp g rdy ch [WaitBlk (ereal d) p rdy, OutBlock ch v]"

inductive sb2gsb :: "(state \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> bool)" where
 "p s \<Longrightarrow> sb2gsb p (State s)"

inductive srb2gsrb :: "(state \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool)" where
 "p s v \<Longrightarrow> srb2gsrb p (State s) v"

inductive pgsb2gsb :: "(gstate \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> bool)" where
 "r1 s \<Longrightarrow> r2 s' \<Longrightarrow> pgsb2gsb r1 r2 (ParState s s') "

inductive pgsrb2gsrb :: "(gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool)" where
 "r1 s v \<Longrightarrow> r2 s' v \<Longrightarrow> pgsrb2gsrb r1 r2 (ParState s s') v"

inductive gsb2gsrb :: "(gstate \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool)" where
 "r s \<Longrightarrow> gsb2gsrb r s t"

lemma combine_assn_emp_ininv:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (Ininv\<^sub>t r g ch @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_inv_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_ininv_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (Ininv\<^sub>t r g ch @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
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

lemma combine_assn_outinv_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (Outinv\<^sub>t r g ch @\<^sub>t P) emp\<^sub>t= false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_inv_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_ininv_outinv:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Ininv\<^sub>t r1 g1 ch @\<^sub>t P) (Outinv\<^sub>t r2 g2 ch @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (IOinv\<^sub>t (pgsb2gsb r1 r2) (pgsrb2gsrb g1 g2) ch @\<^sub>t combine_assn chs P Q)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_inv_assn.simps
                        out_inv_assn.simps in_inv_assn.simps pgsb2gsb.simps pgsrb2gsrb.simps)
          apply (auto elim: sync_elims)
  subgoal for tr tr1 tr2 s1 v1 s2 v2
    apply(rule exI[where x= "[IOBlock ch v1]"])
    apply auto
     apply(rule exI[where x= "ParState s1 s2"])
    using combine_blocks_pairE apply blast
    by (meson combine_blocks_pairE)
  done

lemma combine_assn_emp_waitinv:
  "combine_assn chs emp\<^sub>t (Waitinv\<^sub>t  p dp rdy @\<^sub>t P) \<Longrightarrow>\<^sub>t combine_assn chs emp\<^sub>t P"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def wait_inv_assn.simps emp_assn_def 
join_assn_def false_assn_def)
  by (auto elim: sync_elims)

lemma combine_assn_waitinv_emp:
  "combine_assn chs  (Waitinv\<^sub>t  p dp rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t combine_assn chs  P emp\<^sub>t"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def wait_inv_assn.simps emp_assn_def 
join_assn_def false_assn_def)
  by (auto elim: sync_elims)

lemma combine_assn_waitinv_ininv:
  assumes "ch \<in> chs"
    and "compat_rdy rdy1 ({}, {ch})"
  shows "combine_assn chs (Waitinv\<^sub>t r1 dp rdy1 @\<^sub>t P) (Ininv\<^sub>t r2 g ch @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Waitinv\<^sub>t (pgsrb2gsrb r1 (gsb2gsrb r2)) dp (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
    combine_assn chs P (Ininv\<^sub>t r2 g ch @\<^sub>t Q))"
proof-
  have *:"(Waitinv\<^sub>t (pgsrb2gsrb r1 (gsb2gsrb r2)) dp (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
    combine_assn chs P (Ininv\<^sub>t r2 g ch @\<^sub>t Q)) tr" if
        "(Waitinv\<^sub>t r1 dp rdy1 @\<^sub>t P) tr1" "(Ininv\<^sub>t r2 g ch @\<^sub>t Q) tr2" 
        "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof-
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "Waitinv\<^sub>t r1 dp rdy1 tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "Ininv\<^sub>t r2 g ch tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    have d:"(Waitinv\<^sub>t (pgsrb2gsrb r1 (gsb2gsrb r2)) dp (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
     combine_assn chs P (Ininv\<^sub>t r2 g ch @\<^sub>t Q)) tr" if 
        "0 < d2" "0<d" "dp d"
        "combine_blocks chs (WaitBlk (ereal d) p rdy1 # tr12)
          (WaitBlk (ereal d2) (\<lambda>_. s) ({}, {ch}) # InBlock ch v # tr22) tr" 
        "\<forall>t\<in>{0..d}. r1 (p t) t"
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
          using that(4)
          apply (elim combine_blocks_waitE3)
             apply (rule that(2)) apply (rule d1') using assms(2) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal 
              apply(auto simp add:wait_inv_assn.simps pgsrb2gsrb.simps gsb2gsrb.simps)
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
          using that(4) unfolding d2[symmetric]
          apply (elim combine_blocks_waitE2)
          using assms(2) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal using that apply (auto simp add: wait_inv_assn.simps pgsrb2gsrb.simps gsb2gsrb.simps)
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
          using that(4)
          apply (elim combine_blocks_waitE4)
          apply (rule that(1)) apply (rule d3')
           using assms(2) apply simp
          apply (elim combine_blocks_pairE2')
          using assms by auto
      qed
        qed
      have e: "(Waitinv\<^sub>t (pgsrb2gsrb r1 (gsb2gsrb r2)) dp (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
     combine_assn chs P (Ininv\<^sub>t r2 g ch @\<^sub>t Q)) tr" if 
        "combine_blocks chs (WaitBlk (ereal d) p rdy1 # tr12)
          (WaitBlk \<infinity> (\<lambda>_. s) ({}, {ch}) # tr22) tr" "0 < d " "dp d" 
          "\<forall>t\<in>{0..d}. r1 (p t) t" "r2 s" for d p s
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
            subgoal apply(simp add: wait_inv_assn.simps pgsrb2gsrb.simps gsb2gsrb.simps) by blast
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

lemma combine_assn_waitoutinv_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (WaitOutinv\<^sub>t r dp g rdy ch @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def wait_out_inv_assn.simps)
  using assms by (auto elim: sync_elims)
        
lemma combine_assn_waitoutinv_ininv:
  assumes "ch \<in> chs"
    and "ch \<in> fst rdy"
  shows "combine_assn chs (WaitOutinv\<^sub>t rr dp g1 rdy ch @\<^sub>t P) (Ininv\<^sub>t r g2 ch @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         (IOinv\<^sub>t (pgsb2gsb (\<lambda> s. rr s 0) r) (pgsrb2gsrb g1 g2) ch @\<^sub>t combine_assn chs P Q)"
proof-
  have *:"(IOinv\<^sub>t (pgsb2gsb (\<lambda> s. rr s 0) r) (pgsrb2gsrb g1 g2) ch @\<^sub>t combine_assn chs P Q) tr"
    if "(WaitOutinv\<^sub>t rr dp g1 rdy ch @\<^sub>t P) tr1" "(Ininv\<^sub>t r g2 ch @\<^sub>t Q) tr2" "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "WaitOutinv\<^sub>t rr dp g1 rdy ch tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "Ininv\<^sub>t r g2 ch tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    show ?thesis
      using a(1) apply (cases rule: wait_out_inv_assn.cases)
      subgoal for v
        using b(1) apply (cases rule: in_inv_assn.cases)
        subgoal for s' v'
          using that(3) unfolding a(3) b(3) apply auto
          apply (elim combine_blocks_pairE) using assms(1) apply auto
          apply (auto simp add: conj_assn_def pure_assn_def join_assn_def)
          apply (rule exI[where x="[IOBlock ch v']"])
          apply (auto intro: io_assn.intros)
          unfolding combine_assn_def using a(2) b(2) apply auto
          subgoal for s tr'
            using io_inv_assn.intros[of "(pgsb2gsb (\<lambda>s. rr s 0) r)" "ParState s s'" "(pgsrb2gsrb g1 g2)" v ch]
            by(auto simp add:pgsb2gsb.simps pgsrb2gsrb.simps)
          done
        subgoal for d s' v'
          using that(3) unfolding a(3) b(3) apply auto
          apply (elim combine_blocks_pairE2) using assms by auto
        subgoal for s'
          using that(3) unfolding a(3) b(3) apply auto
          apply (elim combine_blocks_pairE2) by (rule assms)
        done
      using b(1) apply (cases rule: in_inv_assn.cases)
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

end