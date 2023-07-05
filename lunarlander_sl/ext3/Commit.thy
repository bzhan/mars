theory Commit
  imports
    Complementlemma
begin


text \<open>Commitment\<close>

datatype ctr =
  cE
| cI cname         
| cO cname real
| cW ereal "cname set \<times> cname set" "cname set \<times> cname set"
| cseq ctr ctr ("_[@] _" [91,90] 90)
(*
| cor ctr ctr ("_[\<or>] _" [86,85] 85) *)
| crepn nat "nat \<Rightarrow> ctr"
(*
| crep "nat \<Rightarrow> ctr" *)

inductive commit :: "cname set \<Rightarrow> ctr \<Rightarrow> trace \<Rightarrow> bool" where
  commitE: "commit chs cE []"
| commitI1: "ch \<in> chs \<Longrightarrow> commit chs (cI ch) [InBlock ch v]"
| commitI2: "ch \<notin> chs \<Longrightarrow> commit chs (cI ch) []"
| commitO1: "ch \<in> chs \<Longrightarrow> commit chs (cO ch v) [OutBlock ch v]"
| commitO2: "ch \<notin> chs \<Longrightarrow> commit chs (cO ch v) []"
| commitW1: " a \<inter> chs \<subseteq> fst rdy \<Longrightarrow> b \<inter> fst rdy = {} \<Longrightarrow>
              c \<inter> chs \<subseteq> snd rdy \<Longrightarrow> d \<inter> snd rdy = {} \<Longrightarrow> s > 0 \<Longrightarrow> 
             commit chs (cW s (a,b) (c,d)) [WaitBlk s p rdy]"
| commitW2: " a \<inter> chs \<subseteq> fst rdy \<Longrightarrow> b \<inter> fst rdy = {} \<Longrightarrow>
              c \<inter> chs \<subseteq> snd rdy \<Longrightarrow> d \<inter> snd rdy = {} \<Longrightarrow> s1>0\<Longrightarrow>
              tr1 = [WaitBlk s1 p rdy] \<Longrightarrow>
             commit chs (cW s2 (a,b) (c,d)) tr2\<Longrightarrow>s2>0\<Longrightarrow> 
             commit chs (cW (s1+s2) (a,b) (c,d)) (tr1 @ tr2)"
| commitseq1: "commit chs c1 tr1 \<Longrightarrow>
              commit chs c2 tr2\<Longrightarrow>
              commit chs (cseq c1 c2) (tr1 @ tr2)"
| commitseq2: "commit chs (c1) (tr1@[WaitBlk s1 p1 rdy])\<Longrightarrow>
              commit chs (c2) ([WaitBlk s2 p2 rdy]@tr2)\<Longrightarrow>
              p1 s1 = p2 0 \<Longrightarrow> s1>0 \<Longrightarrow> s2>0 \<Longrightarrow>
              commit chs (cseq c1 c2) 
              (tr1@[WaitBlk (s1+s2) (\<lambda> t. if  t\<le> s1 then p1 t else p2(t-s1)) rdy]@tr2)"
(*
| commitor1: "commit chs c1 tr \<Longrightarrow> commit chs (cor c1 c2) tr"  
| commitor2: "commit chs c2 tr \<Longrightarrow> commit chs (cor c1 c2) tr"*)
| commirepn1: "commit chs (crepn 0 c) []"
| commirepn2: "commit chs (crepn i c) tr1 \<Longrightarrow> 
               commit chs (c (i+1)) tr2 \<Longrightarrow> 
               commit chs (crepn (i+1) c) (tr1 @ tr2)"
(*
| commirep1: " commit chs (crepn i c) tr \<Longrightarrow>
               commit chs (crep c) tr"*)

inductive_cases commitEE: "commit chs cE tr"
inductive_cases commitIE: "commit chs (cI ch) tr"
inductive_cases commitOE: "commit chs (cO ch v) tr"
inductive_cases commitWE: "commit chs (cW s (a,b) (c,d)) tr"
inductive_cases commitSE: "commit chs (cseq c1 c2) tr"
inductive_cases commitRNE: "commit chs (crepn i c) tr"
(*
inductive_cases commitRE: "commit chs (crep c) tr" *)


lemma commit_W_prop1:"commit chs (cW s (a,b) (c,d)) tr \<Longrightarrow> s>0"
  apply(rule commitWE[of chs s a b c d tr])
    apply auto
  by (simp add: add_pos_pos)

  
lemma commit_W_prop2:" ch\<in>chs \<Longrightarrow> s>0 \<Longrightarrow> 
       combine_blocks chs ([OutBlock ch v]@tr) (tr1 @ tr2) x \<Longrightarrow>
       commit chs (cW s (a, b) (c, d)) tr1 \<Longrightarrow> False"
  apply(rule commitWE[of chs s a b c d tr1])
    apply auto
  by(auto elim: sync_elims)

lemma commit_W_prop3:" ch1\<in>chs \<Longrightarrow> ch2\<in>chs \<Longrightarrow> s1>0 \<Longrightarrow> s1<s2 \<Longrightarrow> 
       combine_blocks chs ([WaitBlk (ereal s1) p rdy, OutBlock ch1 v1]@tr')
         (tr @ [InBlock ch2 v2] @ tr'') x \<Longrightarrow> fst rdy \<subseteq> d \<Longrightarrow> snd rdy \<subseteq> b \<Longrightarrow>
       commit chs (cW (ereal s2) (a, b) (c, d)) tr \<Longrightarrow> False"
proof(induction "length tr" arbitrary: s1 s2 tr p x rule: less_induct)
  case less
  thm less
  show ?case 
    apply(rule commitWE[of chs "(ereal s2)" a b c d tr])
    subgoal using less by auto
    subgoal for rdy' p'
      using less
      apply auto
      apply(elim combine_blocks_waitE3)
         apply auto
      subgoal 
        apply(cases rdy)
        apply(cases rdy')
        by auto
      by(auto elim: sync_elims)
    subgoal for rdy' ss1 p' ss2 tr2
      using less(6)
      thm less
      apply auto
      apply(cases "s1<ss1")
      subgoal
        apply(elim combine_blocks_waitE3)
        using less
           apply auto
        subgoal 
        apply(cases rdy)
        apply(cases rdy')
        by auto
      by(auto elim: sync_elims)
    apply(cases "s1>ss1")
    subgoal
      apply(cases ss1)
      apply auto
      apply(elim combine_blocks_waitE4)
        apply auto
      subgoal 
        using less
        apply(cases rdy)
        apply(cases rdy')
        by auto
      subgoal for r tr'
        apply(cases ss2)
          apply auto
        subgoal for r'
          using less(1)[of tr2 "s1-r" r' "(\<lambda>t. p (t + r))" tr']
          using less by auto
        done
      done
    apply(cases "s1=ss1")
    subgoal
      apply simp
      apply(elim combine_blocks_waitE2)
        using less
           apply auto
        subgoal 
        apply(cases rdy)
        apply(cases rdy')
          by auto
        apply(rule commitWE[of chs ss2 a b c d tr2])
          apply auto
        by(auto elim: sync_elims)
      by auto
    done
qed


lemma commit_W_prop4:" ch1\<in>chs \<Longrightarrow> ch2\<in>chs \<Longrightarrow> s2>0 \<Longrightarrow> s1>s2 \<Longrightarrow> 
       combine_blocks chs ([WaitBlk (ereal s1) p rdy, OutBlock ch1 v1]@tr')
         (tr @ [InBlock ch2 v2] @tr'') x \<Longrightarrow> fst rdy \<subseteq> d \<Longrightarrow> snd rdy \<subseteq> b \<Longrightarrow>
       commit chs (cW (ereal s2) (a, b) (c, d)) tr \<Longrightarrow> False"
proof(induction "length tr" arbitrary: s1 s2 tr p x rule: less_induct)
  case less
  thm less
  show ?case 
    apply(rule commitWE[of chs "(ereal s2)" a b c d tr])
    subgoal using less by auto
    subgoal for rdy' p'
      using less
      apply auto
      apply(elim combine_blocks_waitE4)
         apply auto
      subgoal 
        apply(cases rdy)
        apply(cases rdy')
        by auto
      by(auto elim: sync_elims)
    subgoal for rdy' ss1 p' ss2 tr2
      using less(6)
      thm less
      apply auto
      apply(cases "s1<ss1")
      subgoal
        using less 
        by (metis add_increasing2 commit_W_prop3 inf.absorb_iff2 inf.orderE less_eq_ereal_def less_ereal.simps(1))
    apply(cases "s1>ss1")
    subgoal
      apply(cases ss1)
      apply auto
      apply(elim combine_blocks_waitE4)
        apply auto
      subgoal 
        using less
        apply(cases rdy)
        apply(cases rdy')
        by auto
      subgoal for r tr'
        apply(cases ss2)
          apply auto
        subgoal for r'
          using less(1)[of tr2 r' "s1-r" "(\<lambda>t. p (t + r))" tr']
          using less by auto
        done
      done
    apply(cases "s1=ss1")
    subgoal
      apply simp
      apply(elim combine_blocks_waitE2)
        using less
           apply auto
        subgoal 
        apply(cases rdy)
        apply(cases rdy')
          by auto
        apply(rule commitWE[of chs ss2 a b c d tr2])
          apply auto
        by(auto elim: sync_elims)
      by auto
    done
qed


lemma commit_W_prop5:" ch1\<in>chs \<Longrightarrow> ch2\<in>chs \<Longrightarrow> s2>0 \<Longrightarrow> s1>0 \<Longrightarrow> 
       combine_blocks chs ([WaitBlk (ereal s1) p rdy, OutBlock ch1 v1]@tr')
         (tr @ [InBlock ch2 v2] @tr'') x \<Longrightarrow> fst rdy \<subseteq> d \<Longrightarrow> snd rdy \<subseteq> b \<Longrightarrow>
       commit chs (cW (ereal s2) (a, b) (c, d)) tr \<Longrightarrow> s1=s2"
  using commit_W_prop4 commit_W_prop3
  by (metis linorder_less_linear)

lemma commit_W_prop6:" 0 < s \<Longrightarrow> ch \<in> chs \<Longrightarrow> 
    combine_blocks chs ([WaitBlk \<infinity> p rdy]@trr) (tr @ [InBlock ch v] @ tr'') x \<Longrightarrow>
    commit chs (cW (ereal s) (a, b) (c, d)) tr \<Longrightarrow> False"
proof(induction "length tr" arbitrary: s tr p x rule: less_induct)
  case less
  thm less
  show ?case 
    apply(rule commitWE[of chs s a b c d tr])
    subgoal using less by auto
    subgoal for rdy' p'
      using less(2,3,4,5)
      apply auto
      apply(cases "\<not> compat_rdy rdy rdy'")
      subgoal
        by(auto elim: sync_elims)
      subgoal
        apply(elim combine_blocks_waitE4)
           apply auto
        by(auto elim: sync_elims)
      done
    subgoal for rdy' s1 p' s2 tr2
      using less(2,3,4,5)
      apply auto
      apply(cases "\<not> compat_rdy rdy rdy'")
      subgoal
        by(auto elim: sync_elims)
      subgoal
        apply(cases s1)
        apply auto
        apply(elim combine_blocks_waitE4)
           apply auto
        apply(cases s2)
        apply auto
        subgoal for r tr' r'
          thm less(1)
          apply(rule less(1)[of tr2 r' "(\<lambda>t. p (t + r))" tr'])
              apply auto
          done
        done
      done
    done
qed


lemma commit_W_prop7:" s>0 \<Longrightarrow> 
       combine_blocks chs ([WaitBlk (ereal s) p rdy]@tr')(tr @tr'') x 
        \<Longrightarrow> fst rdy \<subseteq> d \<Longrightarrow> snd rdy \<subseteq> b \<Longrightarrow>
       commit chs (cW (ereal s) (a, b) (c, d)) tr \<Longrightarrow> 
       \<exists> x' . combine_blocks chs (tr') (tr'') x'"
  proof(induction "length tr" arbitrary: s tr p x rule: less_induct)
    case less
    show ?case 
      using less(6)
      apply(rule commitWE[of chs s a b c d tr])
      subgoal for rdy' p'
        using less
        apply auto
        apply(elim combine_blocks_waitE2)
        apply auto
         apply(cases rdy)
         apply(cases rdy')
        by auto
      subgoal for rdy' s1 pp s2 tr2
        using less(2,3,4,5,6)
        apply auto
        apply(cases s1)
          apply(cases s2)
        subgoal for r1 r2
          apply auto
          apply(elim combine_blocks_waitE4)
             apply auto
          subgoal
            apply(cases rdy)
            apply(cases rdy')
            by auto
          subgoal for x'
            using less(1)[of tr2 r2 "(\<lambda>t. p (t + r1))" x']
            by auto
          done
           apply auto
        done
      done
  qed


lemma combine_wait_block_prop:"
    d1 > 0 \<Longrightarrow> d2 > 0 \<Longrightarrow> p1 d1 = p2 0 \<Longrightarrow>
    Ex (combine_blocks chs tr3 (trf @ WaitBlk (ereal d1 + d2) 
                (\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1)) rdy # trl)) \<longleftrightarrow> 
    Ex (combine_blocks chs tr3 (trf @ [WaitBlk (ereal d1) p1 rdy,WaitBlk d2 p2 rdy] @ trl))"
  apply auto
  subgoal for tr
  proof(induction "length trf + length tr3" arbitrary: trf tr3 tr d1 p1 rule: less_induct)
    case less
    show ?case 
      apply(cases trf)
      subgoal
        apply(cases tr3)
        subgoal
          using less
          apply auto
          apply(cases d2)
          by(auto elim!: sync_elims)
        subgoal for g tr3'
          apply(cases g)
          subgoal for io ch d
            using less(2,3,4,5)
            apply auto
            apply(cases "ch\<in>chs")
            subgoal
              by(auto elim: sync_elims)
            apply(elim combine_blocks_unpairE3)
             apply simp
            subgoal for tr'
            using less(1)[of "[]" tr3' d1 p1 tr']
            apply auto
            subgoal for x
              apply(rule exI[where x=" CommBlock io ch d # x"])
              apply(rule combine_blocks_unpair1)
              by auto
            done
          done
        subgoal for t' p' rdy''
          apply(cases "\<exists> t p rdy'. g = WaitBlk t p rdy'")
          subgoal apply auto
            subgoal for t p a b
              apply(cases "\<not> compat_rdy (a,b) rdy")
              subgoal using less(5) apply simp
                apply(elim combine_blocks_waitE1)
                by auto
              apply simp
              apply(cases "t\<le>0")
              subgoal 
                using less(2,3,4,5)
                apply simp
                apply(elim combine_blocks_wait_nopo)
                by auto
              apply(cases t)
              subgoal for tt
                using less(2,3,4,5)
                apply auto
                apply(cases "tt<d1")
                subgoal
                  apply(elim combine_blocks_waitE3)
                     apply auto
                  subgoal by (meson ereal_le_add_self ereal_le_less less_eq_ereal_def)
                  subgoal for tr'
                    using less(1)[of "[]" tr3' "d1-tt" "\<lambda> t. p1(t+tt)" tr']
                    apply simp
                    apply(subgoal_tac"(ereal (d1 - tt) + d2) = (ereal d1 + d2 - ereal tt)")
                     prefer 2
                    subgoal using ereal_diff_add_assoc2 ereal_minus(1) by presburger
                    apply(subgoal_tac"(\<lambda>t. if t \<le> d1 - tt then p1 (t + tt) else p2 (t - (d1 - tt))) = (\<lambda>t. if t + tt \<le> d1 then p1 (t + tt) else p2 (t + tt - d1))")
                     prefer 2
                    subgoal apply(rule ext) by (smt (z3))
                    apply auto
                    subgoal for tf'
                      apply(rule exI[where x=" WaitBlk (ereal tt) (\<lambda>t. ParState (p t) (p1 t)) (merge_rdy (a, b) rdy) # tf'"])
                      apply(rule combine_blocks_wait2)
                      by auto
                    done
                  done
                apply(cases "tt=d1")
                subgoal
                  apply(elim combine_blocks_waitE3)
                     apply auto
                  subgoal by (smt (verit, best) add.commute add_diff_eq_ereal add_nonneg_eq_0_iff ereal_le_add_self ereal_less(2) ereal_minus(1) less_eq_ereal_def zero_ereal_def)
                  subgoal for tr'
                    apply(subgoal_tac"WaitBlk (ereal d1 + d2 - ereal d1)(\<lambda>t. if t \<le> 0 then p1 (t + d1) else p2 (t + d1 - d1)) rdy = WaitBlk d2 p2 rdy")
                     prefer 2
                    subgoal apply(rule WaitBlk_ext)
                      subgoal by (simp add: ereal_diff_add_assoc2)
                      by auto
                    apply simp
                    apply(rule exI[where x=" WaitBlk (ereal d1) (\<lambda>t. ParState (p t) (p1 t)) (merge_rdy (a, b) rdy) # tr'"])
                    apply(rule combine_blocks_wait1)
                    by auto
                  done
                apply(cases d2)
                  apply auto
                subgoal for d2'
                  apply(cases "tt<d1+d2'")
                  subgoal
                    apply(elim combine_blocks_waitE3)
                       apply auto
                    subgoal for tr'
                      apply(rule exI[where x= "WaitBlk (ereal d1) (\<lambda>t. ParState (p t) (p1 t))(merge_rdy (a, b) rdy) #  (WaitBlk (ereal (tt - d1)) (\<lambda>t. ParState (p (t+d1)) (p2 t)) (merge_rdy (a, b) rdy) #  tr')"])
                      apply(rule combine_blocks_wait3)
                           apply auto
                      apply(rule combine_blocks_wait2)
                           apply auto
                      apply(subgoal_tac"WaitBlk (ereal (d1 + d2' - tt))(\<lambda>t. if t + tt \<le> d1 then p1 (t + tt) else p2 (t + tt - d1)) rdy = 
                                        WaitBlk (ereal (d2' - (tt - d1))) (\<lambda>\<tau>. p2 (\<tau> + (tt - d1))) rdy")
                       apply simp
                      apply(rule WaitBlk_ext)
                        apply auto by (metis add_diff_eq)
                    done
                  apply(cases "tt = d1 + d2'")
                  subgoal
                    apply simp
                    apply(elim combine_blocks_waitE2)
                      apply auto
                    subgoal for tr'
                      apply(rule exI[where x="WaitBlk (ereal d1) (\<lambda>t. ParState (p t) (p1 t))(merge_rdy (a, b) rdy) #  (WaitBlk (ereal d2') (\<lambda>t. ParState (p (t+d1)) (p2 t)) (merge_rdy (a, b) rdy) #  tr')"])
                      apply(rule combine_blocks_wait3)
                           apply auto
                      apply(rule combine_blocks_wait1)
                      by auto
                    done
                  apply(cases "tt > d1 + d2'")
                  subgoal
                    apply simp
                    apply(elim combine_blocks_waitE4)
                      apply auto
                    subgoal for tr'
                      apply(rule exI[where x="WaitBlk (ereal d1) (\<lambda>t. ParState (p t) (p1 t))(merge_rdy (a, b) rdy) #  (WaitBlk (ereal d2') (\<lambda>t. ParState (p (t+d1)) (p2 t)) (merge_rdy (a, b) rdy) #  tr')"])
                      apply(rule combine_blocks_wait3)
                           apply auto
                      apply(rule combine_blocks_wait3)
                           apply auto
                      apply(subgoal_tac"WaitBlk (ereal (tt - (d1 + d2'))) (\<lambda>t. p (t + (d1 + d2'))) (a, b) = WaitBlk (ereal (tt - d1 - d2')) (\<lambda>\<tau>. p (\<tau> + d2' + d1)) (a, b)")
                      prefer 2
                       apply(rule WaitBlk_ext)
                        apply auto
                      by (metis (no_types, opaque_lifting) add.assoc add.commute)
                    done
                  by auto
                apply(elim combine_blocks_waitE3)
                      apply auto
                subgoal for tr'
                  apply(rule exI[where x= "WaitBlk (ereal d1) (\<lambda>t. ParState (p t) (p1 t))(merge_rdy (a, b) rdy) #  (WaitBlk (ereal (tt - d1)) (\<lambda>t. ParState (p (t+d1)) (p2 t)) (merge_rdy (a, b) rdy) #  tr')"])
                  apply(rule combine_blocks_wait3)
                  apply auto
                  apply(rule combine_blocks_wait2)
                       apply auto
                  apply(subgoal_tac"WaitBlk \<infinity> (\<lambda>t. if t + tt \<le> d1 then p1 (t + tt) else p2 (t + tt - d1)) rdy = WaitBlk \<infinity> (\<lambda>\<tau>. p2 (\<tau> + (tt - d1))) rdy")
                   prefer 2
                  apply(rule WaitBlk_ext)
                     apply auto
                  by (simp add: add_diff_eq)
                done
              subgoal
                using less(2,3,4,5)
                apply auto
                apply(cases d2)
                  apply auto
                subgoal for d2'
                  apply(elim combine_blocks_waitE4)
                  apply auto
                  subgoal for tr'
                    apply(rule exI[where x="WaitBlk (ereal d1) (\<lambda>t. ParState (p t) (p1 t))(merge_rdy (a, b) rdy) #  (WaitBlk (ereal d2') (\<lambda>t. ParState (p (t+d1)) (p2 t)) (merge_rdy (a, b) rdy) #  tr')"])
                    apply(rule combine_blocks_wait3)
                         apply auto
                    apply(rule combine_blocks_wait3)
                         apply auto
                    apply(subgoal_tac"WaitBlk \<infinity> (\<lambda>t. p (t + (d1 + d2'))) (a, b) = WaitBlk \<infinity> (\<lambda>\<tau>. p (\<tau> + d2' + d1)) (a, b)")
                     prefer 2
                     apply(rule WaitBlk_ext)
                       apply auto
                    by (simp add: add.commute add.left_commute)
                  done
                apply(elim combine_blocks_waitE2)
                  apply auto
                subgoal for tr'
                  apply(rule exI[where x="WaitBlk (ereal d1) (\<lambda>t. ParState (p t) (p1 t))(merge_rdy (a, b) rdy) #  (WaitBlk \<infinity> (\<lambda>t. ParState (p (t+d1)) (p2 t)) (merge_rdy (a, b) rdy) #  tr')"])
                  apply(rule combine_blocks_wait3)
                         apply auto
                  apply(rule combine_blocks_wait1)
                  by auto
                done
              by auto
            done
          subgoal using less(5) apply auto
            using combine_blocks.cases
            by (smt (z3) WaitBlk_not_Comm(1) \<open>\<lbrakk>trf = []; tr3 = g # tr3'; g = WaitBlock t' p' rdy''; \<exists>t p rdy'. g = WaitBlk t p rdy'\<rbrakk> \<Longrightarrow> Ex (combine_blocks chs tr3 (trf @ WaitBlk (ereal d1) p1 rdy # WaitBlk d2 p2 rdy # trl))\<close> append_self_conv2 list.inject trace_block.distinct(1))
          done
        done
      done
    subgoal for tra trlist
      using less(5)
      apply(induct rule: combine_blocks.cases, auto)
      subgoal for ch blks1 blks v
        using less(1)[of trlist blks1 d1 p1 blks]
        using less(2,3,4)
        apply auto
        subgoal for x
          apply(rule exI[where x="IOBlock ch v # x"])
          apply(rule )
          by auto
        done
      subgoal for ch blks1 blks v
        using less(1)[of trlist blks1 d1 p1 blks]
        using less(2,3,4)
        apply auto
        subgoal for x
          apply(rule exI[where x="IOBlock ch v # x"])
          apply(rule )
          by auto
        done
      subgoal for ch blks1 blks ch_type v
        using less(1)[of trf blks1 d1 p1 blks]
        using less(2,3,4)
        apply auto
        subgoal for x
          apply(rule exI[where x="CommBlock ch_type ch v # x"])
          apply(rule )
          by auto
        done
      subgoal for ch blks ch_type v
        using less(1)[of trlist tr3 d1 p1 blks]
        using less(2,3,4)
        apply auto
        subgoal for x
          apply(rule exI[where x="CommBlock ch_type ch v # x"])
          apply(rule )
          by auto
        done
      subgoal for blks1 blks a1 b1 a2 b2 t hist1 hist2
        using less(1)[of trlist blks1 d1 p1 blks]
        using less(2,3,4)
        apply auto
        subgoal for x
          apply(rule exI[where x="WaitBlk t (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2) # x"])
          apply(rule )
          by auto
        done
      subgoal for blks1 t2 t1 hist2 a1 b1 blks a2 b2 hist1
        using less(1)[of "WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) (a1, b1) # trlist" blks1 d1 p1 blks]
        using less(2,3,4)
        apply auto
        subgoal for x
          apply(rule exI[where x="WaitBlk (ereal t1) (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2) # x"])
          apply(rule )
          by auto
        done
      subgoal for t1 t2 hist1 a1 b1 blks1 blks a2 b2 hist2
        using less(1)[of trlist "(WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) (a1, b1) # blks1)" d1 p1 blks]
        using less(2,3,4)
        apply auto
        subgoal for x
          apply(rule exI[where x="WaitBlk (ereal t2) (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2)  # x"])
          apply(rule )
          by auto
        done
      done
    done
qed
  subgoal for tr
    proof(induction "length trf + length tr3" arbitrary: trf tr3 tr d1 p1 rule: less_induct)
      case less
      show ?case 
        using less(5)
        apply(induct rule: combine_blocks.cases, auto)
        subgoal for ch blks1 blks2 blks v
          apply (cases trf)
           apply auto
          subgoal for trfl
            using less(1)[of trfl blks1 d1 p1 blks]
            using less(2,3,4,5)
            apply auto
            subgoal for x
              apply(rule exI[where x="IOBlock ch v # x"])
              apply(rule )
              by auto
            done
          done
        subgoal for ch blks1 blks2 blks v
          apply(cases trf)
           apply auto
          subgoal for trfl
            using less(1)[of trfl blks1 d1 p1 blks]
            using less(2,3,4,5)
            apply auto
            subgoal for x
              apply(rule exI[where x="IOBlock ch v # x"])
              apply rule
              by auto
            done
          done
        subgoal for ch blks1 blks ch_type v
          using less(1)[of trf blks1 d1 p1 blks]
          using less(2,3,4,5)
          apply auto
          subgoal for x
            apply(rule exI[where x="CommBlock ch_type ch v # x"])
            apply rule
            by auto
          done
        subgoal for ch blks2 blks ch_type v
          apply(cases trf)
           apply auto
          subgoal for trfl
            using less(1)[of trfl tr3 d1 p1 blks]
            using less(2,3,4,5)
            apply auto
            subgoal for x
              apply(rule exI[where x="CommBlock ch_type ch v # x"])
              apply rule
              by auto
            done
          done
        subgoal for blks1 blks2 blks a1 b1 a2 b2 t hist1 hist2
          apply(cases trf)
           apply auto
          subgoal
            using WaitBlk_cong[of "(ereal d1)" p1 rdy t hist2 "(a2, b2)"]
            apply auto
            using less(2,3,4)
            apply auto
            apply(rule exI[where x="WaitBlk (ereal d1) (\<lambda>\<tau>. ParState (hist1 \<tau>) (if \<tau> \<le> d1 then p1 \<tau> else p2 (\<tau> - d1))) (a1 \<union> a2, b1 \<union> b2) # blks"])
            apply(rule )
                 apply auto
            subgoal
              apply(subgoal_tac"WaitBlk d2 p2 (a2, b2) = WaitBlk (ereal d1 + d2 - ereal d1) (\<lambda>\<tau>. if \<tau> \<le> 0 then p1 (\<tau> + d1) else p2 (\<tau> + d1 - d1)) (a2, b2)")
               prefer 2
               apply(rule WaitBlk_ext)
                 apply auto
              using ereal_0_plus ereal_diff_add_assoc2 ereal_minus(1) by auto
            by (smt (verit) add_nonneg_pos diff_add_eq_ereal ereal_diff_positive ereal_le_add_self ereal_less(2) ereal_minus(1) less_eq_ereal_def)
          subgoal for trfl
            using less(1)[of trfl blks1 d1 p1 blks]
            using less(2,3,4)
            apply auto
            subgoal for x
              apply(rule exI[where x="WaitBlk t (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2) # x"])
              apply(rule)
              by auto
            done
          done
        subgoal for blks1 t2 t1 hist2 a1 b1 blks2 blks a2 b2 hist1
          apply(cases trf)
           apply auto
          subgoal
            using WaitBlk_cong[of "(ereal d1)" p1 rdy t2 hist2 "(a1, b1)"]
            using WaitBlk_cong2[of "(ereal d1)" p1 rdy t2 hist2 "(a1, b1)"]
            apply auto
            using less(1)[of "[]" blks1 "d1-t1" "(\<lambda>\<tau>. hist2 (\<tau> + t1))" blks]
            using less(2,3,4)
            apply auto
            subgoal for x
              apply(rule exI[where x="WaitBlk (ereal t1) (\<lambda>\<tau>. ParState (hist1 \<tau>) (if \<tau> \<le> d1 then p1 \<tau> else p2 (\<tau> - d1))) (a2 \<union> a1, b2 \<union> b1) # x"])
              apply(rule )
                   apply auto
              subgoal
                apply(subgoal_tac"WaitBlk (ereal (d1 - t1) + d2)
       (\<lambda>t. if t \<le> d1 - t1 then hist2 (t + t1) else p2 (t - (d1 - t1))) (a1, b1) = WaitBlk (ereal d1 + d2 - ereal t1)
       (\<lambda>\<tau>. if \<tau> + t1 \<le> d1 then p1 (\<tau> + t1) else p2 (\<tau> + t1 - d1)) (a1, b1)")
                 prefer 2
                 apply(rule WaitBlk_ext)
                   apply auto
                using ereal_diff_add_assoc2 ereal_minus(1) apply presburger
                by (metis diff_diff_eq2)
              by (meson ereal_le_add_self ereal_le_less less_eq_ereal_def)
            done
          subgoal for trfl
            using less(1)[of "WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) (a1, b1) # trfl" blks1 d1 p1 blks]
            using less(2,3,4)
            apply auto
            subgoal for x
              apply(rule exI[where x="WaitBlk (ereal t1) (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a2 \<union> a1, b2 \<union> b1) # x"])
              apply rule
              by auto
            done
          done
        subgoal for t1 t2 hist1 a1 b1 blks1 blks2 blks a2 b2 hist2
          apply(cases trf)
           apply auto
          subgoal
            using WaitBlk_cong[of "(ereal d1)" p1 rdy "(ereal t2)" hist2 "(a2, b2)"]
            using WaitBlk_cong2[of "(ereal d1)" p1 rdy "(ereal t2)" hist2 "(a2, b2)"]
            apply auto
            apply(cases "(t1 - ereal t2)< d2")
            subgoal
              apply(cases t1)
                apply auto
              subgoal for t1'
                apply(elim combine_blocks_waitE3[of chs "(t1' - t2)"])
                   apply auto
                subgoal for x
                  apply(rule exI[where x="WaitBlk (ereal t1') (\<lambda>\<tau>. ParState (hist1 \<tau>) (if \<tau> \<le> t2 then p1 \<tau> else p2 (\<tau> - t2))) (merge_rdy (a1, b1) (a2, b2)) # x"])
                  apply(rule)
                       apply auto
                  subgoal
                    apply(subgoal_tac"WaitBlk (d2 - ereal (t1' - t2)) (\<lambda>t. p2 (t + (t1' - t2))) (a2, b2) = WaitBlk (ereal t2 + d2 - ereal t1')
                        (\<lambda>\<tau>. if \<tau> + t1' \<le> t2 then p1 (\<tau> + t1') else p2 (\<tau> + t1' - t2)) (a2, b2)")
                     prefer 2
                     apply(rule WaitBlk_ext)
                       apply auto
                     apply(cases d2,auto)
                    by (metis (no_types, opaque_lifting) add_diff_cancel_right diff_add_cancel)
                  by(cases d2,auto)
                done
              done
            apply(cases "(t1 - ereal t2) = d2")
            subgoal
              using less(2,3,4)
              apply auto
              apply(elim combine_blocks_waitE2)
                apply auto
              subgoal for x
                apply(subgoal_tac"(ereal t2 + (t1 - ereal t2)) = t1")
                 prefer 2
                subgoal by (simp add: add_diff_eq_ereal ereal_diff_add_assoc2)
                apply auto
                apply(rule exI[where x="WaitBlk t1 (\<lambda>\<tau>. ParState (hist1 \<tau>) (if \<tau> \<le> t2 then p1 \<tau> else p2 (\<tau> - t2))) (merge_rdy (a1, b1) (a2, b2)) # x"])
                apply rule
                    apply auto
                by (metis add_pos_pos ereal_less(2))
              done
            apply(cases "(t1 - ereal t2) > d2")
            subgoal
              using less(2,3,4)
              apply auto
              apply(cases d2)
                apply auto
              subgoal for d2'
              apply(elim combine_blocks_waitE4[of chs "(t1 - ereal t2)"])
                   apply auto
                subgoal for x
                  apply(rule exI[where x="WaitBlk (ereal (t2 + d2')) (\<lambda>\<tau>. ParState (hist1 \<tau>) (if \<tau> \<le> t2 then p1 \<tau> else p2 (\<tau> - t2))) (merge_rdy (a1, b1) (a2, b2)) # x"])
                  apply rule
                       apply auto
                  subgoal
                    apply(subgoal_tac"WaitBlk (t1 - ereal t2 - ereal d2') (\<lambda>t. hist1 (t + d2' + t2)) (a1, b1) = WaitBlk (t1 - ereal (t2 + d2')) (\<lambda>\<tau>. hist1 (\<tau> + (t2 + d2'))) (a1, b1)")
                     prefer 2
                     apply(rule WaitBlk_ext)
                       apply auto
                     apply(cases t1,auto)
                    by (metis (no_types, opaque_lifting) add.assoc add.commute)
                  by(cases t1,auto)
                done
              done
            by auto
          subgoal for trfl
            using less(1)[of trfl "(WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) (a1, b1) # blks1)" d1 p1 blks]
            using less(2,3,4)
            apply auto
            subgoal for x
              apply(rule exI[where x="WaitBlk (ereal t2) (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a2 \<union> a1, b2 \<union> b1) # x"])
              apply rule
              by auto
            done
          done
        done
  qed
  done
            

            

fun constrain :: "cname set \<Rightarrow> trace \<Rightarrow> trace" where
  "constrain chs [] = []"
| "constrain chs ((InBlock ch v)# tr) = 
      (if ch \<in> chs then ((InBlock ch v) # tr) else tr)"
| "constrain chs ((OutBlock ch v)# tr) = 
      (if ch \<in> chs then ((OutBlock ch v) # tr) else tr)"
| "constrain chs ((IOBlock ch v)# tr) = 
      (if ch \<in> chs then ((IOBlock ch v) # tr) else tr)"
| "constrain chs (WaitBlock d p rdy # tr) = (WaitBlock d p rdy # tr)"


definition Validc :: "cname set \<Rightarrow> assn \<Rightarrow> ctr \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> ctr \<Rightarrow> bool" ("\<Turnstile>c(_) ({(1_),(2_)}/ (_)/ {(1_),(2_)})" 70) where
  "\<Turnstile>c(chs) {P,a} S {Q,g} \<longleftrightarrow> 
           (\<forall>s1 tr1. (\<forall> s2 tr2 tr2' tr3 tr3' tr4. P s1 tr1 \<longrightarrow> big_step S s1 tr2 s2 \<longrightarrow>
                        commit chs a tr3 \<longrightarrow> combine_blocks chs (tr2@tr2') (tr3@tr3') tr4 \<longrightarrow> Q s2 (tr1 @ tr2) 
                      \<and> commit chs g tr2 \<and> (\<exists> tr4'. combine_blocks chs (tr2') (tr3') tr4')))"


lemma Validc_skip:
"\<Turnstile>c(chs) {P,cE} Skip {P,cE}"
  unfolding Validc_def apply auto
    apply(auto elim!: skipE commitEE)
  apply rule
  done


lemma Validc_in1:
" ch\<in>chs \<Longrightarrow>
  \<Turnstile>c(chs) {\<lambda> s t. s = ss \<and> P s t,cI ch} Cm (ch[!]e) {(\<lambda> s t. s = ss \<and> (P s @\<^sub>t Out0\<^sub>t ch (e ss)) t),(cO ch (e ss))}"
  unfolding Validc_def apply (auto simp add:join_assn_def)
  subgoal 
    by(auto elim!: sendE commitIE)
  subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(rule exI[where x= tr1])
    apply(auto elim!: sendE commitIE)
      apply(rule)
    by(auto elim: sync_elims)
  subgoal for s1 tr1 s2 tr2 tr3 x
    apply(auto elim!: sendE commitIE)
      apply(rule ) 
    by(auto elim: sync_elims)
  subgoal for s1 tr1 s2 tr2 tr3 x
    apply(auto elim!: sendE commitIE)
    apply(auto elim: sync_elims) 
    done
  done


lemma Validc_in2:
" ch\<in>chs \<Longrightarrow> d>0 \<Longrightarrow> d<PInfty \<Longrightarrow>
  \<Turnstile>c(chs) {\<lambda> s t. s= ss \<and> P s t,cW d ({},{}) ({},{ch}) [@] cI ch} Cm (ch[!]e) {(\<lambda> s t. s=ss \<and> (P s @\<^sub>t (Wait\<^sub>t d (\<lambda>_ . State ss) ({ch},{})) @\<^sub>t Out0\<^sub>t ch (e ss)) t),(cW d ({ch},UNIV-{ch}) ({},UNIV) [@]cO ch (e ss))}"
  unfolding Validc_def apply (auto simp add:join_assn_def)
  subgoal 
    by(auto elim!: sendE commitIE commitSE)
  subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: sendE commitIE commitSE)
    subgoal
      using commit_W_prop2 
      by (metis append.left_neutral append_Cons commit_W_prop1)
    subgoal for tr3'' v dd
      using commit_W_prop5[of ch chs ch d dd "(\<lambda>_. State ss)" "({ch}, {})" "(e ss)" tr2' tr3'' v tr3' x "{ch}" "{}" "{}" "{}"]
      apply auto
      apply(rule exI[where x=tr1])
      apply auto
      apply(rule exI[where x="[WaitBlk (ereal d) (\<lambda>_. State ss) ({ch}, {})]"])
      apply auto 
       apply(rule ) apply auto
      apply(rule )
      done
    subgoal for tr3'' v
      using commit_W_prop6[of d ch chs "(\<lambda>_. State ss)" "({ch}, {})" tr2' tr3'' v tr3' x "{}""{}" "{}" "{ch}"]
      by auto
    done
 subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: sendE commitIE commitSE)
    subgoal
      using commit_W_prop2 
      by (metis append.left_neutral append_Cons commit_W_prop1)
    subgoal for tr3'' v dd
      using commit_W_prop5[of ch chs ch d dd "(\<lambda>_. State ss)" "({ch}, {})" "(e ss)" tr2' tr3'' v tr3' x "{ch}" "{}" "{}" "{}"]
      apply auto
      using commitseq1[of chs "cW (ereal d) ({ch}, UNIV - {ch}) ({}, UNIV)" "[WaitBlk (ereal d) (\<lambda>_. State ss) ({ch}, {})]" "cO ch (e ss)" "[OutBlock ch (e ss)]"]
      apply auto
      using commitW1 commitO1
      by auto
    subgoal for tr3'' v
      using commit_W_prop6[of d ch chs "(\<lambda>_. State ss)" "({ch}, {})" tr2' tr3'' v tr3' x "{}""{}" "{}" "{ch}"]
      by auto
    done
  subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: sendE commitIE commitSE)
    subgoal
      using commit_W_prop2 
      by (metis append.left_neutral append_Cons commit_W_prop1)
    subgoal for tr3'' v dd
      using commit_W_prop5[of ch chs ch d dd "(\<lambda>_. State ss)" "({ch}, {})" "(e ss)" tr2' tr3'' v tr3' x "{ch}" "{}" "{}" "{}"]
      apply auto
      using commit_W_prop7[of d chs "(\<lambda>_. State ss)" "({ch}, {})" "OutBlock ch (e ss) # tr2'" tr3'' "InBlock ch v # tr3'" x "{ch}" "{}" "{}" "{}"]
      apply auto
      by(auto elim: sync_elims) 
    subgoal for tr3'' v
      using commit_W_prop6[of d ch chs "(\<lambda>_. State ss)" "({ch}, {})" tr2' tr3'' v tr3' x "{}""{}" "{}" "{ch}"]
      by auto
    done
  done

lemma Validc_wait1:
" \<Turnstile>c(chs) {\<lambda> s t. s = ss \<and> P s t,if e ss \<le>0 then cE else cW (e ss) ({},{}) ({},{})} Wait e {(\<lambda> s t . s = ss \<and> (P s @\<^sub>t Wait\<^sub>t (e ss) (\<lambda>_ . State s) ({},{})) t),(if e ss \<le> 0 then cE else cW (e ss) ({},UNIV) ({},UNIV))}"
  unfolding Validc_def apply (auto simp add:join_assn_def)
  subgoal 
    by(auto elim!: waitE)
  subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: waitE)
    apply(rule exI[where x=tr1])
    by(auto simp add: emp_assn_def)
  subgoal 
    apply(auto elim!: waitE)
    apply(rule ) 
    done
  subgoal 
    by(auto elim!: waitE commitEE)
  subgoal 
    by(auto elim!: waitE commitEE)
  subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: waitE)
    apply(rule exI[where x=tr1])
    apply auto
    apply(rule )
    by auto
  subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: waitE)
    apply(rule )
    by auto
  subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: waitE commitEE)
    using commit_W_prop7[of "e ss" chs "(\<lambda>_. State ss)" "({}, {})" tr2' tr3 tr3' x "{}" "{}" "{}" "{}"]
    apply auto
    done
  done

lemma Validc_seq1:
  assumes" \<Turnstile>c(chs) {P,a1} T1 {Q,g1} "
     and " \<Turnstile>c(chs) {Q,a2} T2 {R,g2} "
   shows " \<Turnstile>c(chs) {P,a1[@]a2} T1;T2 {R,g1[@]g2}"
  unfolding Validc_def apply clarify
  subgoal for s1 tr1 s2 tr2 tr2' tr3 tr3' tr4
    apply (elim seqE commitSE)
    subgoal premises pre for tr1a s2a tr2a tr1aa tr2aa
      thm pre
    proof-
      have 1:"P s1 tr1 \<longrightarrow>
              big_step T1 s1 tr1a s2a \<longrightarrow>
              commit chs a1 tr1aa \<longrightarrow>
              combine_blocks chs (tr1a @ (tr2a @ tr2')) (tr1aa @ (tr2aa @ tr3')) tr4 \<longrightarrow>
              Q s2a (tr1 @ tr1a) \<and>
              commit chs g1 tr1a \<and> Ex (combine_blocks chs (tr2a @ tr2') (tr2aa @ tr3'))"
        using assms(1) unfolding Validc_def 
        apply (elim allE)
        by auto
      have 2:"Q s2a (tr1 @ tr1a) \<and>
              commit chs g1 tr1a \<and> Ex (combine_blocks chs (tr2a @ tr2') (tr2aa @ tr3'))"
        using 1 pre by auto
      obtain tr4' where 3:"combine_blocks chs (tr2a @ tr2') (tr2aa @ tr3') tr4'"
        using 2 by auto
      have 4:"Q s2a (tr1 @ tr1a) \<longrightarrow>
              big_step T2 s2a tr2a s2 \<longrightarrow>
              commit chs a2 tr2aa \<longrightarrow>
              combine_blocks chs (tr2a @ tr2') (tr2aa @ tr3') tr4' \<longrightarrow>
              R s2 (tr1 @ tr1a @ tr2a) \<and>
              commit chs g2 tr2a \<and> Ex (combine_blocks chs tr2' tr3')"
          using assms(2) unfolding Validc_def 
          apply (elim allE)
        by auto
      have 5:"R s2 (tr1 @ tr1a @ tr2a) \<and>
              commit chs g2 tr2a \<and> Ex (combine_blocks chs tr2' tr3')"
        using 2 3 4 pre by auto
      show ?thesis
        using pre 2 5 apply auto
        apply(rule )
        by auto
    qed
    subgoal for tr1a sm tr2a trf d1 p1 rdy d2 p2 trl
      apply simp
      apply(subgoal_tac "Ex (combine_blocks chs (tr1a @ tr2a @ tr2')
         (trf @ WaitBlk (ereal d1) p1 rdy # WaitBlk d2 p2 rdy # trl @ tr3'))")
       prefer 2
      subgoal
        using combine_wait_block_prop[of d1 d2 p1 p2 chs "(tr1a @ tr2a @ tr2')" trf rdy "trl @ tr3'"]
        by auto
      apply clarify
      subgoal premises pre for tr4'
        thm pre
      proof-
      have 1:"P s1 tr1 \<longrightarrow>
              big_step T1 s1 tr1a sm \<longrightarrow>
              commit chs a1 (trf @ [WaitBlk (ereal d1) p1 rdy]) \<longrightarrow>
              combine_blocks chs (tr1a @ (tr2a @ tr2')) ((trf @ [WaitBlk (ereal d1) p1 rdy]) @ (WaitBlk d2 p2 rdy # trl @ tr3')) tr4' \<longrightarrow>
              Q sm (tr1 @ tr1a) \<and>
              commit chs g1 tr1a \<and> Ex (combine_blocks chs (tr2a @ tr2') (WaitBlk d2 p2 rdy # trl @ tr3'))"
        using assms(1) unfolding Validc_def 
        apply (elim allE)
        by auto
      have 2:"Q sm (tr1 @ tr1a) \<and>
              commit chs g1 tr1a \<and> Ex (combine_blocks chs (tr2a @ tr2') (WaitBlk d2 p2 rdy # trl @ tr3'))"
        using 1 pre by auto
      obtain tr4'' where 3:"combine_blocks chs (tr2a @ tr2') (WaitBlk d2 p2 rdy # trl @ tr3') tr4''"
        using 2 by auto
      have 4:"Q sm (tr1 @ tr1a) \<longrightarrow>
              big_step T2 sm tr2a s2 \<longrightarrow>
              commit chs a2 (WaitBlk d2 p2 rdy # trl) \<longrightarrow>
              combine_blocks chs (tr2a @ tr2') (WaitBlk d2 p2 rdy # trl @ tr3') tr4'' \<longrightarrow>
              R s2 (tr1 @ tr1a @ tr2a) \<and>
              commit chs g2 tr2a \<and> Ex (combine_blocks chs tr2' tr3')"
          using assms(2) unfolding Validc_def 
          apply (elim allE)
        by auto
      have 5:"R s2 (tr1 @ tr1a @ tr2a) \<and>
              commit chs g2 tr2a \<and> Ex (combine_blocks chs tr2' tr3')"
        using 2 3 4 pre by auto
      show ?thesis
        using pre 2 5 apply auto
        apply(rule )
        by auto
    qed

    done
  done
  done


lemma Validc_repn1:
  assumes"\<And> i. \<Turnstile>c(chs) {\<lambda> s t. s = ss i \<and> P s t,a (i+1)} S {\<lambda> s t. s = ss (i+1) \<and> P s t,g (i+1)} "
   shows " \<Turnstile>c(chs) {\<lambda> s t. s = ss 0 \<and> P s t,crepn N a} RepN N S {\<lambda> s t. s = ss N \<and> P s t,crepn N g}"
  unfolding Validc_def
  apply clarify
proof(induction N)
  case 0
  then show ?case 
    apply(auto elim!: skipE commitRNE)
    apply(rule)
    done
  next
    case (Suc N)
    have g:"\<And> i s1 tr1 s2 tr2 tr2' tr3 tr3' tr4.
     s1 = ss i \<and> P s1 tr1 \<longrightarrow>
     big_step S s1 tr2 s2 \<longrightarrow>
     commit chs (a (i + 1)) tr3 \<longrightarrow>
     combine_blocks chs (tr2 @ tr2') (tr3 @ tr3') tr4 \<longrightarrow>
     (s2 = ss (i + 1) \<and> P s2 (tr1 @ tr2)) \<and>
     commit chs (g (i + 1)) tr2 \<and> Ex (combine_blocks chs tr2' tr3')"
      subgoal for i s1 tr1 s2 tr2 tr2' tr3 tr3' tr4
      using assms[of i] 
      unfolding Validc_def
      by blast
    done
  show ?case 
    using Suc(2,3,4,5)
    apply(simp add: RepNf)
    apply(rule commitRNE[of chs "(Suc N)" a tr3])
    subgoal by auto
    subgoal by auto
    apply simp
    subgoal for i tr3a tr3b
      apply(elim seqE)
      subgoal for tr2a s1 tr2b
        apply simp
        using Suc(1)[of tr1 tr2a s1 tr3a "tr2b @ tr2'" "tr3b @ tr3'" tr4]
        apply simp
        apply clarify
        subgoal for tr4'
          using g[of s1 i "tr1 @ tr2a" tr2b s2 tr3b tr2' tr3' tr4']
          apply auto
          using commirepn2[of chs i g tr2a tr2b]
          by auto
        done
      done
    done
qed


fun sync_ctr :: "cname set \<Rightarrow> ctr \<Rightarrow> ctr \<Rightarrow> tassn" where
"sync_ctr chs C1 C2  tr \<longleftrightarrow> (\<exists>tr1 tr2. commit chs C1 tr1 \<and> commit chs C2 tr2 \<and> combine_blocks chs tr1 tr2 tr)"


fun get_in_ch :: "trace_block \<Rightarrow> cname" where
  "get_in_ch (InBlock ch v) = ch"
| "get_in_ch (OutBlock ch v) = undefined"
| "get_in_ch (IOBlock ch v) = undefined"
| "get_in_ch (WaitBlock d p rdy) = undefined"

fun check :: "ctr \<Rightarrow> trace \<Rightarrow> trace \<times> trace" where
  "check cE tr = ([],tr)"
| "check (cI ch) (tr) = 
    (if (\<exists> v tr'. tr = InBlock ch v # tr') then ([hd tr] , tl tr) else ([],tr))"
| "check (cO ch v) (tr) = 
    (if (\<exists> tr'. tr = OutBlock ch v # tr') then ([hd tr] , tl tr) else ([],tr))"


lemma Validc_para1:
  assumes" \<Turnstile>c(chs) {\<lambda>s tr. P1 s \<and> tr = [],a1} p1 {Q1,g1} "
     and " \<Turnstile>c(chs) {\<lambda>s tr. P2 s \<and> tr = [],a2} p2 {Q2,g2} "
     and " \<forall> tr. commit chs g1 tr \<longrightarrow> commit chs a2 tr"
     and " \<forall> tr. commit chs g2 tr \<longrightarrow> commit chs a1 tr"
   shows " \<Turnstile>\<^sub>p {par_assn (sing_assn P1) (sing_assn P2)} Parallel (Single p1) chs (Single p2) 
                              {sync_gassn chs (sing_gassn Q1) (sing_gassn Q2)}"
  unfolding ParValid_def 
  apply auto
  apply(auto elim!: ParallelE SingleE)
  subgoal for tr3 tr1 tr2 s11 s12 s21 s22
    using assms(1)
    unfolding Validc_def
    apply auto
    

    
      





end