theory Commit
  imports
    Complementlemma
begin


text \<open>Commitment\<close>

datatype ctr =
  cE
| cI cname real      
| cO cname real
| cW real "cname set \<times> cname set" "cname set \<times> cname set"
| cseq ctr ctr ("_[@] _" [91,90] 90)
(*
| cor ctr ctr ("_[\<or>] _" [86,85] 85) *)
| crepn nat "nat \<Rightarrow> ctr"
(*
| crep "nat \<Rightarrow> ctr" *)

inductive commit :: "cname set \<Rightarrow> ctr \<Rightarrow> trace \<Rightarrow> bool" where
  commitE: "commit chs cE []"
| commitI1: "ch \<in> chs \<Longrightarrow> commit chs (cI ch v) [InBlock ch v]"
| commitI2: "ch \<notin> chs \<Longrightarrow> commit chs (cI ch v) []"
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
inductive_cases commitIE: "commit chs (cI ch v) tr"
inductive_cases commitOE: "commit chs (cO ch v) tr"
inductive_cases commitWE: "commit chs (cW s (a,b) (c,d)) tr"
inductive_cases commitSE: "commit chs (cseq c1 c2) tr"
inductive_cases commitRNE: "commit chs (crepn i c) tr"
(*
inductive_cases commitRE: "commit chs (crep c) tr" *)


lemma commit_W_prop1:"commit chs (cW s (a,b) (c,d)) tr \<Longrightarrow> s>0"
  apply(rule commitWE[of chs s a b c d tr])
  by auto

  
lemma commit_W_prop2:" ch\<in>chs \<Longrightarrow> s>0 \<Longrightarrow> 
       combine_blocks chs ([OutBlock ch v]@tr) (tr1 @ tr2) x \<Longrightarrow>
       commit chs (cW s (a, b) (c, d)) tr1 \<Longrightarrow> False"
  apply(rule commitWE[of chs s a b c d tr1])
    apply auto
  by(auto elim: sync_elims)

lemma commit_W_prop3:" ch1\<in>chs \<Longrightarrow> ch2\<in>chs \<Longrightarrow> s1>0 \<Longrightarrow> s1<s2 \<Longrightarrow> 
       combine_blocks chs ([WaitBlk s1 p rdy, OutBlock ch1 v1]@tr')
         (tr @ [InBlock ch2 v2] @ tr'') x \<Longrightarrow> fst rdy \<subseteq> d \<Longrightarrow> snd rdy \<subseteq> b \<Longrightarrow>
       commit chs (cW s2 (a, b) (c, d)) tr \<Longrightarrow> False"
proof(induction "length tr" arbitrary: s1 s2 tr p x rule: less_induct)
  case less
  thm less
  show ?case 
    apply(rule commitWE[of chs "s2" a b c d tr])
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
      apply auto
      apply(elim combine_blocks_waitE4)
        apply auto
      subgoal 
        using less
        apply(cases rdy)
        apply(cases rdy')
        by auto
      subgoal for tr'
        using less(1)[of tr2 "s1-ss1" ss2 "(\<lambda>t. p (t + ss1))" tr']
          using less by auto
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
       combine_blocks chs ([WaitBlk s1 p rdy, OutBlock ch1 v1]@tr')
         (tr @ [InBlock ch2 v2] @tr'') x \<Longrightarrow> fst rdy \<subseteq> d \<Longrightarrow> snd rdy \<subseteq> b \<Longrightarrow>
       commit chs (cW s2 (a, b) (c, d)) tr \<Longrightarrow> False"
proof(induction "length tr" arbitrary: s1 s2 tr p x rule: less_induct)
  case less
  thm less
  show ?case 
    apply(rule commitWE[of chs s2 a b c d tr])
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
        by linarith
    apply(cases "s1>ss1")
    subgoal
      apply auto
      apply(elim combine_blocks_waitE4)
        apply auto
      subgoal 
        using less
        apply(cases rdy)
        apply(cases rdy')
        by auto
      subgoal for tr'
        subgoal 
          using less(1)[of tr2 ss2 "s1-ss1" "(\<lambda>t. p (t + ss1))" tr']
          using less by auto
        done
      done
    apply(cases "s1=ss1")
    subgoal
      apply simp
      apply(elim combine_blocks_waitE2)
        using less
           by auto
        subgoal 
        apply(cases rdy)
        apply(cases rdy')
          by auto
        done
    done
qed


lemma commit_W_prop5:" ch1\<in>chs \<Longrightarrow> ch2\<in>chs \<Longrightarrow> s2>0 \<Longrightarrow> s1>0 \<Longrightarrow> 
       combine_blocks chs ([WaitBlk s1 p rdy, OutBlock ch1 v1]@tr')
         (tr @ [InBlock ch2 v2] @tr'') x \<Longrightarrow> fst rdy \<subseteq> d \<Longrightarrow> snd rdy \<subseteq> b \<Longrightarrow>
       commit chs (cW s2 (a, b) (c, d)) tr \<Longrightarrow> s1=s2"
  using commit_W_prop4 commit_W_prop3
  by (metis linorder_less_linear)


lemma commit_W_prop7:" s>0 \<Longrightarrow> 
       combine_blocks chs ([WaitBlk s p rdy]@tr')(tr @tr'') x 
        \<Longrightarrow> fst rdy \<subseteq> d \<Longrightarrow> snd rdy \<subseteq> b \<Longrightarrow>
       commit chs (cW s (a, b) (c, d)) tr \<Longrightarrow> 
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
        subgoal 
          apply(elim combine_blocks_waitE4)
             apply auto
          subgoal
            apply(cases rdy)
            apply(cases rdy')
            by auto
          subgoal for x'
            using less(1)[of tr2 s2 "(\<lambda>t. p (t + s1))" x']
            by auto
          done
        done
      done
  qed


lemma combine_wait_block_prop:"
    d1 > 0 \<Longrightarrow> d2 > 0 \<Longrightarrow> p1 d1 = p2 0 \<Longrightarrow>
    Ex (combine_blocks chs tr3 (trf @ WaitBlk (d1 + d2) 
                (\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1)) rdy # trl)) \<longleftrightarrow> 
    Ex (combine_blocks chs tr3 (trf @ [WaitBlk d1 p1 rdy,WaitBlk d2 p2 rdy] @ trl))"
  apply auto
  subgoal for tr
  proof(induction "length trf + length tr3" arbitrary: trf tr3 tr d1 p1 rule: less_induct)
    case less
    show ?case
    using less(5)
    apply(induct rule: combine_blocks.cases, auto)
    subgoal for ch blks1 blks2 blks v
      apply(cases trf)
       apply auto
      subgoal premises pre for trf'
      proof-
        obtain tr' where 1:"combine_blocks chs blks1 (trf' @ WaitBlk d1 p1 rdy # WaitBlk d2 p2 rdy # trl) tr'"
        using less(1)[of trf' blks1 d1 p1 blks]
        using less(2,3,4) pre by auto
      show ?thesis
        apply(rule exI[where x="IOBlock ch v # tr'"])
        apply(rule )
        using 1 pre by auto
    qed
    done
  subgoal for ch blks1 blks2 blks v
      apply(cases trf)
       apply auto
      subgoal premises pre for trf'
      proof-
        obtain tr' where 1:"combine_blocks chs blks1 (trf' @ WaitBlk d1 p1 rdy # WaitBlk d2 p2 rdy # trl) tr'"
        using less(1)[of trf' blks1 d1 p1 blks]
        using less(2,3,4) pre by auto
      show ?thesis
        apply(rule exI[where x="IOBlock ch v # tr'"])
        apply(rule )
        using 1 pre by auto
    qed
    done
  subgoal for ch blks1 blks ch_type v
    subgoal premises pre 
      proof-
        obtain tr' where 1:"combine_blocks chs blks1 (trf @ WaitBlk d1 p1 rdy # WaitBlk d2 p2 rdy # trl) tr'"
        using less(1)[of trf blks1 d1 p1 blks]
        using less(2,3,4) pre by auto
      show ?thesis
        apply(rule exI[where x="CommBlock ch_type ch v # tr'"])
        apply(rule )
        using 1 pre by auto
    qed
    done
  subgoal for ch blks2 blks ch_type v
    apply(cases trf)
     apply auto
    subgoal premises pre for trf'
    proof-
        obtain tr' where 1:"combine_blocks chs tr3 (trf' @ WaitBlk d1 p1 rdy # WaitBlk d2 p2 rdy # trl) tr'"
        using less(1)[of trf' tr3 d1 p1 blks]
        using less(2,3,4) pre by auto
      show ?thesis
        apply(rule exI[where x="CommBlock ch_type ch v # tr'"])
        apply(rule )
        using 1 pre by auto
    qed
    done
  subgoal for blks1 blks2 blks a1 b1 a2 b2 t hist1 hist2
    apply(cases trf)
     apply auto
    subgoal 
      using WaitBlk_cong[of "(d1 + d2)" "(\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1))" rdy t hist2 "(a2, b2)"]
      apply auto
      apply rule
      apply rule
           apply (auto simp add:less)
      apply (rule combine_blocks_wait1)
      by (auto simp add:less)
    subgoal premises pre for trf'
    proof-
        obtain tr' where 1:"combine_blocks chs blks1 (trf' @ WaitBlk d1 p1 rdy # WaitBlk d2 p2 rdy # trl) tr'"
        using less(1)[of trf' blks1 d1 p1 blks]
        using less(2,3,4) pre by auto
      show ?thesis
        apply(rule exI[where x="WaitBlk t (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2)  # tr'"])
        apply(rule combine_blocks_wait1)
        using 1 pre by auto
    qed
    done
  subgoal for blks1 t2 t1 hist2 a2 b2 blks2 blks a1 b1 hist1
    apply(cases trf)
     apply auto
    subgoal 
      using WaitBlk_cong[of "(d1 + d2)" "(\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1))" rdy t2 hist2 "(a2, b2)"]
      apply auto
      apply(cases "t1<d1")
      subgoal premises pre
      proof-
        have 1:"WaitBlk (d1 + d2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) (a2, b2) = WaitBlk (d1 - t1 + d2) (\<lambda>t. if t \<le> d1 - t1 then p1 (t + t1) else p2 (t - (d1 - t1))) rdy"
          apply(rule WaitBlk_ext_real)
            using WaitBlk_cong2[of "(d1 + d2)" "(\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1))" rdy t2 hist2 "(a2, b2)"]
            using pre apply auto
             apply (smt (verit, best))+
            done
        obtain tr' where 2:"combine_blocks chs blks1
         (WaitBlk (d1-t1) (\<lambda> t. p1 (t+t1)) (a2, b2) # WaitBlk d2 p2 (a2, b2) # blks2) tr'"
          using less(1)[of "[]" blks1 "d1-t1" "(\<lambda> t. p1 (t+t1))" blks] pre 1 less by auto
        show ?thesis
          apply(rule exI[where x="WaitBlk t1 (\<lambda>\<tau>. ParState (hist1 \<tau>) (p1 \<tau>)) (a1 \<union> a2, b1 \<union> b2) # tr'"])
          apply(rule )
               apply(auto simp add: pre 2)
          done
      qed
      apply(cases "t1=d1")
      subgoal
        apply auto
        apply(rule )
        apply(rule combine_blocks_wait1)
            apply auto
        apply(subgoal_tac"WaitBlk d2 p2 (a2, b2) = WaitBlk d2 (\<lambda>\<tau>. hist2 (\<tau> + d1)) (a2, b2)")
         apply auto
        apply(rule WaitBlk_ext_real)
          apply auto
        using WaitBlk_cong2[of "(d1 + d2)" "(\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1))" rdy t2 hist2 "(a2, b2)"]
        by (smt (verit, best) less.prems(3))
      apply(cases "t1>d1")
      subgoal
        apply auto
        apply(rule )
        apply(rule combine_blocks_wait3)
             apply (auto simp add:less)
        apply(rule combine_blocks_wait2)
             apply (auto simp add:less)
        apply(subgoal_tac"WaitBlk (d2 - (t1 - d1)) (\<lambda>\<tau>. p2 (\<tau> + (t1 - d1))) (a2, b2) = WaitBlk (d1 + d2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) (a2, b2)")
         apply auto
        apply(rule WaitBlk_ext_real)
          apply auto
        using WaitBlk_cong2[of "(d1 + d2)" "(\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1))" rdy t2 hist2 "(a2, b2)"]
        by (smt (verit, best) less.prems(3))
      by auto
    subgoal premises pre for trf'
    proof-
        obtain tr' where 1:"combine_blocks chs blks1 (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) (a2, b2) # trf' @ WaitBlk d1 p1 rdy # WaitBlk d2 p2 rdy # trl) tr'"
        using less(1)[of "WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) (a2, b2) #trf'" blks1 d1 p1 blks]
        using less(2,3,4) pre by auto
      show ?thesis
        apply(rule exI[where x="WaitBlk t1 (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2)  # tr'"])
        apply(rule combine_blocks_wait2)
        using 1 pre by auto
    qed
    done
  subgoal for t1 t2 hist1 a1 b1 blks1 blks2 blks a2 b2 hist2
    apply(cases trf)
     apply auto
    subgoal
      using WaitBlk_cong[of "(d1 + d2)" "(\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1))" rdy t2 hist2 "(a2, b2)"]
      apply auto
      apply(rule )
      apply(rule combine_blocks_wait3)
           apply (auto simp add:less)
      using less(2,3,4) apply auto
      apply(rule combine_blocks_wait3)
           apply auto
      apply(subgoal_tac"WaitBlk (t1 - d1 - d2) (\<lambda>\<tau>. hist1 (\<tau> + d2 + d1)) (a1, b1) = WaitBlk (t1 - (d1 + d2)) (\<lambda>\<tau>. hist1 (\<tau> + (d1 + d2))) (a1, b1)")
       apply auto
      apply(rule WaitBlk_ext)
        apply auto
      by (simp add: add.commute add.left_commute)
    subgoal premises pre for trf'
    proof-
        obtain tr' where 1:"combine_blocks chs (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) (a1, b1) # blks1) (trf' @ WaitBlk d1 p1 rdy # WaitBlk d2 p2 rdy  # trl) tr'"
        using less(1)[of "trf'" "(WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) (a1, b1) # blks1)" d1 p1 blks]
        using less(2,3,4) pre by auto
      show ?thesis
        apply(rule exI[where x="WaitBlk t2 (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2)  # tr'"])
        apply(rule combine_blocks_wait3)
        using 1 pre less by auto
    qed
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
      apply(cases trf)
       apply auto
      subgoal premises pre for trf'
      proof-
        obtain tr' where 1:"combine_blocks chs (blks1)
            (trf' @ WaitBlk (d1 + d2) (\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1)) rdy # trl) tr'"
          using less(1)[of trf' blks1 d1 p1 blks]
          using pre less(2,3,4) by auto 
        show ?thesis
        apply(rule exI[where x="IOBlock ch v # tr'"])
        apply(rule )
        using 1 pre by auto
    qed
    done
  subgoal for ch blks1 blks2 blks v
      apply(cases trf)
       apply auto
      subgoal premises pre for trf'
      proof-
        obtain tr' where 1:"combine_blocks chs (blks1)
            (trf' @ WaitBlk (d1 + d2) (\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1)) rdy # trl) tr'"
          using less(1)[of trf' blks1 d1 p1 blks]
          using pre less(2,3,4) by auto 
        show ?thesis
        apply(rule exI[where x="IOBlock ch v # tr'"])
        apply(rule )
        using 1 pre by auto
    qed
    done
  subgoal for ch blks1 blks ch_type v
    subgoal premises pre 
      proof-
        obtain tr' where 1:"combine_blocks chs (blks1)
            (trf @ WaitBlk (d1 + d2) (\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1)) rdy # trl) tr'"
          using less(1)[of trf blks1 d1 p1 blks]
          using pre less(2,3,4) by auto 
        show ?thesis
        apply(rule exI[where x="CommBlock ch_type ch v # tr'"])
        apply(rule )
        using 1 pre by auto
    qed
    done
  subgoal for ch blks2 blks ch_type v
    apply(cases trf)
       apply auto
      subgoal premises pre for trf'
      proof-
        obtain tr' where 1:"combine_blocks chs tr3
            (trf' @ WaitBlk (d1 + d2) (\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1)) rdy # trl) tr'"
          using less(1)[of trf' tr3 d1 p1 blks]
          using pre less(2,3,4) by auto 
        show ?thesis
        apply(rule exI[where x="CommBlock ch_type ch v # tr'"])
        apply(rule )
        using 1 pre by auto
    qed
    done
  subgoal for blks1 blks2 blks a1 b1 a2 b2 t hist1 hist2
    apply(cases trf)
     apply auto
    subgoal
      using WaitBlk_cong[of "d1" "p1" rdy t hist2 "(a2, b2)"]
      apply auto
      apply(rule)
      apply(rule combine_blocks_wait2)
      apply(auto simp add: less)
      apply(subgoal_tac"WaitBlk d2 (\<lambda>\<tau>. if \<tau> \<le> 0 then p1 (\<tau> + t) else p2 (\<tau> + t - t)) (a2, b2) = WaitBlk d2 p2 (a2, b2)")
       apply auto
      apply(rule WaitBlk_ext)
      using less
      by auto
    subgoal premises pre for trf'
    proof-
        obtain tr' where 1:"combine_blocks chs (blks1)
            (trf' @ WaitBlk (d1 + d2) (\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1)) rdy # trl) tr'"
          using less(1)[of trf' blks1 d1 p1 blks]
          using pre less(2,3,4) by auto 
        show ?thesis
        apply(rule exI[where x="WaitBlk t (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2) # tr'"])
        apply(rule combine_blocks_wait1)
        using 1 pre less by auto
    qed
    done
  subgoal for blks1 t2 t1 hist2 a2 b2 blks2 blks a1 b1 hist1
    apply(cases trf)
     apply auto
    subgoal
      using WaitBlk_cong[of "d1" "p1" rdy t2 hist2 "(a2, b2)"]
      apply auto
      subgoal premises pre
      proof-
        have 1:"WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) (a2, b2) = WaitBlk (d1 - t1) (\<lambda>t. p1 (t + t1)) rdy"
          apply(rule WaitBlk_ext)
          using pre apply auto
          using WaitBlk_cong2[of "d1" "p1" rdy t2 hist2 "(a2, b2)"]
          by auto
        obtain tr' where 2:"combine_blocks chs (blks1)
            (WaitBlk ((d1-t1) + d2) (\<lambda>t. if t \<le> d1-t1 then p1 (t + t1)  else p2 (t - (d1 - t1))) rdy # trl) tr'"
          using less(1)[of "[]" blks1 "d1-t1" "\<lambda> t. p1(t+t1)" blks]
          using pre less(2,3,4) 1 by auto 
        show ?thesis
        apply(rule exI[where x="WaitBlk t1 (\<lambda>\<tau>. ParState (hist1 \<tau>) (if \<tau> \<le> t2 then p1 \<tau> else p2 (\<tau> - t2))) (a1 \<union> a2, b1 \<union> b2) # tr'"])
        apply(rule combine_blocks_wait2)
          using 2 pre less apply auto
          apply(subgoal_tac"WaitBlk (t2 + d2 - t1) (\<lambda>\<tau>. if \<tau> + t1 \<le> t2 then p1 (\<tau> + t1) else p2 (\<tau> + t1 - t2))
       (a2, b2) = WaitBlk ((d1-t1) + d2) (\<lambda>t. if t \<le> d1-t1 then p1 (t + t1)  else p2 (t - (d1 - t1))) rdy")
           apply auto
          apply(rule WaitBlk_ext)
            apply auto
          by (simp add: diff_diff_eq2)
    qed
    done
  subgoal premises pre for trf'
    proof-
        obtain tr' where 1:"combine_blocks chs (blks1)
            (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) (a2, b2) # trf' @ WaitBlk (d1 + d2) (\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1)) rdy # trl) tr'"
          using less(1)[of "WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) (a2, b2) #trf'" blks1 d1 p1 blks]
          using pre less(2,3,4) by auto 
        show ?thesis
        apply(rule exI[where x="WaitBlk t1 (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2) # tr'"])
        apply(rule combine_blocks_wait2)
        using 1 pre less by auto
    qed
    done
  subgoal for t1 t2 hist1 a1 b1 blks1 blks2 blks a2 b2 hist2
    apply(cases trf)
     apply auto
    subgoal
      using WaitBlk_cong[of t2 hist2 "(a2, b2)" "d1" "p1" rdy]
      apply auto
      apply(cases "t1-d1<d2")
      subgoal premises pre
        using pre(3)
        apply(elim combine_blocks_waitE3)
        apply(auto simp add: pre)
        apply(rule )
        apply(rule combine_blocks_wait2)
        using pre less
             apply auto
        apply(subgoal_tac"WaitBlk (d1 + d2 - t1)
              (\<lambda>\<tau>. if \<tau> + t1 \<le> d1 then p1 (\<tau> + t1) else p2 (\<tau> + t1 - d1)) (a2, b2) = WaitBlk (d2 - (t1 - d1)) (\<lambda>t. p2 (t + (t1 - d1))) (a2, b2)")
        apply auto
        apply(rule WaitBlk_ext)
          apply auto
        by (metis add_diff_eq)
      apply(cases "t1-d1=d2")
      apply auto
      subgoal premises pre
        using pre(3)
        apply(elim combine_blocks_waitE2)
        apply(auto simp add: pre)
        apply(rule )
        apply(rule combine_blocks_wait1)
        using pre less
             apply auto
        done
      apply(cases "t1-d1>d2")
      subgoal premises pre
        using pre(3)
        apply(elim combine_blocks_waitE4)
        using less(2,3,4)
        apply(auto simp add: pre)
        apply(rule )
        apply(rule combine_blocks_wait3)
        using pre less
             apply auto
        apply(subgoal_tac"WaitBlk (t1 - (d1 + d2)) (\<lambda>\<tau>. hist1 (\<tau> + (d1 + d2))) (a1, b1) = WaitBlk (t1 - d1 - d2) (\<lambda>t. hist1 (t + d2 + d1)) (a1, b1)")
        apply auto
        apply(rule WaitBlk_ext)
          apply auto
        by (simp add: add.commute add.left_commute)
      by auto
    subgoal premises pre for trf'
    proof-
        obtain tr' where 1:"combine_blocks chs (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) (a1, b1) # blks1)
            (trf' @ WaitBlk (d1 + d2) (\<lambda>t. if t \<le> d1 then p1 t else p2 (t - d1)) rdy # trl) tr'"
          using less(1)[of "trf'" "WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) (a1, b1) #blks1" d1 p1 blks]
          using pre less(2,3,4) by auto 
        show ?thesis
        apply(rule exI[where x="WaitBlk t2 (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (a1 \<union> a2, b1 \<union> b2) # tr'"])
        apply(rule combine_blocks_wait3)
        using 1 pre less by auto
    qed
    done
  done
qed
  done



lemma combine_reverse_prop:"
    Ex (combine_blocks chs tr1 tr2) \<Longrightarrow> 
    Ex (combine_blocks chs tr2 tr1)"
  apply auto
  subgoal for tr
  proof(induction "length tr1 + length tr2" arbitrary: tr1 tr2 tr rule: less_induct)
    case less
    show ?case 
      using less(2)
      apply(induct rule: combine_blocks.cases, auto)
      subgoal for ch blks1 blks2 blks v
        using less(1)[of blks1 blks2 blks]
        apply auto
        subgoal for blks'
          apply(rule exI[where x= "IOBlock ch v # blks'"])
          apply rule by auto
        done
      subgoal for ch blks1 blks2 blks v
        using less(1)[of blks1 blks2 blks]
        apply auto
        subgoal for blks'
          apply(rule exI[where x= "IOBlock ch v # blks'"])
          apply rule by auto
        done
      subgoal for ch blks1 blks ch_type v
        using less(1)[of blks1 tr2 blks]
        apply auto
        subgoal for blks'
          apply(rule exI[where x="CommBlock ch_type ch v # blks'"])
          apply rule by auto
        done
      subgoal for ch blks2 blks ch_type v
        using less(1)[of tr1 blks2 blks]
        apply auto
        subgoal for blks'
          apply(rule exI[where x="CommBlock ch_type ch v # blks'"])
          apply rule by auto
        done
      subgoal for blks1 blks2 blks a1 b1 a2 b2 t p1 p2
        using less(1)[of blks1 blks2 blks]
        apply auto
        subgoal for blks'
          apply(rule exI[where x= "WaitBlk t (\<lambda>\<tau>. ParState (p2 \<tau>) (p1 \<tau>)) (a1 \<union> a2, b1 \<union> b2) # blks'"])
          apply(rule combine_blocks_wait1) by auto
        done
      subgoal for blks1 t2 t1 p2 a1 b1 blks2 blks a2 b2 p1
        using less(1)[of blks1 "WaitBlk (t2 - t1) (\<lambda>\<tau>. p2 (\<tau> + t1)) (a1, b1) # blks2" blks]
        apply auto
        subgoal for blks'
          apply(rule exI[where x= "WaitBlk (t1) (\<lambda>\<tau>. ParState (p2 \<tau>) (p1 \<tau>)) (a2 \<union> a1, b2 \<union> b1) # blks'"])
          apply rule
          by auto
        done
      subgoal for t1 t2 p1 a1 b1 blks1 blks2 blks a2 b2 p2
        using less(1)[of "WaitBlk (t1 - t2) (\<lambda>\<tau>. p1 (\<tau> + t2)) (a1, b1) # blks1" blks2 blks]
        apply auto
        subgoal for blks'
          apply(rule exI[where x="WaitBlk (t2) (\<lambda>\<tau>. ParState (p2 \<tau>) (p1 \<tau>)) (a1 \<union> a2, b1 \<union> b2) # blks'"])
          apply rule
          by auto
        done
      done
  qed
  done

lemma combine_wait_block_prop1:"
    d1 > 0 \<Longrightarrow> d2 > d1 \<Longrightarrow> 
    Ex (combine_blocks chs tr3 (trf @ WaitBlk d2 p rdy # trl)) \<longleftrightarrow> 
    Ex (combine_blocks chs tr3 (trf @ [WaitBlk d1 p rdy,WaitBlk (d2-d1) (\<lambda>t. p(t+d1)) rdy] @ trl))"
  using combine_wait_block_prop[of d1 "d2-d1" p "\<lambda>t. p(t+d1)" chs tr3 trf rdy trl]
  apply(subgoal_tac"WaitBlk (d1 + (d2 - d1)) (\<lambda>t. if t \<le> d1 then p t else p (t - d1 + d1)) rdy = WaitBlk d2 p rdy")
  subgoal by (simp add: ereal_diff_gr0)
  subgoal premises pre
  proof-
    have 1:"(d1 + (d2 - d1)) = d2" 
      using pre 
      by (smt (verit, best) add.commute add_0 add_diff_eq_ereal ereal_minus(1) zero_ereal_def)
    have 2:"(\<lambda>t. if t \<le> d1 then p t else p (t - d1 + d1)) = p"
      apply (rule ) by auto
    show ?thesis using 1 2 by auto
  qed
  done

lemma combine_wait_block_prop2:"
    d1 > 0 \<Longrightarrow> d2 > d1 \<Longrightarrow> 
    Ex (combine_blocks chs (trf @ WaitBlk d2 p rdy # trl) tr3) \<longleftrightarrow> 
    Ex (combine_blocks chs (trf @ [WaitBlk d1 p rdy,WaitBlk (d2-d1) (\<lambda>t. p(t+d1)) rdy] @ trl) tr3)"
  using combine_wait_block_prop1[of d1 d2 chs tr3 trf p rdy trl] 
  using combine_reverse_prop[of chs tr3 "(trf @ WaitBlk d2 p rdy # trl)"]
  using combine_reverse_prop[of chs "(trf @ WaitBlk d2 p rdy # trl)" tr3]
  using combine_reverse_prop[of chs tr3 "(trf @ [WaitBlk d1 p rdy,WaitBlk (d2-d1) (\<lambda>t. p(t+d1)) rdy] @ trl)"]
  using combine_reverse_prop[of chs "(trf @ [WaitBlk d1 p rdy,WaitBlk (d2-d1) (\<lambda>t. p(t+d1)) rdy] @ trl)" tr3]
 by blast



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
                        commit chs a tr3 \<longrightarrow> combine_blocks chs (tr2@tr2') (tr3@tr3') tr4 \<longrightarrow> 
          Q s2 (tr1 @ tr2)\<and> commit chs g tr2 \<and> (\<exists> tr4'. combine_blocks chs (tr2') (tr3') tr4')))"


lemma Validc_skip:
"\<Turnstile>c(chs) {P,cE} Skip {P,cE}"
  unfolding Validc_def apply auto
    apply(auto elim!: skipE commitEE)
  apply rule
  done


lemma Validc_out1:
" ch\<in>chs \<Longrightarrow>
  \<Turnstile>c(chs) {\<lambda> s t. s = ss \<and> P s t,cI ch (e ss)} Cm (ch[!]e) {(\<lambda> s t. s = ss \<and> (P s @\<^sub>t Out0\<^sub>t ch (e ss)) t),(cO ch (e ss))}"
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


lemma Validc_out2:
" ch\<in>chs \<Longrightarrow> d>0 \<Longrightarrow> 
  \<Turnstile>c(chs) {\<lambda> s t. s= ss \<and> P s t,cW d ({},{}) ({},{ch}) [@] cI ch (e ss)} Cm (ch[!]e) {(\<lambda> s t. s=ss \<and> (P s @\<^sub>t (Wait\<^sub>t d (\<lambda>_ . State ss) ({ch},{})) @\<^sub>t Out0\<^sub>t ch (e ss)) t),(cW d ({ch},UNIV-{ch}) ({},UNIV) [@]cO ch (e ss))}"
  unfolding Validc_def apply (auto simp add:join_assn_def)
  subgoal 
    by(auto elim!: sendE commitIE commitSE)
  subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: sendE commitIE commitSE)
    subgoal
      using commit_W_prop2 
      by (metis append.left_neutral append_Cons commit_W_prop1)
    subgoal for tr3'' dd
      using commit_W_prop5[of ch chs ch d dd "(\<lambda>_. State ss)" "({ch}, {})" "(e ss)" tr2' tr3'' "(e ss)" tr3' x "{ch}" "{}" "{}" "{}"]
      apply auto
      apply(rule exI[where x=tr1])
      apply auto
      apply(rule exI[where x="[WaitBlk d (\<lambda>_. State ss) ({ch}, {})]"])
      apply auto 
       apply(rule ) apply auto
      apply(rule )
      done
    done
 subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: sendE commitIE commitSE)
    subgoal
      using commit_W_prop2 
      by (metis append.left_neutral append_Cons commit_W_prop1)
    subgoal for tr3'' dd
      using commit_W_prop5[of ch chs ch d dd "(\<lambda>_. State ss)" "({ch}, {})" "(e ss)" tr2' tr3'' "(e ss)" tr3' x "{ch}" "{}" "{}" "{}"]
      apply auto
      using commitseq1[of chs "cW (d) ({ch}, UNIV - {ch}) ({}, UNIV)" "[WaitBlk (d) (\<lambda>_. State ss) ({ch}, {})]" "cO ch (e ss)" "[OutBlock ch (e ss)]"]
      apply auto
      using commitW1 commitO1
      by auto
    done
  subgoal for tr1 s2 tr2 tr2' tr3 tr3' x
    apply(auto elim!: sendE commitIE commitSE)
    subgoal
      using commit_W_prop2 
      by (metis append.left_neutral append_Cons commit_W_prop1)
    subgoal for tr3'' dd
      using commit_W_prop5[of ch chs ch d dd "(\<lambda>_. State ss)" "({ch}, {})" "(e ss)" tr2' tr3'' "(e ss)" tr3' x "{ch}" "{}" "{}" "{}"]
      apply auto
      using commit_W_prop7[of d chs "(\<lambda>_. State ss)" "({ch}, {})" "OutBlock ch (e ss) # tr2'" tr3'' "InBlock ch (e ss) # tr3'" x "{ch}" "{}" "{}" "{}"]
      apply auto
      by(auto elim: sync_elims) 
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
         (trf @ WaitBlk (d1) p1 rdy # WaitBlk d2 p2 rdy # trl @ tr3'))")
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
              commit chs a1 (trf @ [WaitBlk (d1) p1 rdy]) \<longrightarrow>
              combine_blocks chs (tr1a @ (tr2a @ tr2')) ((trf @ [WaitBlk (d1) p1 rdy]) @ (WaitBlk d2 p2 rdy # trl @ tr3')) tr4' \<longrightarrow>
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

(*
lemma Validc_repn2:
  assumes"\<And> i. i<N \<Longrightarrow> \<Turnstile>c(chs) {\<lambda> s t. s = ss i \<and> P s t,a (i+1)} S {\<lambda> s t. s = ss (i+1) \<and> P s t,g (i+1)} "
   shows " \<Turnstile>c(chs) {\<lambda> s t. s = ss 0 \<and> P s t,crepn N a} RepN N S {\<lambda> s t. s = ss N \<and> P s t,crepn N g}"
  using assms
  proof(induction N arbitrary: ss a g)
    case 0                                
    then show ?case 
      unfolding Validc_def apply clarify
      apply(auto elim!: skipE commitRNE)
    apply(rule)
    done
  next
    case (Suc N)
    then show ?case 
      
  
qed
*)

fun sync_ctr :: "cname set \<Rightarrow> ctr \<Rightarrow> ctr \<Rightarrow> tassn" where
"sync_ctr chs C1 C2  tr \<longleftrightarrow> (\<exists>tr1 tr2. commit chs C1 tr1 \<and> commit chs C2 tr2 \<and> combine_blocks chs tr1 tr2 tr)"


fun discrete_block :: "trace_block \<Rightarrow> bool" where
  "discrete_block (InBlock ch v) = True"
| "discrete_block (OutBlock ch v) = True"
| "discrete_block (IOBlock ch v) = True"
| "discrete_block (WaitBlock d p rdy) = False"


lemma discrete_block_WaitBlk[simp]:
   "discrete_block (WaitBlk d p rdy) = False"
  apply(auto simp add:WaitBlk_simps)
  done

fun discrete_in_block :: "cname set \<Rightarrow> trace_block \<Rightarrow> bool" where
  "discrete_in_block chs (InBlock ch v) = (ch \<in> chs)"
| "discrete_in_block chs (OutBlock ch v) = (ch \<in> chs)"
| "discrete_in_block chs (IOBlock ch v) = (ch \<in> chs)"
| "discrete_in_block chs (WaitBlock d p rdy) = False"

fun get_time_waitblock :: "trace_block \<Rightarrow> real" where
  "get_time_waitblock (InBlock ch v) = undefined"
| "get_time_waitblock (OutBlock ch v) = undefined"
| "get_time_waitblock (IOBlock ch v) = undefined"
| "get_time_waitblock (WaitBlock d p rdy) = d"

lemma get_time_WaitBlk[simp]:
    "get_time_waitblock (WaitBlk d p rdy) = d"
  apply(auto simp add:WaitBlk_simps)
  done

fun is_get_time_defined :: "trace_block \<Rightarrow> bool" where
  "is_get_time_defined (WaitBlock d p rdy) = True"
| "is_get_time_defined _ = False"

lemma is_get_time_undefined_correct:
  "\<not>is_get_time_defined t \<Longrightarrow> get_time_waitblock t = undefined"
  apply (cases t)
   apply auto subgoal for comm_type ch v
    apply (cases comm_type) by auto
  done

fun cut_time_waitblock :: "trace_block \<Rightarrow> real \<Rightarrow> trace_block \<times> trace_block" where
  "cut_time_waitblock (InBlock ch v) t = undefined"
| "cut_time_waitblock (OutBlock ch v) t = undefined"
| "cut_time_waitblock (IOBlock ch v) t = undefined"
| "cut_time_waitblock (WaitBlock d p rdy) t = (WaitBlock t (\<lambda> x \<in>{0..t}. p x) rdy,WaitBlock (d-t) (\<lambda> x \<in>{0..d-t}. p(x+t)) rdy)"

lemma test: "PInfty = \<infinity>"
  by auto

lemma cut_time_WaitBlk:
      "d2 > d1 \<and> d1 > 0 \<Longrightarrow> cut_time_waitblock (WaitBlk d2 p rdy) d1 = (WaitBlk d1 p rdy,WaitBlk (d2-d1) (\<lambda>t. p(t+d1)) rdy)"
     apply(auto simp add:WaitBlk_simps)
  done


inductive res_ind :: "cname set \<Rightarrow> trace \<Rightarrow> real \<times> nat \<Rightarrow> trace \<times> trace \<Rightarrow> bool" where
  "t = 0 \<Longrightarrow> i = 0 \<Longrightarrow> res_ind chs tr (t, i) ([], tr)"
| "t = 0 \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> discrete_block (hd tr) \<Longrightarrow>
   discrete_in_block chs (hd tr) \<Longrightarrow>
   res_ind chs (tl tr) (0, i-1) (tr1, tr2) \<Longrightarrow>
   res_ind chs tr (t, i) (hd tr # tr1, tr2)"
| "t = 0 \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> discrete_block (hd tr) \<Longrightarrow>
   \<not>discrete_in_block chs (hd tr) \<Longrightarrow>
   res_ind chs (tl tr) (0, i) (tr1, tr2) \<Longrightarrow>
   res_ind chs tr (t, i) (hd tr # tr1, tr2)"
| "t > 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> discrete_block (hd tr) \<Longrightarrow>
   res_ind chs (tl tr) (t, i) (tr1, tr2) \<Longrightarrow>
   res_ind chs tr (t, i) (hd tr # tr1, tr2)"
| "t > 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> \<not>discrete_block (hd tr) \<Longrightarrow>
   get_time_waitblock (hd tr) \<le> t \<Longrightarrow>
   res_ind chs (tl tr) (t - (get_time_waitblock (hd tr)), i) (tr1, tr2) \<Longrightarrow>
   res_ind chs tr (t, i) (hd tr # tr1, tr2)"
| "t > 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> \<not>discrete_block (hd tr) \<Longrightarrow>
   get_time_waitblock (hd tr) > t \<Longrightarrow> i=0 \<Longrightarrow>
   res_ind chs tr (t, i) ([fst (cut_time_waitblock (hd tr) t)], snd (cut_time_waitblock (hd tr) t) # (tl tr))"

inductive is_res_ind :: "cname set \<Rightarrow> trace \<Rightarrow> real \<times> nat \<Rightarrow> bool" where
  "t = 0 \<Longrightarrow> i = 0 \<Longrightarrow> is_res_ind chs tr (t, i)"
| "t = 0 \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> discrete_block (hd tr) \<Longrightarrow>
   discrete_in_block chs (hd tr) \<Longrightarrow>
   is_res_ind chs (tl tr) (0, i-1) \<Longrightarrow>
   is_res_ind chs tr (t, i)"
| "t = 0 \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> discrete_block (hd tr) \<Longrightarrow>
   \<not>discrete_in_block chs (hd tr) \<Longrightarrow>
   is_res_ind chs (tl tr) (0, i) \<Longrightarrow>
   is_res_ind chs tr (t, i)"
| "t > 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> discrete_block (hd tr) \<Longrightarrow>
   is_res_ind chs (tl tr) (t, i) \<Longrightarrow>
   is_res_ind chs tr (t, i)"
| "t > 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> \<not>discrete_block (hd tr) \<Longrightarrow>
   get_time_waitblock (hd tr) \<le> t \<Longrightarrow>
   is_res_ind chs (tl tr) (t - (get_time_waitblock (hd tr)), i) \<Longrightarrow>
   is_res_ind chs tr (t, i)"
| "t > 0 \<Longrightarrow> tr \<noteq> [] \<Longrightarrow> \<not>discrete_block (hd tr) \<Longrightarrow>
   get_time_waitblock (hd tr) > t \<Longrightarrow> i=0 \<Longrightarrow>
   is_res_ind chs tr (t, i)"

lemma res_ind_is_defined :" is_res_ind chs tr (t, i) \<longleftrightarrow> (\<exists> tr1 tr2. res_ind chs tr (t, i) (tr1,tr2))"
proof(induction "length tr" arbitrary: tr t i rule: less_induct)
  case less
  show ?case 
    apply(rule )
    subgoal
      apply(induct rule: is_res_ind.cases)
      subgoal for t i chs tr
        apply auto
        using res_ind.intros(1) by blast
      subgoal premises pre for t i tr chs
      proof-
        have 1:"\<exists> tr1 tr2. res_ind chs (tl tr) (0, i-1) (tr1,tr2)"
          using less[of "tl tr" 0 "i-1"] pre by auto
        obtain tr1 and tr2 where 2:"res_ind chs (tl tr) (0, i-1) (tr1,tr2)"
          using 1 by auto
        show ?thesis
          apply(simp add:pre)
          apply(rule exI[where x="hd tr # tr1"])
          apply(rule exI[where x="tr2"])
          apply(rule res_ind.intros(2))
          using 2 pre by auto
      qed
      subgoal premises pre for t i tr chs
      proof-
        have 1:"\<exists> tr1 tr2. res_ind chs (tl tr) (0, i) (tr1,tr2)"
          using less[of "tl tr" 0 "i"] pre by auto
        obtain tr1 and tr2 where 2:"res_ind chs (tl tr) (0, i) (tr1,tr2)"
          using 1 by auto
        show ?thesis
          apply(simp add:pre)
          apply(rule exI[where x="hd tr # tr1"])
          apply(rule exI[where x="tr2"])
          apply(rule res_ind.intros(3))
          using 2 pre by auto
      qed
      subgoal premises pre for t tr chsa i
      proof-
        have 1:"\<exists> tr1 tr2. res_ind chs (tl tr) (t, i) (tr1,tr2)"
          using less[of "tl tr" t "i"] pre by auto
        obtain tr1 and tr2 where 2:"res_ind chs (tl tr) (t, i) (tr1,tr2)"
          using 1 by auto
        show ?thesis
          apply(simp add:pre)
          apply(rule exI[where x="hd tr # tr1"])
          apply(rule exI[where x="tr2"])
          apply(rule res_ind.intros(4))
          using 2 pre by auto
      qed
      subgoal premises pre for t tr chs i
      proof-
        have 1:"\<exists> tr1 tr2. res_ind chs (tl tr) (t - (get_time_waitblock (hd tr)), i) (tr1,tr2)"
          using less[of "tl tr" "t - (get_time_waitblock (hd tr))" "i"] pre by auto
        obtain tr1 and tr2 where 2:"res_ind chs (tl tr) (t - (get_time_waitblock (hd tr)), i) (tr1,tr2)"
          using 1 by auto
        show ?thesis
          apply(simp add:pre)
          apply(rule exI[where x="hd tr # tr1"])
          apply(rule exI[where x="tr2"])
          apply(rule res_ind.intros(5))
          using 2 pre by auto
      qed
      subgoal for t tr i chs
        apply auto
        using res_ind.intros(6) by blast
      done
    apply auto
    subgoal for tr1 tr2
      apply(induct rule:res_ind.cases)
      subgoal for t i chs tr
        apply auto
        apply(rule is_res_ind.intros(1))
        by auto
      subgoal for t i tr chs tr1a tr2a
        apply auto
        apply(rule is_res_ind.intros(2))
             apply auto
        using less[of "tl tr" 0 "i-1"] 
        by auto
      subgoal for t i tr chs tr1a tr2a
        apply auto
        apply(rule is_res_ind.intros(3))
             apply auto
        using less[of "tl tr" 0 "i"] 
        by auto
      subgoal for t tr chs i tr1a tr2a
        apply auto
        apply(rule is_res_ind.intros(4))
             apply auto
        using less[of "tl tr" t "i"] 
        by auto
      subgoal for t tr chs i tr1a tr2a
        apply auto
        apply(rule is_res_ind.intros(5))
             apply auto
        using less[of "tl tr" "t - (get_time_waitblock (hd tr))" "i"] 
        by auto
      subgoal for t tr i chs
        apply auto
        apply(rule is_res_ind.intros(6))
        by auto
      done
    done
qed


lemma res_ind_combine1 : "combine_blocks chs tr1 tr2 tr \<Longrightarrow> 
      (is_res_ind chs tr1 (t, i) = is_res_ind chs tr2 (t, i))"
  proof(induction "length tr1 + length tr2" arbitrary: tr1 tr2 tr t i rule: less_induct)
    case less
    show ?case 
      using less(2)
      apply(induct rule: combine_blocks.cases)
      subgoal
        by auto
      subgoal for ch chs blks1 blks2 blks v
        apply auto
        subgoal premises pre
          using pre(7)
          apply(induct rule: is_res_ind.cases)
          subgoal for t i chs tr1
            using pre apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr1 chs
            using pre apply auto
            apply(rule is_res_ind.intros(2))
                 apply auto
            using less(1)[of blks1 blks2 blks 0 "i-1"]
            by auto
          subgoal using pre by auto
          subgoal for t tr1 chs i
            using pre apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
            using less(1)[of blks1 blks2 blks t "i"]
            by auto
          subgoal using pre by auto
          subgoal using pre by auto
          done
        subgoal premises pre
          using pre(7)
          apply(induct rule: is_res_ind.cases)
          subgoal for t i chs tr2
            using pre apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr2 chs
            using pre apply auto
            apply(rule is_res_ind.intros(2))
                 apply auto
            using less(1)[of blks1 blks2 blks 0 "i-1"]
            by auto
          subgoal using pre by auto
          subgoal for t tr1 chs i
            using pre apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
            using less(1)[of blks1 blks2 blks t "i"]
            by auto
          subgoal using pre by auto
          subgoal using pre by auto
          done
        done
      subgoal for ch chs blks1 blks2 blks v
        apply auto
        subgoal premises pre
          using pre(7)
          apply(induct rule: is_res_ind.cases)
          subgoal for t i chs tr1
            using pre apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr1 chs
            using pre apply auto
            apply(rule is_res_ind.intros(2))
                 apply auto
            using less(1)[of blks1 blks2 blks 0 "i-1"]
            by auto
          subgoal using pre by auto
          subgoal for t tr1 chs i
            using pre apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
            using less(1)[of blks1 blks2 blks t "i"]
            by auto
          subgoal using pre by auto
          subgoal using pre by auto
          done
        subgoal premises pre
          using pre(7)
          apply(induct rule: is_res_ind.cases)
          subgoal for t i chs tr2
            using pre apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr2 chs
            using pre apply auto
            apply(rule is_res_ind.intros(2))
                 apply auto
            using less(1)[of blks1 blks2 blks 0 "i-1"]
            by auto
          subgoal using pre by auto
          subgoal for t tr1 chs i
            using pre apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
            using less(1)[of blks1 blks2 blks t "i"]
            by auto
          subgoal using pre by auto
          subgoal using pre by auto
          done
        done
      subgoal for ch comms blks1 blks2 blks ch_type v
        apply auto
        subgoal premises pre
          using pre(7)
          apply(induct rule: is_res_ind.cases)
          subgoal for t i chs tr1
            using pre
            apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr1 chs
            using pre 
            apply auto
            apply(cases ch_type)
            by auto
          subgoal for t i tr1 chs
            using pre 
            apply auto
            using less(1)[of blks1 blks2 blks 0 i]
            by auto
          subgoal for t tr1 chs i
            using pre 
            apply auto
            using less(1)[of blks1 blks2 blks t i]
            by auto
          subgoal for t i tr1 chs
            apply(cases ch_type)
            by auto
          subgoal for t i tr1 chs
            apply(cases ch_type)
            by auto
          done
        subgoal premises pre
          using pre(7)
          apply(induct rule: is_res_ind.cases)
          subgoal for t i chs tr2
            using pre
            apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr2 chs
            using pre 
            apply auto
            apply(rule is_res_ind.intros(3))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks 0 i]
            by auto
          subgoal for t i tr2 chs
            using pre 
            apply auto
            apply(rule is_res_ind.intros(3))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks 0 i]
            by auto
          subgoal for t tr2 chs i
            using pre 
            apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks t i]
            by auto
          subgoal for t tr2 chs i
            using pre 
            apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks t i]
            by auto
          subgoal for t tr2 i chs
            using pre 
            apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks t i]
            by auto
          done
        done
      subgoal for ch comms blks1 blks2 blks ch_type v
        apply auto
        subgoal premises pre
          using pre(7)
          apply(induct rule: is_res_ind.cases)
          subgoal for t i chs tr1
            using pre
            apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr1 chs
            using pre 
            apply auto
            apply(rule is_res_ind.intros(3))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks 0 i]
            by auto
          subgoal for t i tr1 chs
            using pre 
            apply auto
            apply(rule is_res_ind.intros(3))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks 0 i]
            by auto
          subgoal for t tr1 chs i
            using pre 
            apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks t i]
            by auto
          subgoal for t tr1 chs i
            using pre 
            apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks t i]
            by auto
          subgoal for t tr1 i chs
            using pre 
            apply auto
            apply(rule is_res_ind.intros(4))
                 apply auto
              apply(cases ch_type)
            apply auto
            apply(cases ch_type)
               apply auto
            using less(1)[of blks1 blks2 blks t i]
            by auto
          done
        subgoal premises pre
          using pre(7)
          apply(induct rule: is_res_ind.cases)
          subgoal for t i chs tr2
            using pre
            apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr1 chs
            using pre 
            apply auto
            apply(cases ch_type)
            by auto
          subgoal for t i tr2 chs
            using pre 
            apply auto
            using less(1)[of blks1 blks2 blks 0 i]
            by auto
          subgoal for t tr2 chs i
            using pre 
            apply auto
            using less(1)[of blks1 blks2 blks t i]
            by auto
          subgoal for t i tr2 chs
            apply(cases ch_type)
            by auto
          subgoal for t i tr2 chs
            apply(cases ch_type)
            by auto
          done
        done
      subgoal for comms blks1 blks2 blks rdy1 rdy2 tt hist hist1 hist2 rdy
        apply auto
        subgoal premises pre
          using pre(10)
          apply(induct rule: is_res_ind.cases)
          subgoal 
            using pre
            apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr1 chs
            using pre 
            by (auto simp add: WaitBlk_simps)
          subgoal for t i tr1 chs
            using pre 
            by (auto simp add: WaitBlk_simps)
          subgoal for t tr1 chs i
            using pre 
            by (auto simp add: WaitBlk_simps)
          subgoal for t tr1 chs i
            using pre 
            apply(auto simp add: WaitBlk_simps)
            apply(rule is_res_ind.intros(5))
                apply auto
            subgoal 
              using less(1)[of blks1 blks2 blks "t-tt" i]
              by auto
            done
          subgoal for t tr1 chs i
            using pre 
            apply(auto simp add: WaitBlk_simps)
            subgoal 
            apply(rule is_res_ind.intros(6))
              by auto
            done
          done
        subgoal premises pre
          using pre(10)
          apply(induct rule: is_res_ind.cases)
          subgoal 
            using pre
            apply auto
            apply(rule is_res_ind.intros(1))
            by auto
          subgoal for t i tr2 chs
            using pre 
            by (auto simp add: WaitBlk_simps)
          subgoal for t i tr2 chs
            using pre 
            by (auto simp add: WaitBlk_simps)
          subgoal for t tr2 chs i
            using pre 
            by (auto simp add: WaitBlk_simps)
          subgoal for t tr2 chs i
            using pre 
            apply(auto simp add: WaitBlk_simps)
            apply(rule is_res_ind.intros(5))
                apply auto
            subgoal 
              using less(1)[of blks1 blks2 blks "t-tt" i]
              by auto
            done
          subgoal for t tr2 chs i
            using pre 
            apply(auto simp add: WaitBlk_simps)
            subgoal 
            apply(rule is_res_ind.intros(6))
              by auto
              done
            done
          done
        subgoal for comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy
          apply auto
          subgoal premises pre
            using pre(11)
            apply(induct rule: is_res_ind.cases)
            subgoal
              apply auto
              apply(rule is_res_ind.intros(1))
              by auto
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal premises pre' for t tr1 chs i
              thm pre
            proof-
              have "is_res_ind chs (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1,i)"
                using less(1)[of blks1 "(WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" i]
                using pre pre' by (auto simp add: WaitBlk_simps)
              then show ?thesis
                subgoal 
                  apply(induct rule: is_res_ind.cases)
                  using pre pre'
                       apply(auto simp add: WaitBlk_simps)
                  subgoal apply(rule is_res_ind.intros(6)) by auto
                  subgoal apply(rule is_res_ind.intros(5)) by auto
                  subgoal apply(rule is_res_ind.intros(6)) by auto
                  done
                done
            qed
            subgoal for t tr1 i chs
              using pre apply auto
              apply(rule is_res_ind.intros(6))
                  by auto
              done
          subgoal premises pre
            using pre(11)
            apply(induct rule: is_res_ind.cases)
            subgoal
              apply auto
              apply(rule is_res_ind.intros(1))
              by auto
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal premises pre' for t tr2 chs i  
            proof-
              have "is_res_ind chs (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1,i)"
                apply(rule is_res_ind.intros(5))
                using pre pre'
                  apply (auto simp add: WaitBlk_simps)                
                done
              then have "is_res_ind chs blks1 (t - t1, i)"
                using less(1)[of blks1 "(WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" i]
                using pre pre' by auto
              then show ?thesis
                using pre pre' apply auto
                apply(rule is_res_ind.intros(5))
                    apply (auto simp add: WaitBlk_simps)
                done
            qed
            subgoal for t tr2 i chs
              apply(cases "t1\<le>t")
              subgoal premises pre'
              proof-
              have "is_res_ind chs (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1,i)"
                apply(cases "t1<t")
                subgoal
                  apply(rule is_res_ind.intros(6))
                using pre pre'
                  apply (auto simp add: WaitBlk_simps)
                done
              subgoal
                  apply(rule is_res_ind.intros(1))
                using pre pre'
                  apply (auto simp add: WaitBlk_simps)
                done
              done
              then have "is_res_ind chs blks1 (t - t1, i)"
                using less(1)[of blks1 "(WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" i]
                using pre pre' by auto
              then show ?thesis
                using pre pre' apply auto
                apply(rule is_res_ind.intros(5))
                    apply (auto simp add: WaitBlk_simps)
                done
            qed
            apply(rule is_res_ind.intros(6))
                apply (auto simp add: WaitBlk_simps)
            done
          done
        done
      subgoal for comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy
        apply auto
        subgoal premises pre
            using pre(11)
            apply(induct rule: is_res_ind.cases)
            subgoal
              apply auto
              apply(rule is_res_ind.intros(1))
              by auto
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal premises pre' for t tr1 chs i  
            proof-
              have "is_res_ind chs (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2,i)"
                apply(rule is_res_ind.intros(5))
                using pre pre'
                  apply (auto simp add: WaitBlk_simps)             
                done
              then have "is_res_ind chs blks2 (t - t2, i)"
                using less(1)[of "(WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" i]
                using pre pre' by auto
              then show ?thesis
                using pre pre' apply auto
                apply(rule is_res_ind.intros(5))
                    apply (auto simp add: WaitBlk_simps)
                 done
            qed
            subgoal for t tr1 i chs
              apply(cases "t2\<le>t")
              subgoal premises pre'
              proof-
              have "is_res_ind chs (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2,i)"
                apply(cases "t2<t")
                subgoal
                  apply(rule is_res_ind.intros(6))
                using pre pre'
                  apply (auto simp add: WaitBlk_simps)
                done
              subgoal
                  apply(rule is_res_ind.intros(1))
                using pre pre'
                  apply (auto simp add: WaitBlk_simps)
                done
              done
              then have "is_res_ind chs blks2 (t - t2, i)"
                using less(1)[of "(WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" i]
                using pre pre' by auto
              then show ?thesis
                using pre pre' apply auto
                apply(rule is_res_ind.intros(5))
                    apply (auto simp add: WaitBlk_simps)
                done
            qed
            apply(rule is_res_ind.intros(6))
                apply (auto simp add: WaitBlk_simps)
            done
          done
        subgoal premises pre
            using pre(11)
            apply(induct rule: is_res_ind.cases)
            subgoal
              apply auto
              apply(rule is_res_ind.intros(1))
              by auto
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal 
              using pre 
              by (auto simp add: WaitBlk_simps)
            subgoal premises pre' for t tr1 chs i
              thm pre
            proof-
              have "is_res_ind chs (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2,i)"
                using less(1)[of "(WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" i]
                using pre pre' by (auto simp add: WaitBlk_simps)
              then show ?thesis
                subgoal 
                  apply(induct rule: is_res_ind.cases)
                  using pre pre'
                       apply(auto simp add: WaitBlk_simps)
                  subgoal apply(rule is_res_ind.intros(6)) by auto
                  subgoal apply(rule is_res_ind.intros(5)) by auto
                  subgoal apply(rule is_res_ind.intros(6)) by auto
                  done
                done
            qed
            subgoal for t tr1 i chs
              using pre apply auto
              apply(rule is_res_ind.intros(6))
                  apply auto
               done
            done
          done
        done
    qed
                

lemma res_ind_combine2 : "combine_blocks chs tr1 tr2 tr \<Longrightarrow> 
      res_ind chs tr1 (t, i) (tr1',tr1'') \<Longrightarrow>
      res_ind chs tr2 (t, i) (tr2',tr2'') \<Longrightarrow>
      Ex (combine_blocks chs tr1' tr2')"
  proof(induction "length tr1 + length tr2" arbitrary: tr1 tr2 tr t i tr1' tr1'' tr2' tr2'' rule: less_induct)
    case less
    show ?case 
      using less(2)
      apply(induct rule: combine_blocks.cases)
      subgoal
        using less(3)
        apply(induct rule: res_ind.cases)
             apply auto
        using less(4)
        apply(induct rule: res_ind.cases)
             apply auto
        using combine_blocks_empty by auto
      subgoal for ch comms blks1 blks2 blks v
        using less(3)
        apply(induct rule: res_ind.cases)
             apply auto
        subgoal
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          using combine_blocks_empty by auto
        subgoal for tr1r
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          subgoal premises pre for tr2r
          proof-
            have "Ex (combine_blocks comms (tr1r) (tr2r))"
              using less(1)[of blks1 blks2 blks 0 "i-1" tr1r tr1'' tr2r tr2'']
              by(auto simp add:pre)
            then obtain tr' where 1:"combine_blocks comms (tr1r) (tr2r) tr'"
              by auto
            show ?thesis
              apply(rule exI[where x= "IOBlock ch v # tr'"])
              apply(rule )
              using 1 pre by auto
          qed
          done
        subgoal for tr1r
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          subgoal premises pre for tr2r
          proof-
            have "Ex (combine_blocks comms (tr1r) (tr2r))"
              using less(1)[of blks1 blks2 blks t "i" tr1r tr1'' tr2r tr2'']
              by(auto simp add:pre)
            then obtain tr' where 1:"combine_blocks comms (tr1r) (tr2r) tr'"
              by auto
            show ?thesis
              apply(rule exI[where x= "IOBlock ch v # tr'"])
              apply(rule )
              using 1 pre by auto
          qed
          done
        done
      subgoal for ch comms blks1 blks2 blks v
        using less(3)
        apply(induct rule: res_ind.cases)
             apply auto
        subgoal
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          using combine_blocks_empty by auto
        subgoal for tr1r
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          subgoal premises pre for tr2r
          proof-
            have "Ex (combine_blocks comms (tr1r) (tr2r))"
              using less(1)[of blks1 blks2 blks 0 "i-1" tr1r tr1'' tr2r tr2'']
              by(auto simp add:pre)
            then obtain tr' where 1:"combine_blocks comms (tr1r) (tr2r) tr'"
              by auto
            show ?thesis
              apply(rule exI[where x= "IOBlock ch v # tr'"])
              apply(rule )
              using 1 pre by auto
          qed
          done
        subgoal for tr1r
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          subgoal premises pre for tr2r
          proof-
            have "Ex (combine_blocks comms (tr1r) (tr2r))"
              using less(1)[of blks1 blks2 blks t "i" tr1r tr1'' tr2r tr2'']
              by(auto simp add:pre)
            then obtain tr' where 1:"combine_blocks comms (tr1r) (tr2r) tr'"
              by auto
            show ?thesis
              apply(rule exI[where x= "IOBlock ch v # tr'"])
              apply(rule )
              using 1 pre by auto
          qed
          done
        done
      subgoal for ch comms blks1 blks2 blks ch_type v
        using less(3)
        apply(induct rule: res_ind.cases)
        apply auto
        subgoal
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          using combine_blocks_empty by auto
        subgoal apply(cases ch_type) by auto
        subgoal premises pre for tr1r
          proof-
            have "Ex (combine_blocks comms tr1r tr2')"
              using less(1)[of blks1 blks2 blks 0 "i" tr1r tr1'' tr2' tr2'']
              using pre less(4) by auto
            then obtain tr' where 1:"combine_blocks comms tr1r tr2' tr'"
              by auto
            show ?thesis
              apply(rule exI[where x= "CommBlock ch_type ch v # tr'"])
              apply(rule )
              using 1 pre by auto
          qed
        subgoal premises pre for tr1r
          proof-
            have "Ex (combine_blocks comms (tr1r) tr2')"
              using less(1)[of blks1 blks2 blks t "i" tr1r tr1'' tr2' tr2'']
              using less(4)
              by(auto simp add:pre)
            then obtain tr' where 1:"combine_blocks comms (tr1r) (tr2') tr'"
              by auto
            show ?thesis
              apply(rule exI[where x= "CommBlock ch_type ch v # tr'"])
              apply(rule )
              using 1 pre by auto
          qed
          subgoal apply(cases ch_type) by auto
          subgoal apply(cases ch_type) by auto
          done
      subgoal for ch comms blks1 blks2 blks ch_type v
        using less(4)
        apply(induct rule: res_ind.cases)
        apply auto
        subgoal
          using less(3)
          apply(induct rule: res_ind.cases)
               apply auto
          using combine_blocks_empty by auto
        subgoal apply(cases ch_type) by auto
        subgoal premises pre for tr2r
          proof-
            have "Ex (combine_blocks comms tr1' tr2r)"
              using less(1)[of blks1 blks2 blks 0 "i" tr1' tr1'' tr2r tr2'']
              using pre less(3) by auto
            then obtain tr' where 1:"combine_blocks comms tr1' tr2r tr'"
              by auto
            show ?thesis
              apply(rule exI[where x= "CommBlock ch_type ch v # tr'"])
              apply(rule )
              using 1 pre by auto
          qed
        subgoal premises pre for tr2r
          proof-
            have "Ex (combine_blocks comms tr1' tr2r)"
              using less(1)[of blks1 blks2 blks t "i" tr1' tr1'' tr2r tr2'']
              using less(3)
              by(auto simp add:pre)
            then obtain tr' where 1:"combine_blocks comms tr1' tr2r tr'"
              by auto
            show ?thesis
              apply(rule exI[where x= "CommBlock ch_type ch v # tr'"])
              apply(rule )
              using 1 pre by auto
          qed
          subgoal apply(cases ch_type) by auto
          subgoal apply(cases ch_type) by auto
          done
      subgoal for comms blks1 blks2 blks rdy1 rdy2 tt hist hist1 hist2 rdy
        using less(3)
        apply(induct rule: res_ind.cases)
        apply auto
        subgoal
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          using combine_blocks_empty by auto
        subgoal for tr1r
          using less(4)
            apply(induct rule: res_ind.cases)
                 apply auto
            subgoal premises pre for tr2r
            proof-
              have "Ex (combine_blocks chs tr1r tr2r)"
                using less(1)[of blks1 blks2 blks "t-tt" i tr1r tr1'' tr2r tr2''] pre by auto
              then obtain tr' where 1:"combine_blocks chs tr1r tr2r tr'"
                by auto
              show ?thesis
                apply(rule exI[where x="WaitBlk tt (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (merge_rdy rdy1 rdy2) # tr'"])
                apply(rule combine_blocks_wait1)
                using pre 1 by auto
            qed
            done
          subgoal
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          using cut_time_WaitBlk[of t tt hist1 rdy1]
          using cut_time_WaitBlk[of t tt hist2 rdy2]
          apply auto
          apply rule 
          apply (rule combine_blocks_wait1)
              apply auto
          apply rule
          done                  
        done
      subgoal for comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy
        using less(3)
        apply(induct rule: res_ind.cases)
             apply auto
        subgoal
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          using combine_blocks_empty by auto
        subgoal for tr1r
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          subgoal premises pre for tr2r
            thm res_ind.intros(5)
          proof-
            have 1:"res_ind chs (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t - t1, i) (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # tr2r, tr2'')" 
              using res_ind.intros(5)[of "t-t1" "WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2" chs i tr2r tr2'']
              using pre by auto
            obtain tr' where 2:"combine_blocks comms tr1r (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # tr2r) tr'"
              using less(1)[of blks1 "WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2" blks "t-t1" i tr1r tr1'' "WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # tr2r" tr2'']
              using 1 pre by auto 
            show ?thesis
              apply(rule exI[where x="WaitBlk t1 (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (merge_rdy rdy1 rdy2) # tr'"])
              apply(rule combine_blocks_wait2)
                   apply (auto simp add: pre)
              using less(1)[of blks1 "WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2" blks "t-t1" i tr1r tr1'' "WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # tr2r" tr2'']
              using 1 2 pre by auto 
          qed
          apply(cases "t=t1")
          subgoal 
            using cut_time_WaitBlk[of t t2 hist2 rdy2]
            apply auto
            subgoal premises pre
              using pre(4)
              apply(induct rule: res_ind.cases)
                   apply auto
              apply rule
              apply (rule combine_blocks_wait1)
              using pre apply auto
              apply(rule )
              done
            done
          subgoal premises pre
          proof-
            have 1:"res_ind chs (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t - t1, 0)
   ([WaitBlk (t - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2], tr2'')"
              using res_ind.intros(6)[of "t-t1" "WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2" i chs]
              using pre apply auto
              using cut_time_WaitBlk[of "t-t1" "t2-t1" "(\<lambda>\<tau>. hist2 (\<tau> + t1))" rdy2]
              using cut_time_WaitBlk[of t t2 hist2 rdy2]
              apply auto
              done
            obtain tr' where 2:"combine_blocks chs tr1r [WaitBlk (t - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2] tr'"
              using less(1)[of blks1 "(WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" 0 tr1r tr1'' "[WaitBlk (t - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2]" tr2'']
              using 1 pre by auto
            show ?thesis
            using cut_time_WaitBlk[of t t2 hist2 rdy2] pre
            apply auto
            apply(rule exI[where x="WaitBlk t1 (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (merge_rdy rdy1 rdy2) #tr'"])
            apply(rule combine_blocks_wait2)
                 apply auto
            using 2 by auto
        qed
        done
      subgoal
          using less(4)
          apply(induct rule: res_ind.cases)
               apply auto
          using cut_time_WaitBlk[of t t1 hist1 rdy1]
          using cut_time_WaitBlk[of t t2 hist2 rdy2]
          apply auto
          apply rule
          apply (rule combine_blocks_wait1)
              apply auto
          apply rule
          done
        done
      subgoal for comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy
        using less(4)
        apply(induct rule: res_ind.cases)
             apply auto
        subgoal
          using less(3)
          apply(induct rule: res_ind.cases)
               apply auto
          using combine_blocks_empty by auto
        subgoal for tr2r
          using less(3)
          apply(induct rule: res_ind.cases)
               apply auto
          subgoal premises pre for tr1r
            proof-
            have 1:"res_ind chs (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t - t2, i) (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # tr1r, tr1'')" 
              using res_ind.intros(5)[of "t-t2" "WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1" chs i tr1r tr1'']
              using pre by auto
            obtain tr' where 2:"combine_blocks comms (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # tr1r) tr2r tr'"
              using less(1)[of "WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1" blks2 blks "t-t2" i "WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # tr1r" tr1'' "tr2r" tr2'']
              using 1 pre by auto 
            show ?thesis
              apply(rule exI[where x="WaitBlk t2 (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (merge_rdy rdy1 rdy2) # tr'"])
              apply(rule combine_blocks_wait3)
                   apply (auto simp add: pre)
              using 1 2 pre by auto 
          qed
          apply(cases "t=t2")
          subgoal 
            using cut_time_WaitBlk[of t t1 hist1 rdy1]
            apply auto
            subgoal premises pre
              using pre(4)
              apply(induct rule: res_ind.cases)
                   apply auto
              apply rule
              apply (rule combine_blocks_wait1)
              using pre apply auto
              apply(rule )
              done
            done
          subgoal premises pre
          proof-
            have 1:"res_ind chs (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t - t2, 0)
   ([WaitBlk (t - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1], tr1'')"
              using res_ind.intros(6)[of "t-t2" "WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1" i chs]
              using pre apply auto
              using cut_time_WaitBlk[of "t-t2" "t1-t2" "(\<lambda>\<tau>. hist1 (\<tau> + t2))" rdy1]
              using cut_time_WaitBlk[of t t1 hist1 rdy1]
              apply auto
              done
            obtain tr' where 2:"combine_blocks chs [WaitBlk (t - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1] tr2r tr'"
              using less(1)[of "(WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" 0 "[WaitBlk (t - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1]" tr1'' tr2r tr2'']
              using 1 pre by auto
            show ?thesis
            using cut_time_WaitBlk[of t t1 hist1 rdy1] pre
            apply auto
            apply(rule exI[where x="WaitBlk t2 (\<lambda>\<tau>. ParState (hist1 \<tau>) (hist2 \<tau>)) (merge_rdy rdy1 rdy2) #tr'"])
            apply(rule combine_blocks_wait3)
                 apply auto
            using 2 by auto
        qed
        done
      subgoal
          using less(3)
          apply(induct rule: res_ind.cases)
               apply auto
          using cut_time_WaitBlk[of t t1 hist1 rdy1]
          using cut_time_WaitBlk[of t t2 hist2 rdy2]
          apply auto
          apply rule
          apply (rule combine_blocks_wait1)
              apply auto
          apply rule
          done
        done
      done
  qed


inductive match :: "proc \<Rightarrow> state \<Rightarrow> ctr \<Rightarrow> state \<Rightarrow> bool" where
  "match Skip s cE s"
| "match (Cm (ch[!]e)) s (cO ch (e s)) s"
| "d>0 \<Longrightarrow> match (Cm (ch[!]e)) s (cW d ({ch},UNIV-{ch}) ({},UNIV) [@]cO ch (e s)) s"
| "match (Cm (ch[?]x)) s (cI ch v) (s(x:=v))"
| "d>0 \<Longrightarrow> match (Cm (ch[?]x)) s (cW d ({},UNIV) ({ch},UNIV-{ch}) [@]cI ch v) (s(x:=v))"
| "e s > 0 \<Longrightarrow> match (Wait e) s (cW (e s) ({},UNIV) ({},UNIV)) s"
| "e s \<le> 0 \<Longrightarrow> match (Wait e) s (cE) s"
| "match P1 s0 ctr1 s1 \<Longrightarrow> match P2 s1 ctr2 s2 \<Longrightarrow> match (P1;P2) s0 (ctr1[@]ctr2) s2"

inductive chs_of_proc_in :: "proc \<Rightarrow> cname set \<Rightarrow> bool" where
  "chs_of_proc_in Skip chs"
| "ch\<in>chs \<Longrightarrow> chs_of_proc_in (Cm (ch[!]e)) chs"
| "ch\<in>chs \<Longrightarrow> chs_of_proc_in (Cm (ch[?]v)) chs"
| "chs_of_proc_in (Wait e) chs"
| "chs_of_proc_in P1 chs \<Longrightarrow> chs_of_proc_in P2 chs \<Longrightarrow> chs_of_proc_in (P1;P2) chs"


lemma match_pro1 : "match P s0 ctr s1 \<Longrightarrow> big_step P s0 tr s2 \<Longrightarrow> chs_of_proc_in P chs
               \<Longrightarrow>  commit chs ctr tr \<Longrightarrow> s1=s2"
  proof(induction P arbitrary: s0 s1 s2 ctr tr)
    case pp:(Cm x)
    show ?case 
      using pp(2)
      apply(cases x)
      subgoal for ch e
        apply auto
        apply(elim sendE)
        subgoal
          using pp(1)
          apply(induct rule:match.cases)
          by auto
        subgoal for d
          using pp(1)
          apply(induct rule:match.cases)
          by auto
        done
      subgoal for ch y
        apply auto
        apply(elim receiveE)
        subgoal for v
          using pp(1)
          apply(induct rule:match.cases)
                 apply auto
          subgoal for vv
            using pp(4)
            apply(induct rule:commit.cases)
            by auto
          subgoal for d vv
            using pp(4)
            apply(induct rule:commit.cases)
                      apply auto
            using pp(3)
             apply(induct rule:chs_of_proc_in.cases)
                 apply auto
            subgoal premises pre
              using pre(4)
              apply(induct rule:commit.cases)
              using pre by auto
            by (meson WaitBlk_not_Comm(1) commitIE list.discI list.inject)
          done
        subgoal for d v
          using pp(1)
          apply(induct rule:match.cases)
                 apply auto
          subgoal for vv
            using pp(4)
            apply(induct rule:commit.cases)
            by auto
          subgoal for dd vv
            using pp(4)
            apply(induct rule:commit.cases)
                      apply auto
            using pp(3)
             apply(induct rule:chs_of_proc_in.cases)
                 apply auto
            subgoal premises pre
              using pre(4)
              apply(induct rule:commit.cases)
              using pre by auto
            subgoal premises pre
              using pre(3)
              apply(induct rule:commit.cases)
              using pre by auto
            done
          done
        done
      done
  next
    case pp:Skip
    show ?case 
      using pp(2)
      apply(elim skipE)
      using pp(1)
      apply(induct rule:match.cases)
             apply auto
      done
  next
    case pp:(Assign x1a x2)
    show ?case 
      using pp(1)
      apply(induct rule:match.cases)
      by auto
  next
    case pp:(Seq P1 P2)
    show ?case 
      using pp(3)
      apply(induct rule:match.cases)
             apply auto
      using pp(4)
      apply(elim seqE)
      using pp
      sorry
  next
    case pp:(Cond x1a P1 P2)
    show ?case 
      using pp(3)
      apply(induct rule:match.cases)
      by auto
  next
    case (Wait x)
    then show ?case sorry
  next
    case pp:(IChoice P1 P2)
    show ?case 
      using pp(3)
      apply(induct rule:match.cases)
      by auto
  next
    case pp:(EChoice x)
    show ?case 
      using pp(2)
      apply(induct rule:match.cases)
      by auto
  next
    case pp:(Rep P)
    show ?case 
      using pp(2)
      apply(induct rule:match.cases)
      by auto
  next
    case pp:(Cont x1a x2)
    show ?case 
      using pp(1)
      apply(induct rule:match.cases)
      by auto
  next
    case pp:(Interrupt x1a x2 x3)
    show ?case 
      using pp(2)
      apply(induct rule:match.cases)
      by auto
  qed
    







(*
fun res :: "cname set \<Rightarrow> trace \<Rightarrow> real \<times> nat \<Rightarrow> trace \<times> trace" where
  "res chs tr (t, i) = (
    if t < 0 then undefined else
    if t = 0 then
      if i = 0 then ([],tr) 
      else if tr = []
        then undefined 
        else if discrete_block (hd tr) then
               if discrete_in_block chs (hd tr) then
                 ((hd tr) # fst (res chs (tl tr) (0,i-1)), snd (res chs (tl tr) (0,i-1)))
               else
                 ((hd tr) # fst (res chs (tl tr) (0,i)), snd (res chs (tl tr) (0,i)))
             else undefined
    else
      if tr = [] then undefined
      else
        if discrete_block (hd tr) then
          ((hd tr) # fst (res chs (tl tr) (t,i)), snd (res chs (tl tr) (t,i)))
        else if get_time_waitblock (hd tr) \<le> t then
          ((hd tr) # fst (res chs (tl tr) (t - real_of_ereal (get_time_waitblock (hd tr)),i)),
                     snd (res chs (tl tr) (t - real_of_ereal (get_time_waitblock (hd tr)),i)))
        else if i = 0 then
          ([fst (cut_time_waitblock (hd tr) t)], snd (cut_time_waitblock (hd tr) t) # (tl tr)) 
        else undefined)"

fun is_res_defined :: "cname set \<Rightarrow> trace \<Rightarrow> real \<times> nat \<Rightarrow> bool" where
  "is_res_defined chs tr (t, i) = (if t<0 then False else
(if t=0 then (if i = 0 then True 
                       else (if tr = [] then False 
                                        else (if discrete_block (hd tr) then (if discrete_in_block chs (hd tr) then  is_res_defined chs (tl tr) (0,i-1) else is_res_defined chs (tl tr) (0,i))
                                                                        else False)))
        else (if tr = [] then False
                         else (if discrete_block (hd tr) then is_res_defined chs (tl tr) (t,i)
                                                         else (if (get_time_waitblock (hd tr)\<le>t) then  is_res_defined chs (tl tr) (t - real_of_ereal (get_time_waitblock (hd tr)),i)
                                                                                                 else (if i=0 then True 
                                                                                                              else False))))))"


lemma res_combine1 : "combine_blocks chs tr1 tr2 tr \<Longrightarrow> 
      (is_res_defined chs tr1 (t, i) \<longleftrightarrow> is_res_defined chs tr2 (t, i))"
  proof(induction "length tr1 + length tr2" arbitrary: tr1 tr2 tr t i rule: less_induct)
    case less
    show ?case 
      using less(2)
      apply(induct rule: combine_blocks.cases)
      subgoal
        by auto
      subgoal for ch comms blks1 blks2 blks v
        apply clarify
        apply(cases "t<0")
        apply simp
        apply(cases "t=0")
        subgoal 
          apply(cases "i=0")
          subgoal by auto
          apply clarify
          subgoal premises pre 
          proof-
            have 1:"is_res_defined comms (InBlock ch v # blks1) (0, i) = is_res_defined comms (blks1) (0, i-1)"
              using pre by auto
            have 2:"is_res_defined comms (OutBlock ch v # blks2) (0, i) = is_res_defined comms (blks2) (0, i-1)"
              using pre by auto
            have 3:"is_res_defined comms (blks1) (0, i-1) = is_res_defined comms (blks2) (0, i-1)"
              using less(1)[of blks1 blks2 blks 0 "i-1"] pre by auto
            show ?thesis using 1 2 3 by auto
          qed
          done
        subgoal premises pre
        proof-
          have 1:"is_res_defined comms (InBlock ch v # blks1) (t, i) = is_res_defined comms (blks1) (t, i)"
            using pre by auto
          have 2:"is_res_defined comms (OutBlock ch v # blks2) (t, i) = is_res_defined comms (blks2) (t, i)"
            using pre by auto
          have 3:"is_res_defined comms (blks1) (t, i) = is_res_defined comms (blks2) (t, i)"
            using less(1)[of blks1 blks2 blks t i] pre by auto
          show ?thesis using 1 2 3 by auto
        qed
        done
      subgoal for ch comms blks1 blks2 blks v
        apply clarify
        apply(cases "t<0")
        apply simp
        apply(cases "t=0")
        subgoal 
          apply(cases "i=0")
          subgoal by auto
          apply clarify
          subgoal premises pre 
          proof-
            have 1:"is_res_defined comms (OutBlock ch v # blks1) (0, i) = is_res_defined comms (blks1) (0, i-1)"
              using pre by auto
            have 2:"is_res_defined comms (InBlock ch v # blks2) (0, i) = is_res_defined comms (blks2) (0, i-1)"
              using pre by auto
            have 3:"is_res_defined comms (blks1) (0, i-1) = is_res_defined comms (blks2) (0, i-1)"
              using less(1)[of blks1 blks2 blks 0 "i-1"] pre by auto
            show ?thesis using 1 2 3 by auto
          qed
          done
        subgoal premises pre
        proof-
          have 1:"is_res_defined comms (OutBlock ch v # blks1) (t, i) = is_res_defined comms (blks1) (t, i)"
            using pre by auto
          have 2:"is_res_defined comms (InBlock ch v # blks2) (t, i) = is_res_defined comms (blks2) (t, i)"
            using pre by auto
          have 3:"is_res_defined comms (blks1) (t, i) = is_res_defined comms (blks2) (t, i)"
            using less(1)[of blks1 blks2 blks t i] pre by auto
          show ?thesis using 1 2 3 by auto
        qed
        done
      subgoal for ch comms blks1 blks2 blks ch_type v
        apply clarify
        apply(cases "t<0")
        apply simp
        apply(cases "t=0")
        subgoal
          apply(cases "i=0")
           apply simp
          apply(subgoal_tac"is_res_defined comms (CommBlock ch_type ch v # blks1) (t, i) = is_res_defined comms (blks1) (t, i)")
           prefer 2 subgoal apply(cases ch_type) by auto
          using less(1)[of blks1 blks2 blks t i] by auto
        apply(subgoal_tac"is_res_defined comms (CommBlock ch_type ch v # blks1) (t, i) = is_res_defined comms (blks1) (t, i)")
         prefer 2 subgoal apply(cases ch_type) by auto
        using less(1)[of blks1 blks2 blks t i] by auto
      subgoal for ch comms blks1 blks2 blks ch_type v
        apply clarify
        apply(cases "t=0")
        subgoal
          apply(cases "i=0")
           apply simp
          apply(subgoal_tac"is_res_defined comms (CommBlock ch_type ch v # blks2) (t, i) = is_res_defined comms (blks2) (t, i)")
           prefer 2 subgoal apply(cases ch_type) by auto
          using less(1)[of blks1 blks2 blks t i] by auto
        apply(subgoal_tac"is_res_defined comms (CommBlock ch_type ch v # blks2) (t, i) = is_res_defined comms (blks2) (t, i)")
         prefer 2 subgoal apply(cases ch_type) by auto
        using less(1)[of blks1 blks2 blks t i] by auto
      subgoal for comms blks1 blks2 blks rdy1 rdy2 d hist hist1 hist2 rdy
        apply(cases "t<0")
        apply simp
        apply(cases "t=0")
        subgoal
          apply(cases "i=0")
           apply simp
          apply (cases d) using WaitBlk_simps by auto
        apply(cases d)
        subgoal for r apply clarify 
          apply(simp only: WaitBlk_simps)
          apply(cases "ereal r \<le> t")
          subgoal premises pre
          proof-
            have 1:"is_res_defined comms (WaitBlock (ereal r) (restrict hist1 {0..r}) rdy1 # blks1) (t, i) = is_res_defined comms (blks1) (t-r, i)"
              using pre by auto
            have 2:"is_res_defined comms (WaitBlock (ereal r) (restrict hist2 {0..r}) rdy2 # blks2) (t, i) = is_res_defined comms (blks2) (t-r, i)"
              using pre by auto
            have 3:"is_res_defined comms (blks1) (t-r, i) = is_res_defined comms (blks2) (t-r, i)"
              using less(1)[of blks1 blks2 blks "t-r" i] pre by auto
            show ?thesis using 1 2 3 by auto
          qed
          apply(cases "i=0")
          by auto
        subgoal
          apply clarify 
          apply(simp only: WaitBlk_simps)
          apply(cases "i=0")
          by auto
        by auto
      subgoal for comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy
        apply(cases t2)
        subgoal for t2'
          apply clarify 
          apply(simp only: WaitBlk_simps)
          apply(cases "t<t1")
          subgoal 
            apply(cases "i=0")
            by auto
          apply(cases "t<t2")
          subgoal premises pre
          proof-
            have 0:"(ereal t2' - ereal t1) = ereal (t2'-t1)"
              by auto
            have 1:"is_res_defined comms (WaitBlock (ereal t1) (restrict hist1 {0..t1}) rdy1 # blks1) (t, i) = is_res_defined comms (blks1) (t-t1, i)"
              using pre by auto
            have 2:"is_res_defined comms (WaitBlock (ereal t2') (restrict hist2 {0..t2'}) rdy2 # blks2) (t, i) = is_res_defined comms (WaitBlock (ereal (t2' - t1)) (\<lambda>\<tau>\<in>{0..t2' - t1}. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i)"
              apply(cases i) 
              using pre  by auto
            have 3:"is_res_defined comms (blks1) (t-t1, i) = is_res_defined comms (WaitBlock (ereal (t2' - t1)) (\<lambda>\<tau>\<in>{0..t2' - t1}. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i)"
              using less(1)[of blks1 "(WaitBlock (ereal (t2' - t1)) (\<lambda>\<tau>\<in>{0..t2' - t1}. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" i]
              using pre
              apply(simp only: 0 WaitBlk_simps)
              by auto
            show ?thesis using 1 2 3 by auto
          qed
          subgoal premises pre
          proof-
            have 0:"(ereal t2' - ereal t1) = ereal (t2'-t1)"
              by auto
            have 1:"is_res_defined comms (WaitBlock (ereal t1) (restrict hist1 {0..t1}) rdy1 # blks1) (t, i) 
                  = is_res_defined comms (blks1) (t-t1, i)"
              using pre by auto
            have 2:"is_res_defined comms (WaitBlock (ereal t2') (restrict hist2 {0..t2'}) rdy2 # blks2) (t, i)       
                  = is_res_defined comms (WaitBlock (ereal (t2'-t1)) (\<lambda>\<tau>\<in>{0..t2' - t1}. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i)"
              using pre by auto
            have 3:"is_res_defined comms (blks1) (t-t1, i) = is_res_defined comms (WaitBlock (ereal (t2'-t1)) (\<lambda>\<tau>\<in>{0..t2' - t1}. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i)"
              using less(1)[of blks1 "(WaitBlock (ereal (t2' - t1)) (\<lambda>\<tau>\<in>{0..t2' - t1}. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" i]
              using pre
              apply(simp only: 0 WaitBlk_simps)
              by auto
            show ?thesis using 1 2 3 by auto
          qed
          done
         apply clarify 
          apply(simp only: WaitBlk_simps)
          apply(cases "t<t1")
          subgoal 
            apply(cases "i=0")
            by auto
          apply(cases "t<t2")
          subgoal premises pre
          proof-
            have 0:"(\<infinity> - ereal t1) = \<infinity>"
              by auto
            have 1:"is_res_defined comms (WaitBlock (ereal t1) (restrict hist1 {0..t1}) rdy1 # blks1) (t, i) = is_res_defined comms (blks1) (t-t1, i)"
              using pre by auto
            have 2:"is_res_defined comms (WaitBlock \<infinity> (restrict hist2 {0..}) rdy2 # blks2) (t, i) = is_res_defined comms (WaitBlock \<infinity> (\<lambda>\<tau>\<in>{0..}. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i)"
              apply(cases i) 
              using pre  by auto
            have 3:"is_res_defined comms (blks1) (t-t1, i) = is_res_defined comms (WaitBlock \<infinity> (\<lambda>\<tau>\<in>{0..}. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i)"
              using less(1)[of blks1 "(WaitBlock \<infinity> (\<lambda>\<tau>\<in>{0..}. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" i]
              using pre
              apply(simp only: 0 WaitBlk_simps)
              by auto
            show ?thesis using 1 2 3 by auto
          qed
          by auto
        subgoal for comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy
        apply(cases t1)
        subgoal for t1'
          apply clarify 
          apply(simp only: WaitBlk_simps)
          apply(cases "t<t2")
          subgoal 
            apply(cases "i=0")
            by auto
          apply(cases "t<t1")
          subgoal premises pre
          proof-
            have 0:"(ereal t1' - ereal t2) = ereal (t1'-t2)"
              by auto
            have 1:"is_res_defined comms (WaitBlock (ereal t2) (restrict hist2 {0..t2}) rdy2 # blks2) (t, i) = is_res_defined comms (blks2) (t-t2, i)"
              using pre by auto
            have 2:"is_res_defined comms (WaitBlock (ereal t1') (restrict hist1 {0..t1'}) rdy1 # blks1) (t, i) = is_res_defined comms (WaitBlock (ereal (t1' - t2)) (\<lambda>\<tau>\<in>{0..t1' - t2}. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i)"
              apply(cases i) 
              using pre  by auto
            have 3:"is_res_defined comms (blks2) (t-t2, i) = is_res_defined comms (WaitBlock (ereal (t1' - t2)) (\<lambda>\<tau>\<in>{0..t1' - t2}. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i)"
              using less(1)[of "(WaitBlock (ereal (t1' - t2)) (\<lambda>\<tau>\<in>{0..t1' - t2}. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" i]
              using pre
              apply(simp only: 0 WaitBlk_simps)
              by auto
            show ?thesis using 1 2 3 by auto
          qed
          subgoal premises pre
          proof-
            have 0:"(ereal t1' - ereal t2) = ereal (t1'-t2)"
              by auto
            have 1:"is_res_defined comms (WaitBlock (ereal t2) (restrict hist2 {0..t2}) rdy2 # blks2) (t, i) 
                  = is_res_defined comms (blks2) (t-t2, i)"
              using pre by auto
            have 2:"is_res_defined comms (WaitBlock (ereal t1') (restrict hist1 {0..t1'}) rdy1 # blks1) (t, i)       
                  = is_res_defined comms (WaitBlock (ereal (t1'-t2)) (\<lambda>\<tau>\<in>{0..t1' - t2}. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i)"
              using pre by auto
            have 3:"is_res_defined comms (blks2) (t-t2, i) = is_res_defined comms (WaitBlock (ereal (t1'-t2)) (\<lambda>\<tau>\<in>{0..t1' - t2}. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i)"
              using less(1)[of "(WaitBlock (ereal (t1' - t2)) (\<lambda>\<tau>\<in>{0..t1' - t2}. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" i]
              using pre
              apply(simp only: 0 WaitBlk_simps)
              by auto
            show ?thesis using 1 2 3 by auto
          qed
          done
         apply clarify 
          apply(simp only: WaitBlk_simps)
          apply(cases "t<t2")
          subgoal 
            apply(cases "i=0")
            by auto
          apply(cases "t<t1")
          subgoal premises pre
          proof-
            have 0:"(\<infinity> - ereal t2) = \<infinity>"
              by auto
            have 1:"is_res_defined comms (WaitBlock (ereal t2) (restrict hist2 {0..t2}) rdy2 # blks2) (t, i) = is_res_defined comms (blks2) (t-t2, i)"
              using pre by auto
            have 2:"is_res_defined comms (WaitBlock \<infinity> (restrict hist1 {0..}) rdy1 # blks1) (t, i) = is_res_defined comms (WaitBlock \<infinity> (\<lambda>\<tau>\<in>{0..}. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i)"
              apply(cases i) 
              using pre  by auto
            have 3:"is_res_defined comms (blks2) (t-t2, i) = is_res_defined comms (WaitBlock \<infinity> (\<lambda>\<tau>\<in>{0..}. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i)"
              using less(1)[of "(WaitBlock \<infinity> (\<lambda>\<tau>\<in>{0..}. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" i]
              using pre
              apply(simp only: 0 WaitBlk_simps)
              by auto
            show ?thesis using 1 2 3 by auto
          qed
          by auto
        done
    qed


lemma res_combine2 : "combine_blocks chs tr1 tr2 tr \<Longrightarrow> 
       is_res_defined chs tr1 (t, i) \<Longrightarrow>
       is_res_defined chs tr2 (t, i) \<Longrightarrow>
       \<exists> tr'. combine_blocks chs (fst (res chs tr1 (t,i))) (fst (res chs tr2 (t,i))) tr'"
  proof(induction "length tr1 + length tr2" arbitrary: tr1 tr2 tr t i rule: less_induct)
    case less
    show ?case 
      using less(2)
      apply(induct rule: combine_blocks.cases)
      subgoal using less(3,4) 
        apply(cases "t<0") apply auto
        subgoal using combine_blocks_empty by auto
        apply(cases "t=0") by auto
      subgoal for ch comms blks1 blks2 blks v
        using less(3,4) 
        apply(cases "t<0") subgoal by auto
        apply(cases "t=0")
        subgoal
          apply(cases "i=0")
          subgoal apply auto using combine_blocks_empty by auto
          apply clarify
          subgoal premises pre
          proof-
            have 1:"is_res_defined comms (InBlock ch v # blks1) (0, i) = is_res_defined comms (blks1) (0, i-1)"
              using pre by auto
            have 2:"is_res_defined comms (OutBlock ch v # blks2) (0, i) = is_res_defined comms (blks2) (0, i-1)"
              using pre by auto
            have 3:"fst (res comms (InBlock ch v # blks1) (0, i)) = InBlock ch v # fst (res comms (blks1) (0, i-1))"
              using pre by auto
            have 4:"fst (res comms (OutBlock ch v # blks2) (0, i)) = OutBlock ch v # fst (res comms (blks2) (0, i-1))"
              using pre by auto
            obtain tr where 5:"combine_blocks comms (fst (res comms blks1 (0, i - 1))) (fst (res comms blks2 (0, i - 1))) tr"
              using less(1)[of blks1 blks2 blks 0 "i-1"] pre 1 2 
              by(auto simp del: is_res_defined.simps res.simps)
            show ?thesis
              apply(rule exI[where x= "IOBlock ch v#tr"])
              apply(simp only:3 4)
              apply(rule combine_blocks_pair1)
              using 5 pre by auto
          qed
          done
        subgoal premises pre
        proof-
          have 1:"is_res_defined comms (InBlock ch v # blks1) (t, i) = is_res_defined comms (blks1) (t, i)"
            using pre by auto
          have 2:"is_res_defined comms (OutBlock ch v # blks2) (t, i) = is_res_defined comms (blks2) (t, i)"
            using pre by auto
          have 3:"fst (res comms (InBlock ch v # blks1) (t, i)) = InBlock ch v # fst (res comms (blks1) (t, i))"
            using pre by auto
          have 4:"fst (res comms (OutBlock ch v # blks2) (t, i)) = OutBlock ch v # fst (res comms (blks2) (t, i))"
            using pre by auto
          obtain tr where 5:"combine_blocks comms (fst (res comms blks1 (t, i))) (fst (res comms blks2 (t, i))) tr"
            using less(1)[of blks1 blks2 blks t i] pre 1 2 
            by(auto simp del: is_res_defined.simps res.simps)
          show ?thesis
            apply(rule exI[where x= "IOBlock ch v#tr"])
            apply(simp only:3 4 pre)
            apply(rule combine_blocks_pair1)
            using 5 pre by auto
        qed
        done
      subgoal for ch comms blks1 blks2 blks v
        using less(3,4) 
        apply(cases "t<0") subgoal by auto
        apply(cases "t=0")
        subgoal
          apply(cases "i=0")
          subgoal apply auto using combine_blocks_empty by auto
          apply clarify
          subgoal premises pre
          proof-
            have 1:"is_res_defined comms (OutBlock ch v # blks1) (0, i) = is_res_defined comms (blks1) (0, i-1)"
              using pre by auto
            have 2:"is_res_defined comms (InBlock ch v # blks2) (0, i) = is_res_defined comms (blks2) (0, i-1)"
              using pre by auto
            have 3:"fst (res comms (OutBlock ch v # blks1) (0, i)) = OutBlock ch v # fst (res comms (blks1) (0, i-1))"
              using pre by auto
            have 4:"fst (res comms (InBlock ch v # blks2) (0, i)) = InBlock ch v # fst (res comms (blks2) (0, i-1))"
              using pre by auto
            obtain tr where 5:"combine_blocks comms (fst (res comms blks1 (0, i - 1))) (fst (res comms blks2 (0, i - 1))) tr"
              using less(1)[of blks1 blks2 blks 0 "i-1"] pre 1 2 
              by(auto simp del: is_res_defined.simps res.simps)
            show ?thesis
              apply(rule exI[where x= "IOBlock ch v#tr"])
              apply(simp only:3 4)
              apply(rule combine_blocks_pair2)
              using 5 pre by auto
          qed
          done
        subgoal premises pre
        proof-
          have 1:"is_res_defined comms (OutBlock ch v # blks1) (t, i) = is_res_defined comms (blks1) (t, i)"
            using pre by auto
          have 2:"is_res_defined comms (InBlock ch v # blks2) (t, i) = is_res_defined comms (blks2) (t, i)"
            using pre by auto
          have 3:"fst (res comms (OutBlock ch v # blks1) (t, i)) = OutBlock ch v # fst (res comms (blks1) (t, i))"
            using pre by auto
          have 4:"fst (res comms (InBlock ch v # blks2) (t, i)) = InBlock ch v # fst (res comms (blks2) (t, i))"
            using pre by auto
          obtain tr where 5:"combine_blocks comms (fst (res comms blks1 (t, i))) (fst (res comms blks2 (t, i))) tr"
            using less(1)[of blks1 blks2 blks t i] pre 1 2 
            by(auto simp del: is_res_defined.simps res.simps)
          show ?thesis
            apply(rule exI[where x= "IOBlock ch v#tr"])
            apply(simp only:3 4 pre)
            apply(rule combine_blocks_pair2)
            using 5 pre by auto
        qed
        done
      subgoal for ch comms blks1 blks2 blks ch_type v
        apply(cases "t<0")
        subgoal using less by auto
        apply(cases "t=0")
        subgoal 
          apply(cases "i=0")
          subgoal using combine_blocks_empty by auto
          subgoal premises pre
          proof-
            have 1:"is_res_defined comms (CommBlock ch_type ch v # blks1) (t, i) = is_res_defined comms (blks1) (t, i)"
              using pre apply(cases ch_type) by auto
            have 2:"fst (res comms (CommBlock ch_type ch v # blks1) (t, i)) = CommBlock ch_type ch v # fst (res comms (blks1) (t, i))"
              using pre apply(cases ch_type) by auto
            obtain tr where 3:"combine_blocks comms (fst (res comms blks1 (t, i))) (fst (res comms blks2 (t, i))) tr"
              using less(1)[of blks1 blks2 blks t i] pre 1 less(3,4) 
              by(auto simp del: is_res_defined.simps res.simps)
            show ?thesis
              apply(rule exI[where x= "CommBlock ch_type ch v # tr"])
              using 2
              apply(simp only: pre)
              apply(rule combine_blocks_unpair1)
              using 3 pre by auto
          qed
          done
        subgoal premises pre
        proof-
          have 1:"is_res_defined comms (CommBlock ch_type ch v # blks1) (t, i) = is_res_defined comms (blks1) (t, i)"
            using pre apply(cases ch_type) by auto
          have 2:"fst (res comms (CommBlock ch_type ch v # blks1) (t, i)) = CommBlock ch_type ch v # fst (res comms (blks1) (t, i))"
            using pre apply(cases ch_type) by auto
          obtain tr where 3:"combine_blocks comms (fst (res comms blks1 (t, i))) (fst (res comms blks2 (t, i))) tr"
            using less(1)[of blks1 blks2 blks t i] pre 1 less(3,4) 
            by(auto simp del: is_res_defined.simps res.simps)
          show ?thesis
            apply(rule exI[where x= "CommBlock ch_type ch v # tr"])
            using 2
            apply(simp only: pre)
            apply(rule combine_blocks_unpair1)
            using 3 pre by auto
        qed
        done
      subgoal for ch comms blks1 blks2 blks ch_type v
        apply(cases "t<0")
        subgoal using less by auto
        apply(cases "t=0")
        subgoal 
          apply(cases "i=0")
          subgoal using combine_blocks_empty by auto
          subgoal premises pre
          proof-
            have 1:"is_res_defined comms (CommBlock ch_type ch v # blks2) (t, i) = is_res_defined comms (blks2) (t, i)"
              using pre apply(cases ch_type) by auto
            have 2:"fst (res comms (CommBlock ch_type ch v # blks2) (t, i)) = CommBlock ch_type ch v # fst (res comms (blks2) (t, i))"
              using pre apply(cases ch_type) by auto
            obtain tr where 3:"combine_blocks comms (fst (res comms blks1 (t, i))) (fst (res comms blks2 (t, i))) tr"
              using less(1)[of blks1 blks2 blks t i] pre 1 less(3,4) 
              by(auto simp del: is_res_defined.simps res.simps)
            show ?thesis
              apply(rule exI[where x= "CommBlock ch_type ch v # tr"])
              using 2
              apply(simp only: pre)
              apply(rule combine_blocks_unpair2)
              using 3 pre by auto
          qed
          done
        subgoal premises pre
        proof-
          have 1:"is_res_defined comms (CommBlock ch_type ch v # blks2) (t, i) = is_res_defined comms (blks2) (t, i)"
            using pre apply(cases ch_type) by auto
          have 2:"fst (res comms (CommBlock ch_type ch v # blks2) (t, i)) = CommBlock ch_type ch v # fst (res comms (blks2) (t, i))"
            using pre apply(cases ch_type) by auto
          obtain tr where 3:"combine_blocks comms (fst (res comms blks1 (t, i))) (fst (res comms blks2 (t, i))) tr"
            using less(1)[of blks1 blks2 blks t i] pre 1 less(3,4) 
            by(auto simp del: is_res_defined.simps res.simps)
          show ?thesis
            apply(rule exI[where x= "CommBlock ch_type ch v # tr"])
            using 2
            apply(simp only: pre)
            apply(rule combine_blocks_unpair2)
            using 3 pre by auto
        qed
        done
      subgoal for comms blks1 blks2 blks rdy1 rdy2 d hist hist1 hist2 rdy
        apply(cases "t<0")
        subgoal using less by auto
        apply(cases "t=0")
        subgoal 
          apply(cases "i=0")
          subgoal using combine_blocks_empty by auto
          subgoal using less(3,4) 
            apply(cases d) using WaitBlk_simps by auto
          done
        apply(cases d)
        subgoal for r
          apply(cases "t<r")
          subgoal 
            apply(cases "i=0")
            subgoal premises pre
            proof-
              have 1:"fst (res chs tr1 (t, i)) = [WaitBlk t hist1 rdy1]"
                using pre by(simp add:WaitBlk_simps)
              have 2:"fst (res chs tr2 (t, i)) = [WaitBlk t hist2 rdy2]"
                using pre by(simp add:WaitBlk_simps)
              show ?thesis
                apply(rule exI[where x="[WaitBlk t hist rdy]"])
                apply(simp only: 1 2)
                apply(rule combine_blocks_wait1)
                using combine_blocks_empty
                using pre by auto
            qed
            using less(3,4) WaitBlk_simps by auto
          subgoal premises pre
          proof-
            have 1:"is_res_defined chs tr1 (t, i) = is_res_defined chs blks1 (t-r, i)"
              using pre WaitBlk_simps by auto
            have 2:"is_res_defined chs tr2 (t, i) = is_res_defined chs blks2 (t-r, i)"
              using pre WaitBlk_simps by auto
            have 3:"fst (res chs tr1 (t, i)) = WaitBlk d hist1 rdy1 # (fst (res chs blks1 (t-r, i)))"
              using pre WaitBlk_simps by auto
            have 4:"fst (res chs tr2 (t, i)) = WaitBlk d hist2 rdy2 # (fst (res chs blks2 (t-r, i)))"
              using pre WaitBlk_simps by auto
            obtain tr where 5:"combine_blocks chs (fst (res chs blks1 (t - r, i))) (fst (res chs blks2 (t - r, i))) tr"
              using less(1)[of blks1 blks2 blks "t-r" i] pre 1 2 less(3,4) 
              by(auto simp del: is_res_defined.simps res.simps)
            show ?thesis
              apply(rule exI[where x= "WaitBlk d hist rdy # tr"])
              using 3 4
              apply(simp only:pre)
              apply(rule combine_blocks_wait1)
              using 5 pre by auto
          qed
          done
        subgoal 
          apply(cases "i=0")
          subgoal premises pre
            proof-
            have 1:"fst (res chs tr1 (t, i)) = [WaitBlk t hist1 rdy1]"
              using pre cut_time_waitblock.simps
              by(auto simp add:WaitBlk_simps) 
            have 2:"fst (res chs tr2 (t, i)) = [WaitBlk t hist2 rdy2]"
              using pre cut_time_waitblock.simps
              by(auto simp add:WaitBlk_simps)
            show ?thesis
              apply(rule exI[where x="[WaitBlk t hist rdy]"])
              apply(simp only: 1 2)
              apply(rule combine_blocks_wait1)
              using combine_blocks_empty
              using pre by auto
          qed
          using less(3,4) WaitBlk_simps by auto
        by auto
      subgoal for comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy
        apply(cases "t<0")
        subgoal using less(3,4) by auto
        apply(cases "t=0")
        subgoal apply(cases "i=0")
          subgoal using combine_blocks_empty by auto
          subgoal using less(3,4) 
            apply(cases t2) using WaitBlk_simps by auto
          done
        apply(cases t2)
        subgoal for t2'
          apply(cases "t\<le>t1")
          subgoal
          apply(cases "i=0")
            subgoal premises pre
            proof-
              have 1:"fst (res chs tr1 (t, i)) = [WaitBlk t hist1 rdy1]"
                using pre by(simp add:WaitBlk_simps)
              have 2:"fst (res chs tr2 (t, i)) = [WaitBlk t hist2 rdy2]"
                using pre by(simp add:WaitBlk_simps)
              show ?thesis
                apply(rule exI[where x="[WaitBlk t hist rdy]"])
                apply(simp only:1 2)
                apply(rule combine_blocks_wait1)
                using combine_blocks_empty
                using pre by auto
            qed
            using less(3,4) by(simp add:WaitBlk_simps)
          apply(cases "t<t2'")
          subgoal
            apply(cases "i=0")
              subgoal premises pre
              proof-
                have 1:"fst (res chs tr1 (t, i)) = WaitBlk t1 hist1 rdy1 # (fst (res chs blks1 (t-t1, i)))"
                  using pre WaitBlk_simps by auto
                have 2:"fst (res chs tr2 (t, i)) = [WaitBlk t hist2 rdy2]"
                  using pre by(simp add:WaitBlk_simps)
                have 3:"fst (res chs (WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1,i)) = [WaitBlk (t-t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2]"
                  using pre by(simp add:WaitBlk_simps)
                have 4:"Ex (combine_blocks chs (fst (res chs blks1 (t-t1, i))) (fst (res chs (WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i))))"
                  using less(1)[of blks1 "(WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" i]
                  using pre less(3,4) by(simp add:WaitBlk_simps)
                then obtain tr' where 5:"combine_blocks chs (fst (res chs blks1 (t-t1, i))) (fst (res chs (WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i))) tr'"
                  unfolding Ex_def by blast
                have 6:"Ex (combine_blocks chs (fst (res chs tr1 (t, i))) [WaitBlk t1 hist2 rdy2,WaitBlk (t-t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2])"
                  apply(rule exI[where x="WaitBlk (ereal t1) hist rdy # tr'"])
                  apply(simp only:1)
                  apply(rule combine_blocks_wait1)
                  using 5 pre 3 by auto
                show ?thesis
                  apply(simp only:2)
                  using combine_wait_block_prop1[of t1 t chs "(fst (res chs tr1 (t, i)))" "[]" hist2 rdy2 "[]"]
                  using pre 6 by auto
              qed
              using less(3,4) by(simp add:WaitBlk_simps)
            subgoal premises pre
            proof-
              have 1:"fst (res chs tr1 (t, i)) = WaitBlk t1 hist1 rdy1 # (fst (res chs blks1 (t-t1, i)))"
                using pre WaitBlk_simps by auto
              have 2:"fst (res chs tr2 (t, i)) = WaitBlk t2 hist2 rdy2 # (fst (res chs blks2 (t-t2', i)))"
                using pre WaitBlk_simps by auto
              have 3:"fst (res chs (WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i)) = WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # (fst (res chs blks2 (t-t2', i)))"
                using pre WaitBlk_simps by auto
              have 4:"Ex (combine_blocks chs (fst (res chs blks1 (t-t1, i))) (fst (res chs (WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i))))"
                using less(1)[of blks1 "(WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" i]
                using pre less(3,4) by(simp add:WaitBlk_simps)
              then obtain tr' where 5:"combine_blocks chs (fst (res chs blks1 (t-t1, i))) (fst (res chs (WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i))) tr'"
                unfolding Ex_def by blast
              have 6:"Ex (combine_blocks chs (fst (res chs tr1 (t, i))) (WaitBlk t1 hist2 rdy2 # WaitBlk (t2-t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # (fst (res chs blks2 (t-t2', i)))))"
                apply(rule exI[where x="WaitBlk (ereal t1) hist rdy # tr'"])
                apply(auto simp only:1)
                apply(rule combine_blocks_wait1)
                using 5 pre 3 by auto
              show ?thesis 
                apply(simp only: 2)
                using combine_wait_block_prop1[of t1 t2 chs "(fst (res chs tr1 (t, i)))" "[]" hist2 rdy2 "fst (res chs blks2 (t - t2', i))"]
                using pre 6 by auto
            qed
            done
          subgoal 
          apply(cases "t\<le>t1")
          subgoal
          apply(cases "i=0")
            subgoal premises pre
            proof-
              have 1:"fst (res chs tr1 (t, i)) = [WaitBlk t hist1 rdy1]"
                using pre by(simp add:WaitBlk_simps)
              have 2:"fst (res chs tr2 (t, i)) = [WaitBlk t hist2 rdy2]"
                using pre cut_time_waitblock.simps
                by(auto simp add:WaitBlk_simps)
              show ?thesis
                apply(rule exI[where x="[WaitBlk t hist rdy]"])
                apply(simp only:1 2)
                apply(rule combine_blocks_wait1)
                using combine_blocks_empty
                using pre by auto
            qed
            using less(3,4) by(simp add:WaitBlk_simps)
          subgoal
            apply(cases "i=0")
              subgoal premises pre
              proof-
                have 1:"fst (res chs tr1 (t, i)) = WaitBlk t1 hist1 rdy1 # (fst (res chs blks1 (t-t1, i)))"
                  using pre WaitBlk_simps by auto
                have 2:"fst (res chs tr2 (t, i)) = [WaitBlk t hist2 rdy2]"
                  using pre cut_time_waitblock.simps
                  by(auto simp add:WaitBlk_simps)
                have 3:"fst (res chs (WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1,i)) = [WaitBlk (t-t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2]"
                  using pre cut_time_waitblock.simps
                  by(auto simp add:WaitBlk_simps)
                have 4:"Ex (combine_blocks chs (fst (res chs blks1 (t-t1, i))) (fst (res chs (WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i))))"
                  using less(1)[of blks1 "(WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)" blks "t-t1" i]
                  using pre less(3,4) by(simp add:WaitBlk_simps)
                then obtain tr' where 5:"combine_blocks chs (fst (res chs blks1 (t-t1, i))) (fst (res chs (WaitBlk (t2 - ereal t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2) (t-t1, i))) tr'"
                  unfolding Ex_def by blast
                have 6:"Ex (combine_blocks chs (fst (res chs tr1 (t, i))) [WaitBlk t1 hist2 rdy2,WaitBlk (t-t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2])"
                  apply(rule exI[where x="WaitBlk (ereal t1) hist rdy # tr'"])
                  apply(simp only:1)
                  apply(rule combine_blocks_wait1)
                  using 5 pre 3 by auto
                show ?thesis
                  apply(simp only:2)
                  using combine_wait_block_prop1[of t1 t chs "(fst (res chs tr1 (t, i)))" "[]" hist2 rdy2 "[]"]
                  using pre 6 by auto
              qed
              using less(3,4) by(simp add:WaitBlk_simps)
            done
          by auto
      subgoal for comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy
        apply(cases "t<0")
        subgoal using less(3,4) by auto
        apply(cases "t=0")
        subgoal apply(cases "i=0")
          subgoal using combine_blocks_empty by auto
          subgoal using less(3,4) 
            apply(cases t1) using WaitBlk_simps by auto
          done
        apply(cases t1)
        subgoal for t1'
          apply(cases "t\<le>t2")
          subgoal
          apply(cases "i=0")
            subgoal premises pre
            proof-
              have 1:"fst (res chs tr1 (t, i)) = [WaitBlk t hist1 rdy1]"
                using pre by(simp add:WaitBlk_simps)
              have 2:"fst (res chs tr2 (t, i)) = [WaitBlk t hist2 rdy2]"
                using pre by(simp add:WaitBlk_simps)
              show ?thesis
                apply(rule exI[where x="[WaitBlk t hist rdy]"])
                apply(simp only:1 2)
                apply(rule combine_blocks_wait1)
                using combine_blocks_empty
                using pre by auto
            qed
            using less(3,4) by(simp add:WaitBlk_simps)
          apply(cases "t<t1'")
          subgoal
            apply(cases "i=0")
              subgoal premises pre
              proof-
                have 1:"fst (res chs tr2 (t, i)) = WaitBlk t2 hist2 rdy2 # (fst (res chs blks2 (t-t2, i)))"
                  using pre WaitBlk_simps by auto
                have 2:"fst (res chs tr1 (t, i)) = [WaitBlk t hist1 rdy1]"
                  using pre by(simp add:WaitBlk_simps)
                have 3:"fst (res chs (WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2,i)) = [WaitBlk (t-t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1]"
                  using pre by(simp add:WaitBlk_simps)
                have 4:"Ex (combine_blocks chs (fst (res chs (WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i))) (fst (res chs blks2 (t-t2, i))))"
                  using less(1)[of "(WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" i]
                  using pre less(3,4) by(simp add:WaitBlk_simps)
                then obtain tr' where 5:"combine_blocks chs (fst (res chs (WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i))) (fst (res chs blks2 (t-t2, i))) tr'"
                  unfolding Ex_def by blast
                have 6:"Ex (combine_blocks chs [WaitBlk t2 hist1 rdy1,WaitBlk (t-t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1] (fst (res chs tr2 (t, i))))"
                  apply(rule exI[where x="WaitBlk (ereal t2) hist rdy # tr'"])
                  apply(simp only:1)
                  apply(rule combine_blocks_wait1)
                  using 5 pre 3 by auto
                show ?thesis
                  apply(simp only:2)
                  using combine_wait_block_prop2[of t2 t chs  "[]" hist1 rdy1 "[]" "(fst (res chs tr2 (t, i)))"]
                  using pre 6 by auto
              qed
              using less(3,4) by(simp add:WaitBlk_simps)
            subgoal premises pre
            proof-
              have 1:"fst (res chs tr1 (t, i)) = WaitBlk t1 hist1 rdy1 # (fst (res chs blks1 (t-t1', i)))"
                using pre WaitBlk_simps by auto
              have 2:"fst (res chs tr2 (t, i)) = WaitBlk t2 hist2 rdy2 # (fst (res chs blks2 (t-t2, i)))"
                using pre WaitBlk_simps by auto
              have 3:"fst (res chs (WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i)) = WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # (fst (res chs blks1 (t-t1', i)))"
                using pre WaitBlk_simps by auto
              have 4:"Ex (combine_blocks chs (fst (res chs (WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i))) (fst (res chs blks2 (t-t2, i))))"
                using less(1)[of  "(WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" i]
                using pre less(3,4) by(simp add:WaitBlk_simps)
              then obtain tr' where 5:"combine_blocks chs (fst (res chs (WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i))) (fst (res chs blks2 (t-t2, i))) tr'"
                unfolding Ex_def by blast
              have 6:"Ex (combine_blocks chs (WaitBlk t2 hist1 rdy1 # WaitBlk (t1-t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # (fst (res chs blks1 (t-t1', i)))) (fst (res chs tr2 (t, i))))"
                apply(rule exI[where x="WaitBlk (ereal t2) hist rdy # tr'"])
                apply(auto simp only:2)
                apply(rule combine_blocks_wait1)
                using 5 pre 3 by auto
              show ?thesis 
                apply(simp only: 1)
                using combine_wait_block_prop2[of t2 t1 chs  "[]" hist1 rdy1 "fst (res chs blks1 (t - t1', i))" "(fst (res chs tr2 (t, i)))"]
                using pre 6 by auto
            qed
            done
          subgoal 
          apply(cases "t\<le>t2")
          subgoal
          apply(cases "i=0")
            subgoal premises pre
            proof-
              have 1:"fst (res chs tr2 (t, i)) = [WaitBlk t hist2 rdy2]"
                using pre by(simp add:WaitBlk_simps)
              have 2:"fst (res chs tr1 (t, i)) = [WaitBlk t hist1 rdy1]"
                using pre cut_time_waitblock.simps
                by(auto simp add:WaitBlk_simps)
              show ?thesis
                apply(rule exI[where x="[WaitBlk t hist rdy]"])
                apply(simp only:1 2)
                apply(rule combine_blocks_wait1)
                using combine_blocks_empty
                using pre by auto
            qed
            using less(3,4) by(simp add:WaitBlk_simps)
          subgoal
            apply(cases "i=0")
              subgoal premises pre
              proof-
                have 1:"fst (res chs tr2 (t, i)) = WaitBlk t2 hist2 rdy2 # (fst (res chs blks2 (t-t2, i)))"
                  using pre WaitBlk_simps by auto
                have 2:"fst (res chs tr1 (t, i)) = [WaitBlk t hist1 rdy1]"
                  using pre cut_time_waitblock.simps
                  by(auto simp add:WaitBlk_simps)
                have 3:"fst (res chs (WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2,i)) = [WaitBlk (t-t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1]"
                  using pre cut_time_waitblock.simps
                  by(auto simp add:WaitBlk_simps)
                have 4:"Ex (combine_blocks chs (fst (res chs (WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i))) (fst (res chs blks2 (t-t2, i))))"
                  using less(1)[of "(WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)" blks2 blks "t-t2" i]
                  using pre less(3,4) by(simp add:WaitBlk_simps)
                then obtain tr' where 5:"combine_blocks chs (fst (res chs (WaitBlk (t1 - ereal t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1) (t-t2, i))) (fst (res chs blks2 (t-t2, i))) tr'"
                  unfolding Ex_def by blast
                have 6:"Ex (combine_blocks chs [WaitBlk t2 hist1 rdy1,WaitBlk (t-t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1] (fst (res chs tr2 (t, i))))"
                  apply(rule exI[where x="WaitBlk (ereal t2) hist rdy # tr'"])
                  apply(simp only:1)
                  apply(rule combine_blocks_wait1)
                  using 5 pre 3 by auto
                show ?thesis
                  apply(simp only:2)
                  using combine_wait_block_prop2[of t2 t chs "[]" hist1 rdy1 "[]" "(fst (res chs tr2 (t, i)))"]
                  using pre 6 by auto
              qed
              using less(3,4) by(simp add:WaitBlk_simps)
            done
          by auto
        done  
 qed

*)
















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
  subgoal premises pre for tr3 tr1 tr2 s11 s12 s21 s22
  proof-
      obtain tr3' where cc:"combine_blocks chs tr2 tr1 tr3'"
      using combine_reverse_prop[of chs tr1 tr2] pre(1) by auto
      have 1:"commit chs g2 tr2" if cond:"commit chs a2 tr1"
      proof-
        have "P2 s21 \<longrightarrow>
       big_step p2 s21 tr2 s22 \<longrightarrow>
       commit chs a2 tr1 \<longrightarrow>
       combine_blocks chs (tr2) (tr1) tr3' \<longrightarrow>
       Q2 s22 (tr2) \<and> commit chs g2 tr2 \<and> Ex (combine_blocks chs [] [])"
          using assms(2) unfolding Validc_def 
          by (metis append_self_conv2 self_append_conv)
        then show ?thesis
          using pre cc cond
          by auto
      qed
      have 2:"commit chs g1 tr1" if cond:"commit chs a1 tr2"
      proof-
        have "P1 s11 \<longrightarrow>
       big_step p1 s11 tr1 s12 \<longrightarrow>
       commit chs a1 tr2 \<longrightarrow>
       combine_blocks chs (tr1) (tr2) tr3 \<longrightarrow>
       Q1 s12 (tr1) \<and> commit chs g1 tr1 \<and> Ex (combine_blocks chs [] [])"
          using assms(1) unfolding Validc_def 
          by (metis append_self_conv2 self_append_conv)
       then show ?thesis
          using pre cond
          by auto
      qed
      have 3:"commit chs g1 tr1"
      proof(rule ccontr)
        assume "\<not> commit chs g1 tr1"
        then have 41:"\<not> commit chs g1 tr1 \<and> \<not> commit chs g2 tr2 \<and> \<not> commit chs a2 tr1 \<and> \<not> commit chs a1 tr2"
          using 1 2 assms by auto
        have "False"
          using 41 pre assms(1)
          unfolding Validc_def 



      
    

    
      





end