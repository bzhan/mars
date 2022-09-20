theory System_scheduler1
  imports System_scheduler
begin




fun tdsch2' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "tdsch2' k2 k1 0 dis_s2 (Task st2 ent2 t2) task_s2 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> (emp\<^sub>t tr)"
| "tdsch2' 0 (Suc k1') (Suc kk') dis_s2 (Task st2 ent2 t2) task_s2 dis_s1 (Task WAIT ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> 9 / 200 - dis_s1 CHR ''t'' = 0 \<and>
   tdsch2' 0 k1' (Suc kk') dis_s2 (Task st2 ent2 t2) task_s2 (dis_s1(CHR ''t'' := 0)) (Task READY 0 t1) (task_s1(CHR ''t'' := 0)) (Sch p rn rp) s tr"
| "tdsch2' 0 (Suc k1') (Suc kk') dis_s2 (Task st2 ent2 t2) task_s2 dis_s1 (Task READY ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> (if rn \<noteq> - 1 then False else 
  tdsch2' 0 k1' kk' dis_s2 (Task st2 ent2 t2) task_s2 dis_s1 (Task RUNNING (Suc 0) t1) (task_s1(CHR ''c'' := up_ent_c ent1 (task_s1 CHR ''c''))) (Sch p 1 2) (s(CHR ''p'' := 2)) tr)"
| "tdsch2' 0 (Suc k1') (Suc kk') dis_s2 (Task st2 ent2 t2) task_s2 dis_s1 (Task RUNNING ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> (if length p > 0 then False else
  tdsch2' 0 k1' kk' dis_s2 (Task st2 ent2 t2) task_s2 dis_s1 (Task WAIT ent1 t1) task_s1 (Sch [] (- 1) (- 1)) s tr)"
| "tdsch2' (Suc k2') 0 (Suc kk') dis_s2 (Task WAIT ent2 t2) task_s2 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> (9 / 200 - dis_s2 CHR ''t'' = 0 \<and>
  tdsch2' k2' 0 (Suc kk') (dis_s2(CHR ''t'' := 0)) (Task READY 0 t2) (task_s2(CHR ''t'' := 0)) dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr)"
| "tdsch2' (Suc k2') 0 (Suc kk') dis_s2 (Task READY ent2 t2) task_s2 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> 
  (\<up>(rn = -1 \<and> 1 > rp) \<and>\<^sub>t
  tdsch2' k2' 0 kk' dis_s2 (Task RUNNING (Suc 0) t2) (task_s2(CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c''))) dis_s1 (Task st1 ent1 t1) task_s1 (Sch p 2 1) (s(CHR ''p'' := 1))) tr \<or>
  (\<up>(rp \<ge> 1 \<and> kk'> 0 \<and> 9 / 200 - task_s2 CHR ''t'' = 0) \<and>\<^sub>t
  tdsch2' k2' 0 (kk'-1) (dis_s2(CHR ''t'' := 9 / 200)) (Task WAIT ent2 1) (task_s2(CHR ''t'' := 9 / 200)) dis_s1 (Task st1 ent1 t1) task_s1 (Sch (del_proc (p @ [(1, 2)]) 2) rn rp)  (s(CHR ''p'' := 1))) tr"
| "tdsch2' (Suc k2') 0 (Suc kk') dis_s2 (Task RUNNING ent2 t2) task_s2 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> 
  (\<up>(p = []) \<and>\<^sub>t  tdsch2' k2' 0  kk' dis_s2 (Task WAIT ent2 t2) task_s2 dis_s1 (Task st1 ent1 t1) task_s1 (Sch [] (- 1) (- 1)) s) tr"




lemma conj_join_pure_true [simp]:
  "(\<up>True \<and>\<^sub>t P) = P"
  by (auto simp add: pure_assn_def conj_assn_def join_assn_def)



lemma combine_wait_orig_emp1:
"combine_assn chs (wait_orig_assn d p rdy P) emp\<^sub>t \<Longrightarrow>\<^sub>t \<up>(d=0) \<and>\<^sub>t (combine_assn chs P emp\<^sub>t)"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1
    apply(cases rule: wait_orig_assn.cases[of d p rdy P tr1])
    unfolding conj_assn_def pure_assn_def
      apply auto
     by (auto elim!: sync_elims)
  done

lemma combine_emp_wait_orig1:
"combine_assn chs emp\<^sub>t (wait_orig_assn d p rdy P) \<Longrightarrow>\<^sub>t \<up>(d=0) \<and>\<^sub>t (combine_assn chs emp\<^sub>t P)"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1
    apply(cases rule: wait_orig_assn.cases[of d p rdy P tr1])
    unfolding conj_assn_def pure_assn_def
      apply auto
     by (auto elim!: sync_elims)
  done

lemma combine_emp_in_0orig_vassm'1:
  assumes "ch \<in> chs"
  shows "combine_assn chs emp\<^sub>t (in_0orig_vassm'_assn ch V P) \<Longrightarrow>\<^sub>t Q"
  unfolding combine_assn_def entails_tassn_def 
  apply auto
  subgoal for tr tr1 tr2
    apply(auto simp add: emp_assn_def)
    apply(cases rule: in_0orig_vassm'_assn.cases[of ch V P tr2])
      apply simp
    subgoal for v tr2'
      apply auto
      using assms
      by (auto elim!: sync_elims)
    subgoal for v tr2'
      apply auto
      using assms
      by (auto elim!: sync_elims)
    done
  done

lemma combine_emp_waitin_tguar'_vassm'1:
  assumes "ch \<in> chs"
  shows "combine_assn chs emp\<^sub>t (waitin_tguar'_vassm'_assn S p rdy ch V P) \<Longrightarrow>\<^sub>t Q"
  unfolding combine_assn_def entails_tassn_def 
  apply auto
  subgoal for tr tr1 tr2
    apply(auto simp add: emp_assn_def)
    apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S p rdy ch V P tr2])
      apply simp
    subgoal 
      apply auto
      using assms
      by (auto elim!: sync_elims)
    subgoal
      apply auto
      using assms
      by (auto elim!: sync_elims)
    subgoal
      apply auto
      using assms
      by (auto elim!: sync_elims)
    subgoal
      apply auto
      using assms
      by (auto elim!: sync_elims)
    done
  done


lemma combine_wait_orig_in_0orig_vassm'1:
  assumes "ch\<in>chs"
  shows "combine_assn chs (wait_orig_assn d p rdy P) (in_0orig_vassm'_assn ch V Q) \<Longrightarrow>\<^sub>t \<up>(d=0) \<and>\<^sub>t combine_assn chs (P) (in_0orig_vassm'_assn ch V Q)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d p rdy P tr1])
      apply simp
    subgoal
      by (auto simp add:pure_assn_def conj_assn_def)
    subgoal for tr1'
      apply(cases rule:in_0orig_vassm'_assn.cases[of ch V Q tr2])
        apply auto
      subgoal
        using assms
        by (auto elim!: sync_elims)
      subgoal
        using assms
        by (auto elim!: sync_elims)
      done
    done
  done



lemma combine_out_0assm_in_0orig_vassm'1:
"ch \<in> chs \<and> v \<in> V\<Longrightarrow> combine_assn chs (out_0assm_assn ch v P)(in_0orig_vassm'_assn ch V Q) \<Longrightarrow>\<^sub>t combine_assn chs P (Q v)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:out_0assm_assn.cases[of ch v P tr1])
      apply simp
    subgoal 
      apply(cases rule:in_0orig_vassm'_assn.cases[of ch V Q tr2])
        apply auto
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      done
    subgoal 
      apply(cases rule:in_0orig_vassm'_assn.cases[of ch V Q tr2])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      done
    done
  done


lemma combine_out_0assm_in_0orig_vassm'2:
"ch1 \<in> chs \<and> ch2 \<in> chs \<and> ch1\<noteq>ch2 \<Longrightarrow> combine_assn chs (out_0assm_assn ch1 v P)(in_0orig_vassm'_assn ch2 V Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:out_0assm_assn.cases[of ch1 v P tr1])
      apply simp
    subgoal 
      apply(cases rule:in_0orig_vassm'_assn.cases[of ch2 V Q tr2])
        apply auto
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      done
    subgoal 
      apply(cases rule:in_0orig_vassm'_assn.cases[of ch2 V Q tr2])
        apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      done
    done
  done

lemma combine_waitin_tguar'_vassm'_in_0orig_vassm'1:
"ch1\<in>chs \<and> ch2\<in>chs \<Longrightarrow> combine_assn chs (waitin_tguar'_vassm'_assn S p rdy ch1 V P)(in_0orig_vassm'_assn ch2 W Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:in_0orig_vassm'_assn.cases[of ch2 W Q tr2])
      apply auto
    subgoal
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch1 V P tr1])
          apply auto
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        by (auto elim!: sync_elims)
      done
    subgoal
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch1 V P tr1])
          apply auto
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        apply(elim combine_blocks_pairE)
        by auto
      subgoal
        by (auto elim!: sync_elims)
      done
    done
  done

lemma combine_waitin_tguar'_vassm'_out_0assm1:
"ch \<in> chs \<and> v \<in> V \<and> ch \<in> snd rdy \<Longrightarrow> combine_assn chs (waitin_tguar'_vassm'_assn S p rdy ch V P)(out_0assm_assn ch v Q) \<Longrightarrow>\<^sub>t combine_assn chs (P v 0) Q"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of ch v Q tr2])
      apply simp
     apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S p rdy ch V P tr1])
         apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    subgoal
      by (auto elim!: sync_elims)
    apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S p rdy ch V P tr1])
        apply auto 
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      apply(elim combine_blocks_waitE1)
      apply(cases rdy)
      by auto
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      apply(elim combine_blocks_waitE1)
      apply(cases rdy)
      by auto
    done
  done

lemma combine_out_0assm_rdy_emp1:
"ch\<in>chs \<Longrightarrow> combine_assn chs (out_0assm_rdy_assn ch v rdy P) emp\<^sub>t \<Longrightarrow>\<^sub>t Q"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_0assm_rdy_assn.cases[of ch v rdy P])
      apply auto
    by (auto elim!: sync_elims)
  done

lemma combine_in_0assm_rdy_emp1:
"ch\<in>chs \<Longrightarrow> combine_assn chs (in_0assm_rdy_assn ch v rdy P) emp\<^sub>t \<Longrightarrow>\<^sub>t Q"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:in_0assm_rdy_assn.cases[of ch v rdy P])
      apply auto
    by (auto elim!: sync_elims)
  done

lemma combine_out_0assm_rdy_in_0orig_vassm'1:
"ch \<in> chs \<and> v \<in> V\<Longrightarrow> combine_assn chs (out_0assm_rdy_assn ch v rdy P) (in_0orig_vassm'_assn ch V Q) \<Longrightarrow>\<^sub>t combine_assn chs P (Q v)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_rdy_assn.cases[of ch v rdy P tr1])
      apply simp
     apply(cases rule: in_0orig_vassm'_assn.cases[of ch V Q tr2])
       apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    apply(cases rule: in_0orig_vassm'_assn.cases[of ch V Q tr2])
       apply auto
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      by (auto elim!: sync_elims)
    done
  done


lemma combine_out_0assm_rdy_in_0orig_vassm'2:
"ch1\<in>chs\<and>ch2\<in>chs\<and>ch1\<noteq>ch2 \<Longrightarrow> combine_assn chs (out_0assm_rdy_assn ch1 v rdy P) (in_0orig_vassm'_assn ch2 V Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_rdy_assn.cases[of ch1 v rdy P tr1])
      apply simp
     apply(cases rule: in_0orig_vassm'_assn.cases[of ch2 V Q tr2])
       apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    apply(cases rule: in_0orig_vassm'_assn.cases[of ch2 V Q tr2])
       apply auto
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      by (auto elim!: sync_elims)
    done
  done


lemma combine_in_0assm_rdy_in_0orig_vassm'2:
"ch1\<in>chs\<and>ch2\<in>chs\<and>ch1\<noteq>ch2 \<Longrightarrow> combine_assn chs (in_0assm_rdy_assn ch1 v rdy P) (in_0orig_vassm'_assn ch2 V Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: in_0assm_rdy_assn.cases[of ch1 v rdy P tr1])
      apply simp
     apply(cases rule: in_0orig_vassm'_assn.cases[of ch2 V Q tr2])
       apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    apply(cases rule: in_0orig_vassm'_assn.cases[of ch2 V Q tr2])
       apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    apply(cases rule: in_0orig_vassm'_assn.cases[of ch2 V Q tr2])
       apply auto
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      by (auto elim!: sync_elims)
    done
  done

lemma combine_in_0assm_rdy_out_0assm1:
"ch\<in>chs \<and> v\<in>V \<Longrightarrow> combine_assn chs (in_0assm_rdy_assn ch V rdy P) (out_0assm_assn ch v Q) \<Longrightarrow>\<^sub>t combine_assn chs P Q"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases [of ch v Q tr2])
      apply auto
     apply(cases rule: in_0assm_rdy_assn.cases [of ch V rdy P tr1])
        apply auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    subgoal
      apply(elim combine_blocks_pairE)
      by auto
    subgoal
      by (auto elim!: sync_elims)
    apply(cases rule: in_0assm_rdy_assn.cases [of ch V rdy P tr1])
      apply auto
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      apply(elim combine_blocks_waitE1)
      apply(cases rdy)
      by auto
    done
  done

fun properl1 :: "(real \<times> tid) list \<Rightarrow> bool" where
  "properl1 [] = True"
| "properl1 ((rp,rn) # v) = (properl1 v \<and> properp rn rp \<and> rn > 0 \<and> rn \<noteq> 1 \<and> rn \<noteq> 2)"

lemma properl1_p1:
"properl1 (p @ [(a, b)]) = (properl1 p \<and> properp b a \<and> b > 0 \<and> b \<noteq> 1 \<and> b \<noteq> 2)"
proof(induction p arbitrary: a b)
  case Nil
  then show ?case 
    by auto
next
  case (Cons c p)
  show ?case
    apply(cases c)
    subgoal for ca cb
      apply simp
      using Cons[of a b]
      by auto
done
qed

lemma properl1_p2:
"properl1 p \<Longrightarrow> properp rn rp \<Longrightarrow> properp (snd(get_max_default (rp,rn) p)) (fst(get_max_default (rp,rn) p))"
proof(induction p arbitrary: rn rp)
  case Nil
  then show ?case 
    by auto
next
  case (Cons c p)
  then show ?case 
    apply(cases c)
    subgoal for a b
      by auto
    done
qed


lemma properl1_p3:
"properl1 p \<Longrightarrow> properp (snd (get_max p)) (fst (get_max p)) "
proof(induction p)
  case Nil
  then show ?case 
    apply auto
    unfolding properp_def
    by auto
next
  case (Cons c p)
  then show ?case 
    apply(cases c)
    subgoal for a b
      apply auto
      apply(rule properl1_p2)
      by auto
    done
qed


lemma properl1_p4:
"properl1 p \<Longrightarrow> properl1 (del_proc p t)"
proof(induction p)
  case Nil
  then show ?case 
    by auto
next
  case (Cons c p)
  then show ?case 
    apply(cases c)
    subgoal for a b
     by auto
    done
qed



lemma properl1_getmax2:
"properl1 p \<Longrightarrow> snd (get_max p) \<noteq> 1 \<and> (gb \<noteq> 1 \<longrightarrow> snd (get_max_default (ga, gb) p) \<noteq> 1)"
proof(induction p arbitrary: ga gb)
  case Nil
  then show ?case 
    by auto
next
  case (Cons h p)
  then show ?case 
    apply (cases h)
    subgoal for ha hb
      by auto
    done
qed

lemma properl1_getmax21:
"properl1 p \<Longrightarrow> snd (get_max p) \<noteq> 2 \<and> (gb \<noteq> 2 \<longrightarrow> snd (get_max_default (ga, gb) p) \<noteq> 2)"
proof(induction p arbitrary: ga gb)
  case Nil
  then show ?case 
    by auto
next
  case (Cons h p)
  then show ?case 
    apply (cases h)
    subgoal for ha hb
      by auto
    done
qed

lemma properl1_p5':
  "properl1 ((a,b)#p) \<Longrightarrow> snd(get_max_default (a,b) p) > 0"
proof(induction p arbitrary: a b)
  case Nil
  then show ?case 
    by auto
next
  case (Cons g p)
  then show ?case 
    apply(cases g)
    by auto
qed

lemma properl1_p5:
"length p > 0 \<Longrightarrow> properl1 p \<Longrightarrow> properp (snd (get_max p)) (fst (get_max p)) \<and> (snd (get_max p)) > 0 \<and> (snd (get_max p)) \<noteq> 1 \<and> (snd (get_max p)) \<noteq> 2"
proof(induction p)
  case Nil
  then show ?case 
    by auto
next
  case (Cons c p)
  then show ?case 
    apply(cases c)
    subgoal for a b
      apply auto
      subgoal
      apply(rule properl1_p2)
         apply auto
        done
       prefer 2
      subgoal
        using properl1_getmax2 properl1_getmax21 apply auto
        done
      using properl1_p5'[of 1 2 p] 
      apply auto
      unfolding properp_def
      by auto
    done
qed

lemma properl1_p6:
"properl1 p \<Longrightarrow> properl1 (del_proc (p@[(1,2)]) 2)"
proof(induction p)
  case Nil
  then show ?case 
    by auto
next
  case (Cons c p)
  then show ?case 
    apply(cases c)
    subgoal for a b
     by auto
    done
qed

definition proper1 :: "estate \<Rightarrow> bool " where
"proper1 schs = ((properp (run_now schs) (run_prior schs)) \<and> properl1 (pool schs))"



definition propc1 :: "nat \<Rightarrow> estate \<Rightarrow> nat \<Rightarrow> estate \<Rightarrow> estate \<Rightarrow> bool" where
"propc1 k1 task_es1 k2 task_es2 schs = ((k1>0 \<longrightarrow>(status task_es1 = RUNNING \<longleftrightarrow> run_now schs = 1)) \<and> (k2>0 \<longrightarrow>(status task_es2 = RUNNING \<longleftrightarrow> run_now schs = 2)))"



lemma combine_taskdis_sch1':
  "task_dis_assn' 2 k2 dis_s2 task_es2 task_s2 tr1 \<Longrightarrow>
   tdsch1' k1 kk dis_s1 task_es1 task_s1 schs s tr2 \<Longrightarrow>
   task_prior task_es1 = 2 \<Longrightarrow>
   task_prior task_es2 = 1 \<Longrightarrow>
   propc1 k1 task_es1 k2 task_es2 schs \<Longrightarrow> 
   proper1 schs \<Longrightarrow>
   combine_blocks {req_ch 2, preempt_ch 2, run_ch 2, free_ch 2, exit_ch 2} tr1 tr2 tr \<Longrightarrow>
   tdsch2' k2 k1 kk dis_s2 task_es2 task_s2 dis_s1 task_es1 task_s1 schs s tr"
   proof(induction " k2+k1+kk"  arbitrary: k2 k1 kk dis_s2 task_es2 task_s2 dis_s1 task_es1 task_s1 schs s tr1 tr2 tr rule: less_induct)
      case less
      then show ?case 
        apply(cases k2)
        subgoal 
          apply(cases kk)
          subgoal 
            apply(cases k1)
            subgoal
              apply(cases task_es1)
                apply auto
              apply(cases task_es2)
                apply auto
              apply(cases schs)
              apply (auto simp add: emp_assn_def)
              by(auto elim: sync_elims)
            subgoal for k1'
              apply(cases task_es1)
                apply auto
              subgoal for st1 ent1 
                apply(cases task_es2)
                  apply auto
                subgoal for st2 ent2
              apply(cases schs)
                    apply auto
                  apply (cases st1)
                  subgoal
                    apply simp
                    apply(cases k1')
                    subgoal apply auto
                      apply (auto simp add: emp_assn_def)
                      by(auto elim: sync_elims)
                  subgoal by auto
                  done
                apply auto
                done
              done
            done
          done
          subgoal for kk'
            apply auto
            apply(cases k1)
            subgoal
              apply(cases task_es1)
                apply auto
              subgoal for st1 ent1 
              apply(cases task_es2)
                  apply auto
                subgoal for st2 ent2
              apply(cases schs)
                apply auto
                  subgoal premises pre for p rn rp
                    thm pre
                    apply(rule combine_blocks_assn)
                       apply(rule pre(2))
                      apply(rule pre(12))
                     apply(rule pre(5))
                    apply(rule combine_emp_in_0orig_vassm'1)
                    by auto
                  subgoal premises pre for p rn rp
                    thm pre
                    apply(rule combine_blocks_assn)
                       apply(rule pre(2))
                      apply(rule pre(12))
                     apply(rule pre(5))
                    apply(rule combine_emp_in_0orig_vassm'1)
                    by auto
                  subgoal premises pre for p rn rp
                    thm pre
                    apply(rule combine_blocks_assn)
                       apply(rule pre(2))
                      apply(rule pre(12))
                     apply(rule pre(5))
                    apply(rule combine_emp_in_0orig_vassm'1)
                    by auto
                  done
                done
              done
            subgoal for k1'
              apply(cases task_es1)
                apply auto
              subgoal for st1 ent1 
              apply(cases task_es2)
                  apply auto
                subgoal for st2 ent2
              apply(cases schs)
                    apply auto
                  subgoal for p rn rp
                    apply(cases st1)
                      apply simp
                    subgoal 
                      apply(erule disjE)
                      subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_emp_wait_orig1)
                      apply auto
                      unfolding combine_assn_def entails_tassn_def 
                      apply auto
                      subgoal for tr tr1 tr2
                      using pre(1)[of 0 k1' "(Suc kk')" dis_s2 "(Task st2 ent2 1)" task_s2 tr1 "(dis_s1(CHR ''t'' := 0))" "(Task READY 0 2)" "(task_s1(CHR ''t'' := 0))" "(Sch p rn rp)" s tr2 tr]
                      apply auto
                      using pre unfolding propc1_def proper_def
                      by auto
                    done
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_waitin_tguar'_vassm'1)
                      by auto
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_waitin_tguar'_vassm'1)
                      by auto
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_waitin_tguar'_vassm'1)
                      by auto
                    done
                  subgoal 
                    apply (simp only:tdsch1'.simps)
                    apply(erule disjE)
                    subgoal
                      apply(cases "rn\<noteq>-1")
                       apply simp
                      subgoal
                        apply(subgoal_tac"rn = 2")
                         prefer 2
                        subgoal unfolding proper1_def properp_def propc1_def by auto
                        apply simp
                        subgoal premises pre
                          apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                           apply(rule pre(5))
                          apply(rule combine_emp_out_0assm1)
                          by auto
                        done
                      apply simp
                      subgoal premises pre
                        apply(rule pre(1)[of 0 k1' kk'  dis_s2 "(Task st2 ent2 1)" task_s2 tr1 dis_s1 "(Task RUNNING (Suc 0) 2)" "(task_s1(CHR ''c'' := up_ent_c ent1 (task_s1 CHR ''c'')))"
                            "(Sch p 1 2)" "(s(CHR ''p'' := 2))" tr2 tr])
                        apply auto
                        using pre apply auto
                        unfolding propc1_def proper1_def properp_def by auto
                      done
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_in_0orig_vassm'1)
                      by auto
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_in_0orig_vassm'1)
                      by auto
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_in_0orig_vassm'1)
                      by auto
                    done
                  subgoal 
                    apply (simp only:tdsch1'.simps)
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_waitin_tguar'_vassm'1)
                      by auto
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_waitin_tguar'_vassm'1)
                      by auto
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_waitin_tguar'_vassm'1)
                      by auto
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_emp_wait_orig1)
                      apply auto
                      subgoal 
                        apply(cases "(get_max p)")
                        subgoal for a b
                          apply auto
                        apply(subgoal_tac "b = 2")
                         prefer 2
                        subgoal
                          using pre(4) properl1_p5[of p] unfolding proper1_def properp_def by auto
                        apply (rule combine_emp_out_0assm1)
                        by auto
                      done
                      unfolding combine_assn_def entails_tassn_def 
                      apply auto
                      subgoal for tr tr1 tr2
                        apply(rule pre(1)[of 0 k1' kk' dis_s2 "(Task st2 ent2 1)" task_s2 tr1 dis_s1 "(Task WAIT ent1 2)" task_s1 "(Sch [] (- 1) (- 1))" s tr2 tr])
                        apply auto using pre unfolding propc1_def proper1_def properp_def by auto
                      done
                    done
                  done
                done
              done
            done
          done
        done
      subgoal for k2'
        apply(cases task_es2)
          apply auto 
        subgoal for st2 ent2
        apply(cases kk)
        subgoal
          apply(cases k1)
          subgoal
            apply auto
            apply(cases task_es1)
              apply auto
            subgoal for st1 ent1
              apply(cases schs)
                apply auto
              subgoal for p rn rp
                apply(cases st2)
                apply simp
                subgoal premises pre
                  thm pre
                  apply(rule combine_blocks_assn)
                  apply(rule pre(2))
                  apply(rule pre(3))
                   apply(rule pre(6))
                  apply(rule entails_tassn_trans)
                   apply(rule combine_wait_orig_emp1)
                  apply (simp del:fun_upd_apply)
                  apply clarify
                  apply(cases k2')
                   apply auto
                  subgoal
                    unfolding combine_assn_def entails_tassn_def
                    apply auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(3))
                        apply(rule pre'(4))
                       apply(rule pre'(5))
                      by auto
                    done
                  subgoal for k2''
                    unfolding combine_assn_def entails_tassn_def
                    apply auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(5))
                        apply(rule pre'(3))
                       apply(rule pre'(4))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(5))
                        apply(rule pre'(3))
                       apply(rule pre'(4))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(5))
                        apply(rule pre'(3))
                       apply(rule pre'(4))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    done
                  done
                subgoal apply auto
                  subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                       apply(rule pre(13))
                      apply(rule pre(2))
                     apply(rule pre(5))
                    apply(rule combine_out_0assm_emp1)  
                    by auto
                  subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                       apply(rule pre(13))
                      apply(rule pre(2))
                     apply(rule pre(5))
                    apply(rule combine_out_0assm_emp1)  
                    by auto
                  subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                       apply(rule pre(13))
                      apply(rule pre(2))
                     apply(rule pre(5))
                    apply(rule combine_out_0assm_emp1)  
                    by auto
                  done
                subgoal apply auto
                  apply(cases "ent2 = Suc 0")
                  subgoal 
                    apply auto
                    subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                       apply(rule pre(14))
                      apply(rule pre(2))
                     apply(rule pre(5))
                    apply(rule combine_waitin_tguar'_vassm'_emp1)
                    by auto
                    subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                       apply(rule pre(14))
                      apply(rule pre(2))
                     apply(rule pre(5))
                    apply(rule entails_tassn_trans)
                     apply(rule combine_wait_orig_emp1)
                    apply auto
                    apply(rule combine_out_0assm_emp1)
                    by auto
                  done
                by auto
              done
            done
          done
        subgoal for k1'
          apply auto
            apply(cases task_es1)
              apply auto
            subgoal for st1 ent1
              apply(cases schs)
                apply auto
              subgoal for p rn rp
                apply(cases st2)
                  apply simp
                subgoal 
                  apply(cases st1)
                    apply auto
                  subgoal 
                    apply(cases k1')
                    subgoal
                      apply simp
                      subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                       apply(rule pre(2))
                      apply(rule pre(3))
                     apply(rule pre(6))
                    apply(rule entails_tassn_trans)
                     apply(rule combine_wait_orig_emp1)
                    apply(cases k2')
                     apply auto
                    unfolding combine_assn_def entails_tassn_def
                    apply auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(5))
                        apply(rule pre'(3))
                       apply(rule pre'(4))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(5))
                        apply(rule pre'(3))
                       apply(rule pre'(4))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(5))
                        apply(rule pre'(3))
                       apply(rule pre'(4))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    done
                  done
                subgoal by simp
                done
              done
            subgoal apply(cases st1)
                apply(cases k1')
                apply auto
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                apply(rule pre(15))
                apply(rule pre(2))
                apply(rule pre(5))
                apply(rule combine_out_0assm_emp1)
                by auto  
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                apply(rule pre(15))
                apply(rule pre(2))
                apply(rule pre(5))
                apply(rule combine_out_0assm_emp1)
                by auto  
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                apply(rule pre(15))
                apply(rule pre(2))
                apply(rule pre(5))
                apply(rule combine_out_0assm_emp1)
                by auto
              done
            subgoal apply(cases st1)
                apply(cases k1')
                 apply auto
              apply(cases "ent2 = Suc 0")
              subgoal
                apply auto
                subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                apply(rule pre(16))
                apply(rule pre(2))
                apply(rule pre(5))
                apply(rule combine_waitin_tguar'_vassm'_emp1)
                by auto
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                apply(rule pre(16))
                apply(rule pre(2))
                 apply(rule pre(5))
                apply(rule entails_tassn_trans)
                 apply(rule combine_wait_orig_emp1)
                apply auto
                apply(rule combine_out_0assm_emp1)
                by auto
              done
            by auto
          done
        done
      done
    done
  subgoal for kk'
    apply(cases k1)
          subgoal
            apply auto
            apply(cases st2)
              apply simp
            subgoal
            apply(cases schs)
                apply auto
              subgoal for p rn rp
                apply(cases task_es1)
                apply (simp del: tdsch2'.simps)
                subgoal for st1 ent1 tp1
                  apply (simp del: tdsch2'.simps)
                  apply(erule disjE)
                subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                    apply(rule pre(2))
                      apply(rule pre(14))
                     apply(rule pre(6))
                    apply(rule entails_tassn_trans)
                     apply(rule combine_wait_orig_in_0orig_vassm'1)
                     apply (simp del: fun_upd_apply)+
                    apply clarify
                    unfolding combine_assn_def entails_tassn_def
                    apply clarify
                    subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[of k2' 0 "(Suc kk')" "(dis_s2(CHR ''t'' := 0))" "(Task READY 0 1)" "(task_s2(CHR ''t'' := 0))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1 "(Sch p rn rp)" s tr2 tr])
                      using pre' pre unfolding propc1_def
                      by auto
                    done
                  apply(erule disjE)
                  subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                    apply(rule pre(2))
                      apply(rule pre(14))
                     apply(rule pre(6))
                    apply(rule entails_tassn_trans)
                     apply(rule combine_wait_orig_in_0orig_vassm'1)
                     apply (simp del: fun_upd_apply)
                    apply(simp only:pure_assn_entails)
                    apply clarify
                    unfolding combine_assn_def entails_tassn_def
                    apply clarify
                    apply(simp only:tdsch2'.simps)
                    apply simp
                    subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[of k2' 0 "(Suc kk')" "(dis_s2(CHR ''t'' := 0))" "(Task READY 0 1)" "(task_s2(CHR ''t'' := 0))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1 "(Sch p rn rp)" s tr2 tr])
                      using pre' pre unfolding propc1_def
                      by auto
                    done
                  subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                    apply(rule pre(2))
                      apply(rule pre(14))
                     apply(rule pre(6))
                    apply(rule entails_tassn_trans)
                     apply(rule combine_wait_orig_in_0orig_vassm'1)
                     apply (simp del: fun_upd_apply)+
                    apply clarify
                    unfolding combine_assn_def entails_tassn_def
                    apply clarify
                    subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[of k2' 0 "(Suc kk')" "(dis_s2(CHR ''t'' := 0))" "(Task READY 0 1)" "(task_s2(CHR ''t'' := 0))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1 "(Sch p rn rp)" s tr2 tr])
                      using pre' pre unfolding propc1_def
                      by auto
                    done
                  done
                subgoal by auto
                done
              subgoal apply(cases task_es1)
                by auto
              subgoal apply(cases task_es1)
                by auto
              done
            subgoal
              apply (simp del: tdsch2'.simps)
              apply(erule disjE)
              subgoal
              apply(cases schs)
                subgoal for p rn rp
                apply(cases task_es1)
                apply (simp del: tdsch2'.simps)
                subgoal for st1 ent1 tp1
                  apply (simp del: tdsch2'.simps)
                apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(11))
                        apply(rule pre(14))
                       apply(rule pre(5))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_out_0assm_in_0orig_vassm'1)
                       apply simp
                      apply(cases "1 \<le> rp")
                      subgoal 
                        apply (simp add: pre del: fun_upd_apply tdsch2'.simps)
                        apply(cases kk')
                        subgoal
                          apply (simp del: fun_upd_apply)
                          apply(rule combine_waitin_tguar'_vassm'_emp1)
                          by auto
                        subgoal for kk''
                          apply (simp del: fun_upd_apply tdsch2'.simps)
                          unfolding combine_assn_def entails_tassn_def
                          apply clarify
                          apply (erule disjE)
                          subgoal premises pre'
                            thm pre'
                            apply(rule combine_blocks_assn)
                               apply(rule pre'(3))
                              apply(rule pre'(5))
                             apply(rule pre'(4))
                            apply(rule combine_waitin_tguar'_vassm'_in_0orig_vassm'1)
                            by auto
                          apply (erule disjE)
                          subgoal premises pre'
                            thm pre'
                            apply(rule combine_blocks_assn)
                               apply(rule pre'(3))
                              apply(rule pre'(5))
                             apply(rule pre'(4))
                            apply(rule combine_waitin_tguar'_vassm'_in_0orig_vassm'1)
                            by auto
                          subgoal premises pre'
                            thm pre'
                            apply(rule combine_blocks_assn)
                               apply(rule pre'(3))
                              apply(rule pre'(5))
                             apply(rule pre'(4))
                            apply(rule combine_waitin_tguar'_vassm'_in_0orig_vassm'1)
                            by auto
                          done
                        done
                      apply(cases "rn \<noteq> - 1")
                      subgoal
                        apply (simp del: fun_upd_apply tdsch2'.simps)
                        unfolding combine_assn_def entails_tassn_def pure_assn_def conj_assn_def
                        apply auto
                        using pre(4,3) unfolding propc1_def proper1_def properp_def by auto
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_waitin_tguar'_vassm'_out_0assm1)
                      subgoal by auto
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      unfolding combine_assn_def entails_tassn_def
                      apply clarify
                      apply simp
                      apply(rule disjI1)
                      subgoal for tr tr1 tr2
                        apply(rule pre(1)[of k2' 0 kk' dis_s2 "(Task RUNNING (Suc 0) 1)" "(task_s2(CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c'')))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1
                            "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr])
                        using pre
                               apply auto
                        unfolding propc1_def proper1_def properp_def
                        by auto
                      done
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(11))
                        apply(rule pre(14))
                       apply(rule pre(5))
                      apply(rule combine_out_0assm_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(11))
                        apply(rule pre(14))
                       apply(rule pre(5))
                      apply(rule combine_out_0assm_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    done
                  subgoal by auto
                  done
                subgoal
                 apply(cases task_es1)by auto
                subgoal
                  apply(cases task_es1)by auto
                done
              apply(erule disjE)
              subgoal
              apply(cases schs)
                subgoal for p rn rp
                apply(cases task_es1)
                apply (simp del: tdsch2'.simps)
                subgoal for st1 ent1 tp1
                  apply (simp del: tdsch2'.simps)
                apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(11))
                        apply(rule pre(14))
                       apply(rule pre(5))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_out_0assm_in_0orig_vassm'1)
                       apply simp
                      apply(cases "1 \<le> rp")
                      subgoal 
                        apply (simp add: pre del: fun_upd_apply tdsch2'.simps)
                        apply(cases kk')
                        subgoal
                          apply (simp del: fun_upd_apply tdsch2'.simps)
                          apply(rule entails_tassn_trans)
                           apply(rule combine_wait_orig_emp1)
                          apply (simp del: fun_upd_apply tdsch2'.simps)
                          apply clarify
                          apply(rule combine_out_0assm_rdy_emp1)
                          by auto
                        subgoal for kk''
                          apply (simp del: fun_upd_apply tdsch2'.simps)
                          unfolding combine_assn_def entails_tassn_def
                          apply clarify
                          apply (erule disjE)
                          subgoal premises pre'
                            thm pre'
                            apply(rule combine_blocks_assn)
                               apply(rule pre'(3))
                              apply(rule pre'(5))
                             apply(rule pre'(4))
                            apply(rule entails_tassn_trans)
                             apply(rule combine_wait_orig_in_0orig_vassm'1)
                             apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply clarify
                            apply(rule combine_out_0assm_rdy_in_0orig_vassm'2)
                            by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                          apply (erule disjE)
                          subgoal premises pre'
                            thm pre'
                            apply(rule combine_blocks_assn)
                               apply(rule pre'(3))
                              apply(rule pre'(5))
                             apply(rule pre'(4))
                            apply(rule entails_tassn_trans)
                             apply(rule combine_wait_orig_in_0orig_vassm'1)
                             apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply clarify
                            apply(rule combine_out_0assm_rdy_in_0orig_vassm'2)
                            by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                          apply(simp only: tdsch2'.simps)
                          apply(rule disjI2)
                          subgoal premises pre'
                            thm pre'
                            apply(rule combine_blocks_assn)
                               apply(rule pre'(3))
                              apply(rule pre'(5))
                             apply(rule pre'(4))
                            apply(rule entails_tassn_trans)
                            apply(rule combine_wait_orig_in_0orig_vassm'1)
                             apply simp
                            apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply clarify
                            apply(rule entails_tassn_trans)
                             apply(rule combine_out_0assm_rdy_in_0orig_vassm'1)
                            subgoal by auto
                            unfolding combine_assn_def entails_tassn_def
                            apply auto
                            subgoal for tr tr1 tr2
                              apply(rule pre(1)[of k2' 0 kk'' "(dis_s2(CHR ''t'' := 9 / 200))" "(Task WAIT ent2 1)" "(task_s2(CHR ''t'' := 9 / 200))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1
                                    "(Sch (del_proc (p @ [(1, 2)]) 2) rn rp)" "(s(CHR ''p'' := 1))" tr2 tr])
                              using pre' pre properl1_p6[of "p"] properl1_p1[of p 1 2]  apply auto unfolding propc1_def proper1_def properp_def by auto
                            done
                          done
                        done
                      apply(cases "rn \<noteq> - 1")
                      subgoal
                        apply (simp del: fun_upd_apply tdsch2'.simps)
                        unfolding combine_assn_def entails_tassn_def pure_assn_def conj_assn_def
                        apply auto
                        using pre(4,3) unfolding propc1_def proper1_def properp_def by auto
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_out_0assm1)
                       apply simp
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply clarify
                      apply(rule combine_out_0assm_rdy_out_0assm)
                      by auto
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(11))
                        apply(rule pre(14))
                       apply(rule pre(5))
                      apply(rule combine_out_0assm_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(11))
                        apply(rule pre(14))
                       apply(rule pre(5))
                      apply(rule combine_out_0assm_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    done
                  by auto
                subgoal apply(cases task_es1) by auto
                subgoal apply(cases task_es1) by auto
                done
              subgoal
              apply(cases schs)
                subgoal for p rn rp
                apply(cases task_es1)
                apply (simp del: tdsch2'.simps)
                subgoal for st1 ent1 tp1
                  apply (simp del: tdsch2'.simps)
                  apply(erule disjE)
                  subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(11))
                        apply(rule pre(14))
                       apply(rule pre(5))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_out_0assm_in_0orig_vassm'1)
                       apply simp
                      apply(cases "1 \<le> rp")
                      subgoal 
                        apply (simp add: pre del: fun_upd_apply tdsch2'.simps)
                        apply(cases kk')
                        subgoal
                          apply (simp del: fun_upd_apply tdsch2'.simps)
                          apply(rule entails_tassn_trans)
                           apply(rule combine_wait_orig_emp1)
                          apply (simp del: fun_upd_apply tdsch2'.simps)
                          apply clarify
                          apply(rule combine_in_0assm_rdy_emp1)
                          by auto
                        subgoal for kk''
                          apply (simp del: fun_upd_apply tdsch2'.simps)
                          unfolding combine_assn_def entails_tassn_def
                          apply clarify
                          apply (erule disjE)
                          subgoal premises pre'
                            thm pre'
                            apply(rule combine_blocks_assn)
                               apply(rule pre'(3))
                              apply(rule pre'(5))
                             apply(rule pre'(4))
                            apply(rule entails_tassn_trans)
                             apply(rule combine_wait_orig_in_0orig_vassm'1)
                             apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply clarify
                            apply(rule combine_in_0assm_rdy_in_0orig_vassm'2)
                            by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                          apply (erule disjE)
                          subgoal premises pre'
                            thm pre'
                            apply(rule combine_blocks_assn)
                               apply(rule pre'(3))
                              apply(rule pre'(5))
                             apply(rule pre'(4))
                            apply(rule entails_tassn_trans)
                             apply(rule combine_wait_orig_in_0orig_vassm'1)
                             apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply clarify
                            apply(rule combine_in_0assm_rdy_in_0orig_vassm'2)
                            by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                          apply(simp only: tdsch2'.simps)
                          apply(rule disjI2)
                          subgoal premises pre'
                            thm pre'
                            apply(rule combine_blocks_assn)
                               apply(rule pre'(3))
                              apply(rule pre'(5))
                             apply(rule pre'(4))
                            apply(rule entails_tassn_trans)
                            apply(rule combine_wait_orig_in_0orig_vassm'1)
                             apply simp
                            apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply clarify
                            apply(rule combine_in_0assm_rdy_in_0orig_vassm'2)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                            done
                          done
                        done
                      apply(cases "rn \<noteq> - 1")
                      subgoal
                        apply (simp del: fun_upd_apply tdsch2'.simps)
                        unfolding combine_assn_def entails_tassn_def pure_assn_def conj_assn_def
                        apply auto
                        using pre(4,3) unfolding propc1_def proper1_def properp_def by auto
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_out_0assm1)
                       apply simp
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply clarify
                      apply(rule entails_tassn_trans)
                      apply(rule combine_in_0assm_rdy_out_0assm1)
                      subgoal by auto
                      unfolding combine_assn_def entails_tassn_def
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply clarify
                      subgoal for tr tr1 tr2
                        apply simp
                        apply(rule disjI1)
                        apply(rule pre(1)[of k2' 0 kk' dis_s2 "(Task RUNNING (Suc 0) 1)" "(task_s2(CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c'')))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1
                            "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr])
                        apply auto
                        apply(subgoal_tac "(dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + 9 / 200 - task_s2 CHR ''t'')) = dis_s2")
                            apply(subgoal_tac "(task_s2(CHR ''t'' := 9 / 200, CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c''))) = (task_s2(CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c'')))")
                             apply auto
                        using pre unfolding propc1_def proper1_def properp_def by auto
                      done
                    apply(erule disjE)
                  subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(11))
                        apply(rule pre(14))
                       apply(rule pre(5))
                      apply(rule combine_out_0assm_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(11))
                        apply(rule pre(14))
                       apply(rule pre(5))
                      apply(rule combine_out_0assm_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    done
                  by auto
                subgoal apply(cases task_es1) by auto
                subgoal apply(cases task_es1) by auto
                done
              done
            subgoal
              apply (simp del: tdsch2'.simps)
              apply(cases "ent2 = Suc 0")
              subgoal
                apply (simp del: tdsch2'.simps)
                apply(erule disjE)
                subgoal
                  apply(cases schs)
                  subgoal for p rn rp
                    apply(cases task_es1)
                      apply (simp del: tdsch2'.simps)
                    subgoal for st1 ent1 tp1
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(12))
                        apply(rule pre(15))
                       apply(rule pre(5))
                      apply(rule combine_waitin_tguar'_vassm'_in_0orig_vassm'1)
                      by auto
                    apply(erule disjE)
                      subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(12))
                        apply(rule pre(15))
                       apply(rule pre(5))
                      apply(rule combine_waitin_tguar'_vassm'_in_0orig_vassm'1)
                      by auto
                      subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(12))
                        apply(rule pre(15))
                       apply(rule pre(5))
                      apply(rule combine_waitin_tguar'_vassm'_in_0orig_vassm'1)
                      by auto
                    done
                  by auto
                subgoal
                  apply(cases task_es1) by auto
                subgoal
                  apply(cases task_es1) by auto
                done
              subgoal
                  apply(cases schs)
                  subgoal for p rn rp
                    apply(cases task_es1)
                      apply (simp del: tdsch2'.simps)
                    subgoal for st1 ent1 tp1
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(12))
                        apply(rule pre(15))
                       apply(rule pre(5))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_in_0orig_vassm'1)
                      apply simp
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply clarify
                      apply(rule combine_out_0assm_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(erule disjE)
                      subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(12))
                        apply(rule pre(15))
                       apply(rule pre(5))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_in_0orig_vassm'1)
                      apply simp
                      apply (simp only:pure_assn_entails)
                      apply clarify
                      apply(rule entails_tassn_trans)
                       apply(rule combine_out_0assm_in_0orig_vassm'1)
                       apply simp
                      apply(cases "p \<noteq> []")
                      subgoal apply simp
                        apply(cases "get_max p")
                        subgoal for a b
                          apply (simp del: fun_upd_apply tdsch2'.simps)
                          using pre(4) properl1_p5[of p] unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply auto
                      unfolding combine_assn_def entails_tassn_def
                      apply auto
                      subgoal for tr tr1 tr2
                        apply(rule pre(1)[of k2' 0 kk' dis_s2 "(Task WAIT (Suc 0) 1)" task_s2 tr1 dis_s1 "(Task st1 ent1 2)" task_s1 "(Sch [] (- 1) (- 1))" s tr2 tr])
                        using pre unfolding propc1_def proper1_def properp_def by auto
                      done
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(12))
                        apply(rule pre(15))
                       apply(rule pre(5))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_in_0orig_vassm'1)
                       apply simp
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply clarify
                      apply(rule combine_out_0assm_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    done
                  by auto
                subgoal apply(cases task_es1) by auto
                subgoal apply(cases task_es1) by auto
                done
              done
            by auto
          done
        subgoal for k1'
          apply auto
            apply(cases st2)
              apply simp
            subgoal
            apply(cases schs)
                apply auto
              subgoal for p rn rp
                apply(cases task_es1)
                apply (simp del: tdsch2'.simps)
                subgoal for st1 ent1 tp1
                  apply (simp del: tdsch2'.simps)
                  apply(cases st1)
                  subgoal
                    apply (simp del: tdsch2'.simps)

                      
                      































end
