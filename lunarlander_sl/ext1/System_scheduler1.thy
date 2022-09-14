theory System_scheduler1
  imports System_scheduler
begin


lemma combine_wait_orig_emp1:
"combine_assn chs (wait_orig_assn d p rdy P) emp\<^sub>t \<Longrightarrow>\<^sub>t (combine_assn chs P emp\<^sub>t)"
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

lemma combine_taskdis_sch1':
  "task_dis_assn' 2 k2 dis_s2 task_es2 task_s2 tr1 \<Longrightarrow>
   tdsch1' k1 kk dis_s1 task_es1 task_s1 schs s tr2 \<Longrightarrow>
   task_prior task_es1 = 2 \<Longrightarrow>
   task_prior task_es2 = 1 \<Longrightarrow>
   propc k1 task_es1 schs \<Longrightarrow> 
   proper schs \<Longrightarrow>
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
                      using pre unfolding propc_def proper_def
                      by auto
                    done
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_waitin_assms'1)
                      by auto
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_waitin_assms'1)
                      by auto
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                         apply(rule pre(2))
                        apply(rule pre(13))
                       apply(rule pre(5))
                      apply(rule combine_emp_waitin_assms'1)
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
                        subgoal unfolding proper_def properp_def propc_def by auto
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
                        unfolding propc_def proper_def properp_def by auto
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
                          using pre(4) properl_p5[of p] unfolding proper_def properp_def by auto
                        apply (rule combine_emp_out_0assm1)
                        by auto
                      done
                      unfolding combine_assn_def entails_tassn_def 
                      apply auto
                      subgoal for tr tr1 tr2
                        apply(rule pre(1)[of 0 k1' kk' dis_s2 "(Task st2 ent2 1)" task_s2 tr1 dis_s1 "(Task WAIT ent1 2)" task_s1 "(Sch [] (- 1) (- 1))" s tr2 tr])
                        apply auto using pre unfolding propc_def proper_def properp_def by auto
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
                  apply(cases k2')
                   apply simp
                  subgoal for k2''
                    unfolding combine_assn_def entails_tassn_def
                    apply auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(4))
                        apply(rule pre'(2))
                       apply(rule pre'(3))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(4))
                        apply(rule pre'(2))
                       apply(rule pre'(3))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(4))
                        apply(rule pre'(2))
                       apply(rule pre'(3))
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
                         apply(rule pre'(4))
                        apply(rule pre'(2))
                       apply(rule pre'(3))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(4))
                        apply(rule pre'(2))
                       apply(rule pre'(3))
                      apply(rule combine_out_0assm_emp1)
                      by auto
                    subgoal premises pre'
                      thm pre'
                      apply(rule combine_blocks_assn)
                         apply(rule pre'(4))
                        apply(rule pre'(2))
                       apply(rule pre'(3))
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
                    apply simp
                  subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                    apply(rule pre(2))
                      apply(rule pre(12))
                     apply(rule pre(5))
                    apply(rule entails_tassn_trans)
                     apply(rule combine_wait_orig_in_0orig_vassm'1)
                     apply (simp del: fun_upd_apply)+
                    apply clarify
                    unfolding combine_assn_def entails_tassn_def
                    apply clarify
                    subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[of k2' 0 "(Suc kk')" "(dis_s2(CHR ''t'' := 0))" "(Task READY 0 1)" "(task_s2(CHR ''t'' := 0))" tr1 dis_s1 "(Task WAIT ent1 2)" task_s1 "(Sch p rn rp)" s tr2 tr])
                      using pre' pre
                      by auto
                    done
                  subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                    apply(rule pre(2))
                      apply(rule pre(12))
                     apply(rule pre(5))
                    apply(rule entails_tassn_trans)
                     apply(rule combine_wait_orig_in_0orig_vassm'1)
                     apply (simp del: fun_upd_apply)+
                    apply clarify
                    unfolding combine_assn_def entails_tassn_def
                    apply clarify
                    subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[of k2' 0 "(Suc kk')" "(dis_s2(CHR ''t'' := 0))" "(Task READY 0 1)" "(task_s2(CHR ''t'' := 0))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1 "(Sch p rn rp)" s tr2 tr])
                      using pre' pre
                      by auto
                    done
                  subgoal premises pre
                    thm pre
                    apply(rule combine_blocks_assn)
                    apply(rule pre(2))
                      apply(rule pre(12))
                     apply(rule pre(5))
                    apply(rule entails_tassn_trans)
                     apply(rule combine_wait_orig_in_0orig_vassm'1)
                     apply (simp del: fun_upd_apply)+
                    apply clarify
                    unfolding combine_assn_def entails_tassn_def
                    apply clarify
                    subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[of k2' 0 "(Suc kk')" "(dis_s2(CHR ''t'' := 0))" "(Task READY 0 1)" "(task_s2(CHR ''t'' := 0))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1 "(Sch p rn rp)" s tr2 tr])
                      using pre' pre
                      by auto
                    done
                  done
                subgoal apply(cases st1)
                    apply simp
                  subgoal
                    apply(erule disjE)
                    subgoal




















end
