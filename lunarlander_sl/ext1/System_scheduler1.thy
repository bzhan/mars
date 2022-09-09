theory System_scheduler1
  imports System_scheduler
begin

fun tdsch2' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "tdsch2' 0 0 0 dis_s2 (Task st2 ent2 t2) task_s2 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> (emp\<^sub>t tr)"

lemma combine_taskdis_sch1':
  "task_dis_assn' 2 k2 dis_s2 task_es2 task_s2 tr1 \<Longrightarrow>
   tdsch1' k1 kk dis_s1 task_es1 task_s1 schs s tr2 \<Longrightarrow>
   task_prior task_es1 = 2 \<Longrightarrow>
   task_prior task_es2 = 1 \<Longrightarrow>
   propc k1 task_es1 schs \<Longrightarrow> 
   proper schs \<Longrightarrow>
   combine_blocks {req_ch 1, preempt_ch 1, run_ch 1, free_ch 1, exit_ch 1} tr1 tr2 tr \<Longrightarrow>
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



end