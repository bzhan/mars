theory System_scheduler1
  imports System_scheduler
begin




fun tdsch2' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow>state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> real \<Rightarrow> real \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "tdsch2' k2 k1 0 pd2 pc2 dis_s2 (Task st2 ent2 t2) task_s2 pd1 pc1 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> (emp\<^sub>t tr)"

| "tdsch2' 0 (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task st2 ent2 t2) task_s2 pd1 pc1 dis_s1 (Task WAIT ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> pd1 - dis_s1 CHR ''t'' = 0 \<and>
   tdsch2' 0 k1' (Suc kk') pd2 pc2 dis_s2 (Task st2 ent2 t2) task_s2 pd1 pc1 (dis_s1(CHR ''t'' := 0)) (Task READY 0 t1) (task_s1(CHR ''t'' := 0)) (Sch p rn rp) s tr"

| "tdsch2' 0 (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task st2 ent2 t2) task_s2 pd1 pc1 dis_s1 (Task READY ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> (if rn \<noteq> - 1 then False else
  tdsch2' 0 k1' kk' pd2 pc2 dis_s2 (Task st2 ent2 t2) task_s2 pd1 pc1 dis_s1 (Task RUNNING (Suc 0) t1) (task_s1(CHR ''c'' := up_ent_c ent1 (task_s1 CHR ''c''))) (Sch p 1 2) (s(CHR ''p'' := 2)) tr)"

| "tdsch2' 0 (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task st2 ent2 t2) task_s2 pd1 pc1 dis_s1 (Task RUNNING ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> (if length p > 0 then False else
  tdsch2' 0 k1' kk' pd2 pc2 dis_s2 (Task st2 ent2 t2) task_s2 pd1 pc1 dis_s1 (Task WAIT ent1 t1) task_s1 (Sch [] (- 1) (- 1)) s tr)"

| "tdsch2' (Suc k2') 0 (Suc kk') pd2 pc2 dis_s2 (Task WAIT ent2 t2) task_s2 pd1 pc1 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> (pd2 - dis_s2 CHR ''t'' = 0 \<and>
  tdsch2' k2' 0 (Suc kk') pd2 pc2 (dis_s2(CHR ''t'' := 0)) (Task READY 0 t2) (task_s2(CHR ''t'' := 0)) pd1 pc1 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr)"

| "tdsch2' (Suc k2') 0 (Suc kk') pd2 pc2 dis_s2 (Task READY ent2 t2) task_s2 pd1 pc1 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow>
  (\<up>(rn = -1 \<and> 1 > rp) \<and>\<^sub>t
  tdsch2' k2' 0 kk' pd2 pc2 dis_s2 (Task RUNNING (Suc 0) t2) (task_s2(CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c''))) pd1 pc1 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p 2 1) (s(CHR ''p'' := 1))) tr \<or>
  (\<up>(rp \<ge> 1 \<and> kk'> 0 \<and> pd2 - task_s2 CHR ''t'' = 0) \<and>\<^sub>t
  tdsch2' k2' 0 (kk'-1) pd2 pc2 (dis_s2(CHR ''t'' := pd2)) (Task WAIT ent2 1) (task_s2(CHR ''t'' := pd2)) pd1 pc1 dis_s1 (Task st1 ent1 t1) task_s1 (Sch (del_proc (p @ [(1, 2)]) 2) rn rp)  (s(CHR ''p'' := 1))) tr"

| "tdsch2' (Suc k2') 0 (Suc kk') pd2 pc2 dis_s2 (Task RUNNING ent2 t2) task_s2 pd1 pc1 dis_s1 (Task st1 ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow>
  (\<up>(p = []) \<and>\<^sub>t  tdsch2' k2' 0  kk' pd2 pc2 dis_s2 (Task WAIT ent2 t2) task_s2 pd1 pc1 dis_s1 (Task st1 ent1 t1) task_s1 (Sch [] (- 1) (- 1)) s) tr"

| "tdsch2' (Suc k2') (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task WAIT ent2 t2) task_s2 pd1 pc1 dis_s1 (Task WAIT ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> 
  (wait_orig_assn (pd1 - dis_s1 CHR ''t'')
     (\<lambda>t. ParState (ParState (EState (Task WAIT ent2 t2, task_s2)) (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))
           (ParState (ParState (EState (Task WAIT ent1 t1, task_s1)) (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + t))))
             (EState (Sch p rn rp, s))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 1, dispatch_ch 2}) 
      (tdsch2' (Suc k2') (k1') (Suc kk') pd2 pc2 (dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t''))) (Task WAIT ent2 t2) task_s2 pd1 pc1 (dis_s1(CHR ''t'' := 0)) (Task READY 0 t1) (task_s1(CHR ''t'' := 0)) (Sch p rn rp) s)) tr
\<or> (wait_orig_assn (pd2 - dis_s2 CHR ''t'')
     (\<lambda>t. ParState (ParState (EState (Task WAIT ent2 t2, task_s2)) (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))
           (ParState (ParState (EState (Task WAIT ent1 t1, task_s1)) (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + t))))
             (EState (Sch p rn rp, s))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 1, dispatch_ch 2}) 
      (tdsch2' (k2') (Suc k1') (Suc kk') pd2 pc2 (dis_s2(CHR ''t'' := 0)) (Task READY 0 t2) (task_s2(CHR ''t'' := 0)) pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) (Task WAIT ent1 t1) task_s1 (Sch p rn rp) s)) tr
\<or> (wait_orig_assn (pd2 - dis_s2 CHR ''t'')
     (\<lambda>t. ParState (ParState (EState (Task WAIT ent2 t2, task_s2)) (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))
           (ParState (ParState (EState (Task WAIT ent1 t1, task_s1)) (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + t))))
             (EState (Sch p rn rp, s))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 1, dispatch_ch 2}) 
      (tdsch2' (k2') (k1') (Suc kk') pd2 pc2 (dis_s2(CHR ''t'' := 0)) (Task READY 0 t2) (task_s2(CHR ''t'' := 0)) pd1 pc1 (dis_s1(CHR ''t'' := 0)) (Task READY 0 t1) (task_s1(CHR ''t'' := 0)) (Sch p rn rp) s)) tr"

|"tdsch2' (Suc k2') (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task WAIT ent2 t2) task_s2 pd1 pc1 dis_s1 (Task READY ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> 
  (\<up>(pd2 = dis_s2 CHR ''t'') \<and>\<^sub>t 
  tdsch2' (k2') (Suc k1') (Suc kk') pd2 pc2 (dis_s2(CHR ''t'' := 0)) (Task READY 0 t2) (task_s2(CHR ''t'' := 0)) pd1 pc1 dis_s1 (Task READY ent1 t1) task_s1 (Sch p rn rp) s) tr
\<or> (\<up>(pd2 > dis_s2 CHR ''t'' \<and> rn = -1) \<and>\<^sub>t 
  tdsch2' (Suc k2') k1' kk' pd2 pc2 dis_s2 (Task WAIT ent2 t2) task_s2 pd1 pc1 dis_s1 (Task RUNNING (Suc 0) 2) (task_s1(CHR ''c'' := up_ent_c ent1 (task_s1 CHR ''c''))) (Sch p 1 2) (s(CHR ''p'' := 2))) tr"

|"tdsch2' (Suc k2') (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task WAIT ent2 t2) task_s2 pd1 pc1 dis_s1 (Task RUNNING ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow>
  (\<up>(min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') < pd2 - dis_s2 CHR ''t'' ) \<and>\<^sub>t 
   wait_orig_assn (min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))
     (\<lambda>t. ParState (ParState (EState (Task WAIT ent2 t2, task_s2)) (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))
           (ParState
             (ParState (EState (Task RUNNING ent1 t1, task_s1(CHR ''t'' := task_s1 CHR ''t'' + t, CHR ''c'' := task_s1 CHR ''c'' + t)))
               (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + t))))
             (EState (Sch p rn rp, s))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 2, preempt_ch 1})
     (tdsch2' (Suc k2') k1' kk' pd2 pc2 (dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))) (Task WAIT ent2 t2) task_s2 
                                pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))) (Task WAIT ent1 t1)
         (task_s1
          (CHR ''t'' := task_s1 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''),
           CHR ''c'' := task_s1 CHR ''c'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')))
         (Sch [] (- 1) (- 1)) s)) tr \<or>
  (\<up>(min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') \<ge> pd2 - dis_s2 CHR ''t'' ) \<and>\<^sub>t 
   wait_orig_assn (pd2 - dis_s2 CHR ''t'')
     (\<lambda>t. ParState (ParState (EState (Task WAIT ent2 t2, task_s2)) (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))
           (ParState
             (ParState (EState (Task RUNNING ent1 t1, task_s1(CHR ''t'' := task_s1 CHR ''t'' + t, CHR ''c'' := task_s1 CHR ''c'' + t)))
               (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + t))))
             (EState (Sch p rn rp, s))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 2, preempt_ch 1}) 
     (tdsch2' k2' (Suc k1') (Suc kk') pd2 pc2 (dis_s2(CHR ''t'' := 0)) (Task READY 0 t2) (task_s2(CHR ''t'' := 0)) 
                                      pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) (Task RUNNING ent1 t1) (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''))) 
          (Sch p rn rp) s )) tr  "

|"tdsch2' (Suc k2') (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task READY ent2 t2) task_s2 pd1 pc1 dis_s1 (Task WAIT ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> 
  (\<up>(pd1 = dis_s1 CHR ''t'') \<and>\<^sub>t 
  tdsch2' (Suc k2') k1' (Suc kk') pd2 pc2 dis_s2 (Task READY ent2 t2) task_s2 pd1 pc1 (dis_s1(CHR ''t'' := 0)) (Task READY 0 t1) (task_s1(CHR ''t'' := 0)) (Sch p rn rp) s ) tr \<or>
  (\<up>(pd1 > dis_s1 CHR ''t'') \<and>\<^sub>t 
  tdsch2' k2' (Suc k1') kk' pd2 pc2 dis_s2 (Task RUNNING (Suc 0) t2) (task_s2(CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c''))) pd1 pc1 dis_s1 (Task WAIT ent1 t1) task_s1 (Sch p 2 1) (s(CHR ''p'' := 1))) tr"

|"tdsch2' (Suc k2') (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task READY ent2 t2) task_s2 pd1 pc1 dis_s1 (Task READY ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> 
  tdsch2' (Suc k2') k1' kk' pd2 pc2 dis_s2 (Task READY ent2 t2) task_s2 pd1 pc1 dis_s1 (Task RUNNING (Suc 0) t1) (task_s1(CHR ''c'' := up_ent_c ent1 (task_s1 CHR ''c''))) (Sch p 1 2) (s(CHR ''p'' := 2)) tr \<or>
  tdsch2' k2' (Suc k1') kk' pd2 pc2 dis_s2 (Task RUNNING (Suc 0) t2) (task_s2(CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c''))) pd1 pc1 dis_s1 (Task READY ent1 t1) task_s1 (Sch p 2 1) (s(CHR ''p'' := 1)) tr"

|"tdsch2' (Suc k2') (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task READY ent2 t2) task_s2 pd1 pc1 dis_s1 (Task RUNNING ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow> 
  (\<up>(kk' > 0 \<and> min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') \<le> pd2 - task_s2 CHR ''t'') \<and>\<^sub>t 
  wait_orig_assn (min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))
     (\<lambda>t. ParState
           (ParState (EState (Task READY ent2 t2, task_s2(CHR ''t'' := task_s2 CHR ''t'' + t)))
             (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))
           (ParState
             (ParState (EState (Task RUNNING ent1 t1, task_s1(CHR ''t'' := task_s1 CHR ''t'' + t, CHR ''c'' := task_s1 CHR ''c'' + t)))
               (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + t))))
             (EState (Sch (p @ [(1, 2)]) 1 2, s(CHR ''p'' := 1)))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) 
  (tdsch2' k2' k1' (kk'-1) pd2 pc2 (dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')))
       (Task RUNNING (Suc 0) t2)
       (task_s2(CHR ''t'' := task_s2 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''), CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c'')))
       pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))) (Task WAIT ent1 t1)
       (task_s1
        (CHR ''t'' := task_s1 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''),
         CHR ''c'' := task_s1 CHR ''c'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')))
       (Sch p 2 1) (s(CHR ''p'' := 1)))) tr \<or>
  (\<up>(min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') = 0 ) \<and>\<^sub>t 
   tdsch2' (Suc k2') k1' kk' pd2 pc2 dis_s2 (Task READY ent2 t2) task_s2 pd1 pc1 dis_s1 (Task WAIT ent1 t1) task_s1 (Sch [] (- 1) (- 1)) s) tr \<or>
  (\<up>(kk' > 0 \<and> min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') \<ge> pd2 - task_s2 CHR ''t'') \<and>\<^sub>t 
  wait_orig_assn (pd2 - task_s2 CHR ''t'')
     (\<lambda>t. ParState
           (ParState (EState (Task READY ent2 1, task_s2(CHR ''t'' := task_s2 CHR ''t'' + t)))
             (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))
           (ParState
             (ParState (EState (Task RUNNING ent1 2, task_s1(CHR ''t'' := task_s1 CHR ''t'' + t, CHR ''c'' := task_s1 CHR ''c'' + t)))
               (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + t))))
             (EState (Sch (p @ [(1, 2)]) 1 2, s(CHR ''p'' := 1)))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) 
  (tdsch2' k2' (Suc k1') (kk'-1) pd2 pc2 (dis_s2(CHR ''t'' := pd2)) (Task WAIT ent2 t2) (task_s2(CHR ''t'' := pd2)) 
                                 pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - task_s2 CHR ''t''))) (Task RUNNING ent1 t1)
       (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - task_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - task_s2 CHR ''t'')))
       (Sch [] 1 2) (s(CHR ''p'' := 1)) )) tr"

|"tdsch2' (Suc k2') (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task RUNNING ent2 t2) task_s2 pd1 pc1 dis_s1 (Task WAIT ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow>
  (\<up>(min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'') \<ge> pd1 - dis_s1 CHR ''t'') \<and>\<^sub>t 
  wait_orig_assn (pd1 - dis_s1 CHR ''t'')
     (\<lambda>t. ParState
           (ParState (EState (Task RUNNING ent2 t2, task_s2(CHR ''t'' := task_s2 CHR ''t'' + t, CHR ''c'' := task_s2 CHR ''c'' + t)))
             (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))
           (ParState (ParState (EState (Task WAIT ent1 t1, task_s1)) (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + t))))
             (EState (Sch p rn rp, s))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 1, preempt_ch 2})
  (tdsch2' (Suc k2') k1' (Suc kk') pd2 pc2 (dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t''))) (Task RUNNING ent2 t2) (task_s2
                  (CHR ''t'' := task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t''),
                   CHR ''c'' := task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t'')))   
                pd1 pc1 (dis_s1(CHR ''t'' := 0)) (Task READY 0 t1) (task_s1(CHR ''t'' := 0)) (Sch p rn rp) s)) tr \<or>
  (\<up>(min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'') < pd1 - dis_s1 CHR ''t'') \<and>\<^sub>t 
  wait_orig_assn (min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c''))
     (\<lambda>t. ParState
           (ParState (EState (Task RUNNING (Suc 0) 1, task_s2(CHR ''t'' := task_s2 CHR ''t'' + t, CHR ''c'' := task_s2 CHR ''c'' + t)))
             (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))
           (ParState (ParState (EState (Task WAIT ent1 t1, task_s1)) (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + t))))
             (EState (Sch p rn rp, s))))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 1, preempt_ch 2})  
  (tdsch2' k2' (Suc k1') kk' pd2 pc2 (dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'')))
         (Task WAIT (Suc 0) t2)
         (task_s2
          (CHR ''t'' := task_s2 CHR ''t'' + min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c''),
           CHR ''c'' := task_s2 CHR ''c'' + min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'')))
           pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'')))
         (Task WAIT ent1 t1) task_s1 (Sch [] (- 1) (- 1)) s))tr"

|"tdsch2' (Suc k2') (Suc k1') (Suc kk') pd2 pc2 dis_s2 (Task RUNNING ent2 t2) task_s2 pd1 pc1 dis_s1 (Task READY ent1 t1) task_s1 (Sch p rn rp) s tr \<longleftrightarrow>
  (\<up>(0 < min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'')) \<and>\<^sub>t 
  tdsch2' k2' k1' kk' pd2 pc2 (dis_s2(CHR ''t'' := dis_s2 CHR ''t'')) (Task READY (Suc 0) t2)
       (task_s2(CHR ''t'' := task_s2 CHR ''t'', CHR ''c'' := task_s2 CHR ''c'')) 
      pd1 pc1 dis_s1 (Task RUNNING (Suc 0) t1) (task_s1(CHR ''c'' := up_ent_c ent1 (task_s1 CHR ''c''))) 
       (Sch p 1 2) (s(CHR ''p'' := 2))) tr \<or>
  (\<up>(0 = min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'')) \<and>\<^sub>t 
  tdsch2' k2' (Suc k1') kk' pd2 pc2 dis_s2 (Task WAIT (Suc 0) t2) task_s2
      pd1 pc1 dis_s1 (Task READY ent1 t1) task_s1 
       (Sch [] (- 1) (- 1)) s) tr"

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



lemma combine_out_0assm_srdy_in_0orig_vassm'1:
"ch \<in> chs \<and> v \<in> V\<Longrightarrow> combine_assn chs (out_0assm_srdy_assn ch v rdy P)(in_0orig_vassm'_assn ch V Q) \<Longrightarrow>\<^sub>t combine_assn chs P (Q v)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:out_0assm_srdy_assn.cases[of ch v rdy P tr1])
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

lemma combine_out_0assm_srdy_in_0orig_vassm'2:
"ch1 \<in> chs \<and> ch2 \<in> chs \<and> ch1\<noteq>ch2 \<Longrightarrow> combine_assn chs (out_0assm_srdy_assn ch1 v rdy P)(in_0orig_vassm'_assn ch2 V Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:out_0assm_srdy_assn.cases[of ch1 v rdy P tr1])
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
lemma combine_waitin_tguar'_vassm'_out_0assm1':
"ch\<in>chs \<and> v\<in>V \<and> ch \<in> snd rdy \<Longrightarrow> combine_assn chs (waitin_tguar'_vassm'_assn S p rdy ch V Q) (out_0assm_assn ch v P) \<Longrightarrow>\<^sub>t \<up>(0\<in>S) \<and>\<^sub>t combine_assn chs (Q v 0) P"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of ch v P tr2])
      apply simp
    subgoal
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch V Q tr1])
          apply simp
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      done
    subgoal for d rdya pa tra
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch V Q tr1])
          apply simp
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        by auto
      done
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


lemma combine_wait_orig_wait_orig2:
"compat_rdy rdy1 rdy2 \<and> d1 = d2 \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (wait_orig_assn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
  wait_orig_assn d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs P1 P2)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d2 p2 rdy2 P2 tr2])
      apply auto
    subgoal
      apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
        apply auto
      apply(rule wait_orig_assn.intros(1))
      by auto
    subgoal 
      apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
        apply auto
      apply(elim combine_blocks_waitE2)
       apply auto
      apply(rule wait_orig_assn.intros(2))
      apply auto
      done
    done
  done


lemma combine_wait_orig_wait_orig3:
"compat_rdy rdy1 rdy2 \<and> d1 < d2 \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (wait_orig_assn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
  wait_orig_assn d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs P1 (wait_orig_assn (d2-d1) (\<lambda> t. p2(t+d1)) rdy2 P2))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d2 p2 rdy2 P2 tr2])
      apply auto
    subgoal
      apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
      by auto
    subgoal for tr2'
      apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
        apply auto
      subgoal
        apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr1'
        apply(elim combine_blocks_waitE3)
           apply auto
        apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x ="tr1'"])
        apply auto
        apply(rule exI[where x="(WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2')"])
        apply auto
        apply(rule wait_orig_assn.intros(2))
        by auto
      done
    done
  done


lemma combine_wait_orig_wait_orig4:
"compat_rdy rdy1 rdy2 \<and> d1 > d2 \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (wait_orig_assn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
  wait_orig_assn d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs (wait_orig_assn (d1-d2) (\<lambda> t. p1(t+d2)) rdy1 P1) P2)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
      apply auto
    subgoal
      apply(cases rule: wait_orig_assn.cases[of d2 p2 rdy2 P2 tr2])
      by auto
    subgoal for tr1'
      apply(cases rule: wait_orig_assn.cases[of d2 p2 rdy2 P2 tr2])
        apply auto
      subgoal
        apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr2'
        apply(elim combine_blocks_waitE4)
           apply auto
        apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x ="(WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1')"])
        apply auto
        apply(rule wait_orig_assn.intros(2))
        by auto
      done
    done
  done

lemma combine_wait_orig_wait_orig5:
"compat_rdy rdy1 rdy2 \<and> d1 \<le> d2 \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (wait_orig_assn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
  wait_orig_assn d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs P1 (wait_orig_assn (d2-d1) (\<lambda> t. p2(t+d1)) rdy2 P2))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d2 p2 rdy2 P2 tr2])
      apply auto
    subgoal
      apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
        apply auto
      apply(rule wait_orig_assn.intros(1))
      by auto
    subgoal for tr2'
      apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
        apply auto
      subgoal
        apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr1'
        apply(cases "d2>d1")
        subgoal
        apply(elim combine_blocks_waitE3)
           apply auto
        apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x ="tr1'"])
        apply auto
        apply(rule exI[where x="(WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2')"])
        apply auto
        apply(rule wait_orig_assn.intros(2))
          by auto
        apply simp
        apply(elim combine_blocks_waitE2)
         apply auto
        apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x ="tr1'"])
        apply auto
        apply(rule exI[where x ="tr2'"])
        apply auto
        apply(rule wait_orig_assn.intros(1))
        by auto
      done
    done
  done

lemma combine_wait_orig_wait_orig6:
"compat_rdy rdy1 rdy2 \<and> d1 \<ge> d2 \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (wait_orig_assn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t 
  wait_orig_assn d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs (wait_orig_assn (d1-d2) (\<lambda> t. p1(t+d2)) rdy1 P1) P2)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
      apply auto
    subgoal
      apply(cases rule: wait_orig_assn.cases[of d2 p2 rdy2 P2 tr2])
        apply auto
      apply(rule wait_orig_assn.intros(1))
      by auto
    subgoal for tr1'
      apply(cases rule: wait_orig_assn.cases[of d2 p2 rdy2 P2 tr2])
        apply auto
      subgoal
        apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr2'
        apply(cases "d2<d1")
        subgoal
        apply(elim combine_blocks_waitE4)
           apply auto
        apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x ="(WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1')"])
        apply auto
        apply(rule wait_orig_assn.intros(2))
          by auto
        apply simp
        apply(elim combine_blocks_waitE2)
         apply auto
        apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x ="tr1'"])
        apply auto
        apply(rule wait_orig_assn.intros(1))
        by auto
      done
    done
  done


lemma combine_wait_orig_waitin_tguar'_vassm'1:
"compat_rdy rdy1 rdy2 \<and> d1 \<ge> d2 \<and> ch\<in>chs \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (waitin_tguar'_vassm'_assn ({..<d2}) p2 rdy2 ch V P2) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
      apply auto
    subgoal 
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of "{..<d2}" p2 rdy2 ch V P2 tr2])
      by auto
    subgoal for tr1'
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of "{..<d2}" p2 rdy2 ch V P2 tr2])
          apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        apply(elim combine_blocks_waitE4)
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        apply(elim combine_blocks_waitE4)
        by (auto elim!: sync_elims)
      done
    done
  done


lemma combine_wait_orig_waitin_tguar'_vassm'2:
"compat_rdy rdy1 rdy2 \<and> d1 < d2 \<and> ch\<in>chs \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (waitin_tguar'_vassm'_assn ({..<d2}) p2 rdy2 ch V P2) \<Longrightarrow>\<^sub>t 
    wait_orig_assn d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs P1 (waitin_tguar'_vassm'_assn ({..<d2-d1}) (\<lambda> t. p2(t+d1)) rdy2 ch V (\<lambda> v d. P2 v (d+d1))))"
  unfolding combine_assn_def entails_tassn_def
unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
      apply auto
    subgoal 
      apply(rule wait_orig_assn.intros(1))
      by auto
    subgoal for tr1'
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of "{..<d2}" p2 rdy2 ch V P2 tr2])
          apply simp
      subgoal for v tr2'
        by (auto elim!: sync_elims)
      subgoal for d v tr2'
        apply(cases "d< d1")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE4)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d> d1")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE3)
             apply auto
          apply(rule wait_orig_assn.intros(2))
          apply(rule exI[where x ="tr1'"])
          apply auto
          apply(rule exI[where x="(WaitBlk (d - d1) (\<lambda>t. p2 (t + d1)) rdy2 # InBlock ch v # tr2')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(2))
          by auto
        apply simp
          apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule wait_orig_assn.intros(2))
          apply(rule exI[where x ="tr1'"])
          apply auto
          apply(rule exI[where x="(InBlock ch v # tr2')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(1))
        by auto
      subgoal for v tr2'
        by (auto elim!: sync_elims)
      subgoal for d v tr2'
        apply(cases "d< d1")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE4)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d> d1")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE3)
             apply auto
          apply(rule wait_orig_assn.intros(2))
          apply(rule exI[where x ="tr1'"])
          apply auto
          apply(rule exI[where x="(WaitBlk (d - d1) (\<lambda>t. p2 (t + d1)) rdy2 # InBlock ch v # tr2')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(4))
          by auto
        apply simp
          apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule wait_orig_assn.intros(2))
          apply(rule exI[where x ="tr1'"])
          apply auto
          apply(rule exI[where x="(InBlock ch v # tr2')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(3))
        by auto
      done
    done
  done

lemma combine_wait_orig_waitin_tguar'_vassm'2':
"compat_rdy rdy1 rdy2 \<and> ch\<in>chs \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (waitin_tguar'_vassm'_assn ({..<d2}) p2 rdy2 ch V P2) \<Longrightarrow>\<^sub>t 
   \<up>(d1<d2) \<and>\<^sub>t wait_orig_assn d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs P1 (waitin_tguar'_vassm'_assn ({..<d2-d1}) (\<lambda> t. p2(t+d1)) rdy2 ch V (\<lambda> v d. P2 v (d+d1))))"
  apply(cases "d1\<ge>d2")
  subgoal
    apply(rule combine_wait_orig_waitin_tguar'_vassm'1) by auto
  apply simp
  apply(rule combine_wait_orig_waitin_tguar'_vassm'2) by auto

lemma combine_wait_orig_waitin_tguar'_vassm'3:
"compat_rdy rdy1 rdy2 \<and> d1 > d2 \<and> ch\<in>chs \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (waitin_tguar'_vassm'_assn ({..d2}) p2 rdy2 ch V P2) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
      apply auto
    subgoal 
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of "{..d2}" p2 rdy2 ch V P2 tr2])
      by auto
    subgoal for tr1'
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of "{..d2}" p2 rdy2 ch V P2 tr2])
          apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        apply(elim combine_blocks_waitE4)
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        apply(elim combine_blocks_waitE4)
        by (auto elim!: sync_elims)
      done
    done
  done


lemma combine_wait_orig_waitin_tguar'_vassm'4:
"compat_rdy rdy1 rdy2 \<and> d1 \<le> d2 \<and> ch\<in>chs \<Longrightarrow> combine_assn chs (wait_orig_assn d1 p1 rdy1 P1) (waitin_tguar'_vassm'_assn ({..d2}) p2 rdy2 ch V P2) \<Longrightarrow>\<^sub>t 
    wait_orig_assn d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs P1 (waitin_tguar'_vassm'_assn ({..d2-d1}) (\<lambda> t. p2(t+d1)) rdy2 ch V (\<lambda> v d. P2 v (d+d1))))"
  unfolding combine_assn_def entails_tassn_def
unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d1 p1 rdy1 P1 tr1])
      apply auto
    subgoal 
      apply(rule wait_orig_assn.intros(1))
      by auto
    subgoal for tr1'
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of "{..d2}" p2 rdy2 ch V P2 tr2])
          apply simp
      subgoal for v tr2'
        by (auto elim!: sync_elims)
      subgoal for d v tr2'
        apply(cases "d< d1")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE4)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d> d1")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE3)
             apply auto
          apply(rule wait_orig_assn.intros(2))
          apply(rule exI[where x ="tr1'"])
          apply auto
          apply(rule exI[where x="(WaitBlk (d - d1) (\<lambda>t. p2 (t + d1)) rdy2 # InBlock ch v # tr2')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(2))
          by auto
        apply simp
          apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule wait_orig_assn.intros(2))
          apply(rule exI[where x ="tr1'"])
          apply auto
          apply(rule exI[where x="(InBlock ch v # tr2')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(1))
        by auto
      subgoal for v tr2'
        by (auto elim!: sync_elims)
      subgoal for d v tr2'
        apply(cases "d< d1")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE4)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d> d1")
        subgoal
          apply simp
          apply(elim combine_blocks_waitE3)
             apply auto
          apply(rule wait_orig_assn.intros(2))
          apply(rule exI[where x ="tr1'"])
          apply auto
          apply(rule exI[where x="(WaitBlk (d - d1) (\<lambda>t. p2 (t + d1)) rdy2 # InBlock ch v # tr2')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(4))
          by auto
        apply simp
          apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule wait_orig_assn.intros(2))
          apply(rule exI[where x ="tr1'"])
          apply auto
          apply(rule exI[where x="(InBlock ch v # tr2')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(3))
        by auto
      done
    done
  done


lemma combine_out_0assm_wait_orig1:
  assumes "ch\<in>chs \<and> ch \<in> snd rdy"
    shows "combine_assn chs (out_0assm_assn ch v Q) (wait_orig_assn d p rdy P) \<Longrightarrow>\<^sub>t
          \<up>(d=0) \<and>\<^sub>t combine_assn chs (out_0assm_assn ch v Q) P"
  unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:wait_orig_assn.cases[of d p rdy P tr2])
      apply auto
    unfolding conj_assn_def pure_assn_def
    apply auto
    subgoal for tr2'
      apply(cases rule:out_0assm_assn.cases[of ch v Q tr1])
        apply auto
      subgoal for tr1'
        using assms
         by (auto elim!: sync_elims)
       subgoal for d' a b p' tr1'
         apply(cases rdy)
         using assms
         by (auto elim!: sync_elims)
       done
     done
  done


lemma combine_out_0assm_srdy_wait_orig1:
  assumes "ch\<in>chs \<and> ch \<in> snd rdy \<and> ch \<in> fst rdy'"
    shows "combine_assn chs (out_0assm_srdy_assn ch v rdy' Q) (wait_orig_assn d p rdy P) \<Longrightarrow>\<^sub>t
          \<up>(d=0) \<and>\<^sub>t combine_assn chs (out_0assm_srdy_assn ch v rdy' Q) P"
  unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:wait_orig_assn.cases[of d p rdy P tr2])
      apply auto
    unfolding conj_assn_def pure_assn_def
    apply auto
    subgoal for tr2'
      apply(cases rule:out_0assm_srdy_assn.cases[of ch v rdy'  Q tr1])
        apply auto
      subgoal for tr1'
        using assms
         by (auto elim!: sync_elims)
       subgoal for d' a b p' tr1'
         apply(cases rdy)
         apply(cases rdy')
         using assms
         apply auto
         apply(elim combine_blocks_waitE1)
         by auto
       done
     done
  done

lemma combine_out_0assm_waitin_tguar'_vassm'1:
"ch\<in>chs \<and> v\<in>V \<and> ch \<in> snd rdy \<Longrightarrow> combine_assn chs (out_0assm_assn ch v P) (waitin_tguar'_vassm'_assn S p rdy ch V Q) \<Longrightarrow>\<^sub>t \<up>(0\<in>S) \<and>\<^sub>t combine_assn chs P (Q v 0)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of ch v P tr1])
      apply simp
    subgoal
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch V Q tr2])
          apply simp
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      done
    subgoal for d rdya pa tra
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch V Q tr2])
          apply simp
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        by auto
      done
    done
  done

lemma combine_out_0assm_waitin_tguar'_vassm'2:
"ch1\<in>chs \<and> ch2\<in>chs \<and> ch1 \<in> snd rdy \<and> ch1 \<noteq> ch2 \<Longrightarrow> combine_assn chs (out_0assm_assn ch1 v P) (waitin_tguar'_vassm'_assn S p rdy ch2 V Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of ch1 v P tr1])
      apply simp
    subgoal
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch2 V Q tr2])
          apply simp
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      done
    subgoal for d rdya pa tra
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch2 V Q tr2])
          apply simp
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        by auto
      done
    done
  done

lemma combine_out_0assm_srdy_waitin_tguar'_vassm'1:
"ch\<in>chs \<and> v\<in>V \<and> ch \<in> snd rdy \<and> ch \<in> fst rdy'\<Longrightarrow> combine_assn chs (out_0assm_srdy_assn ch v rdy' P) (waitin_tguar'_vassm'_assn S p rdy ch V Q) \<Longrightarrow>\<^sub>t \<up>(0\<in>S) \<and>\<^sub>t combine_assn chs P (Q v 0)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_srdy_assn.cases[of ch v rdy' P tr1])
      apply simp
    subgoal
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch V Q tr2])
          apply simp
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      done
    subgoal for d rdya pa tra
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch V Q tr2])
          apply simp
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        apply(cases rdy')
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        by auto
      done
    done
  done


lemma combine_out_0assm_srdy_waitin_tguar'_vassm'2:
"ch1\<in>chs \<and> ch2\<in>chs \<and> ch1 \<in> snd rdy \<and> ch1 \<in> fst rdy' \<and> ch1 \<noteq> ch2 \<Longrightarrow> combine_assn chs (out_0assm_srdy_assn ch1 v rdy' P) (waitin_tguar'_vassm'_assn S p rdy ch2 V Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_srdy_assn.cases[of ch1 v rdy' P tr1])
      apply simp
    subgoal
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch2 V Q tr2])
          apply simp
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      done
    subgoal for d rdya pa tra
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch2 V Q tr2])
          apply simp
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        apply(cases rdya)
        by auto
      done
    done
  done


lemma combine_waitin_tguar'_vassm'_waitin_tguar'_vassm'1:
"ch1 \<in> chs \<and> ch2 \<in> chs \<Longrightarrow> combine_assn chs (waitin_tguar'_vassm'_assn S1 p1 rdy1 ch1 V1 P1) (waitin_tguar'_vassm'_assn S2 p2 rdy2 ch2 V2 P2) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S1 p1 rdy1 ch1 V1 P1 tr1])
        apply simp
    subgoal
      apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S2 p2 rdy2 ch2 V2 P2 tr2])
          apply simp
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      done
    subgoal for d1
      apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S2 p2 rdy2 ch2 V2 P2 tr2])
          apply simp
      subgoal
        apply auto
        by (auto elim!: sync_elims)
      subgoal for d2
        apply auto
        apply(cases "compat_rdy rdy1 rdy2")
        subgoal
          apply(cases "d1<d2")
          subgoal
            apply(elim combine_blocks_waitE3)
               apply auto
            by (auto elim!: sync_elims) 
          apply(cases "d1>d2")
          subgoal
            apply(elim combine_blocks_waitE4)
               apply auto
            by (auto elim!: sync_elims)
          apply auto
          apply(elim combine_blocks_waitE2)
           apply auto
          apply(elim combine_blocks_pairE)
          by auto
        apply(elim combine_blocks_waitE1)
        by auto
      subgoal
        apply auto
        by (auto elim!: sync_elims)
      subgoal for d2
        apply auto
        apply(cases "compat_rdy rdy1 rdy2")
        subgoal
          apply(cases "d1<d2")
          subgoal
            apply(elim combine_blocks_waitE3)
               apply auto
            by (auto elim!: sync_elims) 
          apply(cases "d1>d2")
          subgoal
            apply(elim combine_blocks_waitE4)
               apply auto
            by (auto elim!: sync_elims)
          apply auto
          apply(elim combine_blocks_waitE2)
           apply auto
          apply(elim combine_blocks_pairE)
          by auto
        apply(elim combine_blocks_waitE1)
        by auto
      done
subgoal
      apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S2 p2 rdy2 ch2 V2 P2 tr2])
          apply simp
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      subgoal
        apply auto
        apply(elim combine_blocks_pairE)
        by auto
      subgoal 
        apply auto
        by (auto elim!: sync_elims)
      done
    subgoal for d1
      apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S2 p2 rdy2 ch2 V2 P2 tr2])
          apply simp
      subgoal
        apply auto
        by (auto elim!: sync_elims)
      subgoal for d2
        apply auto
        apply(cases "compat_rdy rdy1 rdy2")
        subgoal
          apply(cases "d1<d2")
          subgoal
            apply(elim combine_blocks_waitE3)
               apply auto
            by (auto elim!: sync_elims) 
          apply(cases "d1>d2")
          subgoal
            apply(elim combine_blocks_waitE4)
               apply auto
            by (auto elim!: sync_elims)
          apply auto
          apply(elim combine_blocks_waitE2)
           apply auto
          apply(elim combine_blocks_pairE)
          by auto
        apply(elim combine_blocks_waitE1)
        by auto
      subgoal
        apply auto
        by (auto elim!: sync_elims)
      subgoal for d2
        apply auto
        apply(cases "compat_rdy rdy1 rdy2")
        subgoal
          apply(cases "d1<d2")
          subgoal
            apply(elim combine_blocks_waitE3)
               apply auto
            by (auto elim!: sync_elims) 
          apply(cases "d1>d2")
          subgoal
            apply(elim combine_blocks_waitE4)
               apply auto
            by (auto elim!: sync_elims)
          apply auto
          apply(elim combine_blocks_waitE2)
           apply auto
          apply(elim combine_blocks_pairE)
          by auto
        apply(elim combine_blocks_waitE1)
        by auto
      done
    done
  done


lemma combine_waitin_tguar'_vassm'_wait_orig2:
"ch\<in>chs \<and> compat_rdy rdy1 rdy2 \<Longrightarrow> combine_assn chs (waitin_tguar'_vassm'_assn {0 ..< d1} p1 rdy1 ch V P1)(wait_orig_assn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t
  \<up>(d2<d1) \<and>\<^sub>t wait_orig_assn d2 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)    
(combine_assn chs (waitin_tguar'_vassm'_assn {..< d1-d2} (\<lambda> t. p1(t+d2)) rdy1 ch V (\<lambda> v d. P1 v (d+d2))) (P2))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d2 p2 rdy2 P2 tr2])
      apply simp
    subgoal
     apply(cases rule: waitin_tguar'_vassm'_assn.cases[of "{0..<d1}" p1 rdy1 ch V P1 tr1])
          apply simp
      subgoal 
        apply auto
        apply(rule wait_orig_assn.intros(1))
         apply auto
        apply(rule exI[where x=tr1])
        apply auto
        apply(rule waitin_tguar'_vassm'_assn.intros(1))
        by auto
      subgoal 
        apply auto
        apply(rule wait_orig_assn.intros(1))
        apply(rule exI[where x=tr1])
        apply auto
        apply(rule waitin_tguar'_vassm'_assn.intros(2))
        by auto
      subgoal 
        apply auto
        apply(rule wait_orig_assn.intros(1))
         apply auto
        apply(rule exI[where x=tr1])
        apply auto
        apply(rule waitin_tguar'_vassm'_assn.intros(3))
        by auto
      subgoal 
        apply auto
        apply(rule wait_orig_assn.intros(1))
        apply(rule exI[where x=tr1])
        apply auto
        apply(rule waitin_tguar'_vassm'_assn.intros(4))
        by auto
      done
 subgoal for tr2'
     apply(cases rule: waitin_tguar'_vassm'_assn.cases[of "{0..<d1}" p1 rdy1 ch V P1 tr1])
          apply simp
      subgoal
        apply auto
        by (auto elim!: sync_elims)
      subgoal for d1' v tr1'
        apply auto
        apply(cases "d2\<ge>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply auto
        apply(cases "d2>d1'")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d2<d1'")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          apply(rule wait_orig_assn.intros(2))
           apply auto
          apply(rule exI[where x="(WaitBlk (d1' - d2) (\<lambda>t. p1 (t + d2)) rdy1 # InBlock ch v # tr1')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(2))
          by auto
        apply simp
        apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x="(InBlock ch v # tr1')"])
        apply auto
        apply(rule waitin_tguar'_vassm'_assn.intros(1))
        by auto
      subgoal
        apply auto
        by (auto elim!: sync_elims)
      subgoal for d1' v tr1'
        apply auto
        apply(cases "d2\<ge>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply auto
        apply(cases "d2>d1'")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d2<d1'")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          apply(rule wait_orig_assn.intros(2))
           apply auto
          apply(rule exI[where x="(WaitBlk (d1' - d2) (\<lambda>t. p1 (t + d2)) rdy1 # InBlock ch v # tr1')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(4))
          by auto
        apply simp
        apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x="(InBlock ch v # tr1')"])
        apply auto
        apply(rule waitin_tguar'_vassm'_assn.intros(3))
        by auto
      done
    done
  done


lemma combine_waitin_tguar'_vassm'_wait_orig2':
"ch\<in>chs \<and> compat_rdy rdy1 rdy2 \<Longrightarrow> combine_assn chs (waitin_tguar'_vassm'_assn {0 ..< d1} p1 rdy1 ch V P1)(wait_orig_assn d2 p2 rdy2 P2) \<Longrightarrow>\<^sub>t
  \<up>(d2<d1) \<and>\<^sub>t wait_orig_assn d2 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2)    
(combine_assn chs (waitin_tguar'_vassm'_assn {0..< d1-d2} (\<lambda> t. p1(t+d2)) rdy1 ch V (\<lambda> v d. P1 v (d+d2))) (P2))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d2 p2 rdy2 P2 tr2])
      apply simp
    subgoal
     apply(cases rule: waitin_tguar'_vassm'_assn.cases[of "{0..<d1}" p1 rdy1 ch V P1 tr1])
          apply simp
      subgoal 
        apply auto
        apply(rule wait_orig_assn.intros(1))
         apply auto
        done
      subgoal 
        apply auto
        apply(rule wait_orig_assn.intros(1))
        apply(rule exI[where x=tr1])
        apply auto
        done
      subgoal 
        apply auto
        apply(rule wait_orig_assn.intros(1))
        apply auto
        done
      subgoal 
        apply auto
        apply(rule wait_orig_assn.intros(1))
        by auto
        done
      subgoal for tr2'
     apply(cases rule: waitin_tguar'_vassm'_assn.cases[of "{0..<d1}" p1 rdy1 ch V P1 tr1])
          apply simp
      subgoal
        apply auto
        by (auto elim!: sync_elims)
      subgoal for d1' v tr1'
        apply auto
        apply(cases "d2\<ge>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply auto
        apply(cases "d2>d1'")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d2<d1'")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          apply(rule wait_orig_assn.intros(2))
           apply auto
          apply(rule exI[where x="(WaitBlk (d1' - d2) (\<lambda>t. p1 (t + d2)) rdy1 # InBlock ch v # tr1')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(2))
          by auto
        apply simp
        apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x="(InBlock ch v # tr1')"])
        apply auto
        apply(rule waitin_tguar'_vassm'_assn.intros(1))
        by auto
      subgoal
        apply auto
        by (auto elim!: sync_elims)
      subgoal for d1' v tr1'
        apply auto
        apply(cases "d2\<ge>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply auto
        apply(cases "d2>d1'")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          by (auto elim!: sync_elims)
        apply(cases "d2<d1'")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          apply(rule wait_orig_assn.intros(2))
           apply auto
          apply(rule exI[where x="(WaitBlk (d1' - d2) (\<lambda>t. p1 (t + d2)) rdy1 # InBlock ch v # tr1')"])
          apply auto
          apply(rule waitin_tguar'_vassm'_assn.intros(4))
          by auto
        apply simp
        apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x="(InBlock ch v # tr1')"])
        apply auto
        apply(rule waitin_tguar'_vassm'_assn.intros(3))
        by auto
      done
    done
  done

lemma combine_out_0assm_rdy_waitin_tguar'_vassm'1:
"ch \<in> chs \<and> v\<in>V \<and> \<not> compat_rdy rdy1 rdy2 \<Longrightarrow> combine_assn chs (out_0assm_rdy_assn ch v rdy1 P) (waitin_tguar'_vassm'_assn S p rdy2 ch V Q) \<Longrightarrow>\<^sub>t \<up>(0\<in>S) \<and>\<^sub>t combine_assn chs P (Q v 0)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_rdy_assn.cases[of ch v rdy1 P])
      apply simp
    subgoal
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy2 ch V Q])
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
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy2 ch V Q])
          apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      done
    done
  done

lemma combine_out_0assm_rdy_waitin_tguar'_vassm'2:
"ch1 \<in> chs \<and> ch2 \<in> chs \<and> ch1 \<noteq> ch2 \<and> \<not> compat_rdy rdy1 rdy2 \<Longrightarrow> combine_assn chs (out_0assm_rdy_assn ch1 v rdy1 P) (waitin_tguar'_vassm'_assn S p rdy2 ch2 V Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_rdy_assn.cases[of ch1 v rdy1 P])
      apply simp
    subgoal
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy2 ch2 V Q])
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
      apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy2 ch2 V Q])
          apply auto
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      subgoal
        by (auto elim!: sync_elims)
      done
    done
  done

lemma combine_in_0assm_rdy_waitin_tguar'_vassm'1:
"ch1 \<in> chs \<and> ch2 \<in> chs \<and> \<not> compat_rdy rdy1 rdy2 \<Longrightarrow> combine_assn chs (in_0assm_rdy_assn ch1 V1 rdy1 P1) (waitin_tguar'_vassm'_assn S p2 rdy2 ch2 V2 P2) \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:in_0assm_rdy_assn.cases[of ch1 V1 rdy1 P1 tr1])
       apply auto
    subgoal
      apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S p2 rdy2 ch2 V2 P2 tr2])
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
      apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S p2 rdy2 ch2 V2 P2 tr2])
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
      apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S p2 rdy2 ch2 V2 P2 tr2])
          apply auto
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      by (auto elim!: sync_elims)
    subgoal
      by (auto elim!: sync_elims)
    done
  done
  done


lemma combine_out_0assm_rdy_wait_orig3:
  assumes "d>0 \<and> ch\<in>chs \<and> \<not> compat_rdy rdy' rdy"
      shows "combine_assn chs (out_0assm_rdy_assn ch v rdy' Q) (wait_orig_assn d p rdy P) \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:wait_orig_assn.cases[of d p rdy P tr2])
    using assms apply auto
    subgoal for tr2'
      apply(cases rule:out_0assm_rdy_assn.cases[of ch v rdy' Q tr1])
        apply auto
      subgoal for tr1'
        by (auto elim!: sync_elims)
      by (auto elim!: sync_elims)
    done
      done

lemma combine_wait_orig_out_0assm3:
  assumes "d>0 \<and> ch\<in>chs \<and> ch\<in>snd rdy"
    shows "combine_assn chs (wait_orig_assn d p rdy P)(out_0assm_assn ch v Q) \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:wait_orig_assn.cases[of d p rdy P tr1])
    using assms apply auto
    subgoal for tr1'
      apply(cases rule:out_0assm_assn.cases[of ch v Q tr2])
        apply auto
      subgoal for tr2'
        by (auto elim!: sync_elims)
      apply(cases rdy)
      by (auto elim!: sync_elims)
    done
  done


lemma combine_in_0assm_rdy_wait_orig2:
"ch \<in> chs \<and> \<not>compat_rdy rdy rdy' \<and> d>0 \<Longrightarrow> combine_assn chs (in_0assm_rdy_assn ch V rdy P) (wait_orig_assn d p rdy' Q) \<Longrightarrow>\<^sub>t R"
unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d p rdy' Q tr2])
      apply auto
    apply(cases rule:in_0assm_rdy_assn.cases[of ch V rdy P tr1])
       apply auto
    by (auto elim!: sync_elims)
  done
    
lemma combine_out_0assm_srdy_out_0assm1:
"ch1\<in>chs \<and> ch2 \<in> chs \<and> ch2 \<in> snd srdy\<Longrightarrow> combine_assn chs (out_0assm_srdy_assn ch1 v1 srdy P1) (out_0assm_assn ch2 v2 P2) \<Longrightarrow>\<^sub>t R"
unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_srdy_assn.cases[of ch1 v1 srdy P1 tr1])
      apply auto
    subgoal
     apply(cases rule: out_0assm_assn.cases[of ch2 v2 P2 tr2])
       apply auto
    subgoal
      apply(elim combine_blocks_pairE) 
      by auto
    subgoal
      by (auto elim!: sync_elims)
    done
  subgoal
     apply(cases rule: out_0assm_assn.cases[of ch2 v2 P2 tr2])
      apply auto
    subgoal
      by (auto elim!: sync_elims)
    apply(elim combine_blocks_waitE1)
    apply(cases srdy)
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

lemma properl1_p7:
"properl1 p \<Longrightarrow> p = []"
  apply(cases p)
   apply auto
  unfolding properp_def by auto

definition proper1 :: "estate \<Rightarrow> bool " where
"proper1 schs = ((properp (run_now schs) (run_prior schs)) \<and> properl1 (pool schs))"



definition propc1 :: "nat \<Rightarrow> estate \<Rightarrow> nat \<Rightarrow> estate \<Rightarrow> estate \<Rightarrow> bool" where
"propc1 k1 task_es1 k2 task_es2 schs = ((k1>0 \<longrightarrow>(status task_es1 = RUNNING \<longleftrightarrow> run_now schs = 1)) \<and> (k2>0 \<longrightarrow>(status task_es2 = RUNNING \<longleftrightarrow> run_now schs = 2)))"


lemma combine_taskdis_sch1':
  "task_dis_assn' 2 k2 pd2 pc2 dis_s2 task_es2 task_s2 tr1 \<Longrightarrow>
   tdsch1' k1 kk pd1 pc1 dis_s1 task_es1 task_s1 schs s tr2 \<Longrightarrow>
   task_prior task_es1 = 2 \<Longrightarrow>
   task_prior task_es2 = 1 \<Longrightarrow>
   propc1 k1 task_es1 k2 task_es2 schs \<Longrightarrow> 
   proper1 schs \<Longrightarrow>
   combine_blocks {req_ch 2, preempt_ch 2, run_ch 2, free_ch 2, exit_ch 2} tr1 tr2 tr \<Longrightarrow>
   tdsch2' k2 k1 kk pd2 pc2 dis_s2 task_es2 task_s2 pd1 pc1 dis_s1 task_es1 task_s1 schs s tr"
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
                    apply(rule combine_out_0assm_srdy_emp1)
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
                apply(rule combine_out_0assm_srdy_emp1)
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
                    proof-
                      have a:"dis_s2 CHR ''t'' = pd2" using pre' by auto
                        thm pre'
                        then show ?thesis
                          apply(subst a)
                      apply(rule pre(1)[of k2' 0 "(Suc kk')" "(dis_s2(CHR ''t'' := 0))" "(Task READY 0 1)" "(task_s2(CHR ''t'' := 0))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1 "(Sch p rn rp)" s tr2 tr])
                      using pre' pre unfolding propc1_def
                      by auto
                  qed
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
                    proof-
                      have a:"dis_s2 CHR ''t'' = pd2" using pre' by auto
                        thm pre'
                        then show ?thesis
                          apply(subst a)
                      thm pre'
                      apply(rule pre(1)[of k2' 0 "(Suc kk')" "(dis_s2(CHR ''t'' := 0))" "(Task READY 0 1)" "(task_s2(CHR ''t'' := 0))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1 "(Sch p rn rp)" s tr2 tr])
                      using pre' pre unfolding propc1_def
                      by auto
                  qed
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
                    proof-
                      have a:"dis_s2 CHR ''t'' = pd2" using pre' by auto
                        thm pre'
                        then show ?thesis
                          apply(subst a)
                      thm pre'
                      apply(rule pre(1)[of k2' 0 "(Suc kk')" "(dis_s2(CHR ''t'' := 0))" "(Task READY 0 1)" "(task_s2(CHR ''t'' := 0))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1 "(Sch p rn rp)" s tr2 tr])
                      using pre' pre unfolding propc1_def
                      by auto
                  qed
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
                            subgoal premises pre'' for tr tr1 tr2
                            proof-
                              have a:"task_s2 CHR ''t'' = pd2" using pre'' by auto
                              thm pre'
                              then show ?thesis
                                apply(subst a)
                              apply(rule pre(1)[of k2' 0 kk'' "(dis_s2(CHR ''t'' := task_s2 CHR ''t''))" "(Task WAIT ent2 1)" "(task_s2)" tr1 dis_s1 "(Task st1 ent1 2)" task_s1
                                    "(Sch (del_proc (p @ [(1, 2)]) 2) rn rp)" "(s(CHR ''p'' := 1))" tr2 tr])
                                using pre' pre pre'' properl1_p6[of "p"] properl1_p1[of p 1 2]  apply auto unfolding propc1_def proper1_def properp_def by auto
                            qed
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
                      subgoal premises pre' for tr tr1 tr2
                        thm pre'
                      proof-
                        have a:"task_s2 CHR ''t'' = pd2" using pre' by auto
                        then show ?thesis
                          using pre'
                        apply simp
                          apply(rule disjI1)
                          apply(subst a)
                        apply(rule pre(1)[of k2' 0 kk' dis_s2 "(Task RUNNING (Suc 0) 1)" "(task_s2(CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c'')))" tr1 dis_s1 "(Task st1 ent1 2)" task_s1
                            "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr])
                        apply auto
                        apply(subgoal_tac "(dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + pd2 - task_s2 CHR ''t'')) = dis_s2")
                            apply(subgoal_tac "(task_s2(CHR ''t'' := pd2, CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c''))) = (task_s2(CHR ''c'' := up_ent_c ent2 (task_s2 CHR ''c'')))")
                             apply auto
                          using pre unfolding propc1_def proper1_def properp_def by auto
                      qed
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
                      apply(rule combine_out_0assm_srdy_in_0orig_vassm'2)
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
                       apply(rule combine_out_0assm_srdy_in_0orig_vassm'1)
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
                      apply(rule combine_out_0assm_srdy_in_0orig_vassm'2)
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
                    apply(cases "(pd2 - dis_s2 CHR ''t'') > (pd1 - dis_s1 CHR ''t'')")
                    subgoal
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(16))
                         apply(rule pre(6))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_wait_orig_wait_orig4)
                        subgoal using pre by auto 
                        apply (simp del:fun_upd_apply)
                        apply(rule wait_orig_assn_tran)
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                          subgoal by auto
                          subgoal apply simp
                            apply(subgoal_tac "(pd2 - dis_s2 CHR ''t'' - (pd1 - dis_s1 CHR ''t'')) = (pd2 - (dis_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'')))")
                            apply(subgoal_tac "(\<lambda>t. ParState (EState (Task WAIT ent2 1, task_s2))
           (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (t + (pd1 - dis_s1 CHR ''t'')))))) =
                                               (\<lambda>t. ParState (EState (Task WAIT ent2 1, task_s2)) (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') + t))))")
                              apply auto
                            apply(rule ext)
                            by auto
                               apply auto
                          using pre 
                          unfolding propc1_def proper1_def by auto
                        done
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(16))
                         apply(rule pre(6))
                        apply(rule combine_wait_orig_waitin_tguar'_vassm'1)
                        using pre by auto
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(16))
                         apply(rule pre(6))
                        apply(rule combine_wait_orig_waitin_tguar'_vassm'1)
                        using pre by auto
                      subgoal premises pre
                        apply simp
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(16))
                         apply(rule pre(6))
                        apply(rule combine_wait_orig_waitin_tguar'_vassm'1)
                        using pre by auto
                      done
                    apply(cases "(pd2 - dis_s2 CHR ''t'') < (pd1 - dis_s1 CHR ''t'')")
                    subgoal
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(17))
                         apply(rule pre(6))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_wait_orig_wait_orig3)
                        subgoal using pre by auto
                        apply (simp del:fun_upd_apply)
                        apply(rule wait_orig_assn_tran)
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                          subgoal by auto
                          subgoal by auto
                          subgoal apply simp
                            apply(rule disjI1)
                            apply(subgoal_tac "(pd1 - dis_s1 CHR ''t'' - (pd2 - dis_s2 CHR ''t'')) = (pd1 - (dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'')))")
                            apply(subgoal_tac "(\<lambda>t. ParState
           (ParState (EState (Task WAIT ent1 2, task_s1))
             (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t''))))))
           (EState (Sch p rn rp, s)))       = (\<lambda>t. ParState
           (ParState (EState (Task WAIT ent1 2, task_s1))
             (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') + t))))
           (EState (Sch p rn rp, s)))")
                              apply auto
                            apply(rule ext)
                            by auto
                              apply auto
                          using pre 
                          unfolding propc1_def proper1_def by auto
                        done
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(17))
                         apply(rule pre(6))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_wait_orig_waitin_tguar'_vassm'2)
                        subgoal using pre by auto
                        apply (simp del:fun_upd_apply)
                        apply(rule wait_orig_assn_tran)
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                          subgoal by auto
                          subgoal by auto
                          subgoal apply simp
                            apply(rule disjI2)
                            apply(rule disjI1)
                            apply(subgoal_tac "(pd1 - dis_s1 CHR ''t'' - (pd2 - dis_s2 CHR ''t'')) = (pd1 - (dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'')))")
                            apply(subgoal_tac "(\<lambda>t. ParState
                                                 (ParState (EState (Task WAIT ent1 2, task_s1))
                                                   (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t''))))))
                                                 (EState (Sch p rn rp, s)))       = (\<lambda>t. ParState
                                                 (ParState (EState (Task WAIT ent1 2, task_s1))
                                                   (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') + t))))
                                                 (EState (Sch p rn rp, s)))")
                              apply auto
                            apply(subgoal_tac "(\<lambda>v d. if v \<le> rp
            then tdsch1' (Suc k1') kk' pd1 pc1
                  (dis_s1
                   (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
                    CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d))
                  (Task WAIT ent1 2) task_s1 (sched_push 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))
            else if rn \<noteq> - 1
                 then out_0assm_assn (preempt_ch rn) 0
                       (out_0assm_assn (run_ch 2) 0
                         (tdsch1' (Suc k1') kk' pd1 pc1
                           (dis_s1
                            (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
                             CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d))
                           (Task WAIT ent1 2) task_s1 (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))))
                 else out_0assm_assn (run_ch 2) 0
                       (tdsch1' (Suc k1') kk' pd1 pc1
                         (dis_s1
                          (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
                           CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d))
                         (Task WAIT ent1 2) task_s1 (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v)))) =
                        (\<lambda>v d. if v \<le> rp
            then tdsch1' (Suc k1') kk' pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))) (Task WAIT ent1 2) task_s1
                  (sched_push 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))
            else if rn \<noteq> - 1
                 then out_0assm_assn (preempt_ch rn) 0
                       (out_0assm_assn (run_ch 2) 0
                         (tdsch1' (Suc k1') kk' pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))) (Task WAIT ent1 2)
                           task_s1 (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))))
                 else out_0assm_assn (run_ch 2) 0
                       (tdsch1' (Suc k1') kk' pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))) (Task WAIT ent1 2)
                         task_s1 (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))))")
                            subgoal by auto
                            subgoal 
                              apply(rule ext)
                              apply(rule ext)
                              subgoal for v d
                                apply(subgoal_tac"(dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))) = (dis_s1
                   (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
                    CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d))")
                                by auto
                              done
                            apply(rule ext)
                            apply auto
                            done
                          using pre 
                          unfolding propc1_def proper1_def by auto
                        done
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(17))
                         apply(rule pre(6))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_wait_orig_waitin_tguar'_vassm'2)
                        subgoal using pre by auto
                        apply (simp del:fun_upd_apply)
                        apply(rule wait_orig_assn_tran)
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                          subgoal by auto
                          subgoal by auto
                          subgoal apply simp
                            apply(rule disjI2)
                            apply(rule disjI2)
                            apply(rule disjI1)
                            apply(subgoal_tac "pd1 - dis_s1 CHR ''t'' - (pd2 - dis_s2 CHR ''t'') = pd1 - (dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))")
                            apply auto
                             apply(subgoal_tac "(\<lambda>t. ParState
                                         (ParState (EState (Task WAIT ent1 2, task_s1))
                                           (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t''))))))
                                         (EState (Sch p rn rp, s)))       = (\<lambda>t. ParState
                                         (ParState (EState (Task WAIT ent1 2, task_s1))
                                           (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') + t))))
                                         (EState (Sch p rn rp, s)))")
                             apply auto
                            subgoal premises pre'
                            proof-
                              have a: "(dis_s1
              (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
               CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d)) = (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t''))))" for d
                                by auto
                              have b:"(\<lambda>v d. if p \<noteq> []
            then out_0assm_assn (run_ch (run_now (sched_get_max (Sch p rn rp) s))) 0
                  (tdsch1' (Suc k1') kk' pd1 pc1
                    (dis_s1
                     (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
                      CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d))
                    (Task WAIT ent1 2) task_s1 (sched_get_max (Sch p rn rp) s) s)
            else tdsch1' (Suc k1') kk' pd1 pc1
                  (dis_s1
                   (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
                    CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d))
                  (Task WAIT ent1 2) task_s1 (sched_get_max (Sch p rn rp) s) s) =
                          (\<lambda>v d. if p \<noteq> []
            then out_0assm_assn (run_ch (run_now (sched_get_max (Sch p rn rp) s))) 0
                  (tdsch1' (Suc k1') kk' pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))) (Task WAIT ent1 2) task_s1
                    (sched_get_max (Sch p rn rp) s) s)
            else tdsch1' (Suc k1') kk' pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))) (Task WAIT ent1 2) task_s1
                  (sched_get_max (Sch p rn rp) s) s)"
                            apply(rule ext)
                              apply(rule ext)
                              subgoal for v d
                                apply(subst a)+
                                by auto
                              done
                            show ?thesis
                              using pre'(2)
                              apply(subst b)+
                            apply auto
                              done
                          qed
                          apply(rule ext)
                          by auto
                          using pre 
                          unfolding propc1_def proper1_def by auto
                        done
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(17))
                         apply(rule pre(6))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_wait_orig_waitin_tguar'_vassm'2)
                        subgoal using pre by auto
                        apply (simp del:fun_upd_apply)
                        apply(rule wait_orig_assn_tran)
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                          subgoal by auto
                          subgoal by auto
                          subgoal apply simp
                            apply(rule disjI2)
                            apply(rule disjI2)
                            apply(rule disjI2)
                            subgoal premises pre'
                            proof-
                              have a:"pd1 - (dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'')) = pd1 - dis_s1 CHR ''t'' - (pd2 - dis_s2 CHR ''t'') "
                                by auto
                              have b:"(\<lambda>t. ParState
           (ParState (EState (Task WAIT ent1 2, task_s1))
             (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') + t))))
           (EState (Sch p rn rp, s))) = (\<lambda>t. ParState
           (ParState (EState (Task WAIT ent1 2, task_s1))
             (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t''))))))
           (EState (Sch p rn rp, s)))"
                                apply(rule ext)
                                by auto
                              have c:"dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') + d) = dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))" for d
                                by auto
                              have d:"(\<lambda>v d. tdsch1' (Suc k1') kk' pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') + d)) (Task WAIT ent1 2) task_s1
             (Sch (del_proc p 2) rn rp) s) = (\<lambda>v d. tdsch1' (Suc k1') kk' pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))) (Task WAIT ent1 2) task_s1
             (Sch (del_proc p 2) rn rp) s)"
                                apply(rule ext)+
                                apply(subst c)
                                by auto
                                show ?thesis
                                using pre'(2)
                                apply(subst a)
                                apply(subst b)
                                apply(subst d)
                                by auto
                            qed
                            done
                          using pre 
                          unfolding propc1_def proper1_def by auto
                        done
                      done
                    apply(cases "(pd2 - dis_s2 CHR ''t'') = (pd1 - dis_s1 CHR ''t'')")
                    subgoal
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(18))
                         apply(rule pre(6))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_wait_orig_wait_orig2)
                        subgoal using pre by auto
                        apply (simp del:fun_upd_apply)
                        apply(rule wait_orig_assn_tran)
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                          using pre 
                          unfolding propc1_def proper1_def by auto
                        done
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(18))
                         apply(rule pre(6))
                        apply(rule combine_wait_orig_waitin_tguar'_vassm'1)
                        using pre by auto
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(18))
                         apply(rule pre(6))
                        apply(rule combine_wait_orig_waitin_tguar'_vassm'1)
                        using pre by auto
                      subgoal premises pre
                        apply simp
                        thm pre
                        apply(rule combine_blocks_assn)
                        apply(rule pre(2))
                          apply(rule pre(18))
                         apply(rule pre(6))
                        apply(rule combine_wait_orig_waitin_tguar'_vassm'1)
                        using pre by auto
                      done
                    by auto
                  subgoal
                    apply(cases "(pd2 - dis_s2 CHR ''t'') = 0")
                    subgoal 
                      apply(simp del:tdsch1'.simps tdsch2'.simps)
                      apply(cases rule:wait_orig_assn.cases[of 0 "(\<lambda>t. ParState (EState (Task WAIT ent2 1, task_s2)) (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))"
     "({}, {dispatch_ch 2})" "(task_dis_assn' 2 k2' (dis_s2 CHR ''t'') pc2 (dis_s2(CHR ''t'' := 0)) (Task READY 0 1) (task_s2(CHR ''t'' := 0)))" tr1 ])
                        apply(simp del:tdsch1'.simps tdsch2'.simps)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI1)
                        apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                        using pre 
                        unfolding propc1_def proper1_def by auto
                      by auto
                    apply(cases "(pd2 - dis_s2 CHR ''t'') > 0")
                    subgoal
                     apply(simp del:tdsch2'.simps)
                     apply(subgoal_tac"rn = -1")
                       prefer 2
                      subgoal
                      unfolding propc1_def proper1_def properp_def by auto
                    apply(simp del:tdsch2'.simps)
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply simp
                      apply(rule disjI2)
                      apply (simp add: pre)
                      apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                      using pre
                      unfolding propc1_def proper1_def properp_def by auto
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(17))
                       apply(rule pre(6))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_in_0orig_vassm'1)
                      subgoal by auto
                      using pre by auto
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(17))
                       apply(rule pre(6))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_in_0orig_vassm'1)
                      subgoal by auto
                      using pre by auto
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(17))
                       apply(rule pre(6))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_in_0orig_vassm'1)
                      subgoal by auto
                      using pre by auto
                    done
                  apply(cases rule:wait_orig_assn.cases[of "(pd2 - dis_s2 CHR ''t'')"
     "(\<lambda>t. ParState (EState (Task WAIT ent2 1, task_s2)) (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + t))))" "({}, {dispatch_ch 2})"
     "(task_dis_assn' 2 k2' pd2 pc2 (dis_s2(CHR ''t'' := 0)) (Task READY 0 1) (task_s2(CHR ''t'' := 0)))" tr1])
                  by auto
                subgoal 
                  apply(simp del:tdsch2'.simps)
                  apply(cases "(pd2 - dis_s2 CHR ''t'') > min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                  subgoal
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(16))
                       apply(rule pre(6))
                      apply(rule combine_wait_orig_waitin_tguar'_vassm'3)
                      using pre 
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(16))
                       apply(rule pre(6))
                      apply(rule combine_wait_orig_waitin_tguar'_vassm'3)
                      using pre 
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(16))
                       apply(rule pre(6))
                      apply(rule combine_wait_orig_waitin_tguar'_vassm'3)
                      using pre 
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(subgoal_tac "p = []")
                     prefer 2
                    subgoal using properl1_p7 unfolding proper1_def by auto
                    apply(simp del:tdsch2'.simps)
                    subgoal premises pre
                      apply(simp add: pre)
                      apply(rule disjI1)
                      thm pre
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(16))
                       apply(rule pre(6))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_wait_orig4)
                      subgoal using pre 
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply (auto simp del:fun_upd_apply)
                      apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, dispatch_ch 2})")
                      prefer 2 subgoal by auto
                      apply (auto simp del:fun_upd_apply)
                       apply(rule wait_orig_assn_tran)
                      unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply auto
                          subgoal premises pre'
                          proof-
                            have a: "(pd2 - (dis_s2 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))) = (pd2 - dis_s2 CHR ''t'' - min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))"
                            by auto
                           have b:"(\<lambda>t. ParState (EState (Task WAIT ent2 1, task_s2))
           (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') + t)))) =
                                            (\<lambda>t. ParState (EState (Task WAIT ent2 1, task_s2))
           (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (t + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))))))"
                             apply (rule ext)
                             by auto
                           show ?thesis
                             apply(subst a)
                             apply(subst b)
                             using pre'
                             by auto
                         qed
                         using pre 
                         unfolding propc1_def proper1_def properp_def by auto
                       done
                     done
                   apply(cases "(pd2 - dis_s2 CHR ''t'') \<le> min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                  subgoal
                    apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply (simp only:tdsch2'.simps)
                      apply(rule disjI2)
                      using pre(16)
                      apply(auto)
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(17))
                       apply(rule pre(6))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_waitin_tguar'_vassm'4)
                      subgoal using pre 
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(simp del:tdsch2'.simps fun_upd_apply)
                      apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, dispatch_ch 2})")
                      prefer 2 subgoal by auto
                      apply (auto simp del:fun_upd_apply)
                      apply(rule wait_orig_assn_tran)
                      unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                                apply simp
                          subgoal apply(simp only:tdsch1'.simps)
                            apply (rule disjI1)
                            subgoal premises pre'
                            proof-
                              have a:"min (pd1 -
             (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
              CHR ''t'')(pc1 - (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''))) CHR ''c'') 
                  = min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') - (pd2 - dis_s2 CHR ''t'')"
                                by auto
                              have b:"(\<lambda>t. ParState
           (ParState
             (EState
               (Task RUNNING ent1 2, task_s1
                (CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''),
                 CHR ''t'' :=
                   (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                    CHR ''t'' +
                   t,
                 CHR ''c'' :=
                   (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                    CHR ''c'' +
                   t)))
             (EState
               (estate.None, dis_s1
                (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
                 CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + t))))
           (EState (Sch p rn rp, s))) = (\<lambda>t. ParState
           (ParState
             (EState
               (Task RUNNING ent1 2, task_s1
                (CHR ''t'' := task_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t'')), CHR ''c'' := task_s1 CHR ''c'' + (t + (pd2 - dis_s2 CHR ''t'')))))
             (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t''))))))
           (EState (Sch p rn rp, s)))"
                                apply (rule ext)
                                by auto
                              have c:"(dis_s1
             (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
              CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d)) = (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t''))))" for d
                                by auto
                              have d:"(task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''),
               CHR ''t'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''t'' +
                 d,
               CHR ''c'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''c'' +
                 d)) = (task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')), CHR ''c'' := task_s1 CHR ''c'' + (d + (pd2 - dis_s2 CHR ''t''))))" for d
                                by auto
                              have e:"(\<lambda>v d. tdsch1' (Suc k1') kk' pd1 pc1
             (dis_s1
              (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
               CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d))
             (Task RUNNING ent1 2)
             (task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''),
               CHR ''t'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''t'' +
                 d,
               CHR ''c'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''c'' +
                 d))
             (Sch (p @ [(1, 2)]) 1 2) (s(CHR ''p'' := 1))) = (\<lambda>v d. tdsch1' (Suc k1') kk' pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))) (Task RUNNING ent1 2)
             (task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')), CHR ''c'' := task_s1 CHR ''c'' + (d + (pd2 - dis_s2 CHR ''t''))))
             (Sch (p @ [(1, 2)]) 1 2) (s(CHR ''p'' := 1)))"
                                apply(rule ext)
                                apply(rule ext)
                                apply(subst c)
                                apply(subst d)
                                by auto
                              show ?thesis
                                apply(subst a)
                                apply(subst b)
                                apply(subst e)
                                using pre' by auto
                            qed
                            done
                          using pre 
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply (simp only:tdsch2'.simps)
                      apply(rule disjI2)
                      using pre(16)
                      apply(auto)
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(17))
                       apply(rule pre(6))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_waitin_tguar'_vassm'4)
                      subgoal using pre 
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(simp del:tdsch2'.simps fun_upd_apply)
                      apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, dispatch_ch 2})")
                      prefer 2 subgoal by auto
                      apply (auto simp del:fun_upd_apply)
                      apply(rule wait_orig_assn_tran)
                      unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                                apply simp
                          subgoal apply(simp only:tdsch1'.simps)
                            apply (rule disjI2)
                            apply (rule disjI1)
                            subgoal premises pre'
                            proof-
                              have a:"min (pd1 -
             (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
              CHR ''t'')(pc1 - (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''))) CHR ''c'') 
                  = min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') - (pd2 - dis_s2 CHR ''t'')"
                                by auto
                              have b:"(\<lambda>t. ParState
           (ParState
             (EState
               (Task RUNNING ent1 2, task_s1
                (CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''),
                 CHR ''t'' :=
                   (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                    CHR ''t'' +
                   t,
                 CHR ''c'' :=
                   (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                    CHR ''c'' +
                   t)))
             (EState
               (estate.None, dis_s1
                (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
                 CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + t))))
           (EState (Sch p rn rp, s))) = (\<lambda>t. ParState
           (ParState
             (EState
               (Task RUNNING ent1 2, task_s1
                (CHR ''t'' := task_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t'')), CHR ''c'' := task_s1 CHR ''c'' + (t + (pd2 - dis_s2 CHR ''t'')))))
             (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t''))))))
           (EState (Sch p rn rp, s)))"
                                apply (rule ext)
                                by auto
                              have c:"(dis_s1
             (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
              CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d)) = (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t''))))" for d
                                by auto
                              have d:"(task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''),
               CHR ''t'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''t'' +
                 d,
               CHR ''c'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''c'' +
                 d)) = (task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')), CHR ''c'' := task_s1 CHR ''c'' + (d + (pd2 - dis_s2 CHR ''t''))))" for d
                                by auto
                              show ?thesis
                                apply(subst a)
                                apply(subst b)
                                using pre' by auto
                            qed
                            done
                          using pre 
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(erule disjE)
                    subgoal premises pre
                      thm pre
                      apply (simp only:tdsch2'.simps)
                      apply(rule disjI2)
                      using pre(16)
                      apply(auto)
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(17))
                       apply(rule pre(6))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_waitin_tguar'_vassm'4)
                      subgoal using pre 
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(simp del:tdsch2'.simps fun_upd_apply)
                      apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, dispatch_ch 2})")
                      prefer 2 subgoal by auto
                      apply (auto simp del:fun_upd_apply)
                      apply(rule wait_orig_assn_tran)
                      unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                                apply simp
                          subgoal apply(simp only:tdsch1'.simps)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI1)
                            subgoal premises pre'
                            proof-
                              have a:"min (pd1 -
             (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
              CHR ''t'')(pc1 - (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''))) CHR ''c'') 
                  = min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') - (pd2 - dis_s2 CHR ''t'')"
                                by auto
                              have b:"(\<lambda>t. ParState
           (ParState
             (EState
               (Task RUNNING ent1 2, task_s1
                (CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''),
                 CHR ''t'' :=
                   (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                    CHR ''t'' +
                   t,
                 CHR ''c'' :=
                   (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                    CHR ''c'' +
                   t)))
             (EState
               (estate.None, dis_s1
                (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
                 CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + t))))
           (EState (Sch p rn rp, s))) = (\<lambda>t. ParState
           (ParState
             (EState
               (Task RUNNING ent1 2, task_s1
                (CHR ''t'' := task_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t'')), CHR ''c'' := task_s1 CHR ''c'' + (t + (pd2 - dis_s2 CHR ''t'')))))
             (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t''))))))
           (EState (Sch p rn rp, s)))"
                                apply (rule ext)
                                by auto
                              have c:"(dis_s1
             (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
              CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d)) = (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t''))))" for d
                                by auto
                              have d:"(task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''),
               CHR ''t'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''t'' +
                 d,
               CHR ''c'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''c'' +
                 d)) = (task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')), CHR ''c'' := task_s1 CHR ''c'' + (d + (pd2 - dis_s2 CHR ''t''))))" for d
                                by auto
                              have e:"(\<lambda>v d. tdsch1' (Suc k1') kk' pd1 pc1
             (dis_s1
              (CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''),
               CHR ''t'' := (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) CHR ''t'' + d))
             (Task RUNNING ent1 2)
             (task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''),
               CHR ''t'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''t'' +
                 d,
               CHR ''c'' :=
                 (task_s1(CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''), CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))
                  CHR ''c'' +
                 d))
             (Sch (del_proc p 2) rn rp) s) = (\<lambda>v d. tdsch1' (Suc k1') kk' pd1 pc1 (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')))) (Task RUNNING ent1 2)
             (task_s1
              (CHR ''t'' := task_s1 CHR ''t'' + (d + (pd2 - dis_s2 CHR ''t'')), CHR ''c'' := task_s1 CHR ''c'' + (d + (pd2 - dis_s2 CHR ''t''))))
             (Sch (del_proc p 2) rn rp) s)"
                                apply(subst c)
                                apply(subst d)
                                by auto
                              show ?thesis
                                apply(subst a)
                                apply(subst b)
                                apply(subst e)
                                using pre' by auto
                            qed
                            done
                          using pre 
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(subgoal_tac "p=[]")
                       prefer 2
                      subgoal using properl1_p7 unfolding proper1_def by auto
                      apply(simp del:tdsch2'.simps)
                      subgoal premises pre
                      thm pre
                      apply (simp only:tdsch2'.simps)
                      apply(rule disjI2)
                      using pre(15)
                      apply(auto)
                      apply(rule combine_blocks_assn)
                      apply(rule pre(2))
                      apply(rule pre(16))
                       apply(rule pre(6))
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_wait_orig5)
                      subgoal using pre 
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(simp del:tdsch2'.simps fun_upd_apply)
                      apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, dispatch_ch 2})")
                      prefer 2 subgoal by auto
                      apply (auto simp del:fun_upd_apply)
                      apply(rule wait_orig_assn_tran)
                      unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          thm pre(1)
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                                apply simp
                          subgoal apply(simp only:tdsch1'.simps)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply (rule disjI2)
                            apply simp
                            subgoal premises pre'
                            proof-
                              have a:"(min (pd1 - (task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) (pc1 - (task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'')))) = 
                                     (min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') - (pd2 - dis_s2 CHR ''t''))"
                                by auto
                              have b:"(\<lambda>t. ParState
           (ParState
             (EState
               (Task RUNNING ent1 2, task_s1
                (CHR ''t'' := task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') + t, CHR ''c'' := task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'') + t)))
             (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') + t))))
           (EState (Sch [] rn rp, s))) = (\<lambda>t. ParState
           (ParState
             (EState
               (Task RUNNING ent1 2, task_s1
                (CHR ''t'' := task_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t'')), CHR ''c'' := task_s1 CHR ''c'' + (t + (pd2 - dis_s2 CHR ''t'')))))
             (EState (estate.None, dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + (t + (pd2 - dis_s2 CHR ''t''))))))
           (EState (Sch [] rn rp, s)))"
                                apply (rule ext)
                                by auto
                              have c:"(dis_s1
        (CHR ''t'' :=
           dis_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') +
           min (pd1 - (task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) (pc1 - (task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''))))) = (dis_s1(CHR ''t'' := dis_s1 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))) " 
                                using pre'(1,2)
                                by fastforce
                              have d:"(task_s1
        (CHR ''t'' :=
           task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t'') +
           min (pd1 - (task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) (pc1 - (task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''))),
         CHR ''c'' :=
           task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t'') +
           min (pd1 - (task_s1 CHR ''t'' + (pd2 - dis_s2 CHR ''t''))) (pc1 - (task_s1 CHR ''c'' + (pd2 - dis_s2 CHR ''t''))))) = (task_s1
        (CHR ''t'' := task_s1 CHR ''t'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''),
         CHR ''c'' := task_s1 CHR ''c'' + min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')))" 
                                using pre'(1,2)
                                by fastforce
                              show ?thesis
                                apply(subst a)
                                apply(subst b)
                                apply(subst c)
                                apply(subst d)
                                using pre' by auto
                            qed
                            done
                          using pre 
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      done
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
                apply simp
              subgoal for p rn rp
                apply(cases task_es1)
                apply (simp del: tdsch2'.simps)
                subgoal for st1 ent1 tp1
                  apply (simp del: tdsch2'.simps)
                  apply(cases st1)
                  subgoal
                    apply(erule disjE)
                    subgoal
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_wait_orig1)
                        subgoal by auto
                        apply(simp only: pure_assn_entails)
                        apply clarify
                        apply simp
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal premises pre' for tr tr1 tr2
                          thm pre'
                          apply(subst pre'(1)[symmetric])
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre' pre
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(erule disjE)
                       apply(subgoal_tac"rn = -1 \<and> rp = -1")
                        prefer 2
                      subgoal unfolding proper1_def properp_def propc1_def by auto
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_waitin_tguar'_vassm'1)
                        subgoal by auto
                        apply(simp add: pre del: fun_upd_apply)
                        apply clarify
                        apply(rule entails_tassn_trans)
                         apply(rule combine_waitin_tguar'_vassm'_out_0assm1)
                        subgoal by auto
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal premises pre' for tr tr1 tr2
                          thm pre'
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre' pre
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      done
                    apply(erule disjE)
                    subgoal
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_wait_orig1)
                        subgoal by auto
                        apply(simp only: pure_assn_entails)
                        apply clarify
                        apply simp
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal premises pre' for tr tr1 tr2
                          thm pre'
                          apply(subst pre'(1)[symmetric])
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre' pre
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(erule disjE)
                       apply(subgoal_tac"rn = -1 \<and> rp = -1")
                        prefer 2
                      subgoal unfolding proper1_def properp_def propc1_def by auto
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_waitin_tguar'_vassm'1)
                        subgoal by auto
                        apply(simp add: pre del: fun_upd_apply)
                        apply clarify
                        apply(rule entails_tassn_trans)
                         apply(rule combine_wait_orig_out_0assm1)
                        subgoal by auto
                        apply auto
                        apply(rule combine_out_0assm_rdy_out_0assm)
                        by auto
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      done
                    subgoal
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_wait_orig1)
                        subgoal by auto
                        apply(simp only: pure_assn_entails)
                        apply clarify
                        apply simp
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal premises pre' for tr tr1 tr2
                          thm pre'
                          apply(subst pre'(1)[symmetric])
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre' pre
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(erule disjE)
                       apply(subgoal_tac"rn = -1 \<and> rp = -1")
                        prefer 2
                      subgoal unfolding proper1_def properp_def propc1_def by auto
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_waitin_tguar'_vassm'1)
                        subgoal by auto
                        apply(simp add: pre del: fun_upd_apply)
                        apply clarify
                        apply(rule entails_tassn_trans)
                         apply(rule combine_wait_orig_out_0assm1)
                        subgoal by auto
                        apply auto
                        apply(rule entails_tassn_trans)
                         apply(rule combine_in_0assm_rdy_out_0assm)
                        subgoal by auto
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal premises pre' for tr tr1 tr2
                          thm pre'
                          apply(subst pre'(2)[symmetric])
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre' pre
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        thm pre
                        apply(rule combine_blocks_assn)
                           apply(rule pre(14))
                        apply(rule pre(15))
                         apply(rule pre(5))
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      done
                    done
                  subgoal
                    apply(erule disjE)
                    subgoal
                      apply(subgoal_tac"rn =-1 \<and> rp = -1\<and>p=[]")
                       prefer 2
                      subgoal 
                        unfolding propc1_def proper1_def properp_def using properl1_p7 by auto
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI1)
                        thm pre
                        apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre
                          unfolding propc1_def proper1_def properp_def by auto
                      apply(erule disjE)
                        subgoal premises pre
                          thm pre
                          apply simp
                          apply(rule disjI2)
                          apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(16))
                           apply(rule pre(5))
                          apply(rule entails_tassn_trans)
                           apply(rule combine_out_0assm_in_0orig_vassm'1)
                          subgoal by auto
                          apply (simp del:fun_upd_apply)
                          apply(rule entails_tassn_trans)
                           apply(rule combine_waitin_tguar'_vassm'_out_0assm1)
                          subgoal by auto
                          apply (simp del: fun_upd_apply)
                          unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal premises pre' for tr tr1 tr2
                          thm pre'
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre' pre
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(erule disjE)
                      subgoal premises pre
                          thm pre
                          apply simp
                          apply(rule disjI2)
                          apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(16))
                           apply(rule pre(5))               
                          apply(rule combine_out_0assm_in_0orig_vassm'2)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                        subgoal premises pre
                          thm pre
                          apply simp
                          apply(rule disjI2)
                          apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(16))
                           apply(rule pre(5))               
                          apply(rule combine_out_0assm_in_0orig_vassm'2)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                        done
                    apply(erule disjE)
                    subgoal
                      apply(subgoal_tac"rn =-1 \<and> rp = -1\<and>p=[]")
                       prefer 2
                      subgoal 
                        unfolding propc1_def proper1_def properp_def using properl1_p7 by auto
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI1)
                        thm pre
                        apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre
                          unfolding propc1_def proper1_def properp_def by auto
                      apply(erule disjE)
                        subgoal premises pre
                          thm pre
                          apply simp
                          apply(rule disjI2)
                          apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(16))
                           apply(rule pre(5))
                          apply(rule entails_tassn_trans)
                           apply(rule combine_out_0assm_in_0orig_vassm'1)
                          subgoal by auto
                          apply (simp del: fun_upd_apply)
                          apply(rule entails_tassn_trans)
                           apply(rule combine_wait_orig_out_0assm1)
                          subgoal by auto
                          apply auto
                          apply(rule combine_out_0assm_rdy_out_0assm)
                          by auto
                        apply(erule disjE)
                      subgoal premises pre
                          thm pre
                          apply simp
                          apply(rule disjI2)
                          apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(16))
                           apply(rule pre(5))               
                          apply(rule combine_out_0assm_in_0orig_vassm'2)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                        subgoal premises pre
                          thm pre
                          apply simp
                          apply(rule disjI2)
                          apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(16))
                           apply(rule pre(5))               
                          apply(rule combine_out_0assm_in_0orig_vassm'2)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                        done
                      subgoal
                      apply(subgoal_tac"rn =-1 \<and> rp = -1\<and>p=[]")
                       prefer 2
                      subgoal 
                        unfolding propc1_def proper1_def properp_def using properl1_p7 by auto
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI1)
                        thm pre
                        apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre
                          unfolding propc1_def proper1_def properp_def by auto
                      apply(erule disjE)
                        subgoal premises pre
                          thm pre
                          apply simp
                          apply(rule disjI2)
                          apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(16))
                           apply(rule pre(5))
                          apply(rule entails_tassn_trans)
                           apply(rule combine_out_0assm_in_0orig_vassm'1)
                          subgoal by auto
                          apply (simp del: fun_upd_apply)
                          apply(rule entails_tassn_trans)
                           apply(rule combine_wait_orig_out_0assm1)
                          subgoal by auto
                          apply (simp del: fun_upd_apply)
                          apply clarify
                          apply(rule entails_tassn_trans)
                           apply(rule combine_in_0assm_rdy_out_0assm1)
                          subgoal by auto
                          unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal premises pre' for tr tr1 tr2
                          thm pre'
                          apply(subst pre'(1)[symmetric])
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                          using pre' pre
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      apply(erule disjE)
                      subgoal premises pre
                          thm pre
                          apply simp
                          apply(rule disjI2)
                          apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(16))
                           apply(rule pre(5))               
                          apply(rule combine_out_0assm_in_0orig_vassm'2)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                        subgoal premises pre
                          thm pre
                          apply simp
                          apply(rule disjI2)
                          apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(16))
                           apply(rule pre(5))               
                          apply(rule combine_out_0assm_in_0orig_vassm'2)
                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                        done
                      done
                    subgoal
                    apply(erule disjE)
                    subgoal
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                         apply(rule pre(5))  
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_waitin_tguar'_vassm'1)
                        subgoal by auto
                        apply (simp del: fun_upd_apply)
                        apply clarify
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          apply(cases kk')
                          subgoal
                            by(simp only:tdsch1'.simps)
                          subgoal for kk''
                            apply(simp only:tdsch1'.simps)
                            apply (simp del: fun_upd_apply)
                            apply(erule disjE)
                            subgoal premises pre'
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(rule combine_waitin_tguar'_vassm'_waitin_tguar'_vassm'1)
                              by auto
                            apply(erule disjE)
                            subgoal premises pre'
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(rule combine_waitin_tguar'_vassm'_waitin_tguar'_vassm'1)
                              by auto
                            apply(erule disjE)
                            subgoal premises pre'
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(rule combine_waitin_tguar'_vassm'_waitin_tguar'_vassm'1)
                              by auto
                            apply(subgoal_tac "p=[]")
                             prefer 2
                            subgoal using pre properl1_p7 unfolding proper1_def by auto
                            apply (simp del: fun_upd_apply)
                            subgoal premises pre'
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(rule entails_tassn_trans)
                               apply(rule combine_waitin_tguar'_vassm'_wait_orig2)
                              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply (simp del: fun_upd_apply)
                              apply clarify
                              apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, run_ch 2})")
                               prefer 2 subgoal by auto
                              apply (auto simp del:fun_upd_apply)
                              apply(rule wait_orig_assn_tran)
                              apply(rule entails_tassn_trans)
                               apply(rule combine_waitin_tguar'_vassm'_out_0assm1)
                              subgoal by auto
                              apply (simp del: fun_upd_apply)
                              unfolding combine_assn_def entails_tassn_def
                              apply clarify
                              subgoal premises pre'' for tr tr1 tr2
                                thm pre''
                                apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                 apply simp
                                using pre' pre pre''
                                unfolding propc1_def proper1_def properp_def by auto
                              done
                            done
                          done
                        done
                      apply(erule disjE)
                      subgoal premises pre
                        thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                         apply(rule pre(5))  
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(erule disjE)
                      subgoal premises pre
                        thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                         apply(rule pre(5))  
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(subgoal_tac "p=[]")
                      prefer 2
                      subgoal using properl1_p7 unfolding proper1_def by auto
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      subgoal premises pre
                        apply simp
                        apply(rule disjI2)
                        apply(rule disjI1)
                        thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                         apply(rule pre(5))  
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_wait_orig1)
                        subgoal by auto
                        apply (simp del: fun_upd_apply tdsch2'.simps)
                        apply clarify
                        unfolding combine_assn_def entails_tassn_def
                          apply clarify
                          subgoal premises pre' for tr tr1 tr2
                          thm pre'
                          apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                          apply simp
                          using pre pre'
                          unfolding propc1_def proper1_def properp_def by auto
                        done
                      done
                    apply(erule disjE)
                    subgoal
                      apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                         apply(rule pre(5))  
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_waitin_tguar'_vassm'1)
                        subgoal by auto
                        apply (simp del: fun_upd_apply tdsch2'.simps)
                        apply clarify
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          apply(cases kk')
                          subgoal
                            by(simp only:tdsch1'.simps)
                          subgoal for kk''
                            apply(simp only:tdsch1'.simps)
                            apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply(erule disjE)
                            subgoal premises pre'
                              apply simp
                              apply(rule disjI2)
                              apply(rule disjI2)
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(cases "pd2 - task_s2 CHR ''t'' > min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule combine_wait_orig_waitin_tguar'_vassm'3)
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply(cases "pd2 - task_s2 CHR ''t'' \<le> min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_waitin_tguar'_vassm'4)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply)
                                apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, run_ch 2})")
                               prefer 2 subgoal by auto
                              apply (auto simp del:fun_upd_apply)
                                apply(rule wait_orig_assn_tran)
                                apply(rule combine_out_0assm_rdy_waitin_tguar'_vassm'2)
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              by auto
                            apply(erule disjE)
                            subgoal premises pre'
                              apply simp
                              apply(rule disjI2)
                              apply(rule disjI2)
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(cases "pd2 - task_s2 CHR ''t'' > min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule combine_wait_orig_waitin_tguar'_vassm'3)
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply(cases "pd2 - task_s2 CHR ''t'' \<le> min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_waitin_tguar'_vassm'4)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply)
                                apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, run_ch 2})")
                               prefer 2 subgoal by auto
                              apply (auto simp del:fun_upd_apply)
                                apply(rule wait_orig_assn_tran)
                                apply(rule combine_out_0assm_rdy_waitin_tguar'_vassm'2)
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              by auto
                            apply(erule disjE)
                            subgoal premises pre'
                              apply simp
                              apply(rule disjI2)
                              apply(rule disjI2)
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(cases "pd2 - task_s2 CHR ''t'' > min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule combine_wait_orig_waitin_tguar'_vassm'3)
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply(cases "pd2 - task_s2 CHR ''t'' \<le> min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_waitin_tguar'_vassm'4)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply)
                                apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, run_ch 2})")
                               prefer 2 subgoal by auto
                              apply (auto simp del:fun_upd_apply)
                                apply(rule wait_orig_assn_tran)
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_out_0assm_rdy_waitin_tguar'_vassm'1)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply)
                                apply(subgoal_tac "p=[]")
                                 prefer 2
                                subgoal using properl1_p7 pre pre' unfolding proper1_def by auto
                                apply (simp del: fun_upd_apply tdsch2'.simps)
                                unfolding combine_assn_def entails_tassn_def
                                apply clarify
                                subgoal premises pre'' for tr tr1 tr2
                                  thm pre'
                                  apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                         apply simp
                                  using pre pre' pre''
                                  unfolding propc1_def proper1_def properp_def by auto
                                done
                              by auto
                            apply(subgoal_tac "p=[]")
                                 prefer 2
                                subgoal using properl1_p7 pre unfolding proper1_def by auto
                                apply (simp del: fun_upd_apply tdsch2'.simps)
                            subgoal premises pre'
                              thm pre
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                 apply(rule pre'(6))
                                 apply(rule pre'(4))  
                                apply(cases "(pd2 - task_s2 CHR ''t'') < (min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))")
                            subgoal
                              apply(rule entails_tassn_trans)
                               apply(rule combine_wait_orig_wait_orig3)
                              subgoal 
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply (simp del: fun_upd_apply tdsch2'.simps)
                              apply(rule entails_tassn_trans)
                               apply(rule wait_orig_assn_tran)
                               apply(rule combine_out_0assm_rdy_wait_orig3[where R = "false\<^sub>A"])
                              subgoal 
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              unfolding entails_tassn_def false_assn_def
                              by(auto simp add: wait_orig_assn.simps)
                            apply(cases "(pd2 - task_s2 CHR ''t'') > (min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))")
                            subgoal
                              apply(rule entails_tassn_trans)
                               apply(rule combine_wait_orig_wait_orig4)
                              subgoal 
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply (simp del: fun_upd_apply tdsch2'.simps)
                              apply(rule entails_tassn_trans)
                               apply(rule wait_orig_assn_tran)
                               apply(rule combine_wait_orig_out_0assm3[where R = "false\<^sub>A"])
                              subgoal 
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              unfolding entails_tassn_def false_assn_def
                              by(auto simp add: wait_orig_assn.simps)
                            apply(cases "(pd2 - task_s2 CHR ''t'') = (min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c''))")
                            subgoal
                              apply(rule entails_tassn_trans)
                               apply(rule combine_wait_orig_wait_orig2)
                              subgoal 
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply (simp del: fun_upd_apply tdsch2'.simps)
                              apply(rule entails_tassn_trans)
                               apply(rule wait_orig_assn_tran)
                               apply(rule combine_out_0assm_rdy_out_0assm[where R = "false\<^sub>A"])
                              subgoal 
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              unfolding entails_tassn_def false_assn_def
                              by(auto simp add: wait_orig_assn.simps)
                            by auto
                          done
                        done
                      done
                    apply(erule disjE)
                    subgoal premises pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                         apply(rule pre(5))  
                      apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(erule disjE)
                    subgoal premises pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                         apply(rule pre(5))  
                      apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(subgoal_tac "p=[]")
                    prefer 2
                    subgoal using properl1_p7 unfolding proper1_def by auto
                    apply (simp del: fun_upd_apply tdsch2'.simps)
                    subgoal premises pre
                      apply simp
                      apply(rule disjI2)
                      apply(rule disjI1)
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                       apply(rule pre(5))  
                      apply(rule entails_tassn_trans)
                       apply(rule combine_out_0assm_wait_orig1)
                      subgoal by auto
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply clarify
                      unfolding combine_assn_def entails_tassn_def
                      apply clarify
                      subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                      apply simp
                      using pre pre' 
                      unfolding propc1_def proper1_def properp_def by auto
                      done
                    done
                  apply (simp del: tdsch2'.simps)
                      apply(erule disjE)
                      subgoal premises pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                         apply(rule pre(5))  
                        apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_waitin_tguar'_vassm'1)
                        subgoal by auto
                        apply (simp del: fun_upd_apply tdsch2'.simps)
                        apply clarify
                        unfolding combine_assn_def entails_tassn_def
                        apply clarify
                        subgoal for tr tr1 tr2
                          apply(cases kk')
                          subgoal
                            by(simp only:tdsch1'.simps)
                          subgoal for kk''
                            apply(simp only:tdsch1'.simps)
                            apply (simp del: fun_upd_apply tdsch2'.simps)
                            apply(erule disjE)
                            subgoal premises pre'
                              apply simp
                              apply(rule disjI2)
                              apply(rule disjI2)
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(cases "pd2 - task_s2 CHR ''t'' > min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule combine_wait_orig_waitin_tguar'_vassm'3)
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply(cases "pd2 - task_s2 CHR ''t'' \<le> min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_waitin_tguar'_vassm'4)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply)
                                apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, run_ch 2})")
                               prefer 2 subgoal by auto
                              apply (auto simp del:fun_upd_apply)
                                apply(rule wait_orig_assn_tran)
                                apply(rule combine_in_0assm_rdy_waitin_tguar'_vassm'1)
                                by auto
                              by auto
                            apply(erule disjE)
                            subgoal premises pre'
                              apply simp
                              apply(rule disjI2)
                              apply(rule disjI2)
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(cases "pd2 - task_s2 CHR ''t'' > min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule combine_wait_orig_waitin_tguar'_vassm'3)
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply(cases "pd2 - task_s2 CHR ''t'' \<le> min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_waitin_tguar'_vassm'4)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply)
                                apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, run_ch 2})")
                               prefer 2 subgoal by auto
                              apply (auto simp del:fun_upd_apply)
                                apply(rule wait_orig_assn_tran)
                                apply(rule combine_in_0assm_rdy_waitin_tguar'_vassm'1)
                                by auto
                              by auto
                            apply(erule disjE)
                            subgoal premises pre'
                              apply simp
                              apply(rule disjI2)
                              apply(rule disjI2)
                              thm pre'
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(cases "pd2 - task_s2 CHR ''t'' > min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule combine_wait_orig_waitin_tguar'_vassm'3)
                                by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              apply(cases "pd2 - task_s2 CHR ''t'' \<le> min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_waitin_tguar'_vassm'4)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply)
                                apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, run_ch 2})")
                               prefer 2 subgoal by auto
                              apply (auto simp del:fun_upd_apply)
                                apply(rule wait_orig_assn_tran)
                                apply(rule combine_in_0assm_rdy_waitin_tguar'_vassm'1)
                                by auto
                              by auto
                            apply(subgoal_tac "p=[]")
                             prefer 2
                            subgoal using properl1_p7 pre unfolding proper1_def by auto
                            apply (simp del: fun_upd_apply tdsch2'.simps)
                            subgoal premises pre'
                              apply simp
                              apply (rule disjI1)
                              apply(rule combine_blocks_assn)
                                 apply(rule pre'(3))
                                apply(rule pre'(6))
                               apply(rule pre'(4))
                              apply(cases "pd2 - task_s2 CHR ''t'' > min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_wait_orig4)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply tdsch2'.simps)
                                apply(rule entails_tassn_trans)
                                 apply(rule wait_orig_assn_tran)
                                 apply(rule combine_wait_orig_out_0assm1)
                                subgoal by auto
                                apply (simp del: fun_upd_apply tdsch2'.simps)
                                by(auto simp add: pure_assn_def conj_assn_def wait_orig_assn.simps entails_tassn_def)
                              apply(cases "pd2 - task_s2 CHR ''t'' < min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'')")
                              subgoal
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_wait_orig3)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply tdsch2'.simps)
                                apply(rule entails_tassn_trans)
                                 apply(rule wait_orig_assn_tran)
                                apply(rule combine_in_0assm_rdy_wait_orig2[where R = "false\<^sub>A"])
                                subgoal by auto                  
                                by(auto simp add: false_assn_def wait_orig_assn.simps entails_tassn_def)
                              apply(cases "min (pd1 - task_s1 CHR ''t'') (pc1 - task_s1 CHR ''c'') = pd2 - task_s2 CHR ''t''")
                              subgoal
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_wait_orig2)
                                subgoal
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply (simp del: fun_upd_apply tdsch2'.simps)
                                apply(rule entails_tassn_trans)
                                 apply(rule wait_orig_assn_tran)
                                 apply(rule combine_in_0assm_rdy_out_0assm)
                                subgoal by auto
                                apply(subgoal_tac"({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, run_ch 2, preempt_ch 1}) = ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, preempt_ch 1, run_ch 2})")
                               prefer 2 subgoal by auto
                              apply (auto simp del:fun_upd_apply)
                                apply (rule wait_orig_assn_tran)
                                unfolding combine_assn_def entails_tassn_def
                                apply clarify
                                subgoal premises pre'' for tr tr1 tr2
                                  thm pre'
                                  apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                                         apply simp
                                  using pre pre' pre''
                                  unfolding propc1_def proper1_def properp_def apply auto
                                  apply(subgoal_tac"(dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (pd2 - task_s2 CHR ''t''))) = (dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + pd2 - task_s2 CHR ''t''))")
                                  by auto
                                done
                              by auto
                            done
                          done
                        done
                      apply(erule disjE)
                      subgoal premises pre
                      apply simp
                      apply(rule disjI2)
                      apply(rule disjI1)
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                       apply(rule pre(5))  
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(erule disjE)
                      subgoal premises pre
                      apply simp
                      apply(rule disjI2)
                      apply(rule disjI1)
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                       apply(rule pre(5))  
                        apply(rule combine_out_0assm_waitin_tguar'_vassm'2)
                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(subgoal_tac "p=[]")
                    prefer 2
                    subgoal using properl1_p7 unfolding proper1_def by auto
                    apply (simp del: fun_upd_apply tdsch2'.simps)
                      subgoal premises pre
                      apply simp
                      apply(rule disjI2)
                      apply(rule disjI1)
                        apply(rule combine_blocks_assn)
                          apply(rule pre(14))
                          apply(rule pre(15))
                       apply(rule pre(5))  
                        apply(rule entails_tassn_trans)
                       apply(rule combine_out_0assm_wait_orig1)
                      subgoal by auto
                      apply (simp del: fun_upd_apply tdsch2'.simps)
                      apply clarify
                      unfolding combine_assn_def entails_tassn_def
                      apply clarify
                      subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                      apply simp
                      using pre pre' 
                      unfolding propc1_def proper1_def properp_def by auto
                      done
                    done
                  done
                by auto
              subgoal apply(cases task_es1) by auto
              subgoal apply(cases task_es1) by auto
              done
            apply(cases schs)
            subgoal for p rn rp
              apply(cases task_es1)
              subgoal by auto
              subgoal for st1 ent1 t1
                apply(cases st1)
                subgoal
                  apply(simp del:tdsch2'.simps)
                  apply(cases "ent2 = Suc 0")
                  prefer 2 subgoal by auto
                   apply(simp del:tdsch2'.simps)
                   apply(erule disjE)
                  subgoal
                    apply(erule disjE)
                    subgoal premises pre
                      apply simp
                      apply(rule disjI1)
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                         apply(rule pre(5))  
                        apply(rule entails_tassn_trans)
                       apply(rule combine_waitin_tguar'_vassm'_wait_orig2')
                      subgoal
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(simp del:fun_upd_apply tdsch2'.simps)
                    apply clarify
                    apply(rule wait_orig_assn_tran)
                    unfolding combine_assn_def entails_tassn_def
                      apply clarify
                      subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                             apply simp
                      subgoal 
                      proof-
                        have a:"min (pd2 - (task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t''))) (pc2 - (task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t''))) = min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'') - (pd1 - dis_s1 CHR ''t'') " 
                          by auto
                        have b:" (\<lambda>t. ParState
           (EState
             (Task RUNNING (Suc 0) 1, task_s2
              (CHR ''t'' := task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') + t, CHR ''c'' := task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t'') + t)))
           (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') + t)))) =
                                 (\<lambda>t. ParState
           (EState
             (Task RUNNING (Suc 0) 1, task_s2
              (CHR ''t'' := task_s2 CHR ''t'' + (t + (pd1 - dis_s1 CHR ''t'')), CHR ''c'' := task_s2 CHR ''c'' + (t + (pd1 - dis_s1 CHR ''t'')))))
           (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (t + (pd1 - dis_s1 CHR ''t''))))))"
                          apply(rule ext)+
                          by auto
                        have c:"(dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') + d)) = (dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (d + (pd1 - dis_s1 CHR ''t''))))" for d
                          by auto
                        have d:"(task_s2(CHR ''t'' := task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') + d, CHR ''c'' := task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t'') + d)) = (task_s2(CHR ''t'' := task_s2 CHR ''t'' + (d + (pd1 - dis_s1 CHR ''t'')), CHR ''c'' := task_s2 CHR ''c'' + (d + (pd1 - dis_s1 CHR ''t''))))" for d
                          by auto
                        have e:"(\<lambda>v d. task_dis_assn' 2 k2' pd2 pc2 (dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') + d)) (Task READY (Suc 0) 1)
             (task_s2(CHR ''t'' := task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') + d, CHR ''c'' := task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t'') + d))) =
                                (\<lambda>v d. task_dis_assn' 2 k2' pd2 pc2 (dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (d + (pd1 - dis_s1 CHR ''t'')))) (Task READY (Suc 0) 1)
             (task_s2
              (CHR ''t'' := task_s2 CHR ''t'' + (d + (pd1 - dis_s1 CHR ''t'')), CHR ''c'' := task_s2 CHR ''c'' + (d + (pd1 - dis_s1 CHR ''t'')))))"
                          apply(rule ext)+
                          apply (subst c)
                          apply (subst d)
                          by auto
                        show ?thesis
                          apply simp
                          apply(rule disjI1)
                          using pre'(3)
                          apply(subst a)
                          apply(subst b) 
                          apply(subst e)
                          by auto
                      qed
                      using pre pre' 
                      unfolding propc1_def proper1_def properp_def by auto
                    done
                  apply(erule disjE)
                  subgoal premises pre
                      apply simp
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                         apply(rule pre(5))  
                      apply(rule combine_waitin_tguar'_vassm'_waitin_tguar'_vassm'1)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(erule disjE)
                  subgoal premises pre
                      apply simp
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                         apply(rule pre(5))  
                      apply(rule combine_waitin_tguar'_vassm'_waitin_tguar'_vassm'1)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                  subgoal premises pre
                      apply simp
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                         apply(rule pre(5))  
                      apply(rule combine_waitin_tguar'_vassm'_waitin_tguar'_vassm'1)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    done
                  subgoal
                    apply(erule disjE)
                    subgoal premises pre
                      apply simp
                      apply(rule disjI1)
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                       apply(rule pre(5))  
                      apply(cases "min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'') < pd1 - dis_s1 CHR ''t''")
                      subgoal
                        apply(rule entails_tassn_trans)
                         apply(rule combine_wait_orig_wait_orig3)
                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                        apply(simp del:fun_upd_apply tdsch2'.simps)
                        apply(rule entails_tassn_trans)
                         apply(rule wait_orig_assn_tran)
                         apply(rule combine_out_0assm_srdy_wait_orig1)
                        subgoal by auto
                        by(auto simp add: pure_assn_def conj_assn_def entails_tassn_def wait_orig_assn.simps)
                      apply(cases "min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'') \<ge> pd1 - dis_s1 CHR ''t''")
                        apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_wait_orig6)
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                       apply(auto simp del:fun_upd_apply tdsch2'.simps)
                      apply(rule wait_orig_assn_tran)
                      unfolding combine_assn_def entails_tassn_def
                      apply clarify
                      subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                             apply simp
                      subgoal 
                      proof-
                        have a:"(min (pd2 - (task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t''))) (pc2 - (task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t'')))) = (min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'') - (pd1 - dis_s1 CHR ''t''))"
                          by auto
                        have b:"(\<lambda>t. ParState
           (EState
             (Task RUNNING (Suc 0) 1, task_s2
              (CHR ''t'' := task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') + t, CHR ''c'' := task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t'') + t)))
           (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') + t)))) = 
(\<lambda>t. ParState
           (EState
             (Task RUNNING (Suc 0) 1, task_s2
              (CHR ''t'' := task_s2 CHR ''t'' + (t + (pd1 - dis_s1 CHR ''t'')), CHR ''c'' := task_s2 CHR ''c'' + (t + (pd1 - dis_s1 CHR ''t'')))))
           (EState (estate.None, dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + (t + (pd1 - dis_s1 CHR ''t''))))))"
                          apply(rule ext)
                          by auto
                          have c:"(dis_s2
          (CHR ''t'' :=
             dis_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') +
             min (pd2 - (task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t''))) (pc2 - (task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t''))))) = 
(dis_s2(CHR ''t'' := dis_s2 CHR ''t'' + min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'')))"
                            apply (subst a)
                            by auto
                          have d:"(task_s2
          (CHR ''t'' :=
             task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t'') +
             min (pd2 - (task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t''))) (pc2 - (task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t''))),
           CHR ''c'' :=
             task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t'') +
             min (pd2 - (task_s2 CHR ''t'' + (pd1 - dis_s1 CHR ''t''))) (pc2 - (task_s2 CHR ''c'' + (pd1 - dis_s1 CHR ''t'')))))=
(task_s2
          (CHR ''t'' := task_s2 CHR ''t'' + min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c''),
           CHR ''c'' := task_s2 CHR ''c'' + min (pd2 - task_s2 CHR ''t'') (pc2 - task_s2 CHR ''c'')))"
                            apply(subst a)+
                            by auto
                        show ?thesis
                          apply simp
                          apply(rule disjI2)
                          using pre'(3)
                          apply(subst a)
                          apply(subst b)  
                          apply(subst c)
                          apply(subst d)
                          by auto
                      qed
                      using pre pre' 
                      unfolding propc1_def proper1_def properp_def by auto
                    done
                  subgoal
                    apply(erule disjE)
                    subgoal
                      subgoal premises pre
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                       apply(rule pre(5)) 
                       apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_waitin_tguar'_vassm'2')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(auto simp del:fun_upd_apply tdsch2'.simps)
                      apply(rule entails_tassn_trans)
                       apply(rule wait_orig_assn_tran)
                      apply(rule combine_out_0assm_srdy_waitin_tguar'_vassm'2[where R = "false\<^sub>A"])
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      by(auto simp add: false_assn_def entails_tassn_def wait_orig_assn.simps)
                    done
                  apply(erule disjE)
                  subgoal premises pre
                    apply simp
                    apply(rule disjI2)
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                       apply(rule pre(5)) 
                       apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_waitin_tguar'_vassm'2')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(auto simp del:fun_upd_apply tdsch2'.simps)
                      apply(rule wait_orig_assn_tran)
                      apply(rule entails_tassn_trans)
                       apply(rule combine_out_0assm_srdy_waitin_tguar'_vassm'1)
                      subgoal by auto
                       apply(subgoal_tac "p=[]")
                        prefer 2
                      subgoal using properl1_p7 pre unfolding proper1_def by auto
                      apply (auto simp del: fun_upd_apply tdsch2'.simps)
                      unfolding combine_assn_def entails_tassn_def
                      apply clarify
                      subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                             apply simp
                      using pre pre' 
                      unfolding propc1_def proper1_def properp_def by auto
                    done
                  subgoal premises pre
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                       apply(rule pre(5)) 
                       apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_waitin_tguar'_vassm'2')
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      apply(auto simp del:fun_upd_apply tdsch2'.simps)
                      apply(rule entails_tassn_trans)
                       apply(rule wait_orig_assn_tran)
                      apply(rule combine_out_0assm_srdy_waitin_tguar'_vassm'2[where R = "false\<^sub>A"])
                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                      by(auto simp add: false_assn_def entails_tassn_def wait_orig_assn.simps)
                    done
                  done
                done
              subgoal
                apply(simp del:tdsch2'.simps)
                apply(cases "ent2 = Suc 0")
                 prefer 2 subgoal by auto
                apply(simp del:tdsch2'.simps)
                   apply(erule disjE)
                  subgoal
                    apply(erule disjE)
                     apply(subgoal_tac "rn = 2")
                      prefer 2 subgoal unfolding propc1_def by auto
                     apply(simp del:tdsch2'.simps)
                    subgoal premises pre
                      apply simp
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                         apply(rule pre(5))  
                      apply(rule entails_tassn_trans)
                       apply(rule combine_waitin_tguar'_vassm'_out_0assm1')
                      subgoal by auto
                      apply(simp del:tdsch2'.simps fun_upd_apply)
                      unfolding combine_assn_def entails_tassn_def
                      apply clarify
                      subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                             apply simp
                      using pre pre' 
                      unfolding propc1_def proper1_def properp_def by auto
                    done
                  apply(erule disjE)
                  subgoal premises pre
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                         apply(rule pre(5))  
                      apply(rule combine_waitin_tguar'_vassm'_in_0orig_vassm'1)
                      by auto   
                    apply(erule disjE)
                  subgoal premises pre
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                         apply(rule pre(5))  
                      apply(rule combine_waitin_tguar'_vassm'_in_0orig_vassm'1)
                      by auto
                  subgoal premises pre
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(16))
                         apply(rule pre(5))  
                      apply(rule combine_waitin_tguar'_vassm'_in_0orig_vassm'1)
                      by auto
                    done
                  apply(subgoal_tac"rn =2 \<and> p=[]")
                   prefer 2 subgoal using properl1_p7 unfolding proper1_def propc1_def  by auto
                  apply(simp del:tdsch2'.simps fun_upd_apply)
                  apply(erule disjE)
                  subgoal premises pre
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(17))
                       apply(rule pre(5)) 
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_out_0assm1)
                      subgoal by auto
                      apply(simp del:tdsch2'.simps fun_upd_apply)
                      apply clarify
                      apply(rule combine_out_0assm_srdy_out_0assm1)
                      by auto
                    apply(erule disjE)
                  subgoal premises pre
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(17))
                       apply(rule pre(5)) 
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_in_0orig_vassm'1)
                      subgoal by auto
                      apply(simp del:tdsch2'.simps fun_upd_apply add:pre)
                      apply clarify
                      apply(rule combine_out_0assm_srdy_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(erule disjE)
                    subgoal premises pre
                      apply simp
                      apply(rule disjI2)
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(17))
                       apply(rule pre(5)) 
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_in_0orig_vassm'1)
                      subgoal by auto
                      apply(simp del:tdsch2'.simps fun_upd_apply)
                      apply clarify
                      apply(rule entails_tassn_trans)
                       apply(rule combine_out_0assm_srdy_in_0orig_vassm'1)
                      subgoal by auto
                      unfolding combine_assn_def entails_tassn_def
                      apply clarify
                      subgoal premises pre' for tr tr1 tr2
                      thm pre'
                      apply(rule pre(1)[where ?tr1.0 = tr1 and ?tr2.0 = tr2])
                             apply simp
                      using pre pre' 
                      unfolding propc1_def proper1_def properp_def by auto
                    done
                    subgoal premises pre
                      thm pre
                        apply(rule combine_blocks_assn)
                          apply(rule pre(15))
                          apply(rule pre(17))
                       apply(rule pre(5)) 
                      apply(rule entails_tassn_trans)
                       apply(rule combine_wait_orig_in_0orig_vassm'1)
                      subgoal by auto
                      apply(simp del:tdsch2'.simps fun_upd_apply add:pre)
                      apply clarify
                      apply(rule combine_out_0assm_srdy_in_0orig_vassm'2)
                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    done
                  subgoal
                    unfolding propc1_def by auto
                  done
                by auto
              subgoal apply(cases task_es1) by auto
              subgoal apply(cases task_es1) by auto
              done
            done
          done
        done
      done
  qed


end
