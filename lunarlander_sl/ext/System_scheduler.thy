theory System_scheduler
  imports ext_Complementlemma AssumeGuarantee
begin

type_synonym tid = real

datatype status =
  WAIT | READY | RUNNING


datatype estate =
  Sch (pool:"(real \<times> tid) list") (run_now:tid) (run_prior:real)
| Task (status:status) (entered:nat) (task_prior:real)
| None

fun sched_push :: "tid \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_push t (Sch p rn rp) s = Sch (p @ [(s (CHR ''p''), t)]) rn rp"
| "sched_push t (Task st ent tp) s = undefined"
| "sched_push t None s = undefined"

fun sched_assign :: "tid \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_assign t (Sch p rn rp) s = Sch p t (s (CHR ''p''))"
| "sched_assign t (Task st ent tp) s = undefined"
| "sched_assign t None s = undefined"

fun get_max_default :: "real \<times> tid \<Rightarrow> (real \<times> tid) list \<Rightarrow> real \<times> tid" where
  "get_max_default (prior, t) [] = (prior, t)"
| "get_max_default (prior, t) ((prior2, t2) # rest) =
    (if prior \<ge> prior2 then
       get_max_default (prior, t) rest
     else
       get_max_default (prior2, t2) rest)"

fun get_max :: "(real \<times> tid) list \<Rightarrow> real \<times> tid" where
  "get_max [] = (-1, -1)"
| "get_max ((prior, t) # rest) = get_max_default (prior, t) rest"

fun del_proc :: "(real \<times> tid) list \<Rightarrow> tid \<Rightarrow> (real \<times> tid) list" where
  "del_proc [] t = []"
| "del_proc ((prior, t) # rest) t2 =
    (if t = t2 then rest
     else (prior, t) # del_proc rest t)"

fun sched_get_max :: "estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_get_max (Sch p rn rp) s =
    (let (prior, t) = get_max p in Sch (del_proc p t) t prior)"
| "sched_get_max (Task st ent tp) s = undefined"
| "sched_get_max None s = undefined"

fun sched_clear :: "estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_clear (Sch p rn rp) s = Sch [] (-1) (-1)"
| "sched_clear (Task st ent tp) s = undefined"
| "sched_clear None s = undefined"

fun sched_del_proc :: "tid \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_del_proc t (Sch p rn rp) s = Sch (del_proc p t) rn rp"
| "sched_del_proc t (Task st ent tp) s = undefined"
| "sched_del_proc t None s = undefined"

definition req_ch :: "tid \<Rightarrow> string" where
  "req_ch tid = (
    if tid = 1 then ''reqProcessor1''
    else if tid = 2 then ''reqProcessor2''
    else if tid = 3 then ''reqProcessor3''
    else undefined)"

definition preempt_ch :: "tid \<Rightarrow> string" where
  "preempt_ch tid = (
    if tid = 1 then ''preempt1''
    else if tid = 2 then ''preempt2''
    else if tid = 3 then ''preempt3''
    else undefined)"

definition run_ch :: "tid \<Rightarrow> string" where
  "run_ch tid = (
    if tid = 1 then ''run1''
    else if tid = 2 then ''run2''
    else if tid = 3 then ''run3''
    else undefined)"

definition free_ch :: "tid \<Rightarrow> string" where
  "free_ch tid = (
    if tid = 1 then ''free1''
    else if tid = 2 then ''free2''
    else if tid = 3 then ''free3''
    else undefined)"


definition exit_ch :: "tid \<Rightarrow> string" where
  "exit_ch tid = (
    if tid = 1 then ''exit1''
    else if tid = 2 then ''exit2''
    else if tid = 3 then ''exit3''
    else undefined)"

inductive sched_assn :: "estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "sched_assn (Sch p rn rp) start_s []"
| "start_es = Sch p rn rp \<Longrightarrow>
   rp \<ge> prior \<Longrightarrow>
   t \<in> {1, 2, 3} \<Longrightarrow>
   In\<^sub>t (EState (start_es, start_s)) (req_ch t) prior blk1 \<Longrightarrow>
   sched_assn (sched_push t start_es start_s) start_s rest \<Longrightarrow>
   sched_assn start_es start_s (blk1 @ rest)"
| "start_es = Sch p rn rp \<Longrightarrow>
   rp < prior \<Longrightarrow>
   t \<in> {1, 2, 3} \<Longrightarrow>
   In\<^sub>t (EState (start_es, start_s)) (req_ch t) prior blk1 \<Longrightarrow>
   if run_now start_es \<noteq> -1 then
     Out\<^sub>t (EState (start_es, start_s)) (preempt_ch (run_now start_es)) 0 blk2
   else
     emp\<^sub>t blk2 \<Longrightarrow>
   Out\<^sub>t (EState (sched_assign t start_es (start_s(CHR ''p'' := prior)), start_s(CHR ''p'' := prior)))
        (run_ch t) 0 blk3 \<Longrightarrow>
   sched_assn (sched_assign t start_es (start_s(CHR ''p'' := prior)))
              (start_s(CHR ''p'' := prior)) rest \<Longrightarrow>
   sched_assn start_es start_s (blk1 @ blk2 @ blk3 @ rest)"
| "start_es = Sch p rn rp \<Longrightarrow>
   length p > 0 \<Longrightarrow>
   In\<^sub>t (EState (start_es, start_s)) (free_ch t) 0 blk1 \<Longrightarrow>
   Out\<^sub>t (EState (sched_get_max start_es start_s, start_s)) 
        (run_ch (run_now (sched_get_max start_es start_s))) 0 blk2 \<Longrightarrow>
   sched_assn (sched_get_max start_es start_s) start_s rest \<Longrightarrow>
   sched_assn start_es start_s (blk1 @ blk2 @ rest)"
| "start_es = Sch p rn rp \<Longrightarrow>
   length p = 0 \<Longrightarrow>
   In\<^sub>t (EState (start_es, start_s)) (free_ch t) 0 blk1 \<Longrightarrow>
   sched_assn (sched_clear start_es start_s) start_s rest \<Longrightarrow>
   sched_assn start_es start_s (blk1 @ rest)"
| "start_es = Sch p rn rp \<Longrightarrow>
   In\<^sub>t (EState (start_es, start_s)) (exit_ch t) 0 blk1 \<Longrightarrow> 
   sched_assn (sched_del_proc t start_es start_s) start_s rest \<Longrightarrow> 
   sched_assn start_es start_s (blk1 @ rest)"


definition dispatch_ch :: "tid \<Rightarrow> string" where
  "dispatch_ch tid = (
    if tid = 1 then ''dis1''
    else if tid = 2 then ''dis2''
    else if tid = 3 then ''dis3''
    else undefined)"

definition tid_set :: "tid set" where "tid_set = {1,2,3}"

lemma ch_dist:"dispatch_ch t \<noteq> run_ch t" "dispatch_ch t \<noteq> req_ch t" 
              "dispatch_ch t \<noteq> exit_ch t" "dispatch_ch t \<noteq> preempt_ch t"
              "dispatch_ch t \<noteq> free_ch t"
              "run_ch t \<noteq> dispatch_ch t" "req_ch t \<noteq> dispatch_ch t" 
              "exit_ch t \<noteq> dispatch_ch t" "preempt_ch t \<noteq> dispatch_ch t"
              "free_ch t \<noteq> dispatch_ch t"
              if cond:"t\<in>tid_set"
  using cond
  unfolding dispatch_ch_def run_ch_def req_ch_def exit_ch_def preempt_ch_def free_ch_def tid_set_def 
  by auto

inductive task_assn :: "tid \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "task_assn t (Task st ent tp) start_s []"
| "start_es = Task WAIT ent tp \<Longrightarrow>
   In\<^sub>t (EState (start_es, start_s)) (dispatch_ch t) 0 blk1 \<Longrightarrow>
   task_assn t (Task READY 0 tp) (start_s(CHR ''t'' := 0)) rest \<Longrightarrow>
   task_assn t start_es start_s (blk1 @ rest)"
(*
| "start_es = Task WAIT ent tp \<Longrightarrow>
   (d::real) > 0 \<Longrightarrow>
   blk1 = WaitBlk (ereal d) (\<lambda>_. EState (start_es, start_s)) ({}, {dispatch_ch t}) \<Longrightarrow>
   task_assn t start_es start_s rest \<Longrightarrow>
   task_assn t start_es start_s (blk1 # rest)"
*)
(*
| "start_es = Task READY ent tp \<Longrightarrow>
   init_t = start_s (CHR ''t'') \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   Out\<^sub>t (EState (start_es, start_s)) (req_ch t) tp blk1 \<Longrightarrow>
   WaitIn\<^sub>t wt start_es (\<lambda>t. start_s(CHR ''t'' := init_t + t)) (run_ch t) 0 ({}, {run_ch t}) blk2 \<Longrightarrow>
   task_assn t (Task RUNNING ent tp) (start_s(CHR ''t'' := init_t + wt)) rest \<Longrightarrow>
   task_assn t start_es start_s (blk1 @ blk2 @ rest)"
*)
| "start_es = Task READY ent tp \<Longrightarrow>
   init_t = start_s (CHR ''t'') \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   Waitout\<^sub>t d (\<lambda>_ . EState (start_es, start_s)) (req_ch t) tp ({req_ch t}, {}) blk1 \<Longrightarrow>
   d = 0 \<longrightarrow> Waitin\<^sub>t wt (\<lambda>_ . EState (start_es, start_s(CHR ''t'' := init_t + t))) (run_ch t) 0 ({}, {run_ch t}) blk2 \<Longrightarrow>
   d = 0 \<longrightarrow> task_assn t (Task RUNNING ent tp) (start_s(CHR ''t'' := init_t + wt)) rest \<Longrightarrow>
   task_assn t start_es start_s (blk1 @ blk2 @ rest)"
| "start_es = Task READY ent tp \<Longrightarrow>
   init_t = start_s (CHR ''t'') \<Longrightarrow>
   wt = 0.045 - init_t \<Longrightarrow>
   Out\<^sub>t (EState (start_es, start_s)) (req_ch t) tp blk1 \<Longrightarrow>
   Wait\<^sub>t wt (\<lambda>t. EState (start_es, start_s(CHR ''t'' := init_t + t))) ({run_ch t}, {}) blk2 \<Longrightarrow>
   Out\<^sub>t (EState (start_es, start_s(CHR ''t'' := 0.45))) (exit_ch t) 0 blk3 \<Longrightarrow>
   task_assn t (Task WAIT ent tp) (start_s(CHR ''t'' := 0.45)) rest \<Longrightarrow>
   task_assn t start_es start_s (blk1 @ blk2 @ blk3 @ rest)"
| "start_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = start_s (CHR ''t'') \<Longrightarrow>
   init_c = start_s (CHR ''c'') \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   wt \<le> 0.01 - init_c \<Longrightarrow>
   WaitIn\<^sub>t wt start_es (\<lambda>t. start_s(CHR ''t'' := init_t + t, CHR ''c'' := init_c + t))
           (preempt_ch t) 0 ({preempt_ch t}, {}) blk1 \<Longrightarrow>
   task_assn t (Task READY 1 tp) (start_s(CHR ''t'' := init_t + wt, CHR ''c'' := init_c + wt))
             rest \<Longrightarrow>
   task_assn t start_es start_s (blk1 @ rest)"
| "start_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = start_s (CHR ''t'') \<Longrightarrow>
   init_c = start_s (CHR ''c'') \<Longrightarrow>
   if 0.045 - init_t \<ge> 0.01 - init_c then
     wt = 0.01 - init_c
   else
     wt = 0.045 - init_t \<Longrightarrow>
   Wait\<^sub>t wt (\<lambda>t. EState (start_es, start_s(CHR ''t'' := init_t + t, CHR ''c'' := init_c + t)))
         ({preempt_ch t}, {}) blk1 \<Longrightarrow>
   Out\<^sub>t (EState (start_es, start_s(CHR ''t'' := init_t + wt, CHR ''c'' := init_c + wt)))
        (free_ch t) 0 blk2 \<Longrightarrow>
   task_assn t (Task WAIT 1 tp) (start_s(CHR ''t'' := init_t + wt, CHR ''c'' := init_c + wt))
             rest \<Longrightarrow>
   task_assn t start_es start_s (blk1 @ blk2 @ rest)"

inductive_cases task_assnE: "task_assn t task_es task_s tr"
inductive_cases task_assn_waitE: "task_assn t (Task WAIT x2 x3) task_s tr1"

(*
t := 0
(
  <t_dot = 1 & t < 0.045>;
  t := 0;
  dis[tid]!
)**
*)

inductive dispatch_assn :: "tid \<Rightarrow> state \<Rightarrow> estate tassn" where
  "dispatch_assn t start_s []"
  (* Case for finishing a period *)
| "init_t = start_s (CHR ''t'') \<Longrightarrow>
   init_t < 0.045 \<Longrightarrow>
   wt = 0.045 - init_t \<Longrightarrow>
   Wait\<^sub>t wt (\<lambda>t. EState (None, start_s(CHR ''t'' := init_t + t))) ({}, {}) blk1 \<Longrightarrow>
   Out\<^sub>t (EState (None, start_s(CHR ''t'' := 0))) (dispatch_ch t) 0 blk2 \<Longrightarrow>
   dispatch_assn t (start_s(CHR ''t'' := 0)) rest \<Longrightarrow>
   dispatch_assn t start_s (blk1 @ blk2 @ rest)"
  (* Case for running part of a period 
| "init_t = start_s (CHR ''t'') \<Longrightarrow>
   init_t < 0.045 \<Longrightarrow>
   wt < 0.045 - init_t \<Longrightarrow>
   wt \<ge> 0 \<Longrightarrow>
   Wait\<^sub>t wt (\<lambda>t. EState (None, start_s(CHR ''t'' := init_t + t))) ({}, {}) blk1 \<Longrightarrow>
   dispatch_assn t (start_s(CHR ''t'' := init_t + wt)) rest \<Longrightarrow>
   dispatch_assn t start_s (blk1 @ rest)"*)

inductive task_dis_assn :: "tid \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "task_dis_assn t dis_s task_es task_s []"
| "task_es = Task WAIT ent tp \<Longrightarrow>
   dis_t = dis_s (CHR ''t'') \<Longrightarrow>
   wt = 0.045 - dis_t \<Longrightarrow>
   Wait\<^sub>t wt (\<lambda>t. ParState (EState (task_es, task_s))
                          (EState (None, dis_s(CHR ''t'' := dis_t + t))))
         ({}, {dispatch_ch t}) blk1 \<Longrightarrow>
   IO\<^sub>t (dispatch_ch t) 0 blk2 \<Longrightarrow>
   task_dis_assn t (dis_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0))
                 rest \<Longrightarrow>
   task_dis_assn t dis_s task_es task_s (blk1 @ blk2 @ rest)"
| "task_es = Task READY ent tp \<Longrightarrow>
   init_task_t = task_s (CHR ''t'') \<Longrightarrow>
   dis_t = dis_s (CHR ''t'') \<Longrightarrow>
   wt \<le> 0.045 - init_task_t \<Longrightarrow>
   Waitout\<^sub>t d (\<lambda>_. ParState (EState (task_es, task_s))(EState (None,dis_s(CHR ''t'' := dis_t + t)))) (req_ch t) tp ({req_ch t}, {}) blk1 \<Longrightarrow>
   d=0 \<longrightarrow> Waitin\<^sub>t wt (\<lambda>t. ParState (EState (task_es,task_s(CHR ''t'' := init_t + t))) (EState (None, dis_s(CHR ''t'' := dis_t + t)))) (run_ch t) 0 ({}, {run_ch t}) blk2 \<Longrightarrow>
   d=0 \<longrightarrow> task_dis_assn t (dis_s(CHR ''t'' := dis_t + wt)) (Task RUNNING ent tp) (task_s(CHR ''t'' := init_t + wt)) rest \<Longrightarrow>
   task_dis_assn t dis_s task_es task_s (blk1 @ blk2 @ rest)"
| "task_es = Task READY ent tp \<Longrightarrow>
   init_task_t = task_s (CHR ''t'') \<Longrightarrow>
   init_dis_t = dis_s (CHR ''t'') \<Longrightarrow>
   wt = 0.045 - init_task_t \<Longrightarrow>
   Out\<^sub>t (EState (task_es, task_s)) (req_ch t) tp blk1 \<Longrightarrow>
   Wait\<^sub>t wt (\<lambda>t. ParState (EState (task_es,task_s(CHR ''t'' := init_t + t))) (EState (None, dis_s(CHR ''t'' := dis_t + t)))) ({run_ch t}, {}) blk2 \<Longrightarrow>
   Out\<^sub>t (EState (task_es, task_s(CHR ''t'' := 0.45))) (exit_ch t) 0 blk3 \<Longrightarrow>
   task_dis_assn t (dis_s(CHR ''t'' := dis_t + wt)) (Task WAIT ent tp) (task_s(CHR ''t'' := init_t + wt)) rest \<Longrightarrow>
   task_dis_assn t dis_s task_es task_s (blk1 @ blk2 @ blk3 @ rest)"
| "task_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_c = task_s (CHR ''c'') \<Longrightarrow>
   wt \<le> 0.045 - init_t \<Longrightarrow>
   wt \<le> 0.01 - init_c \<Longrightarrow>
   init_dis_t = dis_s (CHR ''t'') \<Longrightarrow>
   Waitin\<^sub>t wt  (\<lambda>t. EState (task_es,task_s(CHR ''t'' := init_t + t, CHR ''c'' := init_c + t)))
           (preempt_ch t) 0 ({preempt_ch t}, {}) blk1 \<Longrightarrow>
   task_dis_assn t (dis_s(CHR ''t'' := dis_t + wt)) (Task READY 1 tp) (task_s(CHR ''t'' := init_t + wt, CHR ''c'' := init_c + wt))
             rest \<Longrightarrow>
   task_dis_assn t dis task_es task_s (blk1 @ rest)"
| "start_es = Task RUNNING 1 tp \<Longrightarrow>
   init_t = task_s (CHR ''t'') \<Longrightarrow>
   init_c = task_s (CHR ''c'') \<Longrightarrow>
   if 0.045 - init_t \<ge> 0.01 - init_c then
     wt = 0.01 - init_c
   else
     wt = 0.045 - init_t \<Longrightarrow>
   init_dis_t = dis_s (CHR ''t'') \<Longrightarrow>
   Wait\<^sub>t wt (\<lambda>t. EState (task_es, task_s(CHR ''t'' := init_t + t, CHR ''c'' := init_c + t)))
         ({preempt_ch t}, {}) blk1 \<Longrightarrow>
   Out\<^sub>t (EState (task_es, task_s(CHR ''t'' := init_t + wt, CHR ''c'' := init_c + wt)))
        (free_ch t) 0 blk2 \<Longrightarrow>
   task_dis_assn t (dis_s(CHR ''t'' := dis_t + wt)) (Task WAIT 1 tp) (task_s(CHR ''t'' := init_t + wt, CHR ''c'' := init_c + wt))
             rest \<Longrightarrow>
   task_dis_assn t dis_s task_es task_s (blk1 @ blk2 @ rest)"


lemma combine_task_dis:
  "task_assn t task_es task_s tr1 \<Longrightarrow>
   dispatch_assn t' dis_s tr2 \<Longrightarrow>
   t \<in> tid_set \<Longrightarrow>
   t = t' \<Longrightarrow> 
   combine_blocks {dispatch_ch t} tr1 tr2 tr \<Longrightarrow>
   task_dis_assn t dis_s task_es task_s tr"
proof (induction arbitrary: tr tr2 dis_s rule: task_assn.induct)
  case (1 t st ent tp task_s)
  note a1 = 1
  then show ?case
  proof (induction arbitrary: tr rule: dispatch_assn.induct)
    case (1 t' start_s)
    have c1: "tr = []"
      using 1 by (auto elim: sync_elims)
    show ?case
      apply (subst c1)
      by (auto intro: task_dis_assn.intros)
  next
    case (2 init_t start_s wt blk1 t blk2 rest)
    then show ?case
      apply(auto simp add:wait_assn.simps out_assn.simps)
      by (auto elim: sync_elims)
  qed
next
  case (2 task_es ent tp task_s t blk1 rest)
  note a2 = 2
  from a2(5,6,7,8) show ?case
  proof (induction arbitrary: tr  rule: dispatch_assn.induct)
    case (1 t' start_s)
    then show ?case 
      using a2
      apply(auto elim!: in_assn.cases)
      by(auto elim!: sync_elims)
  next
    case (2 init_t start_s wt blk1' t' blk2' rest')
    note b2 = 2
    show ?case 
      thm b2
      thm a2
      using a2(2)
      using b2(2,3,4,5) using b2(8,9,10)
      apply (auto elim!:in_assn.cases wait_assn.cases out_assn.cases)
      subgoal apply (auto elim!: sync_elims) done
      subgoal premises pre for d
      proof(cases "(9 / 200 - init_t) > d")
        case True
        then have "ereal (9 / 200 - init_t) > ereal d"
          by auto
        thm pre
        then obtain tr' where "tr = WaitBlk (ereal d)
            (\<lambda>t. ParState (EState (task_es, task_s))
                  (EState (estate.None, start_s(CHR ''t'' := init_t + t))))
            ({}, {dispatch_ch t'}) # tr' "
           "combine_blocks {dispatch_ch t'} (InBlock (dispatch_ch t') 0 # rest)
            (WaitBlk (ereal (9 / 200 - init_t - d))
              (\<lambda>t. EState (estate.None, start_s(CHR ''t'' := init_t + (t + d)))) ({}, {}) #
             OutBlock (dispatch_ch t') 0 # rest')
            tr'"
          using pre
          apply(elim combine_blocks_waitE3) by auto
        then show ?thesis by (auto elim!: sync_elims)
      next
        case False
        note false1 = False
        show ?thesis 
        proof (cases "d = 9 / 200 - init_t")
          case True
          then obtain tr' where tr':"tr = WaitBlk (ereal d)
            (\<lambda>t. ParState (EState (task_es, task_s))
                  (EState (estate.None, start_s(CHR ''t'' := init_t + t))))
            ({}, {dispatch_ch t'}) # tr' "
           "combine_blocks {dispatch_ch t'} (InBlock (dispatch_ch t') 0 # rest)
            (OutBlock (dispatch_ch t') 0 # rest')
            tr'"
          using pre
          by(auto elim!: combine_blocks_waitE2) 
        then obtain tr'' where tr'':"tr' = IOBlock (dispatch_ch t') 0 # tr'' "
                               "combine_blocks {dispatch_ch t'} rest rest' tr''"
          apply(elim combine_blocks_pairE) by auto
        have 1:"Wait\<^sub>t (9 / 200 - start_s CHR ''t'')
      (\<lambda>t. ParState (EState (Task WAIT ent tp, task_s))
            (EState (estate.None, start_s(CHR ''t'' := start_s CHR ''t'' + t))))
      ({}, {dispatch_ch t'})
      [WaitBlk (ereal (9 / 200 - start_s CHR ''t''))
        (\<lambda>t. ParState (EState (Task WAIT ent tp, task_s))
              (EState (estate.None, start_s(CHR ''t'' := start_s CHR ''t'' + t))))
        ({}, {dispatch_ch t'})]"
          using b2 
          using True pre(9) wait_assn.intros(1) by blast
        have 2:"IO\<^sub>t (dispatch_ch t') 0 [IOBlock (dispatch_ch t') 0]"
          by (simp add: io_assn.intros)
        have 3:"task_dis_assn t' (start_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0))
      tr''"
          using a2(4)[of "(start_s(CHR ''t'' := 0))" rest' tr'']
          using a2(6,7) b2(6,9) tr'' 
          by fastforce
        show ?thesis 
          using task_dis_assn.intros(2)[OF a2(1),of init_t start_s wt task_s t' "[WaitBlk (ereal d)
        (\<lambda>t. ParState (EState (task_es, task_s))
              (EState (estate.None, start_s(CHR ''t'' := init_t + t)))) 
        ({}, {dispatch_ch t'})]" "[IOBlock (dispatch_ch t') 0]" tr'' ]
          apply(simp add:a2 b2 True 1 2 3)
          using tr' tr'' 
          using True a2(1) b2(1) by force
        next
          case False
          then have "(9 / 200 - init_t) < d"
            using false1 by auto
          then obtain tr' where "tr = WaitBlk (ereal (9 / 200 - init_t))
            (\<lambda>t. ParState (EState (task_es, task_s))
                  (EState (estate.None, start_s(CHR ''t'' := init_t + t))))
            ({}, {dispatch_ch t'}) # tr' "
           "combine_blocks {dispatch_ch t'} (WaitBlk (ereal (9 / 200 - init_t - d))
              (\<lambda>t. EState (task_es, task_s)) ({}, {dispatch_ch t'}) # InBlock (dispatch_ch t') 0 # rest)
            (OutBlock (dispatch_ch t') 0 # rest')
            tr'"
          using pre
          apply(elim combine_blocks_waitE4) apply auto 
          by (meson combine_blocks_pairE2' insertI1)
        then show ?thesis 
          by (auto elim!: sync_elims)
        qed
      qed
      subgoal
        by (auto elim!: sync_elims)
      subgoal premises pre for d db
      proof (cases "db > 9 / 200 - init_t")
        case True
        thm pre
        then obtain tr' where "combine_blocks {dispatch_ch t'}
     (WaitBlk (ereal db-(9 / 200 - init_t)) (\<lambda>_. EState (task_es, task_s)) ({}, {dispatch_ch t'}) #
      InBlock (dispatch_ch t') 0 # rest)
     (WaitBlk (ereal d) (\<lambda>_. EState (estate.None, start_s(CHR ''t'' := 0)))
       ({dispatch_ch t'}, {}) #
      OutBlock (dispatch_ch t') 0 # rest') tr'"
          using pre(4,6,8,10) by(auto elim: combine_blocks_waitE4)
        then show ?thesis 
          by(auto elim!: sync_elims) 
      next
        case False
        note false1 = False
        show ?thesis 
        proof (cases "9 / 200 - init_t = db")
          case True
          then obtain tr' where "combine_blocks {dispatch_ch t'}
     (InBlock (dispatch_ch t') 0 # rest)
     (WaitBlk (ereal d) (\<lambda>_. EState (estate.None, start_s(CHR ''t'' := 0)))
       ({dispatch_ch t'}, {}) #
      OutBlock (dispatch_ch t') 0 # rest') tr'"
          using pre(4,6,8,10) by(auto elim: combine_blocks_waitE2)
        then show ?thesis 
          by(auto elim!: sync_elims) 
        next
          case False
          then have "9 / 200 - init_t > db" 
            using false1 by auto
          then obtain tr' where "combine_blocks {dispatch_ch t'}
        (InBlock (dispatch_ch t') 0 # rest)
        (WaitBlk (ereal (9 / 200 - init_t) - ereal db)
          (\<lambda>t. EState (estate.None, start_s(CHR ''t'' := init_t + (t + db)))) ({}, {}) #
         WaitBlk (ereal d) (\<lambda>_. EState (estate.None, start_s(CHR ''t'' := 0)))
          ({dispatch_ch t'}, {}) #
         OutBlock (dispatch_ch t') 0 # rest') tr'"
            using pre(4,6,8,10) by(auto elim: combine_blocks_waitE3)
          then show ?thesis 
            by(auto elim!: sync_elims)
        qed
      qed
      done
  qed
next
  case (3 task_es ent tp init_t task_s wt d t blk1 blk2 rest)
  note a3 = 3
  from a3(7,8,9,10) show ?case 
  proof (induction arbitrary: tr  rule: dispatch_assn.induct)
    case (1 t' start_s)
    note b1 = 1
    show ?case 
      thm a3
      thm b1
      using b1(1,2,3)
      using a3(4,5)
      apply (auto elim!:in_assn.cases waitin_assn.cases waitout_assn.cases)
                 apply (auto elim!: sync_elims)
      apply (auto simp add: ch_dist) 
      subgoal premises pre for tra 
      proof-
        thm pre
        have 1:"task_dis_assn t' start_s (Task RUNNING ent tp) (task_s(CHR ''t'' := init_t + wt)) tra"
          using a3(6,8,9) 
          apply(simp add: pre)
          using dispatch_assn.intros(1)[of t' start_s]
          using pre(8)
          by (smt (verit, best) "3.IH" a3(9) b1(1) pre(4) pre(6))
      obtain start_t where startt:"start_t = start_s CHR ''t''"
        by auto
      have 2:"wt \<le> 9 / 200 - task_s CHR ''t''"
        using a3 by auto
      have 3:"task_dis_assn t' start_s task_es task_s (blk1 @ blk2 @ tra)"
        apply(rule task_dis_assn.intros(3)[where d=0])
              apply(rule a3(1))
             apply(rule a3(2))
            apply(rule startt)
           apply(rule a3(3))
          apply auto
          prefer 3
        apply(simp add:pre(6) startt)
        apply(rule 1)
        sorry
      then show ?thesis using pre by auto
    qed
    done
  next
    case (2 init_t' start_s wt' blk1' t' blk2' rest')
    note b2 = 2
    show ?case 
      thm b2
      thm a3
      thm task_dis_assn.intros(3)
      using b2(4,5,8,9,10) a3(4,5)
      apply auto
      subgoal premises pre 
        thm pre
        using pre(6,7)
        apply(auto elim!:waitout_assn.cases)
        using task_dis_assn.intros(3)[of task_es ent tp init_t task_s init_t' start_s wt d t]
        apply(auto simp add: a3(1,2,3) b2(1))
        sorry
      sorry
      
  qed
next
  case (4 start_es ent tp init_t start_s wt t blk1 blk2 blk3 rest)
  then show ?case sorry
next
  case (5 start_es tp init_t start_s init_c wt t blk1 rest)
  then show ?case sorry
next
  case (6 start_es tp init_t start_s init_c wt t blk1 blk2 rest)
  then show ?case sorry
qed
    



(*

inductive sch_task_assn :: "estate \<Rightarrow> state \<Rightarrow> tid \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> state \<Rightarrow> estate tassn" where
  "sch_task_assn (Sch p rn rp) sch_s t (Task st ent tp) task_s dis_s []"
| "sch_es = Sch p rn rp \<Longrightarrow>
   task_es = Task WAIT ent tp \<Longrightarrow>
   wt = 0.045 - dis_t \<Longrightarrow>
   Wait\<^sub>t wt (\<lambda>t. ParState (EState (task_es, task_s))
                          (EState (None, dis_s(CHR ''t'' := dis_t + t))))
         ({}, {}) blk1 \<Longrightarrow>
   IO\<^sub>t (dis_ch t) 0 blk2 \<Longrightarrow>
   sch_task_assn sch_es sch_s t (Task READY 0 tp) (task_s(CHR ''t'' := 0)) (dis_s(CHR ''t'' := 0))
                 rest \<Longrightarrow>
   sch_task_assn sch_es sch_s t task_es task_s dis_s (blk1 @ blk2 @ rest)"
| "sch_es = Sch p rn rp \<Longrightarrow>
   task_es = Task READY ent tp \<Longrightarrow>
   init_task_t = task_s (CHR ''t'') \<Longrightarrow>
   init_dis_t = dis_s (CHR ''t'') \<Longrightarrow>
   rp \<ge> f(tid) \<Longrightarrow>
   wt \<le> 0.045 - init_task_t \<Longrightarrow>
   IO\<^sub>t  (req_ch t) tp blk1 \<Longrightarrow>
   Waitin\<^sub>t wt (\<lambda>t. ParState (EState (task_es,task_s(CHR ''t'' := init_t + t))) (EState (None, dis_s(CHR ''t'' := dis_t + t)))) (run_ch t) 0 ({run_ch t}, {}) blk2 \<Longrightarrow>
   sch_task_assn 
        (sched_push t sch_es (sch_s(CHR ''p'' := f(tid)))) 
              (sch_s(CHR ''p'' := f(tid))) t  
        (Task RUNNING ent tp) (task_s(CHR ''t'' := init_t + wt)) 
                    (dis_s(CHR ''t'' := dis_t + wt)) rest \<Longrightarrow>
   sch_task_assn sch_es sch_s t task_es task_s dis_s (blk1 @ blk2 @ rest)"
| "sch_es = Sch p rn rp \<Longrightarrow>
   task_es = Task READY ent tp \<Longrightarrow>
   init_task_t = task_s (CHR ''t'') \<Longrightarrow>
   init_dis_t = dis_s (CHR ''t'') \<Longrightarrow>
   rp < f(tid) \<Longrightarrow>
   wt \<le> 0.045 - init_task_t \<Longrightarrow>
   IO\<^sub>t  (req_ch t) tp blk1 \<Longrightarrow>
   if run_now start_es \<noteq> -1 then
     Out\<^sub>t (EState (start_es, start_s)) (preempt_ch (run_now start_es)) 0 blk2
   else
     emp\<^sub>t blk2 \<Longrightarrow>
   IO\<^sub>t  (run_ch t) 0  blk3 \<Longrightarrow>
   sch_task_assn sch_es (sch_s(CHR ''p'' := f(tid))) t  
        (Task RUNNING ent tp) (task_s(CHR ''t'' := init_t + wt)) 
          (dis_s(CHR ''t'' := dis_t + wt)) rest \<Longrightarrow>
   sch_task_assn sch_es sch_s  t  task_es task_s dis_s (blk1 @ blk2 @blk3 @ rest)"



*)

fun dispatch_assn' :: "tid \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> estate tassn" where
  "dispatch_assn' t 0 start_s tr \<longleftrightarrow> (emp\<^sub>t tr)"
  (* Case for finishing a period *)
| "dispatch_assn' t (Suc k) start_s tr \<longleftrightarrow> 
   wait_orig_assn (0.045-start_s (CHR ''t''))
                  (\<lambda>t. EState (None, start_s(CHR ''t'' := start_s (CHR ''t'') + t))) ({}, {})
   (out_orig_assn (dispatch_ch t) 0 (EState (None, start_s(CHR ''t'' := 0))) 
   (dispatch_assn' t k (start_s(CHR ''t'' := 0)))) tr"



fun task_assn' :: "tid \<Rightarrow> nat \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "task_assn' t 0 (Task st ent tp) start_s tr \<longleftrightarrow> (emp\<^sub>t tr) "
| "task_assn' t (Suc k) (Task WAIT ent tp) start_s tr \<longleftrightarrow>
   in_vassm_assn (dispatch_ch t) {0} (EState (Task WAIT ent tp, start_s))
   (\<lambda>_ . task_assn' t k (Task READY 0 tp) (start_s(CHR ''t'' := 0))) tr"
| "task_assn' t (Suc k) (Task READY ent tp) start_s tr \<longleftrightarrow>
   out_0assm_assn (req_ch t) tp 
     (waitin_assms'_assn {0..<0.045-start_s (CHR ''t'')}
          (\<lambda>t . EState (Task READY ent tp, start_s(CHR ''t'' := start_s (CHR ''t'') + t)))
          ({}, {run_ch t}) (run_ch t) {0}
     (\<lambda> v d'. task_assn' t k (Task RUNNING 1 tp)
          (start_s(CHR ''t'' := start_s (CHR ''t'') + d',CHR ''c'' := 0)))) tr \<or> 
   out_0assm_assn (req_ch t) tp 
     (wait_orig_assn (0.045 - start_s (CHR ''t''))
          (\<lambda>t. EState (Task READY ent tp, start_s(CHR ''t'' := start_s (CHR ''t'') + t)))
          ({}, {run_ch t}) 
     (out_0assm_assn (exit_ch t) 0  
     (task_assn' t k (Task WAIT ent tp) (start_s(CHR ''t'' := 0.45))))) tr"
| "task_assn' t (Suc k) (Task RUNNING ent tp) start_s tr \<longleftrightarrow>
   (if ent = 1 then
   waitin_assms'_assn ({0.. 0.045 - start_s (CHR ''t'')} \<inter> {0.. 0.01 - start_s (CHR ''c'')})
     (\<lambda>t. EState (Task RUNNING 1 tp, start_s(CHR ''t'' := start_s (CHR ''t'') + t,
                                             CHR ''c'' := start_s (CHR ''c'') + t)))
     ({preempt_ch t}, {}) (preempt_ch t) {0} 
   (\<lambda> v d. task_assn' t k (Task READY 1 tp)
     (start_s(CHR ''t'' := start_s (CHR ''t'') + d,
              CHR ''c'' := start_s (CHR ''c'') + d))) tr
   \<or>
   wait_guar'_assn {min (0.045-start_s (CHR ''t'')) (0.01-start_s (CHR ''c''))}
     (\<lambda>t. EState (Task RUNNING 1 tp, start_s(CHR ''t'' := start_s (CHR ''t'') + t,
                                             CHR ''c'' := start_s (CHR ''c'') + t)))
     ({preempt_ch t}, {}) 
   (\<lambda> d. out_0assm_assn (free_ch t) 0 
      (task_assn' t k (Task WAIT 1 tp) (start_s(CHR ''t'' := start_s (CHR ''t'') + d,
                                                CHR ''c'' := start_s (CHR ''c'') + d)))) tr
   else False)"
| "task_assn' t n (Sch v va vb) start_s tr \<longleftrightarrow> False"
| "task_assn' t n None start_s tr \<longleftrightarrow> False"


fun task_dis_assn' :: "tid \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "task_dis_assn' t 0 dis_s task_es task_s tr \<longleftrightarrow> (emp\<^sub>t tr)"
| "task_dis_assn' t (Suc k) dis_s (Task WAIT ent tp) task_s tr \<longleftrightarrow>
   wait_orig_assn (0.045 - dis_s (CHR ''t'')) 
            (\<lambda>t. ParState (EState (Task WAIT ent tp, task_s))
                          (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t)))) ({}, {dispatch_ch t})
   (io_orig_assn (dispatch_ch t) 0 
   (task_dis_assn' t k (dis_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0))))tr"
| "task_dis_assn' t (Suc k) dis_s (Task READY ent tp) task_s tr \<longleftrightarrow>
   out_0assm_assn (req_ch t) tp  
   (waitin_assms'_assn {0..<0.045-task_s (CHR ''t'')} 
           (\<lambda>t. ParState (EState (Task READY ent tp, task_s(CHR ''t'' := task_s (CHR ''t'') + t))) 
                         (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t)))) ({}, {run_ch t}) (run_ch t) {0}
   (\<lambda> v d'. task_dis_assn' t k (dis_s(CHR ''t'' := dis_s (CHR ''t'') + d')) (Task RUNNING 1 tp) (task_s(CHR ''t'' := task_s (CHR ''t'') + d',CHR ''c'' := 0)))) tr \<or> 
   out_0assm_assn (req_ch t) tp  
   (wait_orig_assn (0.045 - task_s (CHR ''t'')) 
           (\<lambda>t. ParState (EState (Task READY ent tp, task_s(CHR ''t'' := task_s (CHR ''t'') + t)))
                         (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t)))) ({}, {run_ch t}) 
   (out_0assm_assn (exit_ch t) 0 
   (task_dis_assn' t k (dis_s(CHR ''t'' := dis_s (CHR ''t'') + 0.45-task_s (CHR ''t''))) (Task WAIT ent tp) (task_s(CHR ''t'' := 0.45))))) tr"
| "task_dis_assn' t (Suc k) dis_s (Task RUNNING ent tp) task_s tr \<longleftrightarrow>
   (if ent = 1 then
   waitin_assms'_assn ({0.. 0.045 - task_s (CHR ''t'')} \<inter> {0.. 0.01 - task_s (CHR ''c'')})
     (\<lambda>t. ParState (EState (Task RUNNING 1 tp, task_s(CHR ''t'' := task_s (CHR ''t'') + t,
                                             CHR ''c'' := task_s (CHR ''c'') + t)))
                   (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t))))
     ({preempt_ch t}, {}) (preempt_ch t) {0} 
   (\<lambda> v d. task_dis_assn' t k (dis_s(CHR ''t'' := dis_s (CHR ''t'') + d)) (Task READY 1 tp)
     (task_s(CHR ''t'' := task_s (CHR ''t'') + d,
              CHR ''c'' := task_s (CHR ''c'') + d))) tr
   \<or>
   wait_guar'_assn {min (0.045-task_s (CHR ''t'')) (0.01-task_s (CHR ''c''))}
     (\<lambda>t. ParState (EState (Task RUNNING 1 tp, task_s(CHR ''t'' := task_s (CHR ''t'') + t,
                                             CHR ''c'' := task_s (CHR ''c'') + t)))
                   (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t))))
     ({preempt_ch t}, {}) 
   (\<lambda> d. out_0assm_assn (free_ch t) 0
      (task_dis_assn' t k  (dis_s(CHR ''t'' := dis_s (CHR ''t'') + d)) (Task WAIT 1 tp)
    (task_s(CHR ''t'' := task_s (CHR ''t'') + d, CHR ''c'' := task_s (CHR ''c'') + d)))) tr
   else False)"

thm task_assn'.induct
thm task_assn'.simps


lemma combine_out_tassm0_wait_orig_out_orig:
  assumes "dh \<notin> chs"
   and "ch \<in> chs"
 shows "combine_assn chs (out_0assm_assn dh v P) (wait_orig_assn d p rdy (out_orig_assn ch v' s Q))
        \<Longrightarrow>\<^sub>t (out_0assm_assn dh v  
            (combine_assn chs P (wait_orig_assn d p rdy (out_orig_assn ch v' s Q))))"
  apply(auto simp add:entails_tassn_def combine_assn_def)
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of dh v P tr1])
      apply auto
    subgoal for tr1'
      apply(cases rule: wait_orig_assn.cases[of d p rdy "(out_orig_assn ch v' s Q)" tr2])
        apply auto
      subgoal
        apply(cases rule: out_orig_assn.cases[of ch v' s Q tr2])
          apply auto
        subgoal for tr2'
          using assms
          apply(elim combine_blocks_unpairE1)
            apply auto
          apply(rule out_0assm_assn.intros(1))
          by auto
        subgoal for tr2' d
          using assms
          apply(elim combine_blocks_unpairE3)
           apply auto
          apply(rule out_0assm_assn.intros(1))
          by auto
        done
      subgoal for tr2'
        using assms
          apply(elim combine_blocks_unpairE3)
           apply auto
          apply(rule out_0assm_assn.intros(1))
          by auto
        done
      subgoal for d1 p1 a b tr1'
        apply(cases rule: wait_orig_assn.cases[of d p rdy "(out_orig_assn ch v' s Q)" tr2])
          apply auto
        subgoal
          apply(cases rule: out_orig_assn.cases[of ch v' s Q tr2])
            apply auto
          subgoal for tr2'
            using assms
            apply(auto elim:sync_elims)
            done
          subgoal for tr2' d2
            apply(cases "\<not>compat_rdy (a,b) ({ch}, {})")
            subgoal
             by(auto elim:sync_elims)
           apply(cases "d1>d2")
           subgoal 
             apply auto
             thm combine_blocks_waitE4
             apply(rule combine_blocks_waitE4[of chs ])





lemma combine_task_dis':
  "task_assn' t k task_es task_s tr1 \<Longrightarrow>
   dispatch_assn' t' kk dis_s tr2 \<Longrightarrow>
   t \<in> tid_set \<Longrightarrow>
   t = t' \<Longrightarrow>
   combine_blocks {dispatch_ch t} tr1 tr2 tr \<Longrightarrow>
   task_dis_assn' t k dis_s task_es task_s tr"
proof(induction k arbitrary: kk task_es task_s dis_s tr1 tr2 tr)
  case 0
  note 0 = 0
  then show ?case 
    apply(cases task_es)
      apply auto
    subgoal for st ent tp
  proof(induction kk)
    case 0
    then show ?case 
      apply auto 
      subgoal premises pre
        apply (rule combine_blocks_assn)
           apply (rule pre(1))
        apply(rule pre(2))
         apply(rule pre(5))
        by (auto elim!: sync_elims)
      done
  next
    case (Suc kk)
    then show ?case 
      apply auto 
      subgoal premises pre
        thm pre
        apply(rule combine_blocks_assn)
           apply(rule pre (2))
          apply(rule pre (3))
         apply(rule pre (6))
        apply(rule entails_tassn_trans)
         apply(rule combine_emp_wait_orig5)
        apply(rule combine_emp_out_orig1)
        by auto
      done
  qed
  done
next
  case (Suc k)
  note suc1 = Suc
  then show ?case 
  proof(induction kk)
    case 0
    then show ?case 
      apply(cases task_es)
      apply auto
      subgoal for st ent tp
        apply(cases st) apply simp
        subgoal premises pre
          thm pre
          apply(rule combine_blocks_assn)
             apply(rule pre(2))
            apply(rule pre(3))
           apply(rule pre(6))
          apply(rule combine_in_vassm_emp1)
          by auto
         apply simp
        subgoal apply(erule disjE)
          subgoal premises pre
            thm pre
            apply(rule disjI1)
            apply(rule combine_blocks_assn)
               apply(rule pre(8))
              apply(rule pre(2))
             apply(rule pre(5))
            apply(rule entails_tassn_trans)
             apply(rule combine_out_0assm_emp2)
            subgoal using ch_dist pre(3) by auto
            apply(rule out_0assm_assn_tran)
            subgoal 
              apply(rule entails_tassn_trans)
             apply(rule combine_waitin_assms'_emp2)
              subgoal using ch_dist pre(3) by auto
              apply(rule waitin_assms'_assn_tran)
              unfolding entails_tassn_def combine_assn_def
              apply clarify
              subgoal for v d tr tr1 tr2
                using pre(1)[of "(Task RUNNING (Suc 0) tp)"
                                "(task_s(CHR ''t'' := task_s CHR ''t'' + d, CHR ''c'' := 0))"
                                tr1 0 
                                "(dis_s(CHR ''t'' := dis_s CHR ''t'' + d))" tr2 tr]
                apply(subgoal_tac"dispatch_assn' t' 0 (dis_s(CHR ''t'' := dis_s CHR ''t'' + d)) tr2")
                subgoal by blast
                by auto
              done
            done
          subgoal premises pre
            thm pre
            apply(rule disjI2)
            apply(rule combine_blocks_assn)
              apply(rule pre(8))
              apply(rule pre(2))
             apply(rule pre(5))
            apply(rule entails_tassn_trans)
             apply(rule combine_out_0assm_emp2)
            subgoal using ch_dist pre(3) by auto
            apply(rule out_0assm_assn_tran)
            subgoal 
              apply(rule entails_tassn_trans)
               apply(rule combine_wait_orig_emp2)
              apply(rule wait_orig_assn_tran)
              apply(rule entails_tassn_trans)
               apply(rule combine_out_0assm_emp2)
              subgoal using ch_dist pre(3) by auto
              apply(rule out_0assm_assn_tran)
              subgoal 
                unfolding entails_tassn_def combine_assn_def
                apply clarify
                subgoal for tr tr1 tr2
                  using pre(1)[of "(Task WAIT ent tp)" "(task_s(CHR ''t'' := 9 / 20))" tr1 0
                              "(dis_s(CHR ''t'' := dis_s CHR ''t'' + 9 / 20 - task_s CHR ''t''))"
                               tr2 tr]
                  apply(subgoal_tac "dispatch_assn' t' 0 (dis_s(CHR ''t'' := dis_s CHR ''t'' + 9 / 20 - task_s CHR ''t''))tr2")
                   apply blast
                  by auto
                done
              done
            done
          done
        subgoal apply simp
          apply(cases "ent = Suc 0")
          subgoal 
            apply simp
            apply(erule disjE)
            subgoal apply(rule disjI1)
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                   apply(rule pre(9))
                  apply(rule pre(2))
                apply(rule pre(5))
                apply(rule entails_tassn_trans)
                 apply(rule combine_waitin_assms'_emp2)
                subgoal using ch_dist pre(3) by auto
                apply(rule waitin_assms'_assn_tran)
                apply clarify
                subgoal for v d
                  unfolding entails_tassn_def combine_assn_def
                  apply clarify
                  subgoal for tr tr1 tr2
                    using pre(1)[of "(Task READY (Suc 0) tp)" 
                                    "(task_s(CHR ''t'' := task_s CHR ''t'' + d, CHR ''c'' := task_s CHR ''c'' + d))" 
                                    tr1 0 "(dis_s(CHR ''t'' := dis_s CHR ''t'' + d))"
                                    tr2 tr]
                    apply(subgoal_tac "dispatch_assn' t' 0 (dis_s(CHR ''t'' := dis_s CHR ''t'' + d)) tr2")
                     apply blast
                    by auto
                  done
                done
              done
            subgoal apply(rule disjI2)
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                   apply(rule pre(9))
                  apply(rule pre(2))
                 apply(rule pre(5))
                apply(rule entails_tassn_trans)
                 apply(rule combine_wait_guar'_emp2)
                apply(rule wait_guar'_assn_tran)
                apply clarify
                subgoal for v
                  apply(rule entails_tassn_trans)
                   apply(rule combine_out_0assm_emp2)
                  subgoal using ch_dist pre(3) by auto
                  apply(rule out_0assm_assn_tran)
                  unfolding entails_tassn_def combine_assn_def
                  apply clarify
                  subgoal for tr tr1 tr2
                    using pre(1)[of "(Task WAIT (Suc 0) tp)" 
                     "(task_s(CHR ''t'' :=task_s CHR ''t'' + min (9 / 200 - task_s CHR ''t'') (1 / 100 - task_s CHR ''c''),
                              CHR ''c'' :=task_s CHR ''c'' + min (9 / 200 - task_s CHR ''t'') (1 / 100 - task_s CHR ''c'')))"
                     tr1 0 "(dis_s (CHR ''t'' := dis_s CHR ''t'' + min (9 / 200 - task_s CHR ''t'') (1 / 100 - task_s CHR ''c'')))"
                        tr2 tr]
                    apply(subgoal_tac "dispatch_assn' t' 0
                       (dis_s (CHR ''t'' := dis_s CHR ''t'' + min (9 / 200 - task_s CHR ''t'') (1 / 100 - task_s CHR ''c''))) tr2")
                     apply blast
                    by auto
                  done
                done
              done
            done
          subgoal by auto
          done
        done
      done
  next
    case (Suc kk)
    note suc2 = Suc
    then show ?case 
      apply auto
      apply(cases task_es)
        apply auto
      subgoal for st ent tp
        apply(cases st) apply simp
        subgoal premises pre
          thm pre
          apply(rule combine_blocks_assn)
             apply(rule pre(3))
            apply(rule pre(4))
           apply(rule pre(7))
          apply(rule entails_tassn_trans)
           apply(rule combine_in_vassm_wait_orig1)
            apply simp
           apply simp
          apply auto
          apply(rule wait_orig_assn_tran)
          apply(rule entails_tassn_trans)
           apply(rule combine_in_vassm_out_orig1)
            apply auto
          apply(rule io_orig_assn_tran)
          unfolding entails_tassn_def combine_assn_def
          apply clarify
          subgoal for tr tr1 tr2
            using pre(2)[of "(Task READY 0 tp)" "(\<lambda>a. if a = CHR ''t'' then 0 else task_s a)" tr1
                            kk "(\<lambda>a. if a = CHR ''t'' then 0 else dis_s a)" tr2 tr]
            by auto
          done
        subgoal apply simp
          apply(erule disjE)
          subgoal apply(rule disjI1)
            subgoal premises pre
              thm pre
              apply(rule combine_blocks_assn)
                 apply(rule pre(9))
                apply(rule pre(3))
               apply(rule pre(6))
              apply(rule combine_out_tassm_wait_orig2)
          
        
  qed
  
      

  
qed


























end