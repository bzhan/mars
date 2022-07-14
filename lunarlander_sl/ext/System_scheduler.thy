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
     else (prior, t) # del_proc rest t2)"

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

(*
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
    
*)


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

definition up_ent_c :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "up_ent_c ent c = (if ent = 0 then 0 else c)"

fun task_assn' :: "tid \<Rightarrow> nat \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "task_assn' t 0 (Task st ent tp) start_s tr \<longleftrightarrow> (emp\<^sub>t tr) "
| "task_assn' t (Suc k) (Task WAIT ent tp) start_s tr \<longleftrightarrow>
   in_vassm_assn (dispatch_ch t) {0} (EState (Task WAIT ent tp, start_s))
   (\<lambda>_ . task_assn' t k (Task READY 0 tp) (start_s(CHR ''t'' := 0))) tr"
| "task_assn' t (Suc k) (Task READY ent tp) start_s tr \<longleftrightarrow>
   out_0assm_assn (req_ch t) tp 
     (waitin_tguar'_vassm'_assn {0..<0.045-start_s (CHR ''t'')}
          (\<lambda>t . EState (Task READY ent tp, start_s(CHR ''t'' := start_s (CHR ''t'') + t)))
          ({}, {run_ch t}) (run_ch t) {0}
     (\<lambda> v d'. task_assn' t k (Task RUNNING 1 tp)
          (start_s(CHR ''t'' := start_s (CHR ''t'') + d',
                   CHR ''c'' := (up_ent_c ent (start_s (CHR ''c''))))))) tr \<or> 
   out_0assm_assn (req_ch t) tp 
     (wait_orig_assn (0.045 - start_s (CHR ''t''))
          (\<lambda>t. EState (Task READY ent tp, start_s(CHR ''t'' := start_s (CHR ''t'') + t)))
          ({}, {run_ch t}) 
     (out_0assm_rdy_assn (exit_ch t) 0 ({exit_ch t},{run_ch t})
     (task_assn' t k (Task WAIT ent tp) (start_s(CHR ''t'' := 0.045))))) tr \<or>
   out_0assm_assn (req_ch t) tp 
     (wait_orig_assn (0.045 - start_s (CHR ''t''))
          (\<lambda>t. EState (Task READY ent tp, start_s(CHR ''t'' := start_s (CHR ''t'') + t)))
          ({}, {run_ch t}) 
     (in_0assm_rdy_assn (run_ch t) 0  ({exit_ch t},{run_ch t})
     (task_assn' t k (Task WAIT ent tp) (start_s(CHR ''t'' := 0.045))))) tr"
| "task_assn' t (Suc k) (Task RUNNING ent tp) start_s tr \<longleftrightarrow>
   (if ent = 1 then
   waitin_tguar'_vassm'_assn ({0..< 0.045 - start_s (CHR ''t'')} 
                            \<inter> {0..< 0.01 - start_s (CHR ''c'')})
     (\<lambda>t. EState (Task RUNNING 1 tp, start_s(CHR ''t'' := start_s (CHR ''t'') + t,
                                             CHR ''c'' := start_s (CHR ''c'') + t)))
     ({preempt_ch t}, {}) (preempt_ch t) {0} 
   (\<lambda> v d. task_assn' t k (Task READY 1 tp)
     (start_s(CHR ''t'' := start_s (CHR ''t'') + d,
              CHR ''c'' := start_s (CHR ''c'') + d))) tr
   \<or>
   wait_orig_assn (min (0.045-start_s (CHR ''t'')) (0.01-start_s (CHR ''c'')))
     (\<lambda>t. EState (Task RUNNING 1 tp, start_s(CHR ''t'' := start_s (CHR ''t'') + t,
                                             CHR ''c'' := start_s (CHR ''c'') + t)))
     ({preempt_ch t}, {}) 
   (out_0assm_assn (free_ch t) 0 
      (task_assn' t k (Task WAIT 1 tp) 
               (start_s(CHR ''t'' := start_s (CHR ''t'') + 
                              (min (0.045-start_s (CHR ''t'')) (0.01-start_s (CHR ''c''))),
                        CHR ''c'' := start_s (CHR ''c'') + 
                              (min (0.045-start_s (CHR ''t'')) (0.01-start_s (CHR ''c''))))))) tr
   else False)"
| "task_assn' t n (Sch v va vb) start_s tr \<longleftrightarrow> False"
| "task_assn' t n None start_s tr \<longleftrightarrow> False"


fun task_dis_assn' :: "tid \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "task_dis_assn' t 0 dis_s task_es task_s tr \<longleftrightarrow> (emp\<^sub>t tr)"
| "task_dis_assn' t (Suc k) dis_s (Task WAIT ent tp) task_s tr \<longleftrightarrow>
   wait_orig_assn (0.045 - dis_s (CHR ''t'')) 
            (\<lambda>t. ParState (EState (Task WAIT ent tp, task_s))
                          (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t))))
                  ({}, {dispatch_ch t})
   (io_orig_assn (dispatch_ch t) 0 
   (task_dis_assn' t k (dis_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0))))tr"
| "task_dis_assn' t (Suc k) dis_s (Task READY ent tp) task_s tr \<longleftrightarrow>
   out_0assm_assn (req_ch t) tp  
   (waitin_tguar'_vassm'_assn {0..<0.045-task_s (CHR ''t'')} 
           (\<lambda>t. ParState (EState (Task READY ent tp, task_s(CHR ''t'' := task_s (CHR ''t'') + t))) 
                         (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t)))) 
                  ({}, {run_ch t}) (run_ch t) {0}
   (\<lambda> v d'. task_dis_assn' t k (dis_s(CHR ''t'' := dis_s (CHR ''t'') + d')) 
                               (Task RUNNING 1 tp) 
           (task_s(CHR ''t'' := task_s (CHR ''t'') + d',
                   CHR ''c'' := up_ent_c ent (task_s (CHR ''c'')))))) tr \<or> 
   out_0assm_assn (req_ch t) tp  
   (wait_orig_assn (0.045 - task_s (CHR ''t'')) 
           (\<lambda>t. ParState (EState (Task READY ent tp, task_s(CHR ''t'' := task_s (CHR ''t'') + t)))
                         (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t)))) 
                  ({}, {run_ch t}) 
   (out_0assm_rdy_assn (exit_ch t) 0 ({dispatch_ch t, exit_ch t}, {run_ch t})
   (task_dis_assn' t k (dis_s(CHR ''t'' := dis_s (CHR ''t'') + 0.045-dis_s (CHR ''t''))) 
                       (Task WAIT ent tp) (task_s(CHR ''t'' := 0.045))))) tr \<or>
   out_0assm_assn (req_ch t) tp  
   (wait_orig_assn (0.045 - task_s (CHR ''t'')) 
           (\<lambda>t. ParState (EState (Task READY ent tp, task_s(CHR ''t'' := task_s (CHR ''t'') + t)))
                         (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t)))) 
                  ({}, {run_ch t}) 
   (in_0assm_rdy_assn (run_ch t) 0 ({dispatch_ch t, exit_ch t}, {run_ch t})
   (task_dis_assn' t k (dis_s(CHR ''t'' := dis_s (CHR ''t'') + 0.045-dis_s (CHR ''t''))) 
                       (Task WAIT ent tp) (task_s(CHR ''t'' := 0.045))))) tr"
| "task_dis_assn' t (Suc k) dis_s (Task RUNNING ent tp) task_s tr \<longleftrightarrow>
   (if ent = 1 then
   waitin_tguar'_vassm'_assn ({0..< 0.045 - task_s (CHR ''t'')} \<inter> {0..< 0.01 - task_s (CHR ''c'')})
     (\<lambda>t. ParState (EState (Task RUNNING 1 tp, task_s(CHR ''t'' := task_s (CHR ''t'') + t,
                                             CHR ''c'' := task_s (CHR ''c'') + t)))
                   (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t))))
     ({preempt_ch t}, {}) (preempt_ch t) {0} 
   (\<lambda> v d. task_dis_assn' t k (dis_s(CHR ''t'' := dis_s (CHR ''t'') + d)) (Task READY 1 tp)
     (task_s(CHR ''t'' := task_s (CHR ''t'') + d, CHR ''c'' := task_s (CHR ''c'') + d))) tr
   \<or>
   wait_orig_assn (min (0.045-task_s (CHR ''t'')) (0.01-task_s (CHR ''c'')))
     (\<lambda>t. ParState (EState (Task RUNNING 1 tp, task_s(CHR ''t'' := task_s (CHR ''t'') + t,
                                             CHR ''c'' := task_s (CHR ''c'') + t)))
                   (EState (None, dis_s(CHR ''t'' := dis_s (CHR ''t'') + t))))
     ({preempt_ch t}, {}) 
   (out_0assm_assn (free_ch t) 0
      (task_dis_assn' t k  (dis_s(CHR ''t'' := dis_s (CHR ''t'') + 
                   (min (0.045-task_s (CHR ''t'')) (0.01-task_s (CHR ''c''))))) 
                           (Task WAIT 1 tp)
                           (task_s(CHR ''t'' := task_s (CHR ''t'') + 
                   (min (0.045-task_s (CHR ''t'')) (0.01-task_s (CHR ''c''))), 
                           CHR ''c'' := task_s (CHR ''c'') + 
                   (min (0.045-task_s (CHR ''t'')) (0.01-task_s (CHR ''c''))))))) tr
   else False)"
| "task_dis_assn' t n dis_s (Sch v va vb) task_s tr \<longleftrightarrow> False"
| "task_dis_assn' t n dis_s None task_s tr \<longleftrightarrow> False"

thm task_assn'.induct
thm task_assn'.simps


lemma combine_out_0assm_wait_orig_out_orig:
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
      subgoal for d1 a b p1 tr1'
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
            subgoal
           apply(cases "d1>d2")
           subgoal 
             apply(elim combine_blocks_waitE4)
                apply auto
             apply(rule out_0assm_assn.intros(2))
             by auto
           apply(cases "d2=d1")
           subgoal 
             apply simp
             apply(elim combine_blocks_waitE2)
              apply auto
             apply(rule out_0assm_assn.intros(2))
             by auto
           apply(elim combine_blocks_waitE3)
              apply auto
           apply(rule out_0assm_assn.intros(2))
           by auto
         done
       done
     subgoal for tr2'
       apply(cases "\<not>compat_rdy (a,b) rdy")
            subgoal
              by(auto elim:sync_elims)
            subgoal
           apply(cases "d1>d")
           subgoal 
             apply(elim combine_blocks_waitE4)
                apply auto
             apply(rule out_0assm_assn.intros(2))
             apply auto
              apply (cases rdy)
             by auto
           apply(cases "d=d1")
           subgoal 
             apply simp
             apply(elim combine_blocks_waitE2)
              apply auto
             apply(rule out_0assm_assn.intros(2))
              apply auto
             apply(cases rdy)
             by auto
           apply(elim combine_blocks_waitE3)
              apply auto
           apply(rule out_0assm_assn.intros(2))
            apply auto
           apply(cases rdy)
           by auto
         done
       done
     done
   done

lemma combine_in_0assm_wait_orig_out_orig:
  assumes "dh \<notin> chs"
   and "ch \<in> chs"
 shows "combine_assn chs (in_0assm_assn dh v P) (wait_orig_assn d p rdy (out_orig_assn ch v' s Q))
        \<Longrightarrow>\<^sub>t (in_0assm_assn dh v  
            (combine_assn chs P (wait_orig_assn d p rdy (out_orig_assn ch v' s Q))))"
  apply(auto simp add:entails_tassn_def combine_assn_def)
  subgoal for tr tr1 tr2
    apply(cases rule: in_0assm_assn.cases[of dh v P tr1])
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
          apply(rule in_0assm_assn.intros(1))
          by auto
        subgoal for tr2' d
          using assms
          apply(elim combine_blocks_unpairE3)
           apply auto
          apply(rule in_0assm_assn.intros(1))
          by auto
        done
      subgoal for tr2'
        using assms
          apply(elim combine_blocks_unpairE3)
           apply auto
          apply(rule in_0assm_assn.intros(1))
          by auto
        done
      subgoal for d1 a b p1 tr1'
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
            subgoal
           apply(cases "d1>d2")
           subgoal 
             apply(elim combine_blocks_waitE4)
                apply auto
             apply(rule in_0assm_assn.intros(2))
             by auto
           apply(cases "d2=d1")
           subgoal 
             apply simp
             apply(elim combine_blocks_waitE2)
              apply auto
             apply(rule in_0assm_assn.intros(2))
             by auto
           apply(elim combine_blocks_waitE3)
              apply auto
           apply(rule in_0assm_assn.intros(2))
           by auto
         done
       done
     subgoal for tr2'
       apply(cases "\<not>compat_rdy (a,b) rdy")
            subgoal
              by(auto elim:sync_elims)
            subgoal
           apply(cases "d1>d")
           subgoal 
             apply(elim combine_blocks_waitE4)
                apply auto
             apply(rule in_0assm_assn.intros(2))
             apply auto
              apply (cases rdy)
             by auto
           apply(cases "d=d1")
           subgoal 
             apply simp
             apply(elim combine_blocks_waitE2)
              apply auto
             apply(rule in_0assm_assn.intros(2))
              apply auto
             apply(cases rdy)
             by auto
           apply(elim combine_blocks_waitE3)
              apply auto
           apply(rule in_0assm_assn.intros(2))
            apply auto
           apply(cases rdy)
           by auto
         done
       done
     done
   done

lemma combine_out_0assm_out_orig:
  assumes "dh \<notin> chs"
   and "ch \<in> chs"
 shows "combine_assn chs (out_0assm_assn dh v P) (out_orig_assn ch v' s Q)
        \<Longrightarrow>\<^sub>t (out_0assm_assn dh v  
            (combine_assn chs P (out_orig_assn ch v' s Q)))"
  apply(auto simp add:entails_tassn_def combine_assn_def)
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of dh v P tr1])
      apply auto
    subgoal for tr1'
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
      subgoal for d1 a b p1 tr1'
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
            subgoal
           apply(cases "d1>d2")
           subgoal 
             apply(elim combine_blocks_waitE4)
                apply auto
             apply(rule out_0assm_assn.intros(2))
             by auto
           apply(cases "d2=d1")
           subgoal 
             apply simp
             apply(elim combine_blocks_waitE2)
              apply auto
             apply(rule out_0assm_assn.intros(2))
             by auto
           apply(elim combine_blocks_waitE3)
              apply auto
           apply(rule out_0assm_assn.intros(2))
           by auto
         done
       done
       done
     done

lemma combine_in_0assm_out_orig:
  assumes "dh \<notin> chs"
   and "ch \<in> chs"
 shows "combine_assn chs (in_0assm_assn dh v P) (out_orig_assn ch v' s Q)
        \<Longrightarrow>\<^sub>t (in_0assm_assn dh v  
            (combine_assn chs P (out_orig_assn ch v' s Q)))"
  apply(auto simp add:entails_tassn_def combine_assn_def)
  subgoal for tr tr1 tr2
    apply(cases rule: in_0assm_assn.cases[of dh v P tr1])
      apply auto
    subgoal for tr1'
      apply(cases rule: out_orig_assn.cases[of ch v' s Q tr2])
          apply auto
        subgoal for tr2'
          using assms
          apply(elim combine_blocks_unpairE1)
            apply auto
          apply(rule in_0assm_assn.intros(1))
          by auto
        subgoal for tr2' d
          using assms
          apply(elim combine_blocks_unpairE3)
           apply auto
          apply(rule in_0assm_assn.intros(1))
          by auto
        done
      subgoal for d1 a b p1 tr1'
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
            subgoal
           apply(cases "d1>d2")
           subgoal 
             apply(elim combine_blocks_waitE4)
                apply auto
             apply(rule in_0assm_assn.intros(2))
             by auto
           apply(cases "d2=d1")
           subgoal 
             apply simp
             apply(elim combine_blocks_waitE2)
              apply auto
             apply(rule in_0assm_assn.intros(2))
             by auto
           apply(elim combine_blocks_waitE3)
              apply auto
           apply(rule in_0assm_assn.intros(2))
           by auto
         done
       done
       done
   done


lemma combine_out_0assm_rdy_out_orig:
  assumes "dh \<notin> chs"
   and "ch \<in> chs"
 shows "combine_assn chs (out_0assm_rdy_assn dh v rdy P) (out_orig_assn ch v' s Q)
        \<Longrightarrow>\<^sub>t (out_0assm_rdy_assn dh v (merge_rdy rdy ({ch}, {}))
            (combine_assn chs P (out_orig_assn ch v' s Q)))"
  apply(auto simp add:entails_tassn_def combine_assn_def)
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_rdy_assn.cases[of dh v rdy P tr1])
      apply auto
    subgoal for tr1'
      apply(cases rule: out_orig_assn.cases[of ch v' s Q tr2])
          apply auto
        subgoal for tr2'
          using assms
          apply(elim combine_blocks_unpairE1)
            apply auto
          apply(rule out_0assm_rdy_assn.intros(1))
          by auto
        subgoal for tr2' d
          using assms
          apply(elim combine_blocks_unpairE3)
           apply auto
          apply(rule out_0assm_rdy_assn.intros(1))
          by auto
        done
      subgoal for d1 p1 tr1'
        apply(cases rule: out_orig_assn.cases[of ch v' s Q tr2])
            apply auto
          subgoal for tr2'
            using assms
            apply(auto elim:sync_elims)
            done
          subgoal for tr2' d2
            apply(cases "\<not>compat_rdy rdy ({ch}, {})")
            subgoal
              by(auto elim:sync_elims)
            subgoal
           apply(cases "d1>d2")
           subgoal 
             apply(elim combine_blocks_waitE4)
                apply auto
             apply(rule out_0assm_rdy_assn.intros(2))
             by auto
           apply(cases "d2=d1")
           subgoal 
             apply simp
             apply(elim combine_blocks_waitE2)
              apply auto
             apply(rule out_0assm_rdy_assn.intros(2))
             by auto
           apply(elim combine_blocks_waitE3)
              apply auto
           apply(rule out_0assm_rdy_assn.intros(2))
           by auto
         done
       done
       done
     done

lemma combine_in_0assm_rdy_out_orig:
  assumes "dh \<notin> chs"
   and "ch \<in> chs"
 shows "combine_assn chs (in_0assm_rdy_assn dh v rdy P) (out_orig_assn ch v' s Q)
        \<Longrightarrow>\<^sub>t (in_0assm_rdy_assn dh v (merge_rdy rdy ({ch}, {}))
            (combine_assn chs P (out_orig_assn ch v' s Q)))"
  apply(auto simp add:entails_tassn_def combine_assn_def)
  subgoal for tr tr1 tr2
    apply(cases rule: in_0assm_rdy_assn.cases[of dh v rdy P tr1])
      apply auto
    subgoal for tr1'
      apply(cases rule: out_orig_assn.cases[of ch v' s Q tr2])
          apply auto
        subgoal for tr2'
          using assms
          apply(elim combine_blocks_unpairE1)
            apply auto
          apply(rule in_0assm_rdy_assn.intros(1))
          by auto
        subgoal for tr2' d
          using assms
          apply(elim combine_blocks_unpairE3)
           apply auto
          apply(rule in_0assm_rdy_assn.intros(1))
          by auto
        done
      subgoal for d1 p1 tr1'
        apply(cases rule: out_orig_assn.cases[of ch v' s Q tr2])
            apply auto
          subgoal for tr2'
            using assms
            apply(auto elim:sync_elims)
            done
          subgoal for tr2' d2
            apply(cases "\<not>compat_rdy rdy ({ch}, {})")
            subgoal
              by(auto elim:sync_elims)
            subgoal
           apply(cases "d1>d2")
           subgoal 
             apply(elim combine_blocks_waitE4)
                apply auto
             apply(rule in_0assm_rdy_assn.intros(2))
              apply auto
             apply(cases rdy)
             by auto
           apply(cases "d2=d1")
           subgoal 
             apply simp
             apply(elim combine_blocks_waitE2)
              apply auto
             apply(rule in_0assm_rdy_assn.intros(2))
             apply auto
             apply(cases rdy)
             by auto
           apply(elim combine_blocks_waitE3)
              apply auto
           apply(rule in_0assm_rdy_assn.intros(2))
           apply auto
           apply(cases rdy)
           apply auto
         done
       done
       done
     done
   done


lemma combine_wait_tguar'_vassm'_wait_orig2:
  assumes "\<And> s . s\<in>S \<Longrightarrow> s<d"
  and "compat_rdy rdy1 rdy2"
  and "dh \<notin> chs"
  and "ch \<in> chs"
  shows "combine_assn chs (waitin_tguar'_vassm'_assn S p1 rdy1 dh V P)
                      (wait_orig_assn d p2 rdy2 (out_orig_assn ch v' s Q)) \<Longrightarrow>\<^sub>t
         waitin_tguar'_vassm'_assn S (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) dh V
                      (\<lambda> v t. combine_assn chs (P v t) (wait_orig_assn (d-t) (\<lambda> t'. p2(t'+t)) rdy2 (out_orig_assn ch v' s Q)))"
  unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p1 rdy1 dh V P tr1])
        apply auto
    subgoal for v tr1'
      apply(cases rule:wait_orig_assn.cases[of d p2 rdy2 "(out_orig_assn ch v' s Q)" tr2])
        apply auto
      subgoal
        apply(cases rule:out_orig_assn.cases[of ch v' s Q tr2])
          apply auto
        subgoal for tr2'
          apply(elim combine_blocks_unpairE1)
          using assms
          by auto
        subgoal for d tr2'
          apply(elim combine_blocks_unpairE3)
          using assms
          by auto
        done
      subgoal for tr2'
        apply(elim combine_blocks_unpairE3)
          using assms
           apply auto
          subgoal for tr'
            apply(rule waitin_tguar'_vassm'_assn.intros(1))
            by auto
          done
        done
      subgoal for d1 v tr1'
        apply(cases rule:wait_orig_assn.cases[of d p2 rdy2 "(out_orig_assn ch v' s Q)" tr2])
        using assms(1)[of d1]
          apply auto
        subgoal for tr2'
          apply(elim combine_blocks_waitE3)
          using assms
             apply auto
          subgoal for tr'
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr''
              apply(rule waitin_tguar'_vassm'_assn.intros(2))
                 apply auto
              apply(rule exI[where x="tr1'"])
              apply auto
              apply(rule exI[where x="(WaitBlk (d - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2')"])
              apply auto
              apply(rule wait_orig_assn.intros(2))
              by auto
            done
          done
        done
      subgoal for w tr1'
        apply(cases rule:wait_orig_assn.cases[of d p2 rdy2 "(out_orig_assn ch v' s Q)" tr2])
        apply auto
      subgoal
        apply(cases rule:out_orig_assn.cases[of ch v' s Q tr2])
          apply auto
        subgoal for tr2'
          apply(elim combine_blocks_unpairE1)
          using assms
          by auto
        subgoal for d tr2'
          apply(elim combine_blocks_unpairE3)
          using assms
          by auto
        done
      subgoal for tr2'
        apply(elim combine_blocks_unpairE3)
          using assms
           apply auto
          subgoal for tr'
            apply(rule waitin_tguar'_vassm'_assn.intros(3))
            by auto
          done
        done
      subgoal for d1 w tr1'
        apply(cases rule:wait_orig_assn.cases[of d p2 rdy2 "(out_orig_assn ch v' s Q)" tr2])
        using assms(1)[of d1]
          apply auto
        subgoal for tr2'
          apply(elim combine_blocks_waitE3)
          using assms
             apply auto
          subgoal for tr'
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr''
              apply(rule waitin_tguar'_vassm'_assn.intros(4))
              by auto
            done
          done
        done
      done
    done


lemma combine_task_dis':
  "task_assn' t k task_es task_s tr1 \<Longrightarrow>
   dispatch_assn' t' kk dis_s tr2 \<Longrightarrow>
   t \<in> tid_set \<Longrightarrow>
   t = t' \<Longrightarrow>
   task_s (CHR ''t'') = dis_s (CHR ''t'') \<Longrightarrow>
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
         apply(rule pre(6))
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
         apply(rule pre (7))
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
           apply(rule pre(7))
          apply(rule combine_in_vassm_emp1)
          by auto
         apply simp
        subgoal apply(erule disjE)
          subgoal premises pre
            thm pre
            apply(rule disjI1)
            apply(rule combine_blocks_assn)
               apply(rule pre(9))
              apply(rule pre(2))
             apply(rule pre(6))
            apply(rule entails_tassn_trans)
             apply(rule combine_out_0assm_emp2)
            subgoal using ch_dist pre(3) by auto
            apply(rule out_0assm_assn_tran)
            subgoal 
              apply(rule entails_tassn_trans)
             apply(rule combine_waitin_tguar'_vassm'_emp2)
              subgoal using ch_dist pre(3) by auto
              apply(rule waitin_tguar'_vassm'_assn_tran)
              unfolding entails_tassn_def combine_assn_def
              apply clarify
              subgoal for v d tr tr1 tr2
                using pre(1)[of "(Task RUNNING (Suc 0) tp)"
                                "(task_s(CHR ''t'' := task_s CHR ''t'' + d, CHR ''c'' := up_ent_c ent (task_s CHR ''c'')))"
                                tr1 0 
                                "(dis_s(CHR ''t'' := dis_s CHR ''t'' + d))" tr2 tr]
                apply(subgoal_tac"dispatch_assn' t' 0 (dis_s(CHR ''t'' := dis_s CHR ''t'' + d)) tr2")
                subgoal using pre(5) 
                  by fastforce
                by auto
              done
            done
          apply(erule disjE)
          subgoal premises pre
            thm pre
            apply(rule disjI2)
            apply(rule disjI1)
            apply(rule combine_blocks_assn)
              apply(rule pre(9))
              apply(rule pre(2))
             apply(rule pre(6))
            apply(rule entails_tassn_trans)
             apply(rule combine_out_0assm_emp2)
            subgoal using ch_dist pre(3) by auto
            apply(rule out_0assm_assn_tran)
            subgoal 
              apply(rule entails_tassn_trans)
               apply(rule combine_wait_orig_emp2)
              apply(rule wait_orig_assn_tran)
              apply(rule entails_tassn_trans)
               apply(rule combine_out_0assm_rdy_emp2)
              subgoal using ch_dist pre(3) by auto
              apply(rule out_0assm_rdy_assn_tran)
              subgoal 
                unfolding entails_tassn_def combine_assn_def
                apply clarify
                subgoal for tr tr1 tr2
                  using pre(1)[of "(Task WAIT ent tp)" "(task_s(CHR ''t'' := 9 / 200))" tr1 0
                              "(dis_s(CHR ''t'' := dis_s CHR ''t'' + 9 / 200 - task_s CHR ''t''))"
                               tr2 tr]
                  apply(subgoal_tac "dispatch_assn' t' 0 (dis_s(CHR ''t'' := dis_s CHR ''t'' + 9 / 200 - task_s CHR ''t''))tr2")
                   subgoal using pre(5) by fastforce 
                  by auto
                done
              done
            done
          subgoal premises pre
            thm pre
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule combine_blocks_assn)
              apply(rule pre(9))
              apply(rule pre(2))
             apply(rule pre(6))
            apply(rule entails_tassn_trans)
             apply(rule combine_out_0assm_emp2)
            subgoal using ch_dist pre(3) by auto
            apply(rule out_0assm_assn_tran)
            subgoal 
              apply(rule entails_tassn_trans)
               apply(rule combine_wait_orig_emp2)
              apply(rule wait_orig_assn_tran)
              apply(rule entails_tassn_trans)
               apply(rule combine_in_0assm_rdy_emp2)
              subgoal using ch_dist pre(3) by auto
              apply(rule in_0assm_rdy_assn_tran)
              subgoal 
                unfolding entails_tassn_def combine_assn_def
                apply clarify
                subgoal for tr tr1 tr2
                  using pre(1)[of "(Task WAIT ent tp)" "(task_s(CHR ''t'' := 9 / 200))" tr1 0
                              "(dis_s(CHR ''t'' := dis_s CHR ''t'' + 9 / 200 - task_s CHR ''t''))"
                               tr2 tr]
                  apply(subgoal_tac "dispatch_assn' t' 0 (dis_s(CHR ''t'' := dis_s CHR ''t'' + 9 / 200 - task_s CHR ''t''))tr2")
                   subgoal using pre(5) by fastforce 
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
                   apply(rule pre(10))
                  apply(rule pre(2))
                apply(rule pre(6))
                apply(rule entails_tassn_trans)
                 apply(rule combine_waitin_tguar'_vassm'_emp2)
                subgoal using ch_dist pre(3) by auto
                apply(rule waitin_tguar'_vassm'_assn_tran)
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
                     subgoal using pre(5) by fastforce
                    by auto
                  done
                done
              done
            subgoal apply(rule disjI2)
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                   apply(rule pre(10))
                  apply(rule pre(2))
                 apply(rule pre(6))
                apply(rule entails_tassn_trans)
                 apply(rule combine_wait_orig_emp2)
                apply(rule wait_orig_assn_tran)
                subgoal 
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
                     subgoal using pre(5) by fastforce
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
           apply(rule pre(8))
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
                 apply(rule pre(10))
                apply(rule pre(3))
               apply(rule pre(7))
              apply(rule entails_tassn_trans)
               apply(rule combine_out_0assm_wait_orig_out_orig)
                subgoal using ch_dist pre by auto
                subgoal by auto
                apply(rule out_0assm_assn_tran)
                apply(rule entails_tassn_trans)
                 apply(rule combine_wait_tguar'_vassm'_wait_orig2)
                subgoal by auto
                subgoal by auto
                subgoal using pre ch_dist by auto
                subgoal by auto
                apply auto
                apply(rule waitin_tguar'_vassm'_assn_tran)
                apply auto
                unfolding combine_assn_def entails_tassn_def
                apply auto
                subgoal for d tr tr1 tr2
                  thm pre(2)
                  apply(subgoal_tac "dispatch_assn' t' (Suc kk) (\<lambda>a. if a = CHR ''t'' then dis_s CHR ''t'' + d else dis_s a) tr2")
                   prefer 2
                  subgoal apply auto
                    apply(subgoal_tac "9 / 200 - dis_s CHR ''t'' - d = 9 / 200 - (dis_s CHR ''t'' + d)")
                     apply auto
                    apply(subgoal_tac "(\<lambda>t'. EState (estate.None,
             \<lambda>a. if a = CHR ''t'' then dis_s CHR ''t'' + (t' + d) else dis_s a))
                                     = (\<lambda>t. EState  (estate.None, 
            (\<lambda>a. if a = CHR ''t'' then dis_s CHR ''t'' + d else dis_s a)
            (CHR ''t'' := dis_s CHR ''t'' + d + t)))")
                    apply(subgoal_tac "(\<lambda>a. if a = CHR ''t'' then dis_s CHR ''t'' + d else dis_s a)
          (CHR ''t'' := 0) = (\<lambda>a. if a = CHR ''t'' then 0 else dis_s a)")
                      apply auto
                    apply(rule ext)
                    by auto
                  subgoal premises pp
                    thm pp
                    apply(rule pre(2))
                       apply(rule pp(3))
                      apply(rule pp(6))
                     apply auto
                    apply(rule pp(5))
                    done
                  done
                done
              done
            apply(erule disjE)
            subgoal apply(rule disjI2) apply(rule disjI1)
            subgoal premises pre
              thm pre
              apply(rule combine_blocks_assn)
                 apply(rule pre(10))
                apply(rule pre(3))
               apply(rule pre(7))
              apply(rule entails_tassn_trans)
               apply(rule combine_out_0assm_wait_orig_out_orig)
                subgoal using ch_dist pre by auto
                subgoal by auto
                apply(rule out_0assm_assn_tran)
                apply(rule entails_tassn_trans)
                 apply(rule combine_wait_orig_wait_orig2)
                subgoal by auto
                apply auto
                apply(rule wait_orig_assn_tran)
                apply(rule entails_tassn_trans)
                 apply(rule combine_out_0assm_rdy_out_orig)
                subgoal using pre ch_dist by auto
                subgoal by auto
                apply (auto del:fun_upd_apply)
                apply(rule out_0assm_rdy_assn_tran)
                unfolding combine_assn_def entails_tassn_def
                apply auto
                subgoal for tr tr1 tr2
                  thm pre(2)
                  apply(subgoal_tac "dispatch_assn' t' (Suc kk) (\<lambda>a. if a = CHR ''t'' then 9 / 200 else dis_s a) tr2")
                   prefer 2 
                  subgoal apply auto
                    apply(subgoal_tac " (\<lambda>a. if a = CHR ''t'' then 9 / 200 else dis_s a)(CHR ''t'' := 0) = (\<lambda>a. if a = CHR ''t'' then 0 else dis_s a)")
                     apply auto
                    apply(rule wait_orig_assn.intros(1))
                    by auto
                  subgoal premises pp
                    thm pp
                    apply(rule pre(2))
                       apply(rule pp(1))
                      apply(rule pp(4))
                     apply auto
                    apply(rule pp(3))
                    done
                  done
                done
              done
            subgoal apply(rule disjI2) apply(rule disjI2)
            subgoal premises pre
              thm pre
              apply(rule combine_blocks_assn)
                 apply(rule pre(10))
                apply(rule pre(3))
               apply(rule pre(7))
              apply(rule entails_tassn_trans)
               apply(rule combine_out_0assm_wait_orig_out_orig)
                subgoal using ch_dist pre by auto
                subgoal by auto
                apply(rule out_0assm_assn_tran)
                apply(rule entails_tassn_trans)
                 apply(rule combine_wait_orig_wait_orig2)
                subgoal by auto
                apply auto
                apply(rule wait_orig_assn_tran)
                apply(rule entails_tassn_trans)
                 apply(rule combine_in_0assm_rdy_out_orig)
                subgoal using pre ch_dist by auto
                subgoal by auto
                apply(auto del:fun_upd_apply)
                apply(rule in_0assm_rdy_assn_tran)
                unfolding combine_assn_def entails_tassn_def
                apply auto
                subgoal for tr tr1 tr2
                  thm pre(2)
                  apply(subgoal_tac "dispatch_assn' t' (Suc kk) (\<lambda>a. if a = CHR ''t'' then 9 / 200 else dis_s a) tr2")
                   prefer 2 
                  subgoal apply auto
                    apply(subgoal_tac " (\<lambda>a. if a = CHR ''t'' then 9 / 200 else dis_s a)(CHR ''t'' := 0) = (\<lambda>a. if a = CHR ''t'' then 0 else dis_s a)")
                     apply auto
                    apply(rule wait_orig_assn.intros(1))
                    by auto
                  subgoal premises pp
                    thm pp
                    apply(rule pre(2))
                       apply(rule pp(1))
                      apply(rule pp(4))
                     apply auto
                    apply(rule pp(3))
                    done
                  done
                done
              done
            done
          subgoal apply simp
            apply(cases "ent \<noteq> Suc 0")
            subgoal by auto
            apply simp
            apply(erule disjE)
          subgoal apply(rule disjI1)
            subgoal premises pre
              thm pre
              apply(rule combine_blocks_assn)
                 apply(rule pre(11))
                apply(rule pre(3))
               apply(rule pre(7))
              apply(rule entails_tassn_trans)
               apply(rule combine_wait_tguar'_vassm'_wait_orig2)
              subgoal by auto
              subgoal by auto
              subgoal using pre ch_dist by auto
              subgoal  by auto
              apply auto
              apply(rule waitin_tguar'_vassm'_assn_tran)
              apply auto
              unfolding combine_assn_def entails_tassn_def
              apply auto
              subgoal for d tr tr1 tr2
                apply(subgoal_tac "dispatch_assn' t' (Suc kk) (\<lambda>a. if a = CHR ''t'' then dis_s CHR ''t'' + d else dis_s a) tr2")
                 prefer 2
                subgoal apply auto
                  apply(subgoal_tac "(9 / 200 - dis_s CHR ''t'' - d) =( 9 / 200 - (dis_s CHR ''t'' + d))")
                   apply auto
                  apply(subgoal_tac "(\<lambda>t'. EState (estate.None,
             \<lambda>a. if a = CHR ''t'' then dis_s CHR ''t'' + (t' + d) else dis_s a)) = 
              (\<lambda>t. EState (estate.None, (\<lambda>a. if a = CHR ''t'' then dis_s CHR ''t'' + d else dis_s a)
            (CHR ''t'' := dis_s CHR ''t'' + d + t)))")
                   apply auto
                  apply(subgoal_tac "(\<lambda>a. if a = CHR ''t'' then dis_s CHR ''t'' + d else dis_s a)
          (CHR ''t'' := 0) = (\<lambda>a. if a = CHR ''t'' then 0 else dis_s a)")
                    apply auto
                  apply(rule ext)
                  by auto
                subgoal premises pp
                  thm pp
                  apply(rule pre(2))
                     apply(rule pp(4))
                    apply(rule pp(7))
                   apply auto
                  apply(rule pp(6))
                  done
                done
              done
            done
          subgoal apply(rule disjI2)
            subgoal premises pre
              thm pre
              apply(rule combine_blocks_assn)
              apply(rule pre(11))
                apply(rule pre(3))
               apply(rule pre(7))
              apply(rule entails_tassn_trans)
               apply(rule combine_wait_orig_wait_orig5)
              subgoal by auto
              subgoal by auto
              apply auto
              apply(rule wait_orig_assn_tran)
              apply(rule entails_tassn_trans)
               apply(rule combine_out_0assm_wait_orig_out_orig)
              subgoal using pre ch_dist by auto
              subgoal by auto
              apply(rule out_0assm_assn_tran)
              unfolding combine_assn_def entails_tassn_def
              apply auto
              subgoal for tr tr1 tr2
                apply(subgoal_tac "dispatch_assn' t' (Suc kk) (\<lambda>a. if a = CHR ''t''
          then dis_s CHR ''t'' +
               min (9 / 200 - dis_s CHR ''t'') (1 / 100 - task_s CHR ''c'')
          else dis_s a) tr2")
                 prefer 2
                 subgoal
                apply(subgoal_tac "(9 / 200 - dis_s CHR ''t'' -
      min (9 / 200 - dis_s CHR ''t'') (1 / 100 - task_s CHR ''c'')) = (9 / 200 -
      (dis_s CHR ''t'' + min (9 / 200 - dis_s CHR ''t'') (1 / 100 - task_s CHR ''c'')))")
                    apply auto
                   apply(subgoal_tac "(\<lambda>t. EState
           (estate.None,
            \<lambda>a. if a = CHR ''t''
                then dis_s CHR ''t'' +
                     (t + min (9 / 200 - dis_s CHR ''t'') (1 / 100 - task_s CHR ''c''))
                else dis_s a)) = (\<lambda>t. EState
           (estate.None,
            (\<lambda>a. if a = CHR ''t''
                 then dis_s CHR ''t'' +
                      min (9 / 200 - dis_s CHR ''t'') (1 / 100 - task_s CHR ''c'')
                 else dis_s a)
            (CHR ''t'' :=
               dis_s CHR ''t'' +
               min (9 / 200 - dis_s CHR ''t'') (1 / 100 - task_s CHR ''c'') +
               t)))")
                    apply auto
                    apply(subgoal_tac "(\<lambda>a. if a = CHR ''t'' then 0 else dis_s a) =
            (\<lambda>a. if a = CHR ''t''
               then dis_s CHR ''t'' +
                    min (9 / 200 - dis_s CHR ''t'') (1 / 100 - task_s CHR ''c'')
               else dis_s a)
          (CHR ''t'' := 0)")
                     apply auto
                   apply(rule ext)
                   by auto
                 subgoal premises pp
                   thm pp
                   apply(rule pre(2))
                      apply(rule pp(1))
                     apply(rule pp(4))
                    apply auto
                   apply(rule pp(3))
                   done
                 done
               done
             done
           done
         done
       done
   qed
qed


inductive waitin_assms'ch_assn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "v \<in> V \<Longrightarrow> 0 \<in> S \<Longrightarrow> (P v 0) tr \<Longrightarrow> (waitin_assms'ch_assn S p rdy ch V P) (InBlock ch v # tr)"
| "v \<in> V \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (P v d) tr \<Longrightarrow> (waitin_assms'ch_assn S p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch v # tr)"
| "0 \<notin> S \<or> w \<notin> V \<or> dh \<noteq> ch\<Longrightarrow> (waitin_assms'ch_assn S p rdy ch V P) (InBlock dh w # tr)"
| "d \<notin> S \<or> w \<notin> V \<or> dh \<noteq> ch\<Longrightarrow> d > 0 \<Longrightarrow> (waitin_assms'ch_assn S p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch w # tr)"


lemma waitin_assms'ch_assn_tran:
assumes "\<And> v d. v \<in> V \<and> d \<in> S \<Longrightarrow> P v d \<Longrightarrow>\<^sub>t Q v d"
shows "waitin_assms'ch_assn S p rdy ch V P \<Longrightarrow>\<^sub>t waitin_assms'ch_assn S p rdy ch V Q"
unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: waitin_assms'ch_assn.cases[of S p rdy ch V P tr])
      apply auto
    subgoal
      apply(rule waitin_assms'ch_assn.intros(1))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal
      apply(rule waitin_assms'ch_assn.intros(2))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal
      apply(rule waitin_assms'ch_assn.intros(3))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal
      apply(rule waitin_assms'ch_assn.intros(3))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal
      apply(rule waitin_assms'ch_assn.intros(3))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal
      apply(rule waitin_assms'ch_assn.intros(4))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal
      apply(rule waitin_assms'ch_assn.intros(4))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal
      apply(rule waitin_assms'ch_assn.intros(4))
      using assms 
      by(auto simp add:entails_tassn_def)
    done
  done



lemma combine_emp_waitin_assms'ch1:
"ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (waitin_assms'ch_assn S p rdy ch V P) \<Longrightarrow>\<^sub>t (waitin_assms'ch_assn S q rdy ch V (\<lambda> v t . combine_assn chs emp\<^sub>t (P v t)))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:waitin_assms'ch_assn.cases[of S p rdy ch V P tr1])
        apply (auto elim!: sync_elims)
    subgoal for w dh tr1' tr'
      apply(rule waitin_assms'ch_assn.intros(3))
      by auto
    subgoal for w dh tr1' tr'
      apply(rule waitin_assms'ch_assn.intros(3))
      by auto
    subgoal for w dh tr1' tr'
      apply(rule waitin_assms'ch_assn.intros(3))
  by auto
  done
  done

lemma combine_emp_waitin_assms'ch2:
"ch \<notin> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (waitin_assms'ch_assn S p rdy ch V P) \<Longrightarrow>\<^sub>t (waitin_assms'ch_assn S q rdy ch V (\<lambda> v t . combine_assn chs emp\<^sub>t (P v t)))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:waitin_assms'ch_assn.cases[of S p rdy ch V P tr1])
        apply (auto elim!: sync_elims)
    subgoal for v tr1' tr'
      apply(rule waitin_assms'ch_assn.intros(1))
      by auto
    subgoal for w dh tr1' tr'
      apply(rule waitin_assms'ch_assn.intros(3))
      by auto
    subgoal for w dh tr1' tr'
      apply(rule waitin_assms'ch_assn.intros(3))
      by auto
    subgoal for w dh tr1' tr'
      apply(rule waitin_assms'ch_assn.intros(3))
  by auto
  done
  done

lemma combine_emp_waitin_assms'ch3:
"combine_assn chs emp\<^sub>t (waitin_assms'ch_assn S p rdy ch V P) \<Longrightarrow>\<^sub>t (waitin_assms'ch_assn S q rdy ch V (\<lambda> v t . combine_assn chs emp\<^sub>t (P v t)))"
  apply(cases "ch \<in> chs")
  apply(rule combine_emp_waitin_assms'ch1) apply auto
  apply(rule combine_emp_waitin_assms'ch2) by auto


fun sched_assn' :: "nat \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "sched_assn' n None s tr \<longleftrightarrow> False"
| "sched_assn' n (Task st ent tp) s tr \<longleftrightarrow> False"
| "sched_assn' 0 (Sch p rn rp) s tr \<longleftrightarrow> (emp\<^sub>t tr)"
| "sched_assn' (Suc k) (Sch p rn rp) s tr \<longleftrightarrow> 
   waitin_assms'_assn UNIV (\<lambda> t. EState(Sch p rn rp, s)) ({},{req_ch 1,req_ch 2,free_ch 1,free_ch 2,exit_ch 1,exit_ch 2})
   (req_ch 1) {2} (\<lambda> v d. if (v\<le>rp) then sched_assn' k (sched_push 1 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))
                                     else if rn \<noteq> -1 then out_0assm_assn (preempt_ch rn) 0 (out_0assm_assn (run_ch 1) 0 
                                         (sched_assn' k (sched_assign 1 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))))
                                            else out_0assm_assn (run_ch 1) 0 
                                         (sched_assn' k (sched_assign 1 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v)))) tr
 \<or> waitin_assms'_assn UNIV (\<lambda> t. EState(Sch p rn rp, s)) ({},{req_ch 1,req_ch 2,free_ch 1,free_ch 2,exit_ch 1,exit_ch 2})
   (req_ch 2) {1} (\<lambda> v d. if (v\<le>rp) then sched_assn' k (sched_push 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))
                                     else if rn \<noteq> -1 then out_0assm_assn (preempt_ch rn) 0 (out_0assm_assn (run_ch 2) 0 
                                         (sched_assn' k (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))))
                                            else out_0assm_assn (run_ch 2) 0 
                                         (sched_assn' k (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v)))) tr
 \<or> waitin_assms'_assn UNIV (\<lambda> t. EState(Sch p rn rp, s)) ({},{req_ch 1,req_ch 2,free_ch 1,free_ch 2,exit_ch 1,exit_ch 2})
   (free_ch 1) {0} (\<lambda> v d. if length p > 0 then out_0assm_assn (run_ch (run_now (sched_get_max (Sch p rn rp) s))) 0 
                                          (sched_assn' k (sched_get_max (Sch p rn rp) s) s)
                                            else 
                                          (sched_assn' k (sched_clear (Sch p rn rp) s) s)) tr
 \<or> waitin_assms'_assn UNIV (\<lambda> t. EState(Sch p rn rp, s)) ({},{req_ch 1,req_ch 2,free_ch 1,free_ch 2,exit_ch 1,exit_ch 2})
   (free_ch 2) {0} (\<lambda> v d. if length p > 0 then out_0assm_assn (run_ch (run_now (sched_get_max (Sch p rn rp) s))) 0 
                                          (sched_assn' k (sched_get_max (Sch p rn rp) s) s)
                                            else 
                                          (sched_assn' k (sched_clear (Sch p rn rp) s) s)) tr
 \<or> waitin_assms'_assn UNIV (\<lambda> t. EState(Sch p rn rp, s)) ({},{req_ch 1,req_ch 2,free_ch 1,free_ch 2,exit_ch 1,exit_ch 2})
   (exit_ch 1) {0} (\<lambda> v d. sched_assn' k (sched_del_proc 1 (Sch p rn rp) s) s) tr
 \<or> waitin_assms'_assn UNIV (\<lambda> t. EState(Sch p rn rp, s)) ({},{req_ch 1,req_ch 2,free_ch 1,free_ch 2,exit_ch 1,exit_ch 2})
   (exit_ch 2) {0} (\<lambda> v d. sched_assn' k (sched_del_proc 2 (Sch p rn rp) s) s) tr"

definition properp :: "tid \<Rightarrow> real \<Rightarrow> bool" where
"properp rn rp = ((rn = 1 \<longleftrightarrow> rp = 2) \<and> (rn = -1 \<longleftrightarrow> rp = -1) \<and> rp \<in> {-1,1,2} \<and> rn \<in> {-1,1,2})"

fun properl :: "(real \<times> tid) list \<Rightarrow> bool" where
  "properl [] = True"
| "properl ((rp,rn) # v) = (properl v \<and> properp rn rp \<and> rn > 0 \<and> rn \<noteq> 1)"

lemma properl_p1:
"properl (p @ [(a, b)]) = (properl p \<and> properp b a \<and> b > 0 \<and> b \<noteq> 1)"
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

lemma properl_p2:
"properl p \<Longrightarrow> properp rn rp \<Longrightarrow> properp (snd(get_max_default (rp,rn) p)) (fst(get_max_default (rp,rn) p))"
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


lemma properl_p3:
"properl p \<Longrightarrow> properp (snd (get_max p)) (fst (get_max p)) "
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
      apply(rule properl_p2)
      by auto
    done
qed


lemma properl_p4:
"properl p \<Longrightarrow> properl (del_proc p t)"
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

lemma proper_getmax1':
"fst (get_max_default (a,b) p) < d \<Longrightarrow> a' < d \<Longrightarrow> fst (get_max_default (a,b) (p@[(a',b')])) < d"
proof(induction p arbitrary: a b)
  case Nil
  then show ?case 
    by auto
next
  case (Cons g p)
  then show ?case 
    apply(cases g)
    subgoal for ga gb
      by auto
    done
qed

lemma proper_getmax1:
"fst (get_max p) < d \<Longrightarrow> a' < d \<Longrightarrow> fst (get_max(p@[(a',b')])) < d"
proof(induction p)
  case Nil
  then show ?case by auto
next
  case (Cons g p)
  then show ?case 
    apply (cases g)
    subgoal for ga gb
      apply auto
      using proper_getmax1'
      by auto
    done
qed


lemma proper_getmax2:
"properl p \<Longrightarrow> snd (get_max p) \<noteq> 1 \<and> (gb \<noteq> 1 \<longrightarrow> snd (get_max_default (ga, gb) p) \<noteq> 1)"
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

lemma properl_p5':
  "properl ((a,b)#p) \<Longrightarrow> snd(get_max_default (a,b) p) > 0"
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

lemma properl_p5:
"length p > 0 \<Longrightarrow> properl p \<Longrightarrow> properp (snd (get_max p)) (fst (get_max p)) \<and> (snd (get_max p)) > 0 \<and> (snd (get_max p)) \<noteq> 1"
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
      apply(rule properl_p2)
         apply auto
        done
       prefer 2
      subgoal
        using proper_getmax2 apply auto
        done
      using properl_p5'[of 1 2 p] 
      apply auto
      unfolding properp_def
      by auto
    done
qed



definition proper :: "estate \<Rightarrow> bool " where
"proper schs = ((properp (run_now schs) (run_prior schs)) \<and> properl (pool schs))"


inductive io_out0_out0 :: "cname \<Rightarrow> real \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "io_orig_assn ch1 v1 (out_0assm_assn ch2 v2 (out_0assm_assn ch3 v3 P)) tr \<Longrightarrow> io_out0_out0 ch1 v1 ch2 v2 ch3 v3 P tr"
| "out_0orig_assn ch2 v2 (io_orig_assn ch1 v1 (out_0assm_assn ch3 v3 P)) tr \<Longrightarrow> io_out0_out0 ch1 v1 ch2 v2 ch3 v3 P tr"



fun tdsch1' :: "nat \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate tassn" where
  "tdsch1' 0 0 dis_s task_es task_s schs s tr \<longleftrightarrow> (emp\<^sub>t tr)"
| "tdsch1' 0 (Suc kk) dis_s task_es task_s (Sch p rn rp) s tr \<longleftrightarrow> 
   waitin_assms'_assn UNIV (\<lambda> t. EState(Sch p rn rp, s)) ({},{req_ch 1,req_ch 2,free_ch 1,free_ch 2,exit_ch 1,exit_ch 2})
   (req_ch 2) {1} (\<lambda> v d. if (v\<le>rp) then tdsch1' 0 kk dis_s task_es task_s (sched_push 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))
                                     else if rn \<noteq> -1 then out_0assm_assn (preempt_ch rn) 0 (out_0assm_assn (run_ch 2) 0 
                                         (tdsch1' 0 kk dis_s task_es task_s (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))))
                                            else out_0assm_assn (run_ch 2) 0 
                                         (tdsch1' 0 kk dis_s task_es task_s (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v)))) tr
 \<or> waitin_assms'_assn UNIV (\<lambda> t. EState(Sch p rn rp, s)) ({},{req_ch 1,req_ch 2,free_ch 1,free_ch 2,exit_ch 1,exit_ch 2})
   (free_ch 2) {0} (\<lambda> v d. if length p > 0 then out_0assm_assn (run_ch (run_now (sched_get_max (Sch p rn rp) s))) 0 
                                          (tdsch1' 0 kk dis_s task_es task_s (sched_get_max (Sch p rn rp) s) s)
                                            else 
                                          (tdsch1' 0 kk dis_s task_es task_s (sched_clear (Sch p rn rp) s) s)) tr
 \<or> waitin_assms'_assn UNIV (\<lambda> t. EState(Sch p rn rp, s)) ({},{req_ch 1,req_ch 2,free_ch 1,free_ch 2,exit_ch 1,exit_ch 2})
   (exit_ch 2) {0} (\<lambda> v d. tdsch1' 0 kk dis_s task_es task_s (sched_del_proc 2 (Sch p rn rp) s) s) tr"
| "tdsch1' (Suc k) 0 dis_s (Task WAIT ent tp) task_s schs s tr \<longleftrightarrow> 
   io_orig_assn (dispatch_ch 1) 0 (tdsch1' k 0 (dis_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0)) schs s) tr"
| "tdsch1' (Suc k) 0 dis_s (Task READY ent tp) task_s schs s tr \<longleftrightarrow> False"
| "tdsch1' (Suc k) 0 dis_s (Task RUNNING ent tp) task_s schs s tr \<longleftrightarrow> False"
| "tdsch1' (Suc k) (Suc kk) dis_s (Task WAIT ent tp) task_s (Sch p rn rp) s tr \<longleftrightarrow> 
 wait_orig_assn (0.045 - dis_s CHR ''t'')
     (\<lambda>t. ParState
           (ParState (EState (Task WAIT ent tp, task_s))
             (EState
               (estate.None, dis_s(CHR ''t'' := dis_s CHR ''t'' + t))))
           (EState (Sch p rn rp, s)))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 1})
     (io_orig_assn (dispatch_ch 1) 0 
      (tdsch1' (k) (Suc kk) (dis_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0)) (Sch p rn rp) s)) tr \<or>
 waitin_assms'_assn {..(0.045 - dis_s CHR ''t'')}
     (\<lambda>t. ParState
                 (ParState (EState (Task WAIT ent tp, task_s))
         
          (EState
                     (estate.None, dis_s(CHR ''t'' := dis_s CHR ''t'' + t))))
                 (EState (Sch p rn rp, s)))
     ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2, dispatch_ch 1}) (req_ch 2) {1}
     (\<lambda> v d. if (v\<le>rp) then tdsch1' (Suc k) kk (dis_s(CHR ''t'' := dis_s CHR ''t'' + d)) (Task WAIT ent tp) (task_s) (sched_push 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))
                                     else if rn \<noteq> -1 then out_0assm_assn (preempt_ch rn) 0 (out_0assm_assn (run_ch 2) 0 
                                         (tdsch1' (Suc k) kk (dis_s(CHR ''t'' := dis_s CHR ''t'' + d)) (Task WAIT ent tp) (task_s) (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))))
                                                       \<or>\<^sub>t io_out0_out0 (dispatch_ch 1) 0 (preempt_ch rn) 0 (run_ch 2) 0 
                                         (tdsch1' k kk (dis_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0)) (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v)))
                                                     else out_0assm_assn (run_ch 2) 0 
                                         (tdsch1' (Suc k) kk (dis_s(CHR ''t'' := dis_s CHR ''t'' + d)) (Task WAIT ent tp) (task_s) (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v)))
                                                       \<or>\<^sub>t io_orig_assn (dispatch_ch 1) 0 (out_0assm_assn (run_ch 2) 0 
                                         (tdsch1' k kk (dis_s(CHR ''t'' := 0)) (Task READY 0 tp) (task_s(CHR ''t'' := 0)) (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v))) (s(CHR ''p'' := v))))) tr"
| "tdsch1' (Suc k) (Suc kk) dis_s (Task READY ent tp) task_s (Sch p rn rp) s tr \<longleftrightarrow> 
      io_orig_assn (req_ch 1) 2 (if rn \<noteq> -1 then out_0assm_assn (preempt_ch rn) 0 (io_orig_assn (run_ch 1) 0 
                                                       (tdsch1' k kk dis_s (Task RUNNING (Suc 0) 2)
                                                        (task_s(CHR ''c'' := up_ent_c ent (task_s CHR ''c''))) (Sch p 1 2) (s(CHR ''p'' := 2))))
                                            else io_orig_assn (run_ch 1) 0 
                                                       (tdsch1' k kk dis_s (Task RUNNING (Suc 0) 2)
                                                        (task_s(CHR ''c'' := up_ent_c ent (task_s CHR ''c''))) (Sch p 1 2) (s(CHR ''p'' := 2)))) tr \<or>
      in_0orig_vassm_assn (req_ch 2) {1} (\<lambda> v. if v \<le> rp then (tdsch1' (Suc k) kk dis_s (Task READY ent tp) task_s (Sch (p @ [(1, 2)]) rn rp)(s(CHR ''p'' := 1))) 
                                                         else if rn \<noteq> -1 then (out_0assm_assn (preempt_ch rn) 0 (out_0assm_assn (run_ch 2) 0 (tdsch1' (Suc k) kk dis_s (Task READY ent 2) task_s (Sch p 2 1) (s(CHR ''p'' := 1))))) 
                                                                        else (out_0assm_assn (run_ch 2) 0 (tdsch1' (Suc k) kk dis_s (Task READY ent 2) task_s (Sch p 2 1) (s(CHR ''p'' := 1))))) tr \<or> 
      in_0orig_vassm_assn (free_ch 2) {0} (\<lambda> v. if length p > 0 then emp\<^sub>t
                                                                else emp\<^sub>t) tr"

thm tdsch1'.simps


lemma combine_wait_orig_waitin_assms'1:
  assumes"ch \<in> chs"
     and "compat_rdy rdy1 rdy2"
   shows "combine_assn chs (wait_orig_assn d p1 rdy1 P) (waitin_assms'_assn UNIV p2 rdy2 ch V Q)
     \<Longrightarrow>\<^sub>t wait_orig_assn d (\<lambda> t. ParState (p1 t)(p2 t)) (merge_rdy rdy1 rdy2) 
          (combine_assn chs P (waitin_assms'_assn UNIV (\<lambda> t. p2(t+d)) rdy2 ch V (\<lambda> v t. Q v (t+d))))"
  unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: wait_orig_assn.cases[of d p1 rdy1 P tr1])
      apply auto
    subgoal
      apply(rule wait_orig_assn.intros(1))
      by auto
    subgoal for tr1'
      apply(cases rule: waitin_assms'_assn.cases[of UNIV p2 rdy2 ch V Q tr2])
          apply simp
      subgoal for v tr2'
        using assms by (auto elim!: sync_elims)
      subgoal for  v  d' tr2'
        apply(cases "d>d'")
        subgoal
          apply auto
          apply(elim combine_blocks_waitE4)
          using assms by (auto elim!: sync_elims)
        apply(cases "d<d'")
        subgoal
          apply auto
          apply(elim combine_blocks_waitE3)
          using assms apply auto
          apply(rule wait_orig_assn.intros(2))
           apply auto
          subgoal for tr'
            apply(rule exI[where x="tr1'"])
            apply auto
            apply(rule exI[where x="(WaitBlk (d' - d) (\<lambda>t. p2 (t + d)) rdy2 # InBlock ch v # tr2')"])
            apply auto
            apply(rule waitin_assms'_assn.intros(2))
            by auto
          done
        apply auto
        apply(elim combine_blocks_waitE2)
          using assms apply auto
          apply(rule wait_orig_assn.intros(2))
           apply auto
          subgoal for tr'
            apply(rule exI[where x="tr1'"])
            apply auto
            apply(rule exI[where x="(InBlock ch v # tr2')"])
            apply auto
            apply(rule waitin_assms'_assn.intros(1))
            by auto
              done
            subgoal for w tr2'
              using assms by (auto elim!: sync_elims)
            subgoal for d' v  tr2'
              apply(cases "d>d'")
              subgoal
                apply auto
                apply(elim combine_blocks_waitE4)
                using assms apply auto
                by (auto elim!: sync_elims)
              apply(cases "d<d'")
              subgoal
                apply auto
                apply(elim combine_blocks_waitE3)
                using assms apply auto
                apply(rule wait_orig_assn.intros(2))
                 apply auto
                subgoal for tr'
                  apply(rule exI[where x="tr1'"])
                  apply auto
                  apply(rule exI[where x="(WaitBlk (d' - d) (\<lambda>t. p2 (t + d)) rdy2 # InBlock ch v # tr2')"])
                  apply auto
                  apply(rule waitin_assms'_assn.intros(4))
                  by auto
                done
              apply auto
              apply(elim combine_blocks_waitE2)
              using assms apply auto
              apply(rule wait_orig_assn.intros(2))
               apply auto
              subgoal for tr'
                apply(rule exI[where x="tr1'"])
                apply auto
                apply(rule exI[where x="(InBlock ch v # tr2')"])
                apply auto
                apply(rule waitin_assms'_assn.intros(3))
                by auto
              done
            done
          done
        done

lemma combine_io_orig_waitin_assms'1:
  assumes"ch \<in> chs"
     and "dh \<notin> chs"
   shows "combine_assn chs (io_orig_assn dh v P) (waitin_assms'_assn UNIV p rdy ch V Q)
     \<Longrightarrow>\<^sub>t io_orig_assn dh v 
          (combine_assn chs P (waitin_assms'_assn UNIV p rdy ch V Q))"
  unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: io_orig_assn.cases[of dh v P tr1])
     apply auto
    subgoal for tr1'
      apply(cases rule: waitin_assms'_assn.cases[of UNIV p rdy ch V Q tr2])
          apply simp
      subgoal for w tr2'
        apply auto
        apply (elim combine_blocks_unpairE1)
        using assms apply auto
        apply(rule io_orig_assn.intros)
        by auto
      subgoal for w d tr2'
        apply auto
        apply(elim combine_blocks_unpairE3)
        using assms apply auto
        apply(rule io_orig_assn.intros)
        by auto
      subgoal for w tr2'
        apply auto
        apply (elim combine_blocks_unpairE1)
        using assms apply auto
        apply(rule io_orig_assn.intros)
        by auto
      subgoal for w d tr2'
        apply auto
        apply(elim combine_blocks_unpairE3)
        using assms apply auto
        apply(rule io_orig_assn.intros)
        by auto
      done
    done
  done


lemma combine_blocks_emptyE'3' [sync_elims]:
  "combine_blocks comms [] (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow> 
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms [] tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)
        
definition propc :: "nat \<Rightarrow> estate \<Rightarrow> estate \<Rightarrow> bool" where
"propc k task_es schs = (k>0 \<longrightarrow>(status task_es = RUNNING \<longleftrightarrow> run_now schs = 1))"



lemma combine_taskdis_sch1':
  "task_dis_assn' 1 k dis_s task_es task_s tr1 \<Longrightarrow>
   sched_assn' kk schs s tr2 \<Longrightarrow>
   task_prior task_es = 2 \<Longrightarrow>
   propc k task_es schs \<Longrightarrow>
   proper schs \<Longrightarrow>
   combine_blocks {req_ch 1, preempt_ch 1, run_ch 1, free_ch 1, exit_ch 1} tr1 tr2 tr \<Longrightarrow>
   tdsch1' k kk dis_s task_es task_s schs s tr"
  thm nat_less_induct 
  thm less_induct
    proof(induction " k+kk"  arbitrary: k kk task_es task_s dis_s schs s tr1 tr2 tr rule: less_induct)
      case less
      then show ?case 
        apply (cases k)
        subgoal 
          apply (cases kk)
          subgoal apply simp
            apply (cases schs)
              apply simp
            subgoal premises pre
              thm pre
              apply (rule combine_blocks_assn)
                 apply(rule pre(1))
                apply(rule pre(2))
               apply(rule pre(6))
              by (auto elim!: sync_elims)
            apply auto
            done
          subgoal for kk'
            apply simp
            apply(cases schs)
            subgoal premises pre for p rn rp
              thm pre
              using pre(3)
              apply (simp only: pre(10))
              apply (subst tdsch1'.simps)
              apply (simp only: sched_assn'.simps)
              apply(erule disjE)
              subgoal premises pre'
                apply(rule disjI1)
                apply (rule combine_blocks_assn)
                   apply(rule pre(2))
                  apply(rule pre')
                 apply(rule pre(7))
                apply(rule combine_emp_waitin_assms'1)
                by auto
              apply(erule disjE)        
              subgoal premises pre'
                apply(rule disjI1)
                apply (rule combine_blocks_assn)
                   apply(rule pre(2))
                  apply(rule pre')
                 apply(rule pre(7))
                apply(rule entails_tassn_trans)
                 apply(rule combine_emp_waitin_assms'2)
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply(rule waitin_assms'_assn_tran)
                apply clarify
                apply simp
                apply(rule conjI)
                subgoal
                  apply clarify
                  apply(rule conjI)
                  subgoal apply clarify
                    unfolding entails_tassn_def combine_assn_def
                    apply clarify
                    subgoal for tr tr1 tr2
                      using pre(1)[of 0 kk' dis_s task_es task_s tr1 "(Sch (p @ [(1, 2)]) rn rp)"" (s(CHR ''p'' := 1))" tr2 tr]
                      using pre(4,5,6)[unfolded pre(10)] 
                      unfolding proper_def properp_def
                      using properl_p1 propc_def
                      by (auto simp add: properp_def)
                    done
                  subgoal apply clarify
                    apply(rule entails_tassn_trans)
                     apply(rule combine_emp_out_0assm3)
                    apply(rule out_0assm_assn_tran)
                    apply(rule entails_tassn_trans)
                     apply(rule combine_emp_out_0assm3)
                    apply(rule out_0assm_assn_tran)
                    unfolding entails_tassn_def combine_assn_def
                    apply clarify
                    subgoal for tr tr1 tr2
                      using pre(1)[of 0 kk' dis_s task_es task_s tr1 "(Sch p 2 1)""(s(CHR ''p'' := 1))" tr2 tr]
                      using pre(4,5,6)[unfolded pre(10)] 
                      unfolding proper_def properp_def propc_def
                      by auto
                    done
                  done
                subgoal
                  apply clarify
                  apply(rule conjI)
                  subgoal apply clarify
                    unfolding entails_tassn_def combine_assn_def
                    apply clarify
                    subgoal for tr tr1 tr2
                      using pre(1)[of 0 kk' dis_s task_es task_s tr1 "(Sch (p @ [(1, 2)]) (- 1) rp)" "(s(CHR ''p'' := 1))" tr2 tr ]
                      using pre(4,5,6)[unfolded pre(10)] 
                      unfolding proper_def properp_def
                      by auto
                    done
                  apply clarify
                  apply(rule entails_tassn_trans)
                   apply(rule combine_emp_out_0assm3)
                  apply(rule out_0assm_assn_tran)
                  unfolding entails_tassn_def combine_assn_def
                  apply clarify
                  subgoal for tr tr1 tr2
                    using pre(1)[of 0 kk' dis_s task_es task_s tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr ]
                    using pre(4,5,6)[unfolded pre(10)] 
                    unfolding proper_def properp_def propc_def
                    by auto
                  done
                done
              apply(erule disjE)
              subgoal premises pre'
                apply(rule disjI2)
                apply(rule disjI1)
                apply (rule combine_blocks_assn)
                   apply(rule pre(2))
                  apply(rule pre')
                 apply(rule pre(7))
                apply(rule combine_emp_waitin_assms'1)
                by auto
              apply(erule disjE)
              subgoal premises pre'
                apply(rule disjI2)
                apply(rule disjI1)
                apply (rule combine_blocks_assn)
                   apply(rule pre(2))
                  apply(rule pre')
                 apply(rule pre(7))
                apply(rule entails_tassn_trans)
                 apply(rule combine_emp_waitin_assms'2)
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply(rule waitin_assms'_assn_tran)
                subgoal for v d
                  apply clarify
                  apply simp
                  apply(rule conjI)
                  subgoal apply clarify
                    apply(rule entails_tassn_trans)
                     apply(rule combine_emp_out_0assm3)
                    apply(rule out_0assm_assn_tran)
                    unfolding entails_tassn_def combine_assn_def
                    apply auto
                    subgoal for tr tr1 tr2
                      using pre(1)[of 0 kk' dis_s task_es task_s tr1 "(case get_max p of (prior, t) \<Rightarrow> Sch (del_proc p t) t prior)" s tr2 tr ]
                      using pre(4,5,6)[unfolded pre(10)] 
                      unfolding proper_def propc_def
                      apply auto
                      apply (cases "get_max p")
                      subgoal for a b apply auto
                        using properl_p3[of p] properl_p4[of p b]
                        by auto
                      done
                    done
                  unfolding entails_tassn_def combine_assn_def
                  apply auto
                  subgoal for tr tr1 tr2
                    using pre(1)[of 0 kk' dis_s task_es task_s tr1 "(Sch [] (- 1) (- 1))" s tr2 tr]
                    using pre(4,5,6) 
                    unfolding proper_def properp_def propc_def
                    by auto
                  done
                done
              apply(erule disjE)
              subgoal premises pre'
                apply(rule disjI2)
                apply(rule disjI2)
                apply (rule combine_blocks_assn)
                   apply(rule pre(2))
                  apply(rule pre')
                 apply(rule pre(7))
                apply(rule combine_emp_waitin_assms'1)
                by auto
              subgoal premises pre'
                apply(rule disjI2)
                apply(rule disjI2)
                apply (rule combine_blocks_assn)
                   apply(rule pre(2))
                  apply(rule pre')
                 apply(rule pre(7))
                apply(rule entails_tassn_trans)
                 apply(rule combine_emp_waitin_assms'2)
                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def)
                apply(rule waitin_assms'_assn_tran)
                apply auto
                unfolding entails_tassn_def combine_assn_def
                 apply auto
                subgoal for tr tr1 tr2
                  using pre(1)[of 0 kk' dis_s task_es task_s tr1 "(Sch (del_proc p 2) rn rp)" s tr2 tr]
                  using pre(4,5,6)[unfolded pre(10)]
                  unfolding proper_def propc_def
                  using properl_p4[of p 2]
                  by auto
                done
              done
             apply auto
            done
          done
        subgoal for k'
          apply(cases kk)
          subgoal
            apply auto
            apply (cases schs)
              apply (cases task_es)
                apply auto
            subgoal for p rn rp st ent
              apply (cases st)
                apply simp
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                   apply(rule pre(2))
                  apply(rule pre(3))
                 apply(rule pre(6))
                apply(rule entails_tassn_trans)
                 apply(rule combine_wait_orig_emp5)
                apply(rule entails_tassn_trans)
                 apply(rule combine_io_orig_emp)
                apply(rule io_orig_assn_tran)
                unfolding entails_tassn_def combine_assn_def
                  apply auto
                subgoal for tr tr1 tr2
                  using pre(1)[of k' 0 "(dis_s(CHR ''t'' := 0))" "(Task READY 0 2)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p rn rp)" s tr2 tr]
                  using pre(4,5) unfolding propc_def by auto
                done
              subgoal 
                apply simp
                apply(erule disjE)
                subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                   apply(rule pre(11))
                  apply(rule pre(2))
                 apply(rule pre(5))
                apply(rule combine_out_0assm_emp1)
                by auto
              apply(erule disjE)
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                   apply(rule pre(11))
                   apply(rule pre(2))
                 apply(rule pre(5))
                apply(rule combine_out_0assm_emp1)
                by auto
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                   apply(rule pre(11))
                   apply(rule pre(2))
                 apply(rule pre(5))
                apply(rule combine_out_0assm_emp1)
                by auto
              done
              apply(cases "ent = 1")
               apply auto
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                   apply(rule pre(12))
                  apply(rule pre(2))
                 apply(rule pre(5))
                apply(rule combine_waitin_tguar'_vassm'_emp1)
                by auto
              subgoal premises pre
                thm pre
                apply(rule combine_blocks_assn)
                   apply(rule pre(12))
                  apply(rule pre(2))
                 apply(rule pre(5))
                apply(rule entails_tassn_trans)
                 apply(rule combine_wait_orig_emp5)
                apply(rule combine_out_0assm_emp1)
                by auto
              done
            done
          subgoal for kk'
            apply auto
            apply (cases schs)
            subgoal for p rn rp
              apply(cases task_es)
              subgoal by auto
              subgoal for st ent tp
                apply (cases st)
                subgoal premises pre
                  thm pre
                  thm fun_upd_def
                  using pre(2) pre(3)
                  apply(simp only: pre(10,11,12))
                  apply(simp only: task_dis_assn'.simps)
                  apply(simp only: sched_assn'.simps)
                  apply(erule disjE)
                  subgoal premises pre'
                    apply simp
                    apply(rule disjI1)
                    thm pre'
                    apply(rule combine_blocks_assn)
                       apply(rule pre'(1))
                      apply(rule pre'(2))
                     apply(rule pre(7))
                    apply(rule entails_tassn_trans)
                     apply(rule combine_wait_orig_waitin_assms'1)
                      apply simp
                    subgoal by auto
                    apply (simp del: fun_upd_apply)
                    apply(rule wait_orig_assn_tran)
                    apply(rule entails_tassn_trans)
                     apply(rule combine_io_orig_waitin_assms'1)
                    subgoal by auto
                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                    apply(rule io_orig_assn_tran)
                    unfolding entails_tassn_def combine_assn_def
                    apply auto
                    subgoal for tr tr1 tr2
                      apply(subgoal_tac "sched_assn' (Suc(kk')) (Sch p rn rp) s tr2")
                      prefer 2
                       apply simp
                      using pre(1)[of k' "(Suc(kk'))" "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p rn rp)" s tr2 tr]
                      using pre unfolding propc_def by auto
                    done
                  apply(erule disjE)
                  subgoal 
                    apply(cases rule: wait_orig_assn.cases[of "(45 / 10 ^ 3 - dis_s CHR ''t'')"
                                                               "(\<lambda>t. ParState (EState (Task WAIT ent tp, task_s))
                                                                     (EState (estate.None, dis_s(CHR ''t'' := dis_s CHR ''t'' + t))))"
                                                               "({}, {dispatch_ch 1})"
                                                               "(io_orig_assn (dispatch_ch 1) 0
                                                                 (task_dis_assn' 1 k' (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                   (task_s(CHR ''t'' := 0))))"
                                                               tr1])
                      apply simp
                    subgoal
                      apply(cases rule: io_orig_assn.cases[of "(dispatch_ch 1)" 0
                                                               "(task_dis_assn' 1 k' (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                 (task_s(CHR ''t'' := 0)))" tr1])
                       apply simp
                      subgoal for tr1'
                        apply(cases rule: waitin_assms'_assn.cases[of UNIV "(\<lambda>t. EState (Sch p rn rp, s))" "({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})"" (req_ch 2)
                                                                           ""{1}"  "(\<lambda>v d. if v \<le> rp
                                                                            then sched_assn' kk' (sched_push 2 (Sch p rn rp) (s(CHR ''p'' := v)))
                                                                                  (s(CHR ''p'' := v))
                                                                            else if rn \<noteq> - 1
                                                                                 then out_0assm_assn (preempt_ch rn) 0
                                                                                       (out_0assm_assn (run_ch 2) 0
                                                                                         (sched_assn' kk'
                                                                                           (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v)))
                                                                                           (s(CHR ''p'' := v))))
                                                                                 else out_0assm_assn (run_ch 2) 0
                                                                                       (sched_assn' kk'
                                                                                         (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v)))
                                                                                         (s(CHR ''p'' := v))))" tr2])
                            apply simp
                        subgoal for v tr2'
                          using pre(7)
                          apply (simp del: tdsch1'.simps)
                          apply(elim combine_blocks_unpairE2) 
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                          subgoal for tr'
                            apply simp
                            apply(rule disjI1)
                            apply(rule wait_orig_assn.intros(1))
                             apply auto
                            apply(rule io_orig_assn.intros)
                            using pre(1)[of k' "Suc kk'" "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1' "(Sch p rn rp)" s tr2 tr']
                            apply auto
                            thm pre
                            using pre(4,5,6,12)[unfolded pre(10,11)]
                            unfolding propc_def
                            by auto
                          subgoal for tr'
                            apply(cases "1\<le>rp")
                            subgoal apply simp
                              apply(rule disjI2)
                              apply(rule waitin_assms'_assn.intros(1))
                                apply auto
                              using pre(1)[of "Suc k'" kk' dis_s "Task WAIT ent tp" task_s tr1 "(Sch (p @ [(1, 2)]) rn rp)" "s(CHR ''p'' := 1)" tr2' tr']
                              thm pre
                              using pre(4,5,6,12)[unfolded pre(10,11)]
                              unfolding propc_def proper_def
                              by (auto simp add:properl_p1 properp_def) 
                            apply(cases "rn \<noteq> -1")
                            subgoal 
                              apply(subgoal_tac "rn \<noteq> 1")
                               prefer 2
                              subgoal
                                using pre
                                unfolding propc_def proper_def properp_def by auto
                              apply(simp del: tdsch1'.simps)
                              apply(cases rule: out_0assm_assn.cases[of " (preempt_ch rn) "0
                                                                 "(out_0assm_assn (run_ch 2) 0 (sched_assn' kk' (Sch p 2 1) (s(CHR ''p'' := 1))))"
                                                                 tr2'])
                              subgoal by auto
                              subgoal for tr2''
                                apply(simp del: tdsch1'.simps)
                                apply(elim combine_blocks_unpairE2) 
                                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                subgoal using pre(6)[unfolded pre(10,11)] unfolding proper_def properp_def
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                subgoal for tr''
                                  apply(cases k')
                                  subgoal
                                    apply(simp del: tdsch1'.simps add:emp_assn_def)
                                    apply(elim combine_blocks_emptyE'3')
                                    subgoal using pre(6)[unfolded pre(10,11)] unfolding proper_def properp_def
                                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    subgoal for tr'''
                                      apply(cases rule: out_0assm_assn.cases[of "(run_ch 2)" 0 "(sched_assn' kk' (Sch p 2 1) (s(CHR ''p'' := 1)))" tr2''])
                                      subgoal by auto
                                      subgoal for tr2'''
                                        apply(simp del: tdsch1'.simps )
                                        apply(elim combine_blocks_emptyE'3')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal for tr''''
                                          apply simp
                                          apply(rule disjI2)
                                          apply(rule waitin_assms'_assn.intros(1))
                                          subgoal by auto
                                          subgoal by auto
                                          subgoal apply auto
                                            unfolding disj_assn_def
                                            apply(rule disjI2)
                                            apply(rule io_out0_out0.intros(1))
                                            apply(rule io_orig_assn.intros)
                                            apply(rule out_0assm_assn.intros(1))
                                            apply(rule out_0assm_assn.intros(1))
                                            using pre(1)[of 0 kk' dis_s "(Task READY 0 tp)" task_s "[]""(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2''' tr'''']
                                            thm pre
                                            using pre(4,5,6,12)[unfolded pre(10,11)]
                                            unfolding propc_def proper_def properp_def
                                            by(auto simp add: emp_assn_def) 
                                          done
                                        done
                                      subgoal for d q rdy tr2'''
                                        by (auto elim!: sync_elims)
                                      done
                                    done
                                  subgoal for k''
                                    apply(simp del: tdsch1'.simps )
                                    apply(erule disjE)
                                    subgoal apply simp
                                      apply(rule disjI2)
                                      apply(rule waitin_assms'_assn.intros(1))
                                        apply auto
                                      unfolding disj_assn_def
                                      apply(rule disjI2)
                                      apply(rule io_out0_out0.intros(1))
                                      apply(rule io_orig_assn.intros)
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                        thm pre'
                                           apply(rule pre'(18))
                                          apply(rule pre'(8))
                                         apply(rule pre'(16))
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                           prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      done
                                    subgoal apply simp
                                      apply(rule disjI2)
                                      apply(rule waitin_assms'_assn.intros(1))
                                        apply auto
                                      subgoal
                                      unfolding disj_assn_def
                                      apply(rule disjI2)
                                      apply(rule io_out0_out0.intros(1))
                                      apply(rule io_orig_assn.intros)
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                        thm pre'
                                           apply(rule pre'(18))
                                          apply(rule pre'(8))
                                         apply(rule pre'(16))
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                           prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      done
                                    subgoal
                                      unfolding disj_assn_def
                                      apply(rule disjI2)
                                      apply(rule io_out0_out0.intros(1))
                                      apply(rule io_orig_assn.intros)
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                        thm pre'
                                           apply(rule pre'(18))
                                          apply(rule pre'(8))
                                         apply(rule pre'(16))
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                           prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      done
                                    done
                                  done
                                done
                                subgoal for tr''
                                  apply(cases rule: out_0assm_assn.cases[of "(run_ch 2)" 0 "(sched_assn' kk' (Sch p 2 1) (s(CHR ''p'' := 1)))" tr2''])
                                  subgoal by auto
                                  subgoal for tr2'''
                                    apply(simp del: tdsch1'.simps )
                                    apply(elim combine_blocks_unpairE2)
                                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    subgoal using pre(6)[unfolded pre(10,11)] unfolding proper_def properp_def
                                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    subgoal for tr'''
                                      apply(cases k')    
                                      subgoal
                                        apply(simp del: tdsch1'.simps add:emp_assn_def)
                                        apply(elim combine_blocks_emptyE'3')
                                        subgoal using pre(6)[unfolded pre(10,11)] unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal for tr''''
                                          subgoal apply simp
                                            apply(rule disjI2)
                                            apply(rule waitin_assms'_assn.intros(1))
                                              apply auto
                                            unfolding disj_assn_def
                                            apply(rule disjI2)
                                            apply(rule io_out0_out0.intros(2))
                                            apply(rule out_0orig_assn.intros)
                                            apply(rule io_orig_assn.intros)
                                            apply(rule out_0assm_assn.intros(1))
                                            using pre(1)[of 0 kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1' "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2''' tr'''']
                                            using pre(4,5,6,12)[unfolded pre(10,11)] 
                                            unfolding propc_def proper_def properp_def
                                            by auto
                                          done
                                        done
                                      subgoal for k''
                                        apply simp
                                        apply(rule disjI2)
                                        apply(rule waitin_assms'_assn.intros(1))
                                        subgoal by auto
                                        subgoal by auto
                                        unfolding disj_assn_def
                                        apply simp
                                        apply(rule disjI2)
                                        apply(rule io_out0_out0.intros(2))
                                        apply(rule out_0orig_assn.intros)
                                        apply(rule io_orig_assn.intros)
                                        apply(erule disjE)
                                        subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                        thm pre'
                                           apply(rule pre'(21))
                                          apply(rule pre'(14))
                                         apply(rule pre'(19))
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                           prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      apply(erule disjE)
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                        thm pre'
                                           apply(rule pre'(21))
                                          apply(rule pre'(14))
                                         apply(rule pre'(19))
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                           prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                        thm pre'
                                           apply(rule pre'(21))
                                          apply(rule pre'(14))
                                         apply(rule pre'(19))
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                           prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      done
                                    done
                                  subgoal for tr'''
                                    apply simp
                                    apply(rule disjI2)
                                    apply(rule waitin_assms'_assn.intros(1))
                                    subgoal by auto
                                    subgoal by auto
                                    unfolding disj_assn_def
                                    apply simp
                                    apply(rule disjI1)
                                    apply(rule out_0assm_assn.intros(1))
                                    apply(rule out_0assm_assn.intros(1))
                                    using pre(1)[of "(Suc k')" kk' dis_s "(Task WAIT ent tp)" task_s tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2''' tr''']
                                    using pre(4,5,6,12)[unfolded pre(10,11)] 
                                    unfolding propc_def proper_def properp_def
                                    by auto
                                  done
                                subgoal for d q rdy tr2'''
                                  apply(simp del: tdsch1'.simps)
                                  apply(elim combine_blocks_unpairE3)
                                  subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                  subgoal for tr'''
                                    apply(cases k')    
                                      subgoal
                                        apply(simp del: tdsch1'.simps add:emp_assn_def)
                                        by(auto elim: sync_elims)
                                      subgoal for k''
                                        apply simp
                                        apply(rule disjI2)
                                        apply(rule waitin_assms'_assn.intros(1))
                                        subgoal by auto
                                        subgoal by auto
                                        unfolding disj_assn_def
                                        apply simp
                                        apply(rule disjI2)
                                        apply(rule io_out0_out0.intros(2))
                                        apply(rule out_0orig_assn.intros)
                                        apply(rule io_orig_assn.intros)
                                        apply(erule disjE)
                                        subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                        thm pre'
                                           apply(rule pre'(22))
                                          apply(rule pre'(14))
                                         apply(rule pre'(20))
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                           prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      apply(erule disjE)
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                        thm pre'
                                           apply(rule pre'(22))
                                          apply(rule pre'(14))
                                         apply(rule pre'(20))
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                           prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                    subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                        thm pre'
                                           apply(rule pre'(22))
                                          apply(rule pre'(14))
                                         apply(rule pre'(20))
                                        apply(rule entails_tassn_trans)
                                         apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                           prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            subgoal for d rdy q tr2''
                              apply(simp del: tdsch1'.simps)
                              apply(elim combine_blocks_unpairE3)
                              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              subgoal for tr''
                                apply(cases k')
                                subgoal
                                  apply(simp del: tdsch1'.simps add:emp_assn_def)
                                  by(auto elim: sync_elims)
                                subgoal for k''
                                  apply simp
                                  apply(rule disjI2)
                                  apply(rule waitin_assms'_assn.intros(1))
                                  subgoal by auto
                                  subgoal by auto
                                  unfolding disj_assn_def
                                  apply simp
                                  apply(rule disjI2)
                                  apply(rule io_out0_out0.intros(1))
                                  apply(rule io_orig_assn.intros)
                                  apply(erule disjE)
                                  subgoal premises pre'
                                    apply(rule combine_blocks_assn)
                                    thm pre'
                                    apply(rule pre'(19))
                                    apply(rule pre'(8))
                                    apply(rule pre'(17))
                                    apply(rule entails_tassn_trans)
                                    apply(rule combine_out_0assm_out_0assm2')
                                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    apply(rule out_0assm_assn_tran)
                                    apply(rule entails_tassn_trans)
                                    apply(rule combine_out_0assm_out_0assm2')
                                    subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    apply(rule out_0assm_assn_tran)
                                    unfolding combine_assn_def entails_tassn_def
                                    apply auto
                                    subgoal for tr tr1 tr2
                                      apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                      prefer 2
                                      subgoal by auto
                                      using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                      using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                      unfolding propc_def proper_def properp_def
                                      by auto
                                    done
                                  apply(erule disjE)
                                    subgoal premises pre'
                                      apply(rule combine_blocks_assn)
                                        thm pre'
                                      apply(rule pre'(19))
                                      apply(rule pre'(8))
                                      apply(rule pre'(17))
                                      apply(rule entails_tassn_trans)
                                      apply(rule combine_out_0assm_out_0assm2')
                                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                      subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                      apply(rule out_0assm_assn_tran)
                                      unfolding combine_assn_def entails_tassn_def
                                      apply auto
                                      subgoal for tr tr1 tr2
                                        apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                        prefer 2
                                        subgoal by auto
                                        using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                        using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                        unfolding propc_def proper_def properp_def
                                        by auto
                                      done
                                    subgoal premises pre'
                                      apply(rule combine_blocks_assn)
                                        thm pre'
                                      apply(rule pre'(19))
                                      apply(rule pre'(8))
                                      apply(rule pre'(17))
                                      apply(rule entails_tassn_trans)
                                      apply(rule combine_out_0assm_out_0assm2')
                                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                      subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                      apply(rule out_0assm_assn_tran)
                                      unfolding combine_assn_def entails_tassn_def
                                      apply auto
                                      subgoal for tr tr1 tr2
                                        apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                  (task_s(CHR ''t'' := 0))) tr1")
                                        prefer 2
                                        subgoal by auto
                                        using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                        using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                        unfolding propc_def proper_def properp_def
                                        by auto
                                      done
                                    done
                                  done
                                done
                              done
                            subgoal
                              apply(simp del: tdsch1'.simps)
                              apply(cases rule: out_0assm_assn.cases[of "(run_ch 2)" 0 "(sched_assn' kk' (Sch p 2 1) (s(CHR ''p'' := 1)))" tr2'])
                              subgoal by auto
                              subgoal for tr2''
                                apply(simp del: tdsch1'.simps)
                                apply(elim combine_blocks_unpairE2)
                                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                subgoal for tr''
                                  apply(cases k')
                                  subgoal
                                    apply(simp del: tdsch1'.simps add:emp_assn_def)
                                    apply(elim combine_blocks_emptyE'3')
                                        subgoal using pre(6)[unfolded pre(10,11)] unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal for tr'''
                                          subgoal apply simp
                                            apply(rule disjI2)
                                            apply(rule waitin_assms'_assn.intros(1))
                                              apply auto
                                            unfolding disj_assn_def
                                            apply(rule disjI2)
                                            apply(rule io_orig_assn.intros)
                                            apply(rule out_0assm_assn.intros(1))
                                            using pre(1)[of 0 kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1' "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2'' tr''']
                                            using pre(4,5,6,12)[unfolded pre(10,11)] 
                                            unfolding propc_def proper_def properp_def
                                            by (auto simp: emp_assn_def)
                                          done
                                        done
                                    subgoal for k''
                                      apply simp
                                      apply(rule disjI2)
                                      apply(rule waitin_assms'_assn.intros(1))
                                      subgoal by auto
                                      subgoal by auto
                                      unfolding disj_assn_def
                                      apply simp
                                      apply(rule disjI2)
                                    apply(rule io_orig_assn.intros)
                                    apply(erule disjE)
                                    subgoal premises pre'
                                      apply(rule combine_blocks_assn)
                                      thm pre'
                                      apply(rule pre'(17))
                                      apply(rule pre'(8))
                                      apply(rule pre'(15))
                                      apply(rule entails_tassn_trans)
                                      apply(rule combine_out_0assm_out_0assm2')
                                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                      subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                      apply(rule out_0assm_assn_tran)
                                      unfolding combine_assn_def entails_tassn_def
                                      apply auto
                                      subgoal for tr tr1 tr2
                                        apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                    (task_s(CHR ''t'' := 0))) tr1")
                                        prefer 2
                                        subgoal by auto
                                        using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                        using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                        unfolding propc_def proper_def properp_def
                                        by auto
                                      done
                                    apply(erule disjE)
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                          thm pre'
                                        apply(rule pre'(17))
                                        apply(rule pre'(8))
                                        apply(rule pre'(15))
                                        apply(rule entails_tassn_trans)
                                        apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                    (task_s(CHR ''t'' := 0))) tr1")
                                          prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                          thm pre'
                                        apply(rule pre'(17))
                                        apply(rule pre'(8))
                                        apply(rule pre'(15))
                                        apply(rule entails_tassn_trans)
                                        apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                    (task_s(CHR ''t'' := 0))) tr1")
                                          prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      done
                                    done
                                  subgoal for tr''
                                    apply simp
                                    apply(rule disjI2)
                                    apply(rule waitin_assms'_assn.intros(1))
                                    subgoal by auto
                                    subgoal by auto
                                    apply auto
                                    unfolding disj_assn_def
                                    apply(rule disjI1)
                                    apply(rule out_0assm_assn.intros(1))
                                    using pre(1)[of "(Suc k')" kk' dis_s "(Task WAIT ent tp)" task_s tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2'' tr'']
                                    using pre(4,5,6,12)[unfolded pre(10,11)] 
                                    unfolding propc_def proper_def properp_def
                                    by auto
                                  done
                                subgoal for d rdy q tr2''
                                  apply(simp del: tdsch1'.simps)
                                  apply(elim combine_blocks_unpairE3)
                                  subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                  subgoal for tr''
                                    apply simp
                                    apply(rule disjI2)
                                    apply(rule waitin_assms'_assn.intros(1))
                                    subgoal by auto
                                    subgoal by auto
                                    apply auto
                                    unfolding disj_assn_def
                                    apply(rule disjI2)
                                    apply(rule io_orig_assn.intros)
                                    apply(cases k')
                                  subgoal
                                    apply(simp del: tdsch1'.simps add:emp_assn_def)
                                    by(auto elim: sync_elims)
                                  subgoal for k''
                                    apply simp
                                    apply(erule disjE)
                                    subgoal premises pre'
                                      apply(rule combine_blocks_assn)
                                      thm pre'
                                      apply(rule pre'(18))
                                      apply(rule pre'(8))
                                      apply(rule pre'(15))
                                      apply(rule entails_tassn_trans)
                                      apply(rule combine_out_0assm_out_0assm2')
                                      subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                      subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                        by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                      apply(rule out_0assm_assn_tran)
                                      unfolding combine_assn_def entails_tassn_def
                                      apply auto
                                      subgoal for tr tr1 tr2
                                        apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                    (task_s(CHR ''t'' := 0))) tr1")
                                        prefer 2
                                        subgoal by auto
                                        using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                        using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                        unfolding propc_def proper_def properp_def
                                        by auto
                                      done
                                    apply(erule disjE)
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                          thm pre'
                                        apply(rule pre'(18))
                                        apply(rule pre'(8))
                                        apply(rule pre'(15))
                                        apply(rule entails_tassn_trans)
                                        apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                    (task_s(CHR ''t'' := 0))) tr1")
                                          prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      subgoal premises pre'
                                        apply(rule combine_blocks_assn)
                                          thm pre'
                                        apply(rule pre'(18))
                                        apply(rule pre'(8))
                                        apply(rule pre'(15))
                                        apply(rule entails_tassn_trans)
                                        apply(rule combine_out_0assm_out_0assm2')
                                        subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        subgoal using pre(6)[unfolded pre(10,11)] using pre' unfolding proper_def properp_def
                                          by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                        apply(rule out_0assm_assn_tran)
                                        unfolding combine_assn_def entails_tassn_def
                                        apply auto
                                        subgoal for tr tr1 tr2
                                          apply(subgoal_tac "(task_dis_assn' 1 (Suc k'') (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                    (task_s(CHR ''t'' := 0))) tr1")
                                          prefer 2
                                          subgoal by auto
                                          using pre(1)[of "(Suc k'')" kk' "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                          using pre(4,5,6,12)[unfolded pre(10,11)] pre'
                                          unfolding propc_def proper_def properp_def
                                          by auto
                                        done
                                      done
                                    done
                                  done
                                done
                              done
                            done
                          subgoal for v2 d2 tr2'
                            using pre(7)
                            apply (simp del: tdsch1'.simps)
                            apply(elim combine_blocks_unpairE3)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                            subgoal for tr'
                              apply simp
                              apply(rule disjI1)
                              apply(rule wait_orig_assn.intros(1))
                               prefer 2
                              subgoal by auto
                              apply(rule io_orig_assn.intros)
                              using pre(1)[of k' "Suc kk'""(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1' "(Sch p rn rp)" s tr2 tr']
                              using pre(4,5,6,12)[unfolded pre(10,11)] 
                              unfolding propc_def proper_def properp_def
                              by auto
                            done
                          subgoal for v tr2'
                            using pre(7)
                            apply(simp del:tdsch1'.simps)
                            apply(elim combine_blocks_unpairE2)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                            subgoal for tr'
                              apply simp
                              apply(rule disjI1)
                              apply(rule wait_orig_assn.intros(1))
                               prefer 2 subgoal by auto
                              apply(rule io_orig_assn.intros)
                              using pre(1)[of k' "(Suc kk')" "(dis_s(CHR ''t'' := 0))""(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1' "(Sch p rn rp)" s tr2 tr']
                              using pre(4,5,6,12)[unfolded pre(10,11)] 
                              unfolding propc_def proper_def properp_def
                              by auto
                            subgoal for tr'
                              apply simp
                              apply(rule disjI2)
                              apply(rule waitin_assms'_assn.intros(3))
                              by auto
                            done
                          subgoal for d v tr2'
                            using pre(7)
                            apply(simp del:tdsch1'.simps)
                            apply(elim combine_blocks_unpairE3)
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                            subgoal for tr'
                              apply simp
                              apply(rule disjI1)
                              apply(rule wait_orig_assn.intros(1))
                               prefer 2 subgoal by auto
                              apply(rule io_orig_assn.intros)
                              using pre(1)[of k' "(Suc kk')" "(dis_s(CHR ''t'' := 0))""(Task READY 0 tp)" "(task_s(CHR ''t'' := 0))" tr1' "(Sch p rn rp)" s tr2 tr']
                              using pre(4,5,6,12)[unfolded pre(10,11)] 
                              unfolding propc_def proper_def properp_def
                              by auto
                            done
                          done
                        done
                      subgoal for tr1'
                        apply(cases rule: waitin_assms'_assn.cases[of UNIV "(\<lambda>t. EState (Sch p rn rp, s))"
                                                                   "({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})" "(req_ch 2)"
                                                                   "{1}" "(\<lambda>v d. if v \<le> rp
                                                                          then sched_assn' kk' (sched_push 2 (Sch p rn rp) (s(CHR ''p'' := v)))
                                                                                (s(CHR ''p'' := v))
                                                                          else if rn \<noteq> - 1
                                                                               then out_0assm_assn (preempt_ch rn) 0
                                                                                     (out_0assm_assn (run_ch 2) 0
                                                                                       (sched_assn' kk'
                                                                                         (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v)))
                                                                                         (s(CHR ''p'' := v))))
                                                                               else out_0assm_assn (run_ch 2) 0
                                                                                     (sched_assn' kk'
                                                                                       (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v)))
                                                                                       (s(CHR ''p'' := v))))"tr2])
                        subgoal by auto
                        subgoal for v tr2'
                          using pre(7)
                          apply(simp del: tdsch1'.simps)
                          apply(elim combine_blocks_unpairE3')
                          subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                          subgoal for tr'
                            apply simp
                            apply(rule disjI2)
                            apply(rule waitin_assms'_assn.intros(1))
                            subgoal by auto
                            subgoal by auto
                            apply(cases "1\<le>rp")
                            subgoal
                              apply auto
                              using pre(1)[of "(Suc k')" kk' dis_s "(Task WAIT ent tp)" task_s tr1 "(Sch (p @ [(1, 2)]) rn rp)" "(s(CHR ''p'' := 1))" tr2' tr']
                              using pre(4,5,6,12)[unfolded pre(10,11)] 
                              using properl_p1
                              unfolding propc_def proper_def properp_def 
                              by auto
                            apply(subgoal_tac "rn \<noteq> 1")
                               prefer 2
                              subgoal
                                using pre
                                unfolding propc_def proper_def properp_def by auto
                            apply(cases "rn \<noteq> - 1")
                            subgoal
                              apply auto
                              unfolding disj_assn_def
                              apply(rule disjI1)
                              subgoal premises pre'
                                thm pre'
                                apply(rule combine_blocks_assn)
                                apply(rule pre'(1))
                                apply(rule pre'(8))
                                 apply(rule pre'(10))
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_out_0assm2)
                                subgoal using pre' by auto
                                subgoal using pre' using pre(6)[unfolded pre(10,11)] unfolding proper_def properp_def
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply(rule out_0assm_assn_tran)
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_out_0assm2)
                                subgoal using pre' by auto
                                subgoal using pre' by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply(rule out_0assm_assn_tran)
                                unfolding entails_tassn_def combine_assn_def
                                apply auto
                                subgoal for tr tr1 tr2
                                  using pre(1)[of "(Suc k')" kk' dis_s "(Task WAIT ent tp)" task_s tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                  using pre(4,5,6,12)[unfolded pre(10,11)] 
                                  using properl_p1
                                  unfolding propc_def proper_def properp_def 
                                  by auto
                                done
                              done
                            subgoal apply auto
                              unfolding disj_assn_def
                              apply(rule disjI1)
                              subgoal premises pre'
                                thm pre'
                                apply(rule combine_blocks_assn)
                                apply(rule pre'(1))
                                apply(rule pre'(8))
                                 apply(rule pre'(10))
                                apply(rule entails_tassn_trans)
                                 apply(rule combine_wait_orig_out_0assm2)
                                subgoal using pre' by auto
                                subgoal using pre' using pre(6)[unfolded pre(10,11)] unfolding proper_def properp_def
                                  by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                apply(rule out_0assm_assn_tran)
                                unfolding entails_tassn_def combine_assn_def
                                apply auto
                                subgoal for tr tr1 tr2
                                  using pre(1)[of "(Suc k')" kk' dis_s "(Task WAIT ent tp)" task_s tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                  using pre(4,5,6,12)[unfolded pre(10,11)] 
                                  using properl_p1
                                  unfolding propc_def proper_def properp_def 
                                  by auto
                                done
                              done
                            done
                          done
                        subgoal for v d tr2'
                          using pre(7)
                          apply(simp del: tdsch1'.simps)
                          apply(cases "(45 / 10 ^ 3 - dis_s CHR ''t'')<d")
                          subgoal
                            apply(elim combine_blocks_waitE3)
                            subgoal by auto
                            subgoal by auto
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                            subgoal for tr'
                              apply(simp del: tdsch1'.simps)
                              apply(cases rule:io_orig_assn.cases[of "(dispatch_ch 1)" 0
                                                                     "(task_dis_assn' 1 k' (dis_s(CHR ''t'' := 0)) (Task READY 0 tp)
                                                                       (task_s(CHR ''t'' := 0)))" tr1'])
                              subgoal by auto
                              subgoal for tr1''
                                apply simp
                                apply(elim combine_blocks_unpairE3)
                                subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                subgoal for tr''
                                  apply(rule disjI1)
                                  apply(subgoal_tac "waitin_assms'_assn UNIV (\<lambda>t. EState (Sch p rn rp, s))
                                                       ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) (req_ch 2)
                                                       {1}
                                                       (\<lambda>v d. if v \<le> rp
                                                              then sched_assn' kk' (sched_push 2 (Sch p rn rp) (s(CHR ''p'' := v)))
                                                                    (s(CHR ''p'' := v))
                                                              else if rn \<noteq> - 1
                                                                   then out_0assm_assn (preempt_ch rn) 0
                                                                         (out_0assm_assn (run_ch 2) 0
                                                                           (sched_assn' kk'
                                                                             (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v)))
                                                                             (s(CHR ''p'' := v))))
                                                                   else out_0assm_assn (run_ch 2) 0
                                                                         (sched_assn' kk'
                                                                           (sched_assign 2 (Sch p rn rp) (s(CHR ''p'' := v)))
                                                                           (s(CHR ''p'' := v))))
                                                                   (WaitBlk (d - (9 / 200 - dis_s CHR ''t'')) (\<lambda>t. EState (Sch p rn rp, s))
                                                                   ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) # InBlock (req_ch 2) 1 # tr2')")
                                     prefer 2
                                  subgoal 
                                    apply(rule waitin_assms'_assn.intros(2))
                                    subgoal by auto
                                    subgoal by auto
                                    subgoal by auto
                                    subgoal by auto
                                    done
                                  apply(rule wait_orig_assn.intros(2))
                                   prefer 2 subgoal by auto
                                  apply simp
                                  apply(rule io_orig_assn.intros)
                                  using pre(1)[of k' "(Suc kk')" "(dis_s(CHR ''t'' := 0))" "(Task READY 0 tp)"
                                               "(task_s(CHR ''t'' := 0))" tr1'' "(Sch p rn rp)" s "(WaitBlk (d - (9 / 200 - dis_s CHR ''t'')) (\<lambda>t. EState (Sch p rn rp, s))
                                                 ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) #
                                                InBlock (req_ch 2) 1 # tr2')" tr'']
                                  using pre(4,5,6,12)[unfolded pre(10,11)] 
                                  using properl_p1
                                  unfolding propc_def proper_def properp_def 
                                  by auto
                                done
                              done
                            done
                          apply(cases "d<(45 / 10 ^ 3 - dis_s CHR ''t'')")
                          subgoal
                            apply(elim combine_blocks_waitE4)
                            subgoal by auto
                            subgoal by auto
                            subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                            subgoal for tr'
                              apply(elim combine_blocks_unpairE3')
                              subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                              subgoal for tr''
                                apply simp
                                apply(rule disjI2)
                                apply(rule waitin_assms'_assn.intros(2))
                                subgoal by auto
                                subgoal by auto
                                subgoal by auto
                                apply(subgoal_tac "task_dis_assn' 1 (Suc k') (dis_s(CHR ''t'' := dis_s CHR ''t'' + d)) (Task WAIT ent tp)
                                                   (task_s)
                                                   (WaitBlk (9 / 200 - dis_s CHR ''t'' - d)
                                                 (\<lambda>t. ParState (EState (Task WAIT ent tp, task_s))
                                                       (EState (estate.None, dis_s(CHR ''t'' := dis_s CHR ''t'' + (t + d)))))
                                                 ({}, {dispatch_ch 1}) #
                                                tr1')")
                                 prefer 2
                                subgoal premises pre'
                                proof -
                                  have a1: "(9 / 200 - (dis_s CHR ''t'' + d)) = (9 / 200 - dis_s CHR ''t'' - d)"
                                    by auto
                                  have a2: "\<And>t. dis_s CHR ''t'' + d + t = dis_s CHR ''t'' + (t + d)"
                                    by auto
                                  show ?thesis
                                    apply (subst a1[symmetric])
                                    apply (subst a2[symmetric])
                                    apply simp
                                    apply (rule wait_orig_assn.intros(2))
                                    using pre' by auto
                                  qed
                                apply(cases "1\<le>rp")
                                subgoal
                                  apply auto
                                  using pre(1)[of "(Suc k')" kk' "(dis_s(CHR ''t'' := dis_s CHR ''t'' + d))" "(Task WAIT ent tp)"
                                                  "(task_s)" 
                                                  "(WaitBlk (9 / 200 - dis_s CHR ''t'' - d)
                                                   (\<lambda>t. ParState (EState (Task WAIT ent tp, task_s))
                                                         (EState (estate.None, dis_s(CHR ''t'' := dis_s CHR ''t'' + (t + d)))))
                                                   ({}, {dispatch_ch 1}) #
                                                  tr1')" "(Sch (p @ [(1, 2)]) rn rp)"
                                                  "(s(CHR ''p'' := 1))" tr2' tr'']
                                  using pre(4,5,6,12)[unfolded pre(10,11)] 
                                  using properl_p1
                                  unfolding propc_def proper_def properp_def 
                                  by auto
                                apply simp
                                apply(cases "rn \<noteq> - 1")
                                subgoal
                                  apply auto
                                  unfolding disj_assn_def
                                  apply(rule disjI1)
                                  subgoal premises pre'
                                    thm pre'(13)
                                    apply(rule combine_blocks_assn)
                                       apply(rule pre'(13))
                                      apply(rule pre'(8))
                                     apply(rule pre'(12))
                                    apply(rule entails_tassn_trans)
                                     apply(rule combine_wait_orig_out_0assm2)
                                    subgoal using pre' by auto
                                    subgoal using pre pre'
                                      unfolding proper_def properp_def
                                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    apply(rule out_0assm_assn_tran)
                                    apply(rule entails_tassn_trans)
                                     apply(rule combine_wait_orig_out_0assm2)
                                    subgoal using pre' by auto
                                    subgoal using pre pre'
                                      unfolding proper_def properp_def
                                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    apply(rule out_0assm_assn_tran)
                                    unfolding combine_assn_def entails_tassn_def
                                    apply auto
                                    subgoal for tr tr1 tr2
                                      using pre(1)[of "(Suc k')" kk' "(dis_s(CHR ''t'' := dis_s CHR ''t'' + d))" "(Task WAIT ent tp)"
                                          task_s tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                      using pre(4,5,6,12)[unfolded pre(10,11)] 
                                      using properl_p1
                                      unfolding propc_def proper_def properp_def 
                                      by auto
                                    done
                                  done
                                apply auto
                                unfolding disj_assn_def
                                  apply(rule disjI1)
                                  subgoal premises pre'
                                    thm pre'(13)
                                    apply(rule combine_blocks_assn)
                                       apply(rule pre'(13))
                                      apply(rule pre'(8))
                                     apply(rule pre'(12))
                                    apply(rule entails_tassn_trans)
                                     apply(rule combine_wait_orig_out_0assm2)
                                    subgoal using pre' by auto
                                    subgoal using pre pre'
                                      unfolding proper_def properp_def
                                      by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                                    apply(rule out_0assm_assn_tran)
                                    unfolding combine_assn_def entails_tassn_def
                                    apply auto
                                    subgoal for tr tr1 tr2
                                      using pre(1)[of "(Suc k')" kk' "(dis_s(CHR ''t'' := dis_s CHR ''t'' + d))" "(Task WAIT ent tp)"
                                          task_s tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                                      using pre(4,5,6,12)[unfolded pre(10,11)] 
                                      using properl_p1
                                      unfolding propc_def proper_def properp_def 
                                      by auto
                                    done
                                  done
                                done
                              done
                            apply(simp del:tdsch1'.simps)
                            sorry
                          subgoal
                            sorry
                          subgoal
                            sorry
                          done
                        done
                      sorry
                    subgoal premises pre
                      thm pre
                   using pre(2) pre(3) pre(4) pre(7)
                   apply(simp add: pre(10,11,12,4) del:tdsch1'.simps)
                   apply(erule disjE)
                   subgoal
                     apply(erule disjE)
                     subgoal premises pre'
                       thm pre'
                       apply (simp only:tdsch1'.simps)
                       apply(rule disjI1)
                       apply(rule combine_blocks_assn)
                          apply(rule pre'(3))
                         apply(rule pre'(4))
                        apply(rule pre'(2))
                       apply(rule entails_tassn_trans)
                        apply(rule combine_out_0assm_waitin_assm'1)
                       subgoal by auto
                       subgoal by auto
                       subgoal by auto
                       apply(rule io_orig_assn_tran)
                       apply(subgoal_tac "rp<2 \<and> rn\<noteq>1")
                        prefer 2
                       subgoal using pre(4,5,6,8,9,10,11,12)
                         unfolding proper_def properp_def propc_def
                         by auto
                       apply (simp del: fun_upd_apply)
                       apply(cases "rn \<noteq> -1")
                       subgoal
                         apply (simp del: fun_upd_apply)
                         apply(rule entails_tassn_trans)
                          apply(rule combine_waitin_tguar'_vassm'_out_0assm2)
                         subgoal using pre 
                           unfolding proper_def properp_def propc_def
                           by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                         apply(rule out_0assm_assn_tran)
                         apply(rule entails_tassn_trans)
                          apply(rule combine_waitin_tguar'_vassm'_out_0assm1)
                         subgoal by auto
                         apply(rule io_orig_assn_tran)
                         apply (simp del: fun_upd_apply)
                         unfolding combine_assn_def entails_tassn_def
                         apply clarify
                         subgoal for tr tr1 tr2
                         using pre(1)[of k' kk' dis_s "(Task RUNNING (Suc 0) 2)" "(task_s(CHR ''c'' := up_ent_c ent (task_s CHR ''c'')))" tr1
                                       "(Sch p 1 ((s(CHR ''p'' := 2)) CHR ''p''))" "(s(CHR ''p'' := 2))" tr2 tr]
                         apply auto
                         using pre(4,5,6,12)[unfolded pre(10,11)] 
                         unfolding propc_def proper_def properp_def 
                         by auto
                       done
                     apply (simp del: fun_upd_apply)
                     apply(rule entails_tassn_trans)
                          apply(rule combine_waitin_tguar'_vassm'_out_0assm1)
                         subgoal by auto
                         apply(rule io_orig_assn_tran)
                         apply (simp del: fun_upd_apply)
                         unfolding combine_assn_def entails_tassn_def
                         apply clarify
                         subgoal for tr tr1 tr2
                           using pre(1)[of k' kk' dis_s "(Task RUNNING (Suc 0) 2)" "(task_s(CHR ''c'' := up_ent_c ent (task_s CHR ''c'')))" tr1
                                       "(Sch p 1 ((s(CHR ''p'' := 2)) CHR ''p''))" "(s(CHR ''p'' := 2))" tr2 tr]
                           apply auto
                           using pre(4,5,6,12)[unfolded pre(10,11)] 
                           unfolding propc_def proper_def properp_def 
                           by auto
                         done
                       apply(erule disjE)
                       subgoal premises pre'
                         thm pre'
                         apply (simp only:tdsch1'.simps)
                         apply(rule disjI2)
                         apply(rule disjI1)
                       apply(rule combine_blocks_assn)
                       apply(rule pre'(3))
                         apply(rule pre'(4))
                        apply(rule pre'(2))
                       apply(rule entails_tassn_trans)
                        apply(rule combine_out_0assm_waitin_assm'2)
                       subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                       apply(rule in_0orig_vassm_assn_tran)
                       apply(subgoal_tac "rp<2 \<and> rn\<noteq>1")
                        prefer 2
                       subgoal using pre(4,5,6,8,9,10,11,12)
                         unfolding proper_def properp_def propc_def
                         by auto
                       apply(cases "1\<le>rp")
                       subgoal apply (simp del: fun_upd_apply)
                         unfolding combine_assn_def entails_tassn_def
                         apply clarify
                         subgoal for tr tr1 tr2
                           apply(subgoal_tac "task_dis_assn' 1 (Suc k') dis_s ((Task READY ent 2)) task_s tr1")
                            prefer 2 
                           subgoal using pre by auto
                           apply auto
                           using pre(1)[of "(Suc k')" kk' dis_s "(Task READY ent 2)" task_s tr1 "(Sch (p @ [(1, 2)]) rn rp)" "(s(CHR ''p'' := 1))" tr2 tr]
                           using pre(4,5,6,12)[unfolded pre(10,11)] properl_p1
                           unfolding propc_def proper_def properp_def 
                           by auto
                         done
                       apply (simp del: fun_upd_apply)
                       apply (cases "rn \<noteq> - 1")
                       subgoal
                         apply (simp del: fun_upd_apply)
                         apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_out_0assm2')
                         subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                         subgoal using pre 
                           unfolding proper_def properp_def propc_def
                           by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                         apply(rule out_0assm_assn_tran)
                         apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_out_0assm2')
                         subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                         subgoal using pre 
                           unfolding proper_def properp_def propc_def
                           by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                         apply(rule out_0assm_assn_tran)
                         unfolding combine_assn_def entails_tassn_def
                         apply clarify
                         subgoal for tr tr1 tr2
                           apply(subgoal_tac "task_dis_assn' 1 (Suc k') dis_s ((Task READY ent 2)) task_s tr1")
                            prefer 2 
                           subgoal using pre by auto
                           apply auto
                           using pre(1)[of "(Suc k')" kk' dis_s "(Task READY ent 2)" task_s tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                           using pre(4,5,6,12)[unfolded pre(10,11)] properl_p1
                           unfolding propc_def proper_def properp_def 
                           by auto
                         done
                       apply (simp del: fun_upd_apply)
                         apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_out_0assm2')
                         subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                         subgoal using pre 
                           unfolding proper_def properp_def propc_def
                           by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                         apply(rule out_0assm_assn_tran)
                         unfolding combine_assn_def entails_tassn_def
                         apply clarify
                         subgoal for tr tr1 tr2
                           apply(subgoal_tac "task_dis_assn' 1 (Suc k') dis_s ((Task READY ent 2)) task_s tr1")
                            prefer 2 
                           subgoal using pre by auto
                           apply auto
                           using pre(1)[of "(Suc k')" kk' dis_s "(Task READY ent 2)" task_s tr1 "(Sch p 2 1)" "(s(CHR ''p'' := 1))" tr2 tr]
                           using pre(4,5,6,12)[unfolded pre(10,11)] properl_p1
                           unfolding propc_def proper_def properp_def 
                           by auto
                         done
                       apply(erule disjE)
                        subgoal premises pre'
                         thm pre'
                         apply(rule combine_blocks_assn)
                       apply(rule pre'(3))
                         apply(rule pre'(4))
                          apply(rule pre'(2))
                         apply(rule combine_out_0assm_waitin_assm'3)
                         by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                       apply(erule disjE)
                       subgoal premises pre'
                         thm pre'
                         apply (simp only:tdsch1'.simps)
                         apply(rule disjI2)
                         apply(rule disjI2)
                       apply(rule combine_blocks_assn)
                       apply(rule pre'(3))
                         apply(rule pre'(4))
                        apply(rule pre'(2))
                       apply(rule entails_tassn_trans)
                        apply(rule combine_out_0assm_waitin_assm'2)
                       subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                       apply(rule in_0orig_vassm_assn_tran)
                       apply(simp del:fun_upd_apply)
                       apply(cases "p \<noteq> []")
                       subgoal
                         apply(simp del:fun_upd_apply)
                         apply(rule entails_tassn_trans)
                         apply(rule combine_out_0assm_out_0assm2')
                         subgoal by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                         subgoal apply(cases "get_max p")
                           using properl_p5[of p] pre(6,10) unfolding properp_def proper_def
                           by(auto simp add: req_ch_def preempt_ch_def run_ch_def free_ch_def exit_ch_def dispatch_ch_def)
                         

                           
                                           

                       




                         sorry
                       sorry


                     




                          

                            




                                
                                        
                                    
                                        





                             



            sorry
          done
        done
   qed
      
     
   

end