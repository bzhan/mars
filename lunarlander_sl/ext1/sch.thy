theory sch
  imports task2
begin


definition Pr :: char where "Pr = CHR ''p''"

definition G :: char where "G = CHR ''g''"


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

fun sched_get_max' :: "estate \<Rightarrow> estate" where
  "sched_get_max' (Sch p rn rp) =
    (let (prior, t) = get_max p in Sch (del_proc p t) t prior)"
| "sched_get_max' (Task st ent tp) = undefined"
| "sched_get_max' None = undefined"

lemma sched_get_max_eq:
"sched_get_max e s = sched_get_max' e"
  apply(cases e)
  by auto

fun sched_clear :: "estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_clear (Sch p rn rp) s = Sch [] (-1) (-1)"
| "sched_clear (Task st ent tp) s = undefined"
| "sched_clear None s = undefined"

fun sched_clear' :: "estate \<Rightarrow> estate" where
  "sched_clear' (Sch p rn rp) = Sch [] (-1) (-1)"
| "sched_clear' (Task st ent tp) = undefined"
| "sched_clear' None = undefined"

lemma sched_clear_eq:
"sched_clear e s = sched_clear' e"
  apply(cases e)
  by auto


fun sched_del_proc :: "tid \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate" where
  "sched_del_proc t (Sch p rn rp) s = Sch (del_proc p t) rn rp"
| "sched_del_proc t (Task st ent tp) s = undefined"
| "sched_del_proc t None s = undefined"


fun sched_del_proc' :: "tid \<Rightarrow> estate \<Rightarrow> estate" where
  "sched_del_proc' t (Sch p rn rp) = Sch (del_proc p t) rn rp"
| "sched_del_proc' t (Task st ent tp) = undefined"
| "sched_del_proc' t None = undefined"

lemma sched_del_proc_eq:
"sched_del_proc t e s = sched_del_proc' t e"
  apply(cases e)
  by auto


fun run_now_assign :: "real \<Rightarrow> estate \<Rightarrow> state \<Rightarrow> estate" where
"run_now_assign rn (Sch p n rp) s = (Sch p rn rp)"

fun run_prior_assign :: "estate \<Rightarrow> state \<Rightarrow> estate" where
"run_prior_assign (Sch p n rp) s = (Sch p n (s Pr))"


definition properp :: "tid \<Rightarrow> real \<Rightarrow> bool" where
"properp rn rp = ((rn = 1 \<longleftrightarrow> rp = 2) \<and> (rn = 2 \<longleftrightarrow> rp = 1) \<and> (rn = -1 \<longleftrightarrow> rp = -1) \<and> rp \<in> {-1,1,2} \<and> rn \<in> {-1,1,2})"

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


definition SCH :: "estate proc" where
"SCH = EChoice [(req_ch 1[?]Pr,IF (\<lambda> s. run_prior (fst s) \<ge> (snd s) Pr) THEN Basic (sched_push 1) 
                   ELSE (IF (\<lambda> s. run_now (fst s) = 2) THEN Cm (preempt_ch 2[!](\<lambda>_ . 0)) ELSE Skip FI; Cm (run_ch 1[!](\<lambda>_ . 0));Basic (run_now_assign 1);Basic run_prior_assign) FI),
                (req_ch 2[?]Pr,IF (\<lambda> s. run_prior (fst s) \<ge> (snd s) Pr) THEN Basic (sched_push 2) 
                   ELSE (IF (\<lambda> s. run_now (fst s) = 1) THEN Cm (preempt_ch 1[!](\<lambda>_ . 0)) ELSE Skip FI; Cm (run_ch 2[!](\<lambda>_ . 0));Basic (run_now_assign 2);Basic run_prior_assign) FI),
                (free_ch 1[?]G,IF (\<lambda> s. length (pool (fst s)) > 0) THEN ((Basic sched_get_max);(IF (\<lambda> s. run_now (fst s) = 1)THEN Cm (run_ch 1[!](\<lambda>_.0)) ELSE Cm (run_ch 2[!](\<lambda>_.0)) FI)) 
                   ELSE Basic sched_clear FI),
                (free_ch 2[?]G,IF (\<lambda> s. length (pool (fst s)) > 0) THEN ((Basic sched_get_max);(IF (\<lambda> s. run_now (fst s) = 1)THEN Cm (run_ch 1[!](\<lambda>_.0)) ELSE Cm (run_ch 2[!](\<lambda>_.0)) FI)) 
                   ELSE Basic sched_clear FI),
                (exit_ch 1[?]G,Basic (sched_del_proc 1)),
                (exit_ch 2[?]G,Basic (sched_del_proc 2))]"

definition QQ :: "(real \<times> tid) list \<Rightarrow> tid \<Rightarrow> real \<Rightarrow> state \<Rightarrow> estate assn \<Rightarrow> estate assn"where 
"QQ p rn rp ss P = (\<lambda> s t. (if rp \<ge> 2 then s = (Sch (p @ [(2, 1)]) rn rp,ss(Pr:=2)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 1) 2 ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t 
        else if rn = 2 then s = (Sch p 1 2, ss(Pr:=2)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 1) 2 ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t ((Out0\<^sub>t (preempt_ch 2) 0) @\<^sub>t (Out0\<^sub>t (run_ch 1) 0) \<or>\<^sub>t (Waitp\<^sub>t  ({preempt_ch 2},{})) @\<^sub>t true\<^sub>A \<or>\<^sub>t (Out0\<^sub>t (preempt_ch 2) 0) @\<^sub>t(Waitp\<^sub>t  ({run_ch 1},{})) @\<^sub>t true\<^sub>A)) t 
                        else s = (Sch p 1 2, ss(Pr:=2)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 1) 2 ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t ((Out0\<^sub>t (run_ch 1) 0) \<or>\<^sub>t (Waitp\<^sub>t ({run_ch 1},{})) @\<^sub>t true\<^sub>A )) t)
         \<or> (\<exists> v\<noteq>2. (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 1) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t true\<^sub>A ) t)
                        \<or> (if rp \<ge> 1 then s = (Sch (p @ [(1, 2)]) rn rp,ss(Pr:=1)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 2) 1 ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t 
        else if rn = 1 then s = (Sch p 2 1, ss(Pr:=1)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 2) 1 ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t ((Out0\<^sub>t (preempt_ch 1) 0) @\<^sub>t (Out0\<^sub>t (run_ch 2) 0) \<or>\<^sub>t (Waitp\<^sub>t  ({preempt_ch 1},{})) @\<^sub>t true\<^sub>A \<or>\<^sub>t (Out0\<^sub>t (preempt_ch 1) 0) @\<^sub>t(Waitp\<^sub>t  ({run_ch 2},{})) @\<^sub>t true\<^sub>A)) t 
                        else s = (Sch p 2 1, ss(Pr:=1)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 2) 1 ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t ((Out0\<^sub>t (run_ch 2) 0) \<or>\<^sub>t (Waitp\<^sub>t  ({run_ch 2},{})) @\<^sub>t true\<^sub>A )) t)
         \<or> (\<exists> v\<noteq>1. (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 2) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t true\<^sub>A ) t)
         \<or> (\<exists> v. if length p > 0 then s = (sched_get_max'(Sch p rn rp),ss(G:=v)) 
                    \<and> (if run_now(sched_get_max'(Sch p rn rp)) = 1 
                        then (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 1) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t ((Out0\<^sub>t (run_ch 1) 0) \<or>\<^sub>t (Waitp\<^sub>t  ({run_ch 1},{})) @\<^sub>t true\<^sub>A )) t  
                        else (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 1) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t ((Out0\<^sub>t (run_ch 2) 0) \<or>\<^sub>t (Waitp\<^sub>t  ({run_ch 2},{})) @\<^sub>t true\<^sub>A )) t) 
                  else s = (sched_clear'(Sch p rn rp),ss(G:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 1) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t)
        \<or>  (\<exists> v. if length p > 0 then s = (sched_get_max'(Sch p rn rp),ss(G:=v)) 
                    \<and> (if run_now(sched_get_max'(Sch p rn rp)) = 1 
                        then (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 2) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t ((Out0\<^sub>t (run_ch 1) 0) \<or>\<^sub>t (Waitp\<^sub>t  ({run_ch 1},{})) @\<^sub>t true\<^sub>A )) t  
                        else (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 2) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) @\<^sub>t ((Out0\<^sub>t (run_ch 2) 0) \<or>\<^sub>t (Waitp\<^sub>t  ({run_ch 2},{})) @\<^sub>t true\<^sub>A )) t) 
                  else s = (sched_clear'(Sch p rn rp),ss(G:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 2) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t)
        \<or>  (\<exists> v. s = (sched_del_proc' 1 (Sch p rn rp),ss(G:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (exit_ch 1) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t)
        \<or>  (\<exists> v. s = (sched_del_proc' 2 (Sch p rn rp),ss(G:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (exit_ch 2) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t))"

lemma Sch_Valid_1:
"\<Turnstile> {\<lambda>s t. s = (Sch p rn rp,ss) \<and> P s t}
   SCH
    {\<lambda> s t. QQ p rn rp ss P s t}"
  unfolding  SCH_def
  apply(rule Valid_echoice)
  apply auto
  subgoal for i a p2
    apply(cases i)
    subgoal 
      apply auto
      apply(rule exI[where x="\<lambda> s t. (s = (Sch p rn rp, ss(Pr:=2)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 1) 2 ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t) \<or> 
                                     (\<exists> v\<noteq>2. s = (Sch p rn rp, ss(Pr:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 1) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t)"])

      apply(rule conjI)
      subgoal 
        apply(rule Valid_pre_or)
        subgoal
        apply(rule Valid_strengthen_post)
          prefer 2
           apply(rule Valid_cond_sp)
            apply(rule Valid_basic_sp1)
           apply(rule Valid_seq)
            apply(rule Valid_cond_sp)
             apply(rule Valid_send_sp_assm0)
            apply(rule Valid_skip)
           apply(rule Valid_seq)
            apply(rule Valid_send_sp_assm0)
            apply(rule Valid_seq)
            apply(rule Valid_basic_sp1)
           apply(rule Valid_basic_sp1)
          apply(rule entails_disjE')
          subgoal
            unfolding entails_def
            apply(rule allI)+
            subgoal for s tr
              apply auto
              unfolding QQ_def 
              apply(rule disjI1)
              apply (auto simp add: Pr_def)
              by (metis prod.exhaust_sel)
            done
          subgoal
            unfolding entails_def
            apply(rule allI)+
            subgoal for s tr
              apply auto
              unfolding QQ_def 
              apply(rule disjI1)
              apply(cases s)
              apply (auto simp add: Pr_def pure_assn_def conj_assn_def join_assn_def)
              subgoal for tr2 tr1b tr2a tr2b
                apply(rule exI[where x=tr1b])
                apply auto
                apply(rule exI[where x=tr2b])
                apply auto
                unfolding disj_assn_def
                apply(erule disjE)
                subgoal 
                  apply(erule disjE)
                  subgoal by auto
                  subgoal 
                    apply(rule disjI2)
                    apply(rule disjI1)
                    by(auto simp add: true_assn_def)
                  done
                subgoal
                apply(erule disjE)
                  subgoal
                    apply(rule disjI2)
                    apply(rule disjI2)
                    by(auto simp add: true_assn_def)
                  subgoal
                    apply(rule disjI2)
                    apply(rule disjI1)
                    by(auto simp add: true_assn_def)
                  done
                done
              subgoal for tr2 tr1a tr2a
                apply(rule exI[where x=tr1a])
                by auto
              done
            done
          done
        subgoal
          apply(rule Valid_ex_pre)
          subgoal for v
          apply(rule Valid_weaken_pre[where P'="\<lambda> s t. (\<up>(v\<noteq>2) \<and>\<^sub>t (P (Sch p rn rp, ss)) @\<^sub>t
                    Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 1) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))t"])
          subgoal
            unfolding entails_def pure_assn_def conj_assn_def
            by auto
          subgoal
            apply(rule Valid_strengthen_post)
             prefer 2
             apply(rule Valid_true)
            unfolding QQ_def
            apply(rule entails_disjI2')
            unfolding entails_def
            by (auto simp add:pure_assn_def conj_assn_def join_assoc)
          done
        done
      done
      apply(rule conjI)
      subgoal unfolding entails_def
        apply(rule allI)+
        subgoal for s tr
          apply(rule impI)
          apply simp
          apply(rule allI)
          subgoal for v
            apply(cases "v=2")
            subgoal apply(rule disjI1)
              apply auto
              apply(auto simp add:join_assn_def) 
              using inrdy_assn.intros(1) by blast
            subgoal apply(rule disjI2)
              apply auto
              apply(rule exI[where x=v])
              apply simp
              apply(auto simp add:join_assn_def) 
              using inrdy_assn.intros(1) by blast
            done
          done
        done
      subgoal unfolding entails_def
        apply(rule allI)+
        subgoal for s tr
          apply(rule impI)
          apply simp
          apply(rule allI)
          subgoal for d
          apply(rule impI)
          apply(rule allI)
          subgoal for v
            apply(cases "v=2")
            subgoal apply(rule disjI1)
              apply auto
              apply(auto simp add:join_assn_def) 
              using inrdy_assn.intros(2) by blast
            subgoal apply(rule disjI2)
              apply auto
              apply(rule exI[where x=v])
              apply simp
              apply(auto simp add:join_assn_def) 
              using inrdy_assn.intros(2) by blast
            done
          done
        done
      done
    done
  subgoal for i'
    apply(cases i')
    subgoal
      apply auto
      apply(rule exI[where x="\<lambda> s t. (s = (Sch p rn rp, ss(Pr:=1)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 2) 1 ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t) \<or> 
                                     (\<exists> v\<noteq>1. s = (Sch p rn rp, ss(Pr:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 2) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t)"])
      apply(rule conjI)
      subgoal 
        apply(rule Valid_pre_or)
        subgoal
        apply(rule Valid_strengthen_post)
          prefer 2
           apply(rule Valid_cond_sp)
            apply(rule Valid_basic_sp1)
           apply(rule Valid_seq)
            apply(rule Valid_cond_sp)
             apply(rule Valid_send_sp_assm0)
            apply(rule Valid_skip)
           apply(rule Valid_seq)
            apply(rule Valid_send_sp_assm0)
            apply(rule Valid_seq)
            apply(rule Valid_basic_sp1)
           apply(rule Valid_basic_sp1)
          apply(rule entails_disjE')
          subgoal
            unfolding entails_def
            apply(rule allI)+
            subgoal for s tr
              apply auto
              unfolding QQ_def 
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI1)
              apply (auto simp add: Pr_def)
              by (metis prod.exhaust_sel)
            done
          subgoal
            unfolding entails_def
            apply(rule allI)+
            subgoal for s tr
              apply auto
              unfolding QQ_def 
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI1)
              apply(cases s)
              apply (auto simp add: Pr_def pure_assn_def conj_assn_def join_assn_def)
              subgoal for tr2 tr1b tr2a tr2b
                apply(rule exI[where x=tr1b])
                apply auto
                apply(rule exI[where x=tr2b])
                apply auto
                unfolding disj_assn_def
                apply(erule disjE)
                subgoal 
                  apply(erule disjE)
                  subgoal by auto
                  subgoal 
                    apply(rule disjI2)
                    apply(rule disjI1)
                    by(auto simp add: true_assn_def)
                  done
                subgoal
                apply(erule disjE)
                  subgoal
                    apply(rule disjI2)
                    apply(rule disjI2)
                    by(auto simp add: true_assn_def)
                  subgoal
                    apply(rule disjI2)
                    apply(rule disjI1)
                    by(auto simp add: true_assn_def)
                  done
                done
              subgoal for tr2 tr1a tr2a
                apply(rule exI[where x=tr1a])
                by auto
              done
            done
          done
        subgoal
          apply(rule Valid_ex_pre)
          subgoal for v
          apply(rule Valid_weaken_pre[where P'="\<lambda> s t. (\<up>(v\<noteq>1) \<and>\<^sub>t (P (Sch p rn rp, ss)) @\<^sub>t
                    Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 2) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))t"])
          subgoal
            unfolding entails_def pure_assn_def conj_assn_def
            by auto
          subgoal
            apply(rule Valid_strengthen_post)
             prefer 2
             apply(rule Valid_true)
            unfolding QQ_def
            apply(rule entails_disjI2')
            unfolding entails_def
            by (auto simp add:pure_assn_def conj_assn_def join_assoc)
          done
        done
      done
      apply(rule conjI)
      subgoal unfolding entails_def
        apply(rule allI)+
        subgoal for s tr
          apply(rule impI)
          apply simp
          apply(rule allI)
          subgoal for v
            apply(cases "v=1")
            subgoal apply(rule disjI1)
              apply auto
              apply(auto simp add:join_assn_def) 
              using inrdy_assn.intros(1) by blast
            subgoal apply(rule disjI2)
              apply auto
              apply(rule exI[where x=v])
              apply simp
              apply(auto simp add:join_assn_def) 
              using inrdy_assn.intros(1) by blast
            done
          done
        done
      subgoal unfolding entails_def
        apply(rule allI)+
        subgoal for s tr
          apply(rule impI)
          apply simp
          apply(rule allI)
          subgoal for d
          apply(rule impI)
          apply(rule allI)
          subgoal for v
            apply(cases "v=1")
            subgoal apply(rule disjI1)
              apply auto
              apply(auto simp add:join_assn_def) 
              using inrdy_assn.intros(2) by blast
            subgoal apply(rule disjI2)
              apply auto
              apply(rule exI[where x=v])
              apply simp
              apply(auto simp add:join_assn_def) 
              using inrdy_assn.intros(2) by blast
            done
          done
        done
      done
    done
  subgoal for i''
    apply(cases i'')
    subgoal
      apply auto
      apply(rule exI[where x="\<lambda> s t. (\<exists> v. s = (Sch p rn rp, ss(G:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 1) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t)"])
      apply(rule conjI)
      subgoal 
        apply(rule Valid_strengthen_post)
        prefer 2
         apply(rule Valid_cond_sp)
          apply(rule Valid_seq)
           apply(rule Valid_basic_sp1)
          apply(rule Valid_cond_sp)
           apply(rule Valid_send_sp_assm0)
          apply(rule Valid_send_sp_assm0)
         apply(rule Valid_basic_sp1)
        apply(rule entails_disjE')
         apply(rule entails_disjE')
        subgoal
          unfolding QQ_def entails_def
          apply(rule allI)+
          apply(rule impI)
          subgoal for s tr
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            apply (auto simp add: pure_assn_def conj_assn_def join_assn_def disj_assn_def)
            subgoal for v tr2 tr1a tr2a
              apply(cases s)
              apply(rule exI[where x=v])
              by auto
            subgoal for v tr1a tr2a tr1b tr2b
              apply(cases s)
              apply(rule exI[where x=v])
              apply (auto simp add:true_assn_def)
              apply(rule exI[where x=tr1a])
              apply (auto simp add:true_assn_def)
              done
            done
          done
        subgoal
          unfolding QQ_def entails_def
          apply(rule allI)+
          apply(rule impI)
          subgoal for s tr
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            apply (auto simp add: pure_assn_def conj_assn_def join_assn_def disj_assn_def)
            subgoal for v tr2 tr1a tr2a
              apply(cases s)
              apply(rule exI[where x=v])
              by auto
            subgoal for v tr1a tr2a tr1b tr2b
              apply(cases s)
              apply(rule exI[where x=v])
              apply (auto simp add:true_assn_def)
              apply(rule exI[where x=tr1a])
              apply (auto simp add:true_assn_def)
              done
            done
          done
        subgoal
          unfolding QQ_def entails_def
          apply(rule allI)+
          apply(rule impI)
          subgoal for s tr
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            apply (auto simp add: pure_assn_def conj_assn_def join_assn_def disj_assn_def)
            subgoal for v tr1 tr2
              apply(cases s)
              apply(rule exI[where x=v])
              by auto
            done
          done
        done
      apply(rule conjI)
      subgoal unfolding entails_def
        apply(rule allI)+
        apply(rule impI)
        apply auto
        by (metis (no_types, opaque_lifting) inrdy_assn.intros(1) join_assn_def)
      subgoal unfolding entails_def
        apply(rule allI)+
        apply(rule impI)
        apply auto
        subgoal for tr d v
          apply(rule exI[where x=v])
          apply (auto simp add:join_assn_def)
          apply(rule exI[where x=tr])
          apply auto
          apply(rule )
          by auto
        done
      done
    subgoal for i'''
      apply(cases i''')
    subgoal
      apply auto
      apply(rule exI[where x="\<lambda> s t. (\<exists> v. s = (Sch p rn rp, ss(G:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 2) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t)"])
      apply(rule conjI)
      subgoal 
        apply(rule Valid_strengthen_post)
        prefer 2
         apply(rule Valid_cond_sp)
          apply(rule Valid_seq)
           apply(rule Valid_basic_sp1)
          apply(rule Valid_cond_sp)
           apply(rule Valid_send_sp_assm0)
          apply(rule Valid_send_sp_assm0)
         apply(rule Valid_basic_sp1)
        apply(rule entails_disjE')
         apply(rule entails_disjE')
        subgoal
          unfolding QQ_def entails_def
          apply(rule allI)+
          apply(rule impI)
          subgoal for s tr
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            apply (auto simp add: pure_assn_def conj_assn_def join_assn_def disj_assn_def)
            subgoal for v tr2 tr1a tr2a
              apply(cases s)
              apply(rule exI[where x=v])
              by auto
            subgoal for v tr1a tr2a tr1b tr2b
              apply(cases s)
              apply(rule exI[where x=v])
              apply (auto simp add:true_assn_def)
              apply(rule exI[where x=tr1a])
              apply (auto simp add:true_assn_def)
              done
            done
          done
        subgoal
          unfolding QQ_def entails_def
          apply(rule allI)+
          apply(rule impI)
          subgoal for s tr
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            apply (auto simp add: pure_assn_def conj_assn_def join_assn_def disj_assn_def)
            subgoal for v tr2 tr1a tr2a
              apply(cases s)
              apply(rule exI[where x=v])
              by auto
            subgoal for v tr1a tr2a tr1b tr2b
              apply(cases s)
              apply(rule exI[where x=v])
              apply (auto simp add:true_assn_def)
              apply(rule exI[where x=tr1a])
              apply (auto simp add:true_assn_def)
              done
            done
          done
        subgoal
          unfolding QQ_def entails_def
          apply(rule allI)+
          apply(rule impI)
          subgoal for s tr
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            apply (auto simp add: pure_assn_def conj_assn_def join_assn_def disj_assn_def)
            subgoal for v tr1 tr2
              apply(cases s)
              apply(rule exI[where x=v])
              by auto
            done
          done
        done
      apply(rule conjI)
      subgoal unfolding entails_def
        apply(rule allI)+
        apply(rule impI)
        apply auto
        by (metis (no_types, opaque_lifting) inrdy_assn.intros(1) join_assn_def)
      subgoal unfolding entails_def
        apply(rule allI)+
        apply(rule impI)
        apply auto
        subgoal for tr d v
          apply(rule exI[where x=v])
          apply (auto simp add:join_assn_def)
          apply(rule exI[where x=tr])
          apply auto
          apply(rule )
          by auto
        done
      done
    subgoal for i''''
      apply(cases i'''')
      subgoal
        apply auto
        apply(rule exI[where x="\<lambda> s t. (\<exists> v. s = (Sch p rn rp, ss(G:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (exit_ch 1) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t)"])
        apply(rule conjI)
        subgoal
          apply(rule Valid_ex_pre)
          apply(rule Valid_strengthen_post)
           prefer 2
           apply(rule Valid_basic_sp1)
          apply auto
          unfolding QQ_def entails_def
          apply(rule allI)+
          apply(rule impI)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI1)
          by auto
        apply(rule conjI)
        subgoal
          unfolding entails_def
          apply auto
          by (metis inrdy_assn.intros(1) join_assn_def)
        subgoal
          unfolding entails_def
          apply (auto simp add:join_assn_def)
          subgoal for tr d v
            apply(rule exI[where x=v])
            apply auto
            apply(rule exI[where x=tr])
            apply auto
            apply(rule ) by auto
          done
        done
      subgoal for i'''''
        subgoal
        apply auto
        apply(rule exI[where x="\<lambda> s t. (\<exists> v. s = (Sch p rn rp, ss(G:=v)) \<and> (P (Sch p rn rp, ss) @\<^sub>t (Inrdy\<^sub>t (Sch p rn rp, ss) (exit_ch 2) v ({},{req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}))) t)"])
        apply(rule conjI)
        subgoal
          apply(rule Valid_ex_pre)
          apply(rule Valid_strengthen_post)
           prefer 2
           apply(rule Valid_basic_sp1)
          apply auto
          unfolding QQ_def entails_def
          apply(rule allI)+
          apply(rule impI)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI2)
          apply(rule disjI2)
          by auto
        apply(rule conjI)
        subgoal
          unfolding entails_def
          apply auto
          by (metis inrdy_assn.intros(1) join_assn_def)
        subgoal
          unfolding entails_def
          apply (auto simp add:join_assn_def)
          subgoal for tr d v
            apply(rule exI[where x=v])
            apply auto
            apply(rule exI[where x=tr])
            apply auto
            apply(rule ) by auto
          done
        done
      done
    done
  done
  done
  done
  done
  done

            
fun SCH_tr:: "nat \<Rightarrow> estate ext_state \<Rightarrow> estate tassn" where
  "SCH_tr 0 (Sch p rn rp,ss)  = emp\<^sub>t" 
| "SCH_tr (Suc k) (Sch p rn rp,ss) = (
   (Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 1) 2
               ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) 
              @\<^sub>t (if rp \<ge> 2 then SCH_tr k (Sch (p @ [(2, 1)]) rn rp,ss(Pr := 2)) 
               else if rn = 2 then Out0\<^sub>t (preempt_ch 2) 0 @\<^sub>t Out0\<^sub>t (run_ch 1) 0 @\<^sub>t SCH_tr k (Sch p 1 2,ss(Pr := 2)) \<or>\<^sub>t
                                     Waitp\<^sub>t  ({preempt_ch 2}, {}) @\<^sub>t true\<^sub>A \<or>\<^sub>t
                                      Out0\<^sub>t (preempt_ch 2) 0 @\<^sub>t Waitp\<^sub>t  ({run_ch 1}, {}) @\<^sub>t true\<^sub>A 
                              else Out0\<^sub>t (run_ch 1) 0 @\<^sub>t SCH_tr k (Sch p 1 2,ss(Pr := 2))\<or>\<^sub>t
                                     Waitp\<^sub>t ({run_ch 1}, {}) @\<^sub>t true\<^sub>A)
 \<or>\<^sub>t(\<exists>\<^sub>t v. \<up>(v\<noteq>2) \<and>\<^sub>t  Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 1) v ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t true\<^sub>A ) 
 \<or>\<^sub>t(Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 2) 1
               ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2})) 
              @\<^sub>t (if rp \<ge> 1 then SCH_tr k (Sch (p @ [(1, 2)]) rn rp,ss(Pr := 1)) 
               else if rn = 1 then Out0\<^sub>t (preempt_ch 1) 0 @\<^sub>t Out0\<^sub>t (run_ch 2) 0 @\<^sub>t SCH_tr k (Sch p 2 1,ss(Pr := 1)) \<or>\<^sub>t
                                     Waitp\<^sub>t  ({preempt_ch 1}, {}) @\<^sub>t true\<^sub>A \<or>\<^sub>t
                                      Out0\<^sub>t (preempt_ch 1) 0 @\<^sub>t Waitp\<^sub>t  ({run_ch 2}, {}) @\<^sub>t true\<^sub>A 
                              else Out0\<^sub>t (run_ch 2) 0 @\<^sub>t SCH_tr k (Sch p 2 1,ss(Pr := 1))\<or>\<^sub>t
                                     Waitp\<^sub>t ({run_ch 2}, {}) @\<^sub>t true\<^sub>A)
  \<or>\<^sub>t(\<exists>\<^sub>t v. \<up>(v\<noteq>1) \<and>\<^sub>t  Inrdy\<^sub>t (Sch p rn rp, ss) (req_ch 2) v ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t true\<^sub>A ) 
  \<or>\<^sub>t(\<exists>\<^sub>t v. Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 1) v ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t 
          (if length p > 0 then if run_now (sched_get_max' (Sch p rn rp)) = 1 
                                then  (Out0\<^sub>t (run_ch 1) 0 @\<^sub>t SCH_tr k (sched_get_max' (Sch p rn rp), ss(G := v)) \<or>\<^sub>t
                                       Waitp\<^sub>t  ({run_ch 1}, {}) @\<^sub>t true\<^sub>A)
                                else  (Out0\<^sub>t (run_ch 2) 0 @\<^sub>t SCH_tr k (sched_get_max' (Sch p rn rp), ss(G := v)) \<or>\<^sub>t
                                       Waitp\<^sub>t  ({run_ch 2}, {}) @\<^sub>t true\<^sub>A)
                           else SCH_tr k (sched_clear' (Sch p rn rp), ss(G := v))))
  \<or>\<^sub>t(\<exists>\<^sub>t v. Inrdy\<^sub>t (Sch p rn rp, ss) (free_ch 2) v ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) @\<^sub>t 
          (if length p > 0 then if run_now (sched_get_max' (Sch p rn rp)) = 1 
                                then  (Out0\<^sub>t (run_ch 1) 0 @\<^sub>t SCH_tr k (sched_get_max' (Sch p rn rp), ss(G := v)) \<or>\<^sub>t
                                       Waitp\<^sub>t  ({run_ch 1}, {}) @\<^sub>t true\<^sub>A)
                                else  (Out0\<^sub>t (run_ch 2) 0 @\<^sub>t SCH_tr k (sched_get_max' (Sch p rn rp), ss(G := v)) \<or>\<^sub>t
                                       Waitp\<^sub>t  ({run_ch 2}, {}) @\<^sub>t true\<^sub>A)
                           else SCH_tr k (sched_clear' (Sch p rn rp), ss(G := v))))
  \<or>\<^sub>t(\<exists>\<^sub>t v. Inrdy\<^sub>t (Sch p rn rp, ss) (exit_ch 1) v ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) 
                             @\<^sub>t SCH_tr k (sched_del_proc' 1 (Sch p rn rp), ss(G := v)))
  \<or>\<^sub>t(\<exists>\<^sub>t v. Inrdy\<^sub>t (Sch p rn rp, ss) (exit_ch 2) v ({}, {req_ch 1, req_ch 2, free_ch 1, free_ch 2, exit_ch 1, exit_ch 2}) 
                             @\<^sub>t SCH_tr k (sched_del_proc' 2 (Sch p rn rp), ss(G := v)))
)"
  



lemma Valid_SCH_rep:
  "\<Turnstile> {\<lambda>s t. s = (Sch p rn rp,ss) \<and> emp\<^sub>t t}
                      Rep SCH
      {\<lambda>s t. (\<exists>n. (emp\<^sub>t @\<^sub>t SCH_tr n (Sch p rn rp,ss)) t)}"
apply(rule Valid_rep'')
  subgoal for n P
    apply(induction n arbitrary:P p rn rp ss)
    subgoal for P
      apply auto
      apply(rule Valid_strengthen_post)
       prefer 2
       apply(rule Valid_skip)
      unfolding entails_def by auto
    subgoal premises pre for n P p rn rp ss
      subgoal
        unfolding RepN.simps
        apply(rule Valid_seq)
         apply(rule Sch_Valid_1)
        thm pre
        unfolding QQ_def
        apply(rule Valid_pre_or)
        subgoal
          apply(cases "2\<le>rp")
          subgoal 
            apply(rule Valid_strengthen_post)
             prefer 2
             apply simp
             apply(rule pre)
            apply(simp only:join_assoc)
            apply(rule tassn_to_assn)
            apply(rule entails_tassn_cancel_left)
            unfolding entails_tassn_def
            apply(rule allI)
            apply(rule impI)
            unfolding disj_assn_def SCH_tr.simps
            apply(rule disjI1)
            by auto
          apply(cases "rn = 2")
          subgoal 
            apply(rule Valid_strengthen_post)
             prefer 2
             apply simp
             apply(rule pre)
            apply(simp only:join_assoc)
            apply(rule tassn_to_assn)
            apply(rule entails_tassn_cancel_left)
            unfolding entails_tassn_def
            apply(rule allI)
            apply(rule impI)
            unfolding disj_assn_def SCH_tr.simps
            apply(rule disjI1)
            apply (auto simp add:join_assn_def true_assn_def)
            subgoal by metis
            subgoal by metis
            subgoal by metis
            done
          subgoal 
            apply(rule Valid_strengthen_post)
             prefer 2
             apply simp
             apply(rule pre)
            apply(simp only:join_assoc)
            apply(rule tassn_to_assn)
            apply(rule entails_tassn_cancel_left)
            unfolding entails_tassn_def
            apply(rule allI)
            apply(rule impI)
            unfolding disj_assn_def SCH_tr.simps
            apply(rule disjI1)
            apply (auto simp add:join_assn_def true_assn_def)
            by metis
          done
        apply(rule Valid_pre_or)
        subgoal
          apply(rule Valid_ex_pre)
          apply(rule Valid_strengthen_post)
          prefer 2
           apply(rule Valid_true)
          subgoal for v
            apply(rule tassn_to_assn)
            apply (simp del:SCH_tr.simps add:join_assoc)
            apply(rule impI)
            apply(rule entails_tassn_cancel_left)
            unfolding entails_tassn_def
            apply(rule allI)
            apply(rule impI)
            unfolding disj_assn_def SCH_tr.simps
            apply(rule disjI2)
            apply(rule disjI1)
            by (auto simp add:join_assn_def true_assn_def ex_assn_def pure_assn_def conj_assn_def)
          done
        apply(rule Valid_pre_or)
        subgoal
          apply(cases "1\<le>rp")
          subgoal 
            apply(rule Valid_strengthen_post)
             prefer 2
             apply simp
             apply(rule pre)
            apply(simp only:join_assoc)
            apply(rule tassn_to_assn)
            apply(rule entails_tassn_cancel_left)
            unfolding entails_tassn_def
            apply(rule allI)
            apply(rule impI)
            unfolding disj_assn_def SCH_tr.simps
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            by auto
          apply(cases "rn = 1")
          subgoal 
            apply(rule Valid_strengthen_post)
             prefer 2
             apply simp
             apply(rule pre)
            apply(simp only:join_assoc)
            apply(rule tassn_to_assn)
            apply(rule entails_tassn_cancel_left)
            unfolding entails_tassn_def
            apply(rule allI)
            apply(rule impI)
            unfolding disj_assn_def SCH_tr.simps
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            apply (auto simp add:join_assn_def true_assn_def)
            subgoal by metis
            subgoal by metis
            subgoal by metis
            done
          subgoal 
            apply(rule Valid_strengthen_post)
             prefer 2
             apply simp
             apply(rule pre)
            apply(simp only:join_assoc)
            apply(rule tassn_to_assn)
            apply(rule entails_tassn_cancel_left)
            unfolding entails_tassn_def
            apply(rule allI)
            apply(rule impI)
            unfolding disj_assn_def SCH_tr.simps
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            apply (auto simp add:join_assn_def true_assn_def)
            by metis
          done
        apply(rule Valid_pre_or)
        subgoal
          apply(rule Valid_ex_pre)
          apply(rule Valid_strengthen_post)
          prefer 2
           apply(rule Valid_true)
          subgoal for v
            apply(rule tassn_to_assn)
            apply (simp del:SCH_tr.simps add:join_assoc)
            apply(rule impI)
            apply(rule entails_tassn_cancel_left)
            unfolding entails_tassn_def
            apply(rule allI)
            apply(rule impI)
            unfolding disj_assn_def SCH_tr.simps
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI2)
            apply(rule disjI1)
            by (auto simp add:join_assn_def true_assn_def ex_assn_def pure_assn_def conj_assn_def)
          done
        apply(rule Valid_pre_or)
        subgoal
          apply(rule Valid_ex_pre)
          subgoal for v
          apply(cases "length p > 0")
            subgoal
              apply(cases "run_now (sched_get_max' (Sch p rn rp)) = 1")
              subgoal
                apply (simp del: SCH_tr.simps)
                 apply(cases "get_max p")
                subgoal for pp tt
                  apply (simp del: SCH_tr.simps)
                  apply(rule Valid_strengthen_post)
                   prefer 2
                   apply(rule pre)
                  apply(rule tassn_to_assn)
                  apply(simp del: SCH_tr.simps add: join_assoc)
                  apply(rule entails_tassn_cancel_left)
                  unfolding entails_tassn_def
                  apply(rule allI)
                  apply(rule impI)
                  unfolding disj_assn_def SCH_tr.simps
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI1)
                  apply (auto simp add:join_assn_def true_assn_def ex_assn_def pure_assn_def conj_assn_def)
                  subgoal by metis
                  subgoal by metis
                  done
                done
              subgoal
                apply (simp del: SCH_tr.simps)
                 apply(cases "get_max p")
                subgoal for pp tt
                  apply (simp del: SCH_tr.simps)
                  apply(rule Valid_strengthen_post)
                   prefer 2
                   apply(rule pre)
                  apply(rule tassn_to_assn)
                  apply(simp del: SCH_tr.simps add: join_assoc)
                  apply(rule entails_tassn_cancel_left)
                  unfolding entails_tassn_def
                  apply(rule allI)
                  apply(rule impI)
                  unfolding disj_assn_def SCH_tr.simps
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI1)
                  apply (auto simp add:join_assn_def true_assn_def ex_assn_def pure_assn_def conj_assn_def)
                  subgoal by metis
                  subgoal by metis
                  done
                done
              done
            subgoal
              apply (simp del: SCH_tr.simps)
              apply(rule Valid_strengthen_post)
              prefer 2
              apply(rule pre)
              apply(rule tassn_to_assn)
              apply(simp del: SCH_tr.simps add: join_assoc)
              apply(rule entails_tassn_cancel_left)
              unfolding entails_tassn_def
              apply(rule allI)
              apply(rule impI)
              unfolding disj_assn_def SCH_tr.simps
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI1)
              by(auto simp add: ex_assn_def)
            done
          done
        apply(rule Valid_pre_or)
        subgoal
          apply(rule Valid_ex_pre)
          subgoal for v
          apply(cases "length p > 0")
            subgoal
              apply(cases "run_now (sched_get_max' (Sch p rn rp)) = 1")
              subgoal
                apply (simp del: SCH_tr.simps)
                 apply(cases "get_max p")
                subgoal for pp tt
                  apply (simp del: SCH_tr.simps)
                  apply(rule Valid_strengthen_post)
                   prefer 2
                   apply(rule pre)
                  apply(rule tassn_to_assn)
                  apply(simp del: SCH_tr.simps add: join_assoc)
                  apply(rule entails_tassn_cancel_left)
                  unfolding entails_tassn_def
                  apply(rule allI)
                  apply(rule impI)
                  unfolding disj_assn_def SCH_tr.simps
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply (auto simp add:join_assn_def true_assn_def ex_assn_def pure_assn_def conj_assn_def)
                  subgoal by metis
                  subgoal by metis
                  done
                done
              subgoal
                apply (simp del: SCH_tr.simps)
                 apply(cases "get_max p")
                subgoal for pp tt
                  apply (simp del: SCH_tr.simps)
                  apply(rule Valid_strengthen_post)
                   prefer 2
                   apply(rule pre)
                  apply(rule tassn_to_assn)
                  apply(simp del: SCH_tr.simps add: join_assoc)
                  apply(rule entails_tassn_cancel_left)
                  unfolding entails_tassn_def
                  apply(rule allI)
                  apply(rule impI)
                  unfolding disj_assn_def SCH_tr.simps
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI2)
                  apply(rule disjI1)
                  apply (auto simp add:join_assn_def true_assn_def ex_assn_def pure_assn_def conj_assn_def)
                  subgoal by metis
                  subgoal by metis
                  done
                done
              done
            subgoal
              apply (simp del: SCH_tr.simps)
              apply(rule Valid_strengthen_post)
              prefer 2
              apply(rule pre)
              apply(rule tassn_to_assn)
              apply(simp del: SCH_tr.simps add: join_assoc)
              apply(rule entails_tassn_cancel_left)
              unfolding entails_tassn_def
              apply(rule allI)
              apply(rule impI)
              unfolding disj_assn_def SCH_tr.simps
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI1)
              by(auto simp add: ex_assn_def)
            done
          done
        apply(rule Valid_pre_or)
        subgoal
          apply(rule Valid_ex_pre)
          subgoal for v
            apply (simp del: SCH_tr.simps)
            apply(rule Valid_strengthen_post)
              prefer 2
              apply(rule pre)
              apply(rule tassn_to_assn)
              apply(simp del: SCH_tr.simps add: join_assoc)
              apply(rule entails_tassn_cancel_left)
              unfolding entails_tassn_def
              apply(rule allI)
              apply(rule impI)
              unfolding disj_assn_def SCH_tr.simps
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI1)
              by(auto simp add: ex_assn_def)
            done
          subgoal
          apply(rule Valid_ex_pre)
          subgoal for v
            apply (simp del: SCH_tr.simps)
            apply(rule Valid_strengthen_post)
              prefer 2
              apply(rule pre)
              apply(rule tassn_to_assn)
              apply(simp del: SCH_tr.simps add: join_assoc)
              apply(rule entails_tassn_cancel_left)
              unfolding entails_tassn_def
              apply(rule allI)
              apply(rule impI)
              unfolding disj_assn_def SCH_tr.simps
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              apply(rule disjI2)
              by(auto simp add: ex_assn_def)
            done
          done
        done
      done
    done



        




end