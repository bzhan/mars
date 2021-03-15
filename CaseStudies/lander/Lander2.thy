
theory Lander2
    imports HHLProver.ContinuousInv  HHLProver.BigStepParallel
begin

text \<open>Variables\<close>

definition Fc :: char where "Fc = CHR ''a''"
definition M :: char where "M = CHR ''b''"
definition V :: char where "V = CHR ''c''"
definition T :: char where "T = CHR ''d''"
definition W :: char where "W = CHR ''e''"

definition Period :: real where "Period = 0.128"


lemma train_vars_distinct [simp]: "T \<noteq> V" "T \<noteq> W"  
                                  "V \<noteq> T" "V \<noteq> W" 
                                  "W \<noteq> T" "W \<noteq> V" 
  unfolding T_def V_def W_def by auto

definition W_upd :: "real \<Rightarrow> real \<Rightarrow> real" where
  "W_upd v w = (-(w - 3.732) * 0.01 + 3.732 - (v - (-1.5)) * 0.6)"

text \<open>Processes\<close>

(*
    Fc ::= (\<lambda>_. 2835);
*)
definition P0 :: proc where
  "P0 =
    Rep (
      Wait (\<lambda>_. Period);
      Cm (''ch_v''[?]V);
      Cm (''ch_m''[?]W);
      Cm (''ch_Fc''[!](\<lambda>s. W_upd (s V) (s W)))
    )"

(*
    V ::= (\<lambda>_. -1.5);
    M ::= (\<lambda>_. 759.5);
*)


fun P0_inv :: "real \<times> real \<Rightarrow> (real\<times> real) list \<Rightarrow> tassn" where
  "P0_inv (v, w) [] = emp\<^sub>t"
| "P0_inv (v, w) ((v', w') # vwrest) = 
   WaitS\<^sub>t Period (\<lambda>t. (\<lambda>_. 0)(V := v, W := w)) ({}, {}) @\<^sub>t
   In\<^sub>t ((\<lambda>_. 0)(V := v, W := w)) ''ch_v'' v' @\<^sub>t 
   In\<^sub>t ((\<lambda>_. 0)(V := v', W := w)) ''ch_m'' w' @\<^sub>t 
   Out\<^sub>t ((\<lambda>_. 0)(V := v', W := w')) ''ch_Fc'' (W_upd v' w') @\<^sub>t
   P0_inv (v', w') (vwrest)"

fun last_P0_inv :: "real \<times> real \<Rightarrow> (real\<times> real) list \<Rightarrow> real\<times>real" where
  "last_P0_inv (v, w) [] = (v, w)"
| "last_P0_inv (v, w) ((v', w') # vwrest) = last_P0_inv (v', w') vwrest"

lemma P0_inv_snoc:
  "P0_inv (v, w) (vwlist @ [(v', w')]) =
   P0_inv (v, w) vwlist @\<^sub>t WaitS\<^sub>t Period (\<lambda>t. (\<lambda>_. 0)(V := fst(last_P0_inv (v, w) vwlist), W := snd(last_P0_inv (v, w) vwlist))) ({}, {}) @\<^sub>t
   In\<^sub>t ((\<lambda>_. 0)(V := fst(last_P0_inv (v, w) vwlist), W := snd(last_P0_inv (v, w) vwlist))) ''ch_v'' v' @\<^sub>t 
   In\<^sub>t ((\<lambda>_. 0)(V := v', W := snd(last_P0_inv (v, w) vwlist))) ''ch_m'' w' @\<^sub>t 
   Out\<^sub>t ((\<lambda>_. 0)(V := v', W := w')) ''ch_Fc'' (W_upd v' w')"
  apply (induct vwlist arbitrary: v w)
  by (auto simp add: join_assoc)


lemma last_P0_inv_snoc [simp]:
  "last_P0_inv (v, w) (vwlist @ [(v', w')]) = (v', w')"
  apply (induct vwlist arbitrary: v w) by auto

lemma P0_rep:
  "\<Turnstile>
    {\<lambda>s tr. s = (\<lambda>_. 0)(V := v, W := w) \<and> emp\<^sub>t tr}
      P0
    {\<lambda>s tr. \<exists>vwlist. s = (\<lambda>_. 0)(V := fst(last_P0_inv (v, w) vwlist), W := snd(last_P0_inv (v, w) vwlist)) \<and> P0_inv (v, w) vwlist tr}"
  apply (rule Valid_weaken_pre)
  unfolding P0_def
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for vwlist
    apply (rule Valid_seq)
    apply (rule Valid_wait_sp) apply (auto simp add:Period_def)
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp)
    apply (rule Valid_ex_pre)
    subgoal for v'
       apply (rule Valid_seq)
        apply (rule Valid_receive_sp)
      apply (rule Valid_ex_pre)
      subgoal for w'
        apply (rule Valid_strengthen_post)
        prefer 2 apply (rule Valid_send_sp)
      apply (auto simp add: entails_def)
      apply (rule exI[where x="vwlist@[(v',w')]"])
        apply (auto simp add: P0_inv_snoc join_assoc Period_def)
        by (simp add: fun_upd_twist)
      done
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

definition P1 :: proc where
  "P1 =
    Rep (
      Interrupt (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))) ((\<lambda>_. True))
      [(''ch_v''[!](\<lambda>s. s V), Cm (''ch_m''[!](\<lambda>s. s W)); Cm (''ch_Fc''[?]W); T ::= (\<lambda>_.0))]
    )"

fun P1_inv :: "real \<times> real \<Rightarrow> real list \<Rightarrow> tassn" where
  "P1_inv (v, w) [] = emp\<^sub>t"
| "P1_inv (v, w) (Fc1 # Fcs) =
   (\<lambda>tr. \<exists>st'. (
      ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
        (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732), W := (\<lambda>s. (s W)^2 / 2500), T := (\<lambda>_. 1))))
        ((\<lambda>_. True)) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
      Out\<^sub>t st' ''ch_m'' (st' W) @\<^sub>t
      In\<^sub>t st' ''ch_Fc'' Fc1 @\<^sub>t
      P1_inv (st' V, Fc1) Fcs) tr)"

inductive P1_inv_ind :: "real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> tassn" where
  "P1_inv_ind v w [] v w []"
| "(ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
      (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732), W := (\<lambda>s. (s W)^2 / 2500), T := (\<lambda>_. 1))))
      ((\<lambda>_. True)) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
    Out\<^sub>t st' ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t st' ''ch_Fc'' Fc1) tr1 \<Longrightarrow>
   P1_inv_ind (st' V) Fc1 Fcs v' w' tr2 \<Longrightarrow>
   P1_inv_ind v w (Fc1 # Fcs) v' w' (tr1 @ tr2)"

lemma join_assnI:
  "P tr1 \<Longrightarrow> Q tr2 \<Longrightarrow> (P @\<^sub>t Q) (tr1 @ tr2)"
  unfolding join_assn_def by auto

lemma join_assnE:
  "(P @\<^sub>t Q) tr \<Longrightarrow> (\<And>tr1 tr2. P tr1 \<Longrightarrow> Q tr2 \<Longrightarrow> tr = tr1 @ tr2 \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding join_assn_def by auto

lemma P1_inv_ind_cons1:
  "P1_inv_ind v w (Fc1 # Fcs) v' w' \<Longrightarrow>\<^sub>t
   (\<exists>\<^sub>tst'. (ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
      (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732), W := (\<lambda>s. (s W)^2 / 2500), T := (\<lambda>_. 1))))
      ((\<lambda>_. True)) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
    Out\<^sub>t st' ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t st' ''ch_Fc'' Fc1) @\<^sub>t P1_inv_ind (st' V) Fc1 Fcs v' w')"
  apply (auto simp add: entails_tassn_def ex_assn_def)
  subgoal for tr
  proof (induct v w "Fc1 # Fcs" v' w' tr rule: P1_inv_ind.induct)
    case (2 v w st' tr1 v' w' tr2)
    show ?case
      apply (rule exI[where x=st'])
      apply (rule join_assnI)
      using 2 by auto
  qed
  done

lemma P1_inv_ind_cons2:
  "(\<exists>\<^sub>tst'. (ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
      (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732), W := (\<lambda>s. (s W)^2 / 2500), T := (\<lambda>_. 1))))
      ((\<lambda>_. True)) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
    Out\<^sub>t st' ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t st' ''ch_Fc'' Fc1) @\<^sub>t P1_inv_ind (st' V) Fc1 Fcs v' w') \<Longrightarrow>\<^sub>t
  P1_inv_ind v w (Fc1 # Fcs) v' w'"
  apply (auto simp add: entails_tassn_def ex_assn_def)
  subgoal premises pre for tr st'
  proof -
    obtain tr1 tr2 where a: "((ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
       (ODE ((\<lambda>_ _. 0)(V := \<lambda>s. s W - 933 / 250, W := \<lambda>s. (s W)\<^sup>2 / 2500, T := \<lambda>_. 1)))
       (\<lambda>_. True) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
      Out\<^sub>t st' ''ch_m'' (st' W) @\<^sub>t In\<^sub>t st' ''ch_Fc'' Fc1) tr1)"
     "P1_inv_ind (st' V) Fc1 Fcs v' w' tr2"
     "tr = tr1 @ tr2"
      using pre join_assnE by blast
    show ?thesis
      unfolding a(3) apply (rule P1_inv_ind.intros(2))
      using a by auto
  qed
  done

lemma P1_inv_ind_cons:
  "P1_inv_ind v w (Fc1 # Fcs) v' w' =
   (\<exists>\<^sub>tst'. (ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
      (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732), W := (\<lambda>s. (s W)^2 / 2500), T := (\<lambda>_. 1))))
      ((\<lambda>_. True)) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
    Out\<^sub>t st' ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t st' ''ch_Fc'' Fc1) @\<^sub>t P1_inv_ind (st' V) Fc1 Fcs v' w')"
  using P1_inv_ind_cons1 P1_inv_ind_cons2 entails_tassn_def by auto

lemma P1_inv_ind_empty':
  "P1_inv_ind v w Fcs v2 w2 tr \<Longrightarrow> Fcs = [] \<Longrightarrow> tr = [] \<and> v = v2 \<and> w = w2"
  apply (induct rule: P1_inv_ind.induct) by auto

lemma P1_inv_ind_empty:
  "P1_inv_ind v w [] v2 w2 tr \<Longrightarrow> tr = [] \<and> v = v2 \<and> w = w2"
  using P1_inv_ind_empty' by auto

lemma P1_inv_ind_empty_rw:
  "P1_inv_ind v w [] v2 w2 = (\<up>(v = v2) \<and>\<^sub>t \<up>(w = w2) \<and>\<^sub>t emp\<^sub>t)"
  apply (auto simp add: conj_assn_def emp_assn_def pure_assn_def)
  apply (rule ext)
  apply (auto simp add: P1_inv_ind_empty)
  by (auto intro: P1_inv_ind.intros(1))

lemma P1_inv_snoc:
  "P1_inv_ind v0 w0 Fcs v w tr1 \<Longrightarrow>
   (ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
            (ODE ((\<lambda>_ _. 0)
               (V := \<lambda>s. s W - 3.732, W := \<lambda>s. (s W)\<^sup>2 / 2500,
                T := \<lambda>_. 1)))
            (\<lambda>_. True) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
    Out\<^sub>t st' ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t st' ''ch_Fc'' Fc1) tr2 \<Longrightarrow> P1_inv_ind v0 w0 (Fcs @ [Fc1]) (st' V) Fc1 (tr1 @ tr2)"
proof (induct rule: P1_inv_ind.induct)
  case (1 v w)
  have "P1_inv_ind v w (Fc1 # []) (st' V) Fc1 (tr2 @ [])"
    apply (rule P1_inv_ind.intros(2)[where st'=st'])
    subgoal using 1 
      by blast
    subgoal
      by (rule P1_inv_ind.intros(1))
    done
  then show ?case
    by auto
next
  case (2 v w st'' Fc1' tr1 Fcs v' w' tr2')
  have a: "P1_inv_ind (st'' V) Fc1' (Fcs @ [Fc1]) (st' V) Fc1 (tr2' @ tr2)"
    apply (rule 2(3)) by (rule 2(4))
  show ?case
    apply auto
    apply (rule P1_inv_ind.intros(2))
     prefer 2 apply (rule a)
    by (rule 2(1))
qed


lemma P1_inv_snoc':
  "(P1_inv_ind v0 w0 Fcs v w @\<^sub>t
   (ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
            (ODE ((\<lambda>_ _. 0)
               (V := \<lambda>s. s W - 3.732, W := \<lambda>s. (s W)\<^sup>2 / 2500,
                T := \<lambda>_. 1)))
            (\<lambda>_. True) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
    Out\<^sub>t st' ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t st' ''ch_Fc'' Fc1)) tr \<Longrightarrow> P1_inv_ind v0 w0 (Fcs @ [Fc1]) (st' V) Fc1 tr"
  unfolding join_assn_def
  apply auto
  subgoal for tr1 tr2a tr2b tr2c
    apply(rule P1_inv_snoc [of v0 w0 Fcs v w tr1 st' Fc1 "tr2a @ tr2b @ tr2c"])
     apply auto
    unfolding join_assn_def
    by auto
  done


lemma P1_rep:
  "\<Turnstile> {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0, W := w0) \<and> (emp\<^sub>t tr)}
    P1
   {\<lambda>s tr. \<exists>v w Fc . s = (\<lambda>_. 0)(V := v, W := w) \<and>
               P1_inv_ind v0 w0 Fc v w tr}"
  unfolding P1_def
  apply (rule Valid_weaken_pre)
  prefer 2
  apply(rule Valid_rep)
   apply(rule Valid_ex_pre)
 apply (rule Valid_ex_pre)
  apply (rule Valid_ex_pre)
  subgoal for v w Fc
    apply (rule Valid_interrupt_Out_sp2[where VS="{V,W,T}"])
    apply (rule Valid_ex_pre)
    subgoal for st'
      apply (rule Valid_seq)
       apply (rule Valid_send_sp2)
      apply (rule Valid_seq)
       apply (rule Valid_receive_sp2)
      apply (rule Valid_ex_pre)
      subgoal for Fc1
        apply (rule Valid_strengthen_post)
         prefer 2 apply (rule Valid_assign_sp)
        apply (auto simp add: entails_def)
        subgoal for tr
          apply (rule exI[where x="st' V"])
          apply (rule exI[where x="Fc1"])
          apply auto
          subgoal apply (rule ext) by (auto simp add: supp_def)
        apply (rule exI[where x="Fc @ [Fc1]"])
          apply (rule P1_inv_snoc'[where v=v and w=w])
          by (auto simp add: join_assoc)
        done
      done
    apply (auto simp add: supp_def)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x=v0]) apply (rule exI[where x=w0])
  apply auto apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def intro: P1_inv_ind.intros)


inductive tol_inv_ind :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> tassn" where
  "tol_inv_ind v0 w0 v1 w1 0 []"
| "(ODEsol(ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))))  (p) (Period) 
   \<Longrightarrow> p 0 = (\<lambda>_. 0)(V := v1, W := w1) 
   \<Longrightarrow> (((Wait\<^sub>t Period (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0, W := w0))) (State (p t))) ({''ch_v''}, {}) 
    @\<^sub>t IO\<^sub>t ''ch_v'' (p Priod V)) @\<^sub>t IO\<^sub>t ''ch_m '' (p Priod W)) @\<^sub>t IO\<^sub>t ''ch_Fc '' (W_upd (p Priod V) (p Priod W))) tr1
   \<Longrightarrow> tol_inv_ind (p Priod V) (p Priod W) (p Priod V) (W_upd (p Priod V) (p Priod W)) n tr2
   \<Longrightarrow> tol_inv_ind v0 w0 v1 w1 (Suc n) (tr1 @ tr2)
"
lemma tol_inv_ind_empty':
  "tol_inv_ind v0 w0 v1 w1 n tr \<Longrightarrow> n = 0  \<Longrightarrow> tr = []"
  apply (induct rule:tol_inv_ind.inducts)
  by auto

lemma tol_inv_ind_empty:
  "tol_inv_ind v0 w0 v1 w1 0 = emp\<^sub>t"
  using tol_inv_ind_empty' unfolding emp_assn_def apply auto
  using tol_inv_ind.intros(1) by auto

lemma tol_inv_ind_suc:
  assumes"(ODEsol(ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))))  (p) (Period) "
   and" p 0 = (\<lambda>_. 0)(V := v1, W := w1) "
 shows" (((Wait\<^sub>t Period (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0, W := w0))) (State (p t))) ({''ch_v''}, {}) 
    @\<^sub>t IO\<^sub>t ''ch_v'' (p Priod V)) @\<^sub>t IO\<^sub>t ''ch_m '' (p Priod W)) @\<^sub>t IO\<^sub>t ''ch_Fc '' (W_upd (p Priod V) (p Priod W)))
    @\<^sub>t tol_inv_ind (p Priod V) (p Priod W) (p Priod V) (W_upd (p Priod V) (p Priod W)) n
    \<Longrightarrow>\<^sub>t tol_inv_ind v0 w0 v1 w1 (Suc n)"
  apply (auto simp add: entails_tassn_def)
  subgoal for tr
    subgoal premises pre
  proof-
obtain tr1 and tr2 where a:"(((Wait\<^sub>t Period (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0, W := w0))) (State (p t)))
         ({''ch_v''}, {}) @\<^sub>t
        IO\<^sub>t ''ch_v'' (p Priod V)) @\<^sub>t
       IO\<^sub>t ''ch_m '' (p Priod W)) @\<^sub>t
      IO\<^sub>t ''ch_Fc '' (W_upd (p Priod V) (p Priod W))) tr1" 
"tol_inv_ind (p Priod V) (p Priod W) (p Priod V) (W_upd (p Priod V) (p Priod W)) n tr2"
"tr = tr1 @ tr2" using pre join_assnE by blast
  show ?thesis
    using a(3) apply auto
    apply(rule tol_inv_ind.intros)
    using assms a by auto
  qed
  done
  done

lemma tol_inv_ind_suc':
"\<up>(((ODEsol(ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))))  (p) (Period)) \<and>
       (p 0 = (\<lambda>_. 0)(V := v1, W := w1))) \<and>\<^sub>t
 (((Wait\<^sub>t Period (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0, W := w0))) (State (p t))) ({''ch_v''}, {}) 
    @\<^sub>t IO\<^sub>t ''ch_v'' (p Priod V)) @\<^sub>t IO\<^sub>t ''ch_m '' (p Priod W)) @\<^sub>t IO\<^sub>t ''ch_Fc '' (W_upd (p Priod V) (p Priod W)))
    @\<^sub>t tol_inv_ind (p Priod V) (p Priod W) (p Priod V) (W_upd (p Priod V) (p Priod W)) n
    \<Longrightarrow>\<^sub>t tol_inv_ind v0 w0 v1 w1 (Suc n)"
  using tol_inv_ind_suc unfolding entails_tassn_def conj_assn_def pure_assn_def by auto

lemma combine_assn_emp_ODEout':
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (ODEout\<^sub>t s ode b s' ch e rdy @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: ode_out_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_emp_ODEout:
  assumes "ch \<in> chs"
  shows "combine_assn chs emp\<^sub>t (ODEout\<^sub>t s ode b s' ch e rdy @\<^sub>t P) \<Longrightarrow>\<^sub>t false\<^sub>A"
  using combine_assn_emp_ODEout' assms by auto
  

lemma combine_assn_wait_odeout:
  assumes "ch \<in> chs"
    and "compat_rdy rdy rdy2"
  shows "combine_assn chs (Wait\<^sub>t d p rdy @\<^sub>t P) (ODEout\<^sub>t s ode b s' ch e rdy2 @\<^sub>t Q)\<Longrightarrow>\<^sub>t 
         (\<up>(ODEsol ode p3 d \<and> p3 0 = s) \<and>\<^sub>t
          (Wait\<^sub>t d (\<lambda>t. ParState (p t) (State (p3 t))) (merge_rdy rdy rdy2) @\<^sub>t
          combine_assn chs P Q))"
proof -
  have *: "(\<up>(ODEsol ode p3 d \<and> p3 0 = s) \<and>\<^sub>t (Wait\<^sub>t d (\<lambda>t. ParState (p t) (State (p3 t))) (merge_rdy rdy rdy2) @\<^sub>t
                        combine_assn chs P Q)) tr"
    if "(Wait\<^sub>t d p rdy @\<^sub>t P) tr1"
       "(ODEout\<^sub>t s ode b s' ch e rdy2 @\<^sub>t Q) tr2"
       "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "Wait\<^sub>t d p rdy tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "ODEout\<^sub>t s ode b s' ch e rdy2 tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    have c: "tr11 = [WaitBlk d p rdy]"
      using a(1) wait_assn.cases by blast
    show ?thesis
      using b(1) apply (cases rule: ode_out_assn.cases)
      subgoal
        using that(3) unfolding a(3) b(3) c
        apply auto
        using assms combine_blocks_pairE2' by blast
      subgoal for d p3'


lemma combine_tol:
"combine_assn {''ch_v'', ''ch_m'', ''ch_Fc''} (P0_inv (v0,w0) p0list) (P1_inv_ind v1 w1 p1list v1e w1e) \<Longrightarrow>\<^sub>t
   tol_inv_ind v0 w0 v1 w1 (length p1list)"
proof (induct p1list arbitrary: p0list v0 w0 v1 w1 v1e w1e)
  case Nil
  note nil1 = Nil
  then show ?case
  proof (cases p0list)
    case Nil
    note nil0 = Nil
    then show ?thesis
      apply auto
      using P1_inv_ind_empty tol_inv_ind_empty 
      unfolding combine_assn_def entails_tassn_def emp_assn_def apply auto
      using combine_blocks_emptyE1 by blast
  next
    case (Cons p0pair p0rest)
    note con0 = Cons
    then show ?thesis
    proof (cases p0pair)
      case (Pair a b)
      then show ?thesis
        using con0 P1_inv_ind_empty_rw tol_inv_ind_empty 
        apply auto
        unfolding combine_assn_def
        apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def emp_assn_def wait_assn.simps)
       by (auto elim: sync_elims)
   qed
 qed
next
  case (Cons p1 p1rest)
  note con1 = Cons
  then show ?case
  proof(cases p0list)
    case Nil
    note nil0 = Nil
    then show ?thesis
      apply auto
      apply (auto simp add:ex_assn_def P1_inv_ind_cons)
      apply(rule combine_assn_ex_pre_right)
      subgoal for s'
        apply (rule entails_tassn_trans)
         apply(auto simp add: join_assoc)
         apply (rule combine_assn_emp_ODEout)
        by auto
      done
  next
    case (Cons p0pair p0rest)
    note con0 = Cons
    then show ?thesis
    proof (cases p0pair)
      case (Pair a b)
      then show ?thesis 
        apply (auto simp add:con0 Pair)
        apply (auto simp add:ex_assn_def P1_inv_ind_cons)
        apply(rule combine_assn_ex_pre_right)
        subgoal for s'
          apply (rule entails_tassn_trans)
           prefer 2 apply(rule tol_inv_ind_suc')
            using con1
        sorry
    qed
qed
qed
end
