
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
   Wait\<^sub>t Period (\<lambda>t. State ((\<lambda>_. 0)(V := v, W := w))) ({}, {}) @\<^sub>t
   In\<^sub>t (State ((\<lambda>_. 0)(V := v, W := w))) ''ch_v'' v' @\<^sub>t 
   In\<^sub>t (State ((\<lambda>_. 0)(V := v', W := w))) ''ch_m'' w' @\<^sub>t 
   Out\<^sub>t (State ((\<lambda>_. 0)(V := v', W := w'))) ''ch_Fc'' (W_upd v' w') @\<^sub>t
   P0_inv (v', w') (vwrest)"

fun last_P0_inv :: "real \<times> real \<Rightarrow> (real\<times> real) list \<Rightarrow> real\<times>real" where
  "last_P0_inv (v, w) [] = (v, w)"
| "last_P0_inv (v, w) ((v', w') # vwrest) = last_P0_inv (v', w') vwrest"

lemma P0_inv_snoc:
  "P0_inv (v, w) (vwlist @ [(v', w')]) =
   P0_inv (v, w) vwlist @\<^sub>t Wait\<^sub>t Period (\<lambda>t. State ((\<lambda>_. 0)(V := fst(last_P0_inv (v, w) vwlist), W := snd(last_P0_inv (v, w) vwlist)))) ({}, {}) @\<^sub>t
   In\<^sub>t (State ((\<lambda>_. 0)(V := fst(last_P0_inv (v, w) vwlist), W := snd(last_P0_inv (v, w) vwlist)))) ''ch_v'' v' @\<^sub>t 
   In\<^sub>t (State ((\<lambda>_. 0)(V := v', W := snd(last_P0_inv (v, w) vwlist)))) ''ch_m'' w' @\<^sub>t 
   Out\<^sub>t (State ((\<lambda>_. 0)(V := v', W := w'))) ''ch_Fc'' (W_upd v' w')"
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
    apply (rule Valid_wait_sp_st) apply (auto simp add:Period_def)
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp_st)
    apply (rule Valid_ex_pre)
    subgoal for v'
       apply (rule Valid_seq)
        apply (rule Valid_receive_sp_st)
      apply (rule Valid_ex_pre)
      subgoal for w'
        apply (rule Valid_strengthen_post)
        prefer 2 apply (rule Valid_send_sp_st)
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
      Out\<^sub>t (State st') ''ch_m'' (st' W) @\<^sub>t
      In\<^sub>t (State st') ''ch_Fc'' Fc1 @\<^sub>t
      P1_inv (st' V, Fc1) Fcs) tr)"

inductive P1_inv_ind :: "real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> tassn" where
  "P1_inv_ind v w [] v w []"
| "(ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
      (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732), W := (\<lambda>s. (s W)^2 / 2500), T := (\<lambda>_. 1))))
      ((\<lambda>_. True)) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
    Out\<^sub>t (State st') ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t (State st') ''ch_Fc'' Fc1) tr1 \<Longrightarrow>
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
    Out\<^sub>t (State st') ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t (State st') ''ch_Fc'' Fc1) @\<^sub>t P1_inv_ind (st' V) Fc1 Fcs v' w')"
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
    Out\<^sub>t (State st') ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t (State st') ''ch_Fc'' Fc1) @\<^sub>t P1_inv_ind (st' V) Fc1 Fcs v' w') \<Longrightarrow>\<^sub>t
  P1_inv_ind v w (Fc1 # Fcs) v' w'"
  apply (auto simp add: entails_tassn_def ex_assn_def)
  subgoal premises pre for tr st'
  proof -
    obtain tr1 tr2 where a: "((ODEout\<^sub>t ((\<lambda>_. 0)(V := v, W := w))
       (ODE ((\<lambda>_ _. 0)(V := \<lambda>s. s W - 933 / 250, W := \<lambda>s. (s W)\<^sup>2 / 2500, T := \<lambda>_. 1)))
       (\<lambda>_. True) st' ''ch_v'' (\<lambda>s. s V) ({''ch_v''}, {}) @\<^sub>t
      Out\<^sub>t (State st') ''ch_m'' (st' W) @\<^sub>t
      In\<^sub>t (State st') ''ch_Fc'' Fc1) tr1)"
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
    Out\<^sub>t (State st') ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t (State st') ''ch_Fc'' Fc1) @\<^sub>t P1_inv_ind (st' V) Fc1 Fcs v' w')"
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
    Out\<^sub>t (State st') ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t (State st') ''ch_Fc'' Fc1) tr2 \<Longrightarrow>
  P1_inv_ind v0 w0 (Fcs @ [Fc1]) (st' V) Fc1 (tr1 @ tr2)"
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
    Out\<^sub>t (State st') ''ch_m'' (st' W) @\<^sub>t
    In\<^sub>t (State st') ''ch_Fc'' Fc1)) tr \<Longrightarrow> P1_inv_ind v0 w0 (Fcs @ [Fc1]) (st' V) Fc1 tr"
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
       apply (rule Valid_send_sp)
      apply (rule Valid_seq)
       apply (rule Valid_receive_sp)
      apply (rule Valid_ex_pre)
      subgoal for w'
        apply (rule Valid_strengthen_post)
         prefer 2 apply (rule Valid_assign_sp)
        apply (auto simp add: entails_def pure_assn_def conj_assn_def)
        subgoal for s tr x
          apply (rule exI[where x="s V"])
          apply (rule exI[where x="s W"])
          apply auto 
          subgoal
            apply (rule ext) 
            apply auto
            subgoal premises pre for xa
            proof(rule ccontr)
              assume a:"s xa \<noteq> 0"
              then have 1:"xa \<noteq> T"
                using pre(1) by auto
              then have 2:"(s (T := x, W := w')) xa \<noteq> 0"
                using pre(5,6) a by auto
              then have 3:"xa \<in> {V, W, T}"
                using pre(3) unfolding supp_def by auto
              have 4:"xa\<notin> {V, W, T}"
                using pre(5,6) 1 by auto
              show False using 3 4 by auto
            qed
            done
          apply (rule exI[where x="Fc @ [s W]"])
          subgoal premises pre 
            using P1_inv_snoc'[of v0 w0 Fc v w "s(T := x, W := w')" "s W" tr]
            using pre(1,4) apply simp
            by (simp add: join_assoc)
          done
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
    @\<^sub>t IO\<^sub>t ''ch_v'' (p Period V)) @\<^sub>t IO\<^sub>t ''ch_m'' (p Period W)) @\<^sub>t IO\<^sub>t ''ch_Fc'' (W_upd (p Period V) (p Period W))) tr1
   \<Longrightarrow> tol_inv_ind (p Period V) (p Period W) (p Period V) (W_upd (p Period V) (p Period W)) n tr2
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
    @\<^sub>t IO\<^sub>t ''ch_v'' (p Period V)) @\<^sub>t IO\<^sub>t ''ch_m'' (p Period W)) @\<^sub>t IO\<^sub>t ''ch_Fc'' (W_upd (p Period V) (p Period W)))
    @\<^sub>t tol_inv_ind (p Period V) (p Period W) (p Period V) (W_upd (p Period V) (p Period W)) n
    \<Longrightarrow>\<^sub>t tol_inv_ind v0 w0 v1 w1 (Suc n)"
  apply (auto simp add: entails_tassn_def)
  subgoal for tr
    subgoal premises pre
  proof-
obtain tr1 and tr2 where a:"(((Wait\<^sub>t Period (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0, W := w0))) (State (p t)))
         ({''ch_v''}, {}) @\<^sub>t
        IO\<^sub>t ''ch_v'' (p Period V)) @\<^sub>t
       IO\<^sub>t ''ch_m'' (p Period W)) @\<^sub>t
      IO\<^sub>t ''ch_Fc'' (W_upd (p Period V) (p Period W))) tr1" 
"tol_inv_ind (p Period V) (p Period W) (p Period V) (W_upd (p Period V) (p Period W)) n tr2"
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
    @\<^sub>t IO\<^sub>t ''ch_v'' (p Period V)) @\<^sub>t IO\<^sub>t ''ch_m'' (p Period W)) @\<^sub>t IO\<^sub>t ''ch_Fc'' (W_upd (p Period V) (p Period W)))
    @\<^sub>t tol_inv_ind (p Period V) (p Period W) (p Period V) (W_upd (p Period V) (p Period W)) n
    \<Longrightarrow>\<^sub>t tol_inv_ind v0 w0 v1 w1 (Suc n)"
  using tol_inv_ind_suc unfolding entails_tassn_def conj_assn_def pure_assn_def by auto


lemma tol_inv_ind_suc'':
  assumes"(ODEsol(ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))))  (p) (Period) "
   and" p 0 = (\<lambda>_. 0)(V := v1, W := w1) "
 shows" Wait\<^sub>t Period (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0, W := w0))) (State (p t))) ({''ch_v''}, {}) 
    @\<^sub>t IO\<^sub>t ''ch_v'' (p Period V) @\<^sub>t IO\<^sub>t ''ch_m'' (p Period W) @\<^sub>t IO\<^sub>t ''ch_Fc'' (W_upd (p Period V) (p Period W))
    @\<^sub>t tol_inv_ind (p Period V) (p Period W) (p Period V) (W_upd (p Period V) (p Period W)) n
    \<Longrightarrow>\<^sub>t tol_inv_ind v0 w0 v1 w1 (Suc n)"
  using tol_inv_ind_suc[of p v1 w1 v0 w0 n] assms
  apply auto
  using join_assoc 
  by fastforce

lemma tol_inv_ind_suc''':
  assumes"(ODEsol(ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))))  (p) (Period) "
   and" p 0 = (\<lambda>_. 0)(V := v1, W := w1) "
   and " Wait\<^sub>t Period (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0, W := w0))) (State (p t))) ({''ch_v''}, {}) tr1"
   and " IO\<^sub>t ''ch_v'' (p Period V) tr2"
   and "IO\<^sub>t ''ch_m'' (p Period W) tr3"
   and "IO\<^sub>t ''ch_Fc'' (W_upd (p Period V) (p Period W)) tr4"
   and "tol_inv_ind (p Period V) (p Period W) (p Period V) (W_upd (p Period V) (p Period W)) n tr5"
 shows" tol_inv_ind v0 w0 v1 w1 (Suc n) (tr1 @ tr2 @ tr3 @ tr4 @ tr5)"
  using tol_inv_ind_suc''[of p v1 w1 v0 w0 n] assms
  apply (auto simp add: entails_tassn_def join_assn_def) 
  by blast
  

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
  

lemma combine_assn_wait_in_odeout:             
  assumes "ch \<in> chs"
    and "d>0"
    and "ch \<in> fst rdy2"
    and "compat_rdy rdy rdy2"
  shows "combine_assn chs (Wait\<^sub>t d p rdy @\<^sub>t In\<^sub>t ss ch v @\<^sub>t P) (ODEout\<^sub>t s ode b s' ch e rdy2 @\<^sub>t Q)\<Longrightarrow>\<^sub>t 
        ((\<exists>\<^sub>t p3. \<up>(ODEsol ode p3 d \<and> p3 0 = s) \<and>\<^sub>t \<up>(p3 d = s') \<and>\<^sub>t
          (Wait\<^sub>t d (\<lambda>t. ParState (p t) (State (p3 t))) (merge_rdy rdy rdy2))) @\<^sub>t (\<up>(e s' = v) \<and>\<^sub>t (IO\<^sub>t ch v)) @\<^sub>t
          combine_assn chs P Q)"
proof -
  have *: "((\<exists>\<^sub>t p3. \<up>(ODEsol ode p3 d \<and> p3 0 = s) \<and>\<^sub>t \<up>(p3 d = s') \<and>\<^sub>t
          (Wait\<^sub>t d (\<lambda>t. ParState (p t) (State (p3 t))) (merge_rdy rdy rdy2))) @\<^sub>t (\<up>(e s' = v) \<and>\<^sub>t (IO\<^sub>t ch v)) @\<^sub>t
          combine_assn chs P Q) tr"
    if "(Wait\<^sub>t d p rdy @\<^sub>t In\<^sub>t ss ch v @\<^sub>t P) tr1"
       "(ODEout\<^sub>t s ode b s' ch e rdy2 @\<^sub>t Q) tr2"
       "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 tr13 where a: "Wait\<^sub>t d p rdy tr11" "In\<^sub>t ss ch v tr12" "P tr13" "tr1 = tr11 @ tr12 @ tr13"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "ODEout\<^sub>t s ode b s' ch e rdy2 tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    show ?thesis
      using a(1) apply (cases rule: wait_assn.cases)
       prefer 2 using assms apply auto
      using b(1) apply (cases rule: ode_out_assn.cases)
      subgoal
        using that(3) unfolding a(4) b(3)
        apply auto
        using assms combine_blocks_pairE2' by blast
      subgoal premises pre for d' p3'
      proof-
        have "d>d' \<or> d<d' \<or> d=d'" by auto
        then show ?thesis
      proof (elim disjE)
        assume d1:"d>d'"
        from that(3)[unfolded a(4) b(3) pre(1,7)]
        obtain tr' where tr':"tr = WaitBlk d' (\<lambda>t. ParState (p t) (State(p3' t))) (merge_rdy rdy rdy2) # tr' "
           "combine_blocks chs (WaitBlk (d - d') (\<lambda>t. p (t + d')) rdy # tr12 @ tr13) ([OutBlock ch (e (p3' d'))] @ tr22) tr'"
          using combine_blocks_waitE4[of chs d p rdy "tr12@tr13" d' "(\<lambda>\<tau>. State (p3' \<tau>))" rdy2
         "[OutBlock ch (e (p3' d'))] @ tr22" tr]
          using pre(8,5) d1 
          by auto
        show ?thesis 
          using tr'(2) pre(2) 
          by (metis append_Cons combine_blocks_pairE2')
      next
        assume d2: "d'>d"
        thm pre
        from that(3)[unfolded a(4) b(3) pre(1,7)]
        obtain tr' where tr':"tr = WaitBlk d (\<lambda>t. ParState (p t) (State(p3' t))) (merge_rdy rdy rdy2) # tr' "
           "combine_blocks chs (tr12 @ tr13) (WaitBlk (d' - d) (\<lambda>t. State (p3' (t + d))) rdy2 # [OutBlock ch (e (p3' d'))] @ tr22) tr'"
          using combine_blocks_waitE3[of chs d p rdy "tr12@tr13" d' "(\<lambda>\<tau>. State (p3' \<tau>))" rdy2
         "[OutBlock ch (e (p3' d'))] @ tr22" tr]
        using pre(3,5) d2 by auto
      show ?thesis
        using a(2) apply(cases rule: in_assn.cases)
        subgoal using tr'(2) 
          by (metis (no_types, lifting) append_Cons combine_blocks_pairE2 pre(2))
        subgoal for d'' using tr'(2) 
          using combine_blocks_waitE1[of chs d'' "(\<lambda>_. ss)" "({}, {ch})" "[InBlock ch v]@tr13"
                 "d'-d" "(\<lambda>t. State (p3' (t + d)))" rdy2 "[OutBlock ch (e (p3' d'))] @ tr22" tr']
          using assms(3) apply auto
          apply (subgoal_tac "\<not> compat_rdy ({}, {ch}) rdy2")
           apply auto
          apply (subgoal_tac "{ch} \<inter> fst rdy2 \<noteq> {}")
           apply (smt (verit, ccfv_threshold) compat_rdy.elims(2) compat_rdy.simps fst_conv)
          by auto
        subgoal using tr'(2) 
          using combine_blocks_waitE1[of chs "\<infinity>" "(\<lambda>_. ss)" "({}, {ch})" "tr13"
                 "d'-d" "(\<lambda>t. State (p3' (t + d)))" rdy2 "[OutBlock ch (e (p3' d'))] @ tr22" tr']
          using assms(3) apply auto
          apply (subgoal_tac "\<not> compat_rdy ({}, {ch}) rdy2")
           apply auto
          apply (subgoal_tac "{ch} \<inter> fst rdy2 \<noteq> {}")
           apply (smt (verit, ccfv_threshold) compat_rdy.elims(2) compat_rdy.simps fst_conv)
          by auto
        done
    next
      assume d3:"d=d'"
        thm pre
        from that(3)[unfolded a(4) b(3) pre(1,7) d3]
        obtain tr' where tr':"tr = WaitBlk d' (\<lambda>t. ParState (p t) (State(p3' t))) (merge_rdy rdy rdy2) # tr' "
           "combine_blocks chs (tr12 @ tr13) ([OutBlock ch (e (p3' d'))] @ tr22) tr'"
          using combine_blocks_waitE2[of chs d' p rdy "tr12@tr13" "(\<lambda>\<tau>. State (p3' \<tau>))" rdy2 "[OutBlock ch (e (p3' d'))] @ tr22" tr]
          using pre(5) by auto
        show ?thesis
          using a(2) apply(cases rule: in_assn.cases)
          subgoal using tr'(2) pre(2)
            apply(auto elim!: combine_blocks_pairE)
            subgoal for tr''
              apply(auto simp add: join_assn_def)
              apply(rule exI[where x="[WaitBlk d' (\<lambda>t. ParState (p t) (State(p3' t))) (merge_rdy rdy rdy2)]"])
              apply auto
              subgoal
                apply(auto simp add: ex_assn_def conj_assn_def pure_assn_def)
                apply(rule exI[where x="p3'"])
                apply(auto simp add: pre d3) 
                using pre(8) wait_assn.intros(1) apply blast
                done
              subgoal
                apply (rule exI[where x="tr'"])
                using tr' apply (auto simp add: conj_assn_def pure_assn_def pre)
                apply (rule exI[where x="[IOBlock ch (e (p3' d'))]"])
                apply auto
                using io_assn.intros apply auto[1]
                using a(3) b(2) 
                by (auto simp add: combine_assn_def)
              done
            done
          subgoal for d''
            using tr'(2)
            by (metis (no_types, lifting) append_Cons combine_blocks_pairE2' pre(2))
          subgoal using tr'(2)
            by (metis (no_types, lifting) append_Cons combine_blocks_pairE2' pre(2))
          done
      qed
    qed
       done
  qed
  show ?thesis
    apply (subst combine_assn_def)
    apply (auto simp add: entails_tassn_def)
    using * by auto
qed


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
         apply (auto elim: sync_elims)
        by(auto simp add:Period_def)
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
         apply (subst join_assoc)
           apply (rule combine_assn_wait_in_odeout)
          apply simp
              apply (auto simp add:Period_def)[1]
          apply auto
          apply (rule entails_tassn_trans)
           apply (rule entails_tassn_cancel_left)
          apply auto
           apply (rule entails_tassn_cancel_left)
           apply (subst join_assoc)
           apply (rule entails_tassn_trans)
            apply(rule combine_assn_in_out)
            apply auto[1]
          apply auto[1]
           apply (rule entails_tassn_trans)
            apply (rule entails_tassn_cancel_left)
            apply (rule entails_tassn_trans)
            apply(rule combine_assn_out_in)
             apply auto[1]
            apply auto[1]
            apply (rule entails_tassn_cancel_left)
            apply(rule con1)
           apply (rule entails_tassn_refl)
          apply(auto simp add: entails_tassn_def join_assn_def)
          subgoal for tr1 tr2 tr3 tr4 tr5
            apply(auto simp add: ex_assn_def conj_assn_def pure_assn_def)
            subgoal for p3
              using tol_inv_ind_suc'''[of p3 v1 w1 v0 w0 tr1 tr2 tr3 tr4 "(length p1rest)" tr5]
              by auto
            done
          done
        done    
    qed
qed
qed

lemma system_Prop:
"\<Turnstile>\<^sub>p {pair_assn (\<lambda> s. s = (\<lambda>_. 0)(V := v0, W := w0)) (\<lambda> s. s = (\<lambda>_. 0)(V := v1, W := w1))} 
        Parallel (Single P0){''ch_v'', ''ch_m'',''ch_Fc''}(Single P1) 
     {\<exists>\<^sub>g n. trace_gassn (tol_inv_ind v0 w0 v1 w1 n)}"
  apply (rule ParValid_conseq')
  apply (rule ParValid_Parallel')
     apply (rule P0_rep)
    apply (rule P1_rep)
  apply auto[1]
   apply (subst sing_gassn_split sing_gassn_ex)+
  apply (rule sync_gassn_ex_pre_left)
  apply (rule sync_gassn_ex_pre_right)
  apply (rule sync_gassn_ex_pre_right)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for list1 v1 w1 list2
 unfolding sync_gassn_state_left sync_gassn_state_right
  apply (rule entails_ex_gassn)
  apply(rule exI[where x="length list2"])
apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
  apply (rule entails_tassn_trans)
   prefer 2
  apply (rule combine_tol)
  apply (rule combine_assn_mono)
  by (auto simp add: entails_tassn_def entails_gassn_def and_gassn_def)
  done



definition landerinv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"landerinv t v w = (15025282795421706426953 - 38191371615549881350000*t + 
  9482947285373987200000*t^2 - 90382078252408000000*t^3 - 
  12597135205472000000*t^4 + 5070724623344300111384 * v + 
  29051341984741759604000 * t * v + 12905500940447680000000*t^2 * v - 
  3452247087952000000*t^3 * v + 3754952256975690758168 * v^2 - 
  4369639740028640264000*t * v^2 + 4290324517728000000000*t^2 * v^2 + 
  10509874347360 * v^3 - 8711967253392000*t * v^3 + 1751645724560 * v^4 - 
  6016579819909859424000*w + 32152462695621728000000*t*w + 
  63926169690400000000*t^2*w + 1659591880613072768000 * v *w - 
  11298598523808000000000*t * v *w + 2216823024256000 * v^2*w + 
  1139598426176000000000*w^2 - 6579819920896000000000*t*w^2)/(160000000000000000000)"


lemma landerinv_prop2:
  "landerinv Period v w \<le> 0 \<Longrightarrow> landerinv 0 v (W_upd v w) \<le> 0"
  sorry

definition landerInv :: "state \<Rightarrow> real" where
  "landerInv s = landerinv (s T) (s V) (s W)"


definition landerode :: "var \<Rightarrow> exp" where
  " landerode = ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))"

lemma landerode_prop:
 assumes "\<forall>x. ((\<lambda>v. landerInv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
    and "\<forall>S. (S T < Period)\<longrightarrow> ((landerInv S = 0) \<longrightarrow> 
       g' (state2vec S) (ODE2Vec (ODE landerode) S) < 0)"
    and "(ODEsol(ODE landerode))  (p) (Period)"
    and "p 0  = (\<lambda>_. 0)(V := v1, W := w1)"
    and "landerInv ((\<lambda>_. 0)(V := v1, W := w1)) \<le> 0"
  shows "\<forall>t\<in>{0..Period}. landerInv (p t) \<le> 0 \<and> p t T = t"
  apply auto
  subgoal premises pre for t
  proof-
    obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec (ODE landerode) (p t))) {-e .. Period+e}"
      using pre assms unfolding ODEsol_def by auto
    have "((\<lambda>t. (state2vec (p t)) $ T) has_vderiv_on (\<lambda>t. (ODE2Vec (ODE landerode) (p t)) $ T)) {-e .. Period+e}"
      apply (rule has_vderiv_on_proj)
      using e by auto
    then have "((\<lambda>t. (state2vec (p t)) $ T) has_vderiv_on (\<lambda>t. 1)) {-e .. Period+e}"
      by(auto simp add: landerode_def state2vec_def)
    then have "((\<lambda>t. (state2vec (p t)) $ T) has_vderiv_on (\<lambda>t. 1)) {0 .. tt}" if "tt\<in>{0..Period}" for tt
      apply(rule has_vderiv_on_subset)
      using e that by auto
    then have "x\<in>{0..tt} \<Longrightarrow>((\<lambda>t. state2vec (p t) $ T) has_derivative (\<lambda> x. x)) (at x within {0..tt})" if "tt\<in>{0..Period}" for tt x
      apply(auto simp add: has_vderiv_on_def has_vector_derivative_def) 
      using that by auto
    then have tt:"p tt T = tt" if "tt\<in>{0..Period}" for tt
      using mvt_simple[of 0 tt "\<lambda> t. p t T" "\<lambda> _ x. x"] that assms(4) 
      apply (auto simp add: state2vec_def) 
      by fastforce
    have 1: "\<forall>t\<in>{-e .. Period+e}. ((\<lambda>t. landerInv(p t)) has_derivative  (\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE landerode) (p t)))) (at t within {-e .. Period+e})"
        using pre assms e
        using chainrule'[of landerInv "\<lambda>x. g'(state2vec x)" p "(ODE landerode)" e Period] 
        by auto
    have 2: "\<forall>s. g' (state2vec(p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec (ODE landerode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (1 *\<^sub>R ODE2Vec (ODE landerode) (p t))" if "t\<in>{-e .. Period+e}" for t
        using 1 unfolding has_derivative_def bounded_linear_def 
        using that linear_iff[of "(\<lambda>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE landerode) (p t)))"]
        by blast
    have 3: "(s *\<^sub>R 1) = s" and "(1 *\<^sub>R s) = s" 
      apply simp by simp
      have 4: "\<forall>s. g' (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE landerode) (p t)) = s *\<^sub>R g' (state2vec(p t)) (ODE2Vec (ODE landerode) (p t))" if "t\<in>{-e .. Period+e}" for t
        using 2 3 that by auto
      have 5: "\<forall>t\<in>{0..<Period}. landerInv(p t) = 0 \<longrightarrow>  g' (state2vec(p t)) (ODE2Vec (ODE landerode) (p t))< 0" if "t\<in>{0 ..<Period}" for t
        apply auto
        subgoal for tt
          apply(subgoal_tac "p tt T < Period")
          using assms(2) apply auto
          using tt[of tt] by auto
        done
      show ?thesis
        using real_inv_le[OF 1, of 0]
        using 5 assms e pre by auto
    qed
subgoal premises pre for t
  proof-
    obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec (ODE landerode) (p t))) {-e .. Period+e}"
      using pre assms unfolding ODEsol_def by auto
    have "((\<lambda>t. (state2vec (p t)) $ T) has_vderiv_on (\<lambda>t. (ODE2Vec (ODE landerode) (p t)) $ T)) {-e .. Period+e}"
      apply (rule has_vderiv_on_proj)
      using e by auto
    then have "((\<lambda>t. (state2vec (p t)) $ T) has_vderiv_on (\<lambda>t. 1)) {-e .. Period+e}"
      by(auto simp add: landerode_def state2vec_def)
    then have "((\<lambda>t. (state2vec (p t)) $ T) has_vderiv_on (\<lambda>t. 1)) {0 .. tt}" if "tt\<in>{0..Period}" for tt
      apply(rule has_vderiv_on_subset)
      using e that by auto
    then have "x\<in>{0..tt} \<Longrightarrow>((\<lambda>t. state2vec (p t) $ T) has_derivative (\<lambda> x. x)) (at x within {0..tt})" if "tt\<in>{0..Period}" for tt x
      apply(auto simp add: has_vderiv_on_def has_vector_derivative_def) 
      using that by auto
    then have tt:"p tt T = tt" if "tt\<in>{0..Period}" for tt
      using mvt_simple[of 0 tt "\<lambda> t. p t T" "\<lambda> _ x. x"] that assms(4) 
      apply (auto simp add: state2vec_def) 
      by fastforce
    show ?thesis
      using tt pre by auto
  qed
  done



inductive tol_inv_prop_ind :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> tassn" where
  "tol_inv_prop_ind v0 w0 v1 w1 0 []"
| "(ODEsol(ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))))  (p) (Period) 
   \<Longrightarrow> p 0 = (\<lambda>_. 0)(V := v1, W := w1) 
   \<Longrightarrow> \<forall> t\<in>{0..Period} . landerInv (p t) \<le> 0
   \<Longrightarrow> (((Wait\<^sub>t Period (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0, W := w0))) (State (p t))) ({''ch_v''}, {}) 
    @\<^sub>t IO\<^sub>t ''ch_v'' (p Period V)) @\<^sub>t IO\<^sub>t ''ch_m'' (p Period W)) @\<^sub>t IO\<^sub>t ''ch_Fc'' (W_upd (p Period V) (p Period W))) tr1
   \<Longrightarrow> tol_inv_prop_ind (p Period V) (p Period W) (p Period V) (W_upd (p Period V) (p Period W)) n tr2
   \<Longrightarrow> tol_inv_prop_ind v0 w0 v1 w1 (Suc n) (tr1 @ tr2)"

lemma inv_prop:
  "landerInv ((\<lambda>_. 0)(V := v1, W := w1)) \<le> 0 \<Longrightarrow> tol_inv_ind v0 w0 v1 w1 n \<Longrightarrow>\<^sub>t tol_inv_prop_ind v0 w0 v1 w1 n"
proof (induction n arbitrary: v0 w0 v1 w1)
  case 0
  then show ?case 
    apply(auto simp add: entails_tassn_def)
    subgoal for tr
      using tol_inv_ind_empty' tol_inv_prop_ind.intros(1) by blast
    done
next
  case suc:(Suc n)
  show ?case 
    apply(auto simp add: entails_tassn_def)
    subgoal premises pre for tr
      using pre
      apply(induct rule: tol_inv_ind.cases)
       apply auto
      subgoal premises pre2 for p tr1 tr2
      proof-
        have 1:"\<forall>t\<in>{0..Period}. landerInv (p t) \<le> 0 \<and> p t T = t"
          apply (rule landerode_prop)
              apply clarify
       apply(simp add:vec2state_def landerInv_def landerinv_def)
              apply (fast intro!: derivative_intros)
             apply(auto simp add:state2vec_def entails_def landerInv_def landerinv_def)
          subgoal for S sorry
          using pre2(2) apply(simp add: landerode_def)
          using pre2(3) apply simp
          using suc(2) 
          by(simp add: landerInv_def landerinv_def)
        have 2:"\<forall>t\<in>{0..Period}. landerInv (p t) \<le> 0"
          using 1 by auto
        have 3:"p Period T = Period"
          using 1 Period_def by auto
        have 4:"landerInv (p Period) \<le> 0"
          using 2 Period_def by auto
        have 5:"tol_inv_prop_ind (p Period V) (p Period W) (p Period V) (W_upd (p Period V) (p Period W)) n tr2"
          using suc(1)[unfolded entails_tassn_def landerInv_def,of "(p Period V)" "(W_upd (p Period V) (p Period W))" "(p Period V)" "(p Period W)"]
          apply simp
          using landerinv_prop2[of "(p Period V)" "(p Period W)"]
          using 4[unfolded landerInv_def 3]
          using pre2(5) by auto
        show ?thesis 
          using tol_inv_prop_ind.intros(2)[of p v1 w1 v0 w0 tr1 n tr2]
          using pre2 2 5 by auto
      qed
      done
    done
qed


lemma system_Prop1:
  assumes "landerInv ((\<lambda>_. 0)(V := v1, W := w1)) \<le> 0"
  shows"\<Turnstile>\<^sub>p {pair_assn (\<lambda> s. s = (\<lambda>_. 0)(V := v0, W := w0)) (\<lambda> s. s = (\<lambda>_. 0)(V := v1, W := w1))} 
        Parallel (Single P0){''ch_v'', ''ch_m'',''ch_Fc''}(Single P1) 
     {\<exists>\<^sub>g n. trace_gassn (tol_inv_prop_ind v0 w0 v1 w1 n)}"
  apply(rule ParValid_conseq)
    apply(rule system_Prop)
   apply (auto simp add: ex_gassn_def trace_gassn_def)
  subgoal for tr n
    apply(rule exI[where x="n"])
    using assms inv_prop 
    by (simp add: entails_tassn_def)
  done


end
