theory BigStepContinuousEx
  imports BigStepContinuous
begin

subsection \<open>Examples\<close>

definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"
definition ch1 :: cname where "ch1 = ''ch1''"
definition ch2 :: cname where "ch2 = ''ch2''"

subsubsection \<open>Example 1\<close>

text \<open>
  The program to be analyzed is:
   x := 0; (ch!1; <x_dot = 2> |> dh?Y) \<squnion> (ch!2; <x_dot = 1> |> dh?Y)
|| ch?Y; wait(Y); dh!0
\<close>

definition ex1a :: "'a proc" where
  "ex1a = (X ::= (\<lambda>_. 0); IChoice
      (Cm (ch1[!](\<lambda>_. 1)); Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 2)))) (\<lambda>_. True)
                                     [(ch2[?]Y, Skip)])
      (Cm (ch1[!](\<lambda>_. 2)); Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
                                     [(ch2[?]Y, Skip)]))"

lemma ex1a_ode:
  "spec_of (Interrupt (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 2))) (\<lambda>_. True) [(ch2[?]Y, Skip)])
           (interrupt_solInf_c (\<lambda>s0 t. (rpart s0)(X := val s0 X + 2 * t))
                               [InSpec2 ch2 (\<lambda>d v s. init (upd (upd s X (val s X + 2 * d)) Y v))])"
proof -
  have 1: "paramODEsolInf (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 2)))
                          (\<lambda>s0 t. (rpart s0)(X := val s0 X + 2 * t))"
    unfolding paramODEsolInf_def apply clarify
    subgoal for s
      apply (rule conjI)
      subgoal apply (cases s)
        by (auto simp add: rpart.simps val.simps)
      unfolding ODEsolInf_def solves_ode_def has_vderiv_on_def
      apply auto
      apply (rule exI[where x="1"])
      apply auto
      apply (rule has_vector_derivative_projI)
      apply (auto simp add: state2vec_def)
      apply (rule has_vector_derivative_eq_rhs)
       apply (auto intro!: derivative_intros)[1]
      by simp
    done
  have 2: "local_lipschitz {- 1<..} UNIV (\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 2))) (vec2state v))"
  proof -
    have eq: "(\<chi> a. (if a = X then \<lambda>_. 2 else (\<lambda>_. 0)) (($) v)) = (\<chi> a. if a = X then 2 else 0)" for v::vec
      by auto
    show ?thesis
      unfolding fun_upd_def vec2state_def
      apply (auto simp add: state2vec_def eq)
      by (rule local_lipschitz_constI)
  qed
  let ?specs = "[InSpec ch2 Y init]"
  show ?thesis
    apply (rule spec_of_post)
     apply (rule spec_of_interrupt_inf_unique[where specs="?specs"])
        apply (rule 1) apply (rule 2)
      apply auto apply (rule spec_of_es.intros)
     apply (rule spec_of_skip)
    subgoal for s0
      apply (rule interrupt_solInf_mono)
       apply auto
      apply (intro spec2_entails.intros)
      subgoal for d v s0
        apply (cases s0) apply (auto simp add: updr.simps rpart.simps val.simps upd.simps)
        by (rule entails_triv)
      done
    done
qed

lemma ex1a_ode2:
  "spec_of (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
                      [(dh[?]Y, Skip)])
           (interrupt_solInf_c (\<lambda>s0 t. (rpart s0)(X := val s0 X + t))
                               [InSpec2 dh (\<lambda>d v s. init (upd (upd s X (val s X + d)) Y v))])"
proof -
  have 1: "paramODEsolInf (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1)))
                       (\<lambda>s0 t. (rpart s0)(X := val s0 X + t))"
    unfolding paramODEsolInf_def apply clarify
    subgoal for s
      apply (rule conjI)
      subgoal apply (cases s)
        by (auto simp add: rpart.simps val.simps)
      unfolding ODEsolInf_def solves_ode_def has_vderiv_on_def
      apply auto
      apply (rule exI[where x="1"])
      apply auto
      apply (rule has_vector_derivative_projI)
      apply (auto simp add: state2vec_def)
      apply (rule has_vector_derivative_eq_rhs)
       apply (auto intro!: derivative_intros)[1]
      by simp
    done
  have 2: "local_lipschitz {- 1<..} UNIV (\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (vec2state v))"
  proof -
    have eq: "(\<chi> a. (if a = X then \<lambda>_. 1 else (\<lambda>_. 0)) (($) v)) = (\<chi> a. if a = X then 1 else 0)" for v::vec
      by auto
    show ?thesis
      unfolding fun_upd_def vec2state_def
      apply (auto simp add: state2vec_def eq)
      by (rule local_lipschitz_constI)
  qed
  let ?specs = "[InSpec dh Y init]"
  show ?thesis
    apply (rule spec_of_post)
     apply (rule spec_of_interrupt_inf_unique[where specs="?specs"])
        apply (rule 1) apply (rule 2)
      apply auto apply (rule spec_of_es.intros)
     apply (rule spec_of_skip)
    subgoal for s0
      apply (rule interrupt_solInf_mono)
       apply auto
      apply (intro spec2_entails.intros)
      subgoal for d v s0
        apply (cases s0) apply (auto simp add: updr.simps rpart.simps val.simps upd.simps)
        by (rule entails_triv)
      done
    done
qed

lemma ex1a_sp:
  "spec_of ex1a
     ((wait_out_c ch1 (\<lambda>_. 1)
        (\<lambda>d. interrupt_solInf_c (\<lambda>s0 t. (rpart s0)(X := val s0 X + 2 * t))
                                [InSpec2 ch2 (\<lambda>d v s. init (upd (upd s X (val s X + 2 * d)) Y v))]) \<or>\<^sub>a
       wait_out_c ch1 (\<lambda>_. 2)
        (\<lambda>d. interrupt_solInf_c (\<lambda>s0 t. (rpart s0)(X := val s0 X + t))
                                [InSpec2 ch2 (\<lambda>d v s. init (upd (upd s X (val s X + d)) Y v))]))
      {{X := (\<lambda>_. 0)}})"
  unfolding ex1a_def
  apply (rule spec_of_post)
   apply (rule Valid_assign_sp)
   apply (rule spec_of_ichoice)
    apply (rule Valid_send_sp)
    apply (rule ex1a_ode)
  apply (rule Valid_send_sp)
   apply (rule ex1a_ode2)
  apply auto by (rule entails_triv)

definition ex1b :: "'a proc" where
  "ex1b = (Cm (ch1[?]Y); Wait (\<lambda>s. val s Y); Cm (ch2[!](\<lambda>_. 0)))"

lemma ex1b_sp:
  "spec_of ex1b
           (wait_in_c ch1 (\<lambda>d v.
              wait_c (\<lambda>s. val s Y) (
                wait_out_c ch2 (\<lambda>_. 0) (\<lambda>d. init)) {{Y := (\<lambda>_. v)}}))"
  unfolding ex1b_def
  apply (rule spec_of_post)
  apply (rule Valid_receive_sp)
   apply (rule Valid_wait_sp)
   apply (rule spec_of_send)
  apply auto by (rule entails_triv)

datatype 'a comm_specg2 =
  InSpecg2 cname "real \<Rightarrow> real \<Rightarrow> 'a gassn2"
| OutSpecg2 cname "real \<Rightarrow> 'a gstate \<Rightarrow> real" "real \<Rightarrow> 'a gassn2"

text \<open>Mapping from path on a single state to path on general states\<close>
definition single_path :: "pname \<Rightarrow> ('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> 'a gstate \<Rightarrow> real \<Rightarrow> 'a gstate" where
  "single_path pn p gs t = gs (pn \<mapsto> updr (the (gs pn)) (p (the (gs pn)) t))"

lemma single_path_State:
  "single_path pn p (State pn s) t = State pn (updr s (p s t))"
  unfolding single_path_def
  by (auto simp add: State_def)

text \<open>Merging two paths\<close>
definition restrict_state :: "pname set \<Rightarrow> 'a gstate \<Rightarrow> 'a gstate" where
  "restrict_state pns gs = (\<lambda>pn. if pn \<in> pns then gs pn else None)"

definition merge_path :: "pname set \<Rightarrow> pname set \<Rightarrow>
                          ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow>
                          ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate)" where
  "merge_path pns1 pns2 p1 p2 = (\<lambda>gs t.
     merge_state (p1 (restrict_state pns1 gs) t) (p2 (restrict_state pns2 gs) t))"

fun delay_path :: "real \<Rightarrow> ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate)" where
  "delay_path d p gs d' = p gs (d' + d)"

lemma restrict_state_eval1:
  assumes "proc_set gs1 = pns1"
  shows "restrict_state pns1 (merge_state gs1 gs2) = gs1"
  apply (rule ext) subgoal for pn
    unfolding restrict_state_def apply auto
     apply (subst merge_state_eval1) using assms apply auto
    unfolding proc_set_def by auto
  done

lemma restrict_state_eval2:
  assumes "proc_set gs1 = pns1"
    and "proc_set gs2 = pns2"
    and "pns1 \<inter> pns2 = {}"
  shows "restrict_state pns2 (merge_state gs1 gs2) = gs2"
  apply (rule ext) subgoal for pn
    unfolding restrict_state_def apply auto
     apply (subst merge_state_eval2) using assms apply auto
    unfolding proc_set_def by auto
  done

lemma merge_path_eval:
  assumes "proc_set gs1 = pns1"
    and "proc_set gs2 = pns2"
    and "pns1 \<inter> pns2 = {}"
  shows
  "merge_path pns1 pns2 p1 p2 (merge_state gs1 gs2) t = merge_state (p1 gs1 t) (p2 gs2 t)"
  unfolding merge_path_def
  by (auto simp add: restrict_state_eval1 restrict_state_eval2 assms)

fun id_path :: "'a gstate \<Rightarrow> real \<Rightarrow> 'a gstate" where
  "id_path gs t = gs"

fun single_val :: "pname \<Rightarrow> 'a eexp \<Rightarrow> 'a gstate \<Rightarrow> real" where
  "single_val pn e gs = e (the (gs pn))"

text \<open>Mapping from specification on single state to specification
  on general states.
\<close>
fun gassn_of :: "pname \<Rightarrow> 'a comm_spec2 \<Rightarrow> 'a comm_specg2" where
  "gassn_of pn (InSpec2 ch Q) = InSpecg2 ch (\<lambda>d v. single_assn pn (Q d v))"
| "gassn_of pn (OutSpec2 ch e Q) = OutSpecg2 ch (\<lambda>d. single_val pn (e d)) (\<lambda>d. single_assn pn (Q d))"

fun rdy_of_comm_specg2 :: "'a comm_specg2 list \<Rightarrow> rdy_info" where
  "rdy_of_comm_specg2 [] = ({}, {})"
| "rdy_of_comm_specg2 (InSpecg2 ch P # rest) = (
    let rdy = rdy_of_comm_specg2 rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_comm_specg2 (OutSpecg2 ch e P # rest) = (
    let rdy = rdy_of_comm_specg2 rest in
      (fst rdy, insert ch (snd rdy)))"

lemma rdy_of_comm_spec_gassn_of:
  "rdy_of_comm_spec2 specs = rdy_of_comm_specg2 (map (gassn_of pn) specs)"
  sorry

inductive interrupt_solInf_cg :: "('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow>
  'a comm_specg2 list \<Rightarrow> 'a gassn2" where
  "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   Q 0 v gs0 gs tr \<Longrightarrow> interrupt_solInf_cg p specs gs0 gs (InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d v gs0 gs tr \<Longrightarrow> p' = (\<lambda>\<tau>\<in>{0..d}. p gs0 \<tau>) \<Longrightarrow>
   rdy = rdy_of_comm_specg2 specs \<Longrightarrow>
   interrupt_solInf_cg p specs gs0 gs (WaitBlockP d p' rdy # InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch e Q \<Longrightarrow>
   v = e 0 gs0 \<Longrightarrow>
   Q 0 gs0 gs tr \<Longrightarrow> interrupt_solInf_cg p specs gs0 gs (OutBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch e Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d gs0 gs tr \<Longrightarrow> p' = (\<lambda>\<tau>\<in>{0..d}. p gs0 \<tau>) \<Longrightarrow>
   v = e d gs0 \<Longrightarrow>
   rdy = rdy_of_comm_specg2 specs \<Longrightarrow>
   interrupt_solInf_cg p specs gs0 gs (WaitBlockP d p' rdy # OutBlockP ch v # tr)"

lemma single_assn_interrupt_solInf:
  "single_assn pn (interrupt_solInf_c p specs) =
   interrupt_solInf_cg (single_path pn p) (map (gassn_of pn) specs)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0' s' tr'
        apply (elim interrupt_solInf_c.cases) apply auto
        subgoal for i ch Q v tr''
          apply (rule interrupt_solInf_cg.intros(1)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch Q d v tr'' a b
          apply (rule interrupt_solInf_cg.intros(2)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          unfolding single_path_State
          using pre rdy_of_comm_spec_gassn_of by (auto intro: single_assn.intros)
        subgoal for i ch e Q tr''
          apply (rule interrupt_solInf_cg.intros(3)[of i _ _ "(\<lambda>d. single_val pn (e d))" "(\<lambda>d. single_assn pn (Q d))" ])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch e Q d tr'' a b
          apply (rule interrupt_solInf_cg.intros(4)[of i _ _ "(\<lambda>d. single_val pn (e d))" "(\<lambda>d. single_assn pn (Q d))"])
          unfolding single_path_State
          using pre rdy_of_comm_spec_gassn_of by (auto intro: single_assn.intros)
        done
      done
    subgoal apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for i ch Q v tr'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0' s' tr''
          apply (subst ptrace_of.simps[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(1)[of i _ _ Q']) by auto
        done
      subgoal for i ch Q d v tr' a b
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          unfolding single_path_State
          apply (subst ptrace_of.simps(2)[symmetric])
          apply (subst ptrace_of_simp3[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(2)[of i _ _ Q']) apply auto
          unfolding rdy_of_comm_spec_gassn_of[symmetric] by auto
        done
      subgoal for i ch e Q tr'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for e' Q' s0'' s' tr''
          apply (subst ptrace_of.simps[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(3)[of i _ _ _ Q']) by auto
        done
      subgoal for i ch e Q d tr' a b
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for e' Q' s0'' s' tr''
          unfolding single_path_State
          apply (subst ptrace_of.simps[symmetric])
          apply (subst ptrace_of_simp3[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(4)[of i _ _ _ Q']) apply auto
          unfolding rdy_of_comm_spec_gassn_of[symmetric] by auto
        done
      done
    done
  done

definition disj_gassn :: "'a gassn2 \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2" (infixr "\<or>\<^sub>g" 35) where
  "(P \<or>\<^sub>g Q) gs0 = (\<lambda>gs tr. P gs0 gs tr \<or> Q gs0 gs tr)"

lemma single_assn_disj:
  "single_assn pn (P \<or>\<^sub>a Q) = (single_assn pn P \<or>\<^sub>g single_assn pn Q)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0' s' tr'
        unfolding disj_gassn_def disj_assn2_def
        by (auto intro: single_assn.intros)
      done
    subgoal unfolding disj_gassn_def disj_assn2_def
      apply (elim disjE single_assn.cases)
      by (auto intro: single_assn.intros)
    done
  done

lemma sync_gassn_disj:
  assumes "sync_gassn chs pns1 pns2 P1 Q gs0 \<Longrightarrow>\<^sub>g R"
    and "sync_gassn chs pns1 pns2 P2 Q gs0 \<Longrightarrow>\<^sub>g R"
  shows "sync_gassn chs pns1 pns2 (P1 \<or>\<^sub>g P2) Q gs0 \<Longrightarrow>\<^sub>g R"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    using assms unfolding disj_gassn_def entails_g_def
    by (auto simp add: sync_gassn.intros)
  done

lemma sync_gassn_disj2:
  assumes "sync_gassn chs pns1 pns2 P1 Q gs0 \<Longrightarrow>\<^sub>g R1 gs0"
    and "sync_gassn chs pns1 pns2 P2 Q gs0 \<Longrightarrow>\<^sub>g R2 gs0"
  shows "sync_gassn chs pns1 pns2 (P1 \<or>\<^sub>g P2) Q gs0 \<Longrightarrow>\<^sub>g (R1 \<or>\<^sub>g R2) gs0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    using assms unfolding disj_gassn_def entails_g_def
    by (auto simp add: sync_gassn.intros)
  done

lemma entails_g_disj2:
  assumes "P1 gs0 \<Longrightarrow>\<^sub>g R1 gs0"
    and "P2 gs0 \<Longrightarrow>\<^sub>g R2 gs0"
  shows "(P1 \<or>\<^sub>g P2) gs0 \<Longrightarrow>\<^sub>g (R1 \<or>\<^sub>g R2) gs0"
  using assms unfolding entails_g_def disj_gassn_def by auto

fun spec_wait_of :: "real \<Rightarrow> ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> 'a comm_specg2 \<Rightarrow> 'a comm_specg2" where
  "spec_wait_of d p (InSpecg2 ch P) = InSpecg2 ch (\<lambda>d' v. P (d + d') v)"
| "spec_wait_of d p (OutSpecg2 ch e P) = OutSpecg2 ch (\<lambda>d' gs. e (d + d') gs) (\<lambda>d'. P (d + d'))"

inductive wait_sol_cg :: "('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> pname \<Rightarrow> 'a eexp \<Rightarrow>
                          (real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2" where
  "e (the (gs0 pn)) > 0 \<Longrightarrow> d = e (the (gs0 pn)) \<Longrightarrow> p' = (\<lambda>t\<in>{0..d}. p gs0 t) \<Longrightarrow>
   P d gs0 gs tr \<Longrightarrow> rdy = ({}, {}) \<Longrightarrow>
   wait_sol_cg p pn e P gs0 gs (WaitBlockP d p' rdy # tr)"
| "\<not>e (the (gs0 pn)) > 0 \<Longrightarrow> P 0 gs0 gs tr \<Longrightarrow> wait_sol_cg p pn e P gs0 gs tr"

lemma compat_rdy_empty [simp]:
  "compat_rdy rdy ({}, {})"
  apply (cases rdy) by auto

lemma merge_rdy_simp1:
  assumes
    "\<And>i. i < length specs \<Longrightarrow>
          case specs ! i of InSpecg2 ch P \<Rightarrow> ch \<in> chs
                          | OutSpecg2 ch e P \<Rightarrow> ch \<in> chs \<and> pn \<in> pns1"
  shows
    "merge_rdy chs (rdy_of_comm_specg2 specs) ({}, {}) = ({}, {})"
  sorry

lemma rdy_of_spec_wait_of [simp]:
  "rdy_of_comm_specg2 (map (spec_wait_of d p) specs) = rdy_of_comm_specg2 specs"
  sorry

lemma sync_gassn_interrupt_solInf_wait:
  assumes "pn2 \<in> pns2"
    and "pns1 \<inter> pns2 = {}"
    and "\<And>i. i < length specs \<Longrightarrow>
          case specs ! i of InSpecg2 ch P \<Rightarrow> ch \<in> chs
                          | OutSpecg2 ch e P \<Rightarrow> ch \<in> chs \<and> pn \<in> pns1"
  shows
  "sync_gassn chs pns1 pns2 (interrupt_solInf_cg p specs) (wait_cg pn2 e Q) s0 \<Longrightarrow>\<^sub>g
   wait_sol_cg (merge_path pns1 pns2 p id_path) pn2 e
    (\<lambda>d. sync_gassn chs pns1 pns2 (interrupt_solInf_cg (delay_path d p) (map (spec_wait_of d p) specs)) Q) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for i ch Q' v tr'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2)
          using assms(3)[of i] by auto
        subgoal
          apply (rule wait_sol_cg.intros(2))
          apply (subst merge_state_eval2)
          using assms apply auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(1)[of i _ _ Q'])
          by auto
        done
      subgoal for i ch Q' d' v tr' a b
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (cases rule: linorder_cases[of d' "e (the (s12 pn2))"])
          subgoal
            apply (elim combine_blocks_waitE3) apply auto
            apply (elim combine_blocks_pairE2)
            using assms(3)[of i] by auto
          subgoal apply auto
            apply (elim combine_blocks_waitE2) apply auto
            subgoal for tr'''
              apply (rule wait_sol_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (rule ext) apply auto
                apply (subst merge_path_eval)
                using assms by auto
              apply (rule sync_gassn.intros) apply auto
              apply (rule interrupt_solInf_cg.intros(1)[of i _ _ "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
              apply auto apply (rule merge_rdy_simp1) using assms(3) by auto
            done
          subgoal
            apply (elim combine_blocks_waitE4) apply auto
            subgoal for tr'''
              apply (rule wait_sol_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (rule ext) apply auto
                apply (subst merge_path_eval)
                using assms by auto
              apply (rule sync_gassn.intros) apply auto
              apply (rule interrupt_solInf_cg.intros(2)[of i _ _ "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
              apply auto apply (rule merge_rdy_simp1) using assms(3) by auto
            done
          done
        subgoal
          apply (rule wait_sol_cg.intros(2))
          subgoal apply (subst merge_state_eval2)
            using assms(1,2) by auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(2)[of i _ _ Q'])
          by auto
        done
      subgoal for i ch e Q' tr'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2)
          using assms(3)[of i] by auto
        subgoal
          apply (rule wait_sol_cg.intros(2))
          apply (subst merge_state_eval2)
          using assms apply auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(3)[of i _ _ e Q'])
          by auto
        done
      subgoal for i ch e' Q' d' tr' a b
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (cases rule: linorder_cases[of d' "e (the (s12 pn2))"])
          subgoal
            apply (elim combine_blocks_waitE3) apply auto
            apply (elim combine_blocks_pairE2)
            using assms(3)[of i] by auto
          subgoal apply auto
            apply (elim combine_blocks_waitE2) apply auto
            subgoal for tr'''
              apply (rule wait_sol_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (rule ext) apply auto
                apply (subst merge_path_eval)
                using assms by auto
              apply (rule sync_gassn.intros) apply auto
              apply (rule interrupt_solInf_cg.intros(3)[of i _ _ "\<lambda>d'. e' (e (the (s12 pn2)) + d')"
                                                                 "\<lambda>d'. Q' (e (the (s12 pn2)) + d')"])
              apply auto apply (rule merge_rdy_simp1) using assms(3) by auto
            done
          subgoal
            apply (elim combine_blocks_waitE4) apply auto
            subgoal for tr'''
              apply (rule wait_sol_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (rule ext) apply auto
                apply (subst merge_path_eval)
                using assms by auto
              apply (rule sync_gassn.intros) apply auto
              apply (rule interrupt_solInf_cg.intros(4)[of i _ _ "\<lambda>d'. e' (e (the (s12 pn2)) + d')"
                                                                 "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
              apply auto apply (rule merge_rdy_simp1) using assms(3) by auto
            done
          done
        subgoal
          apply (rule wait_sol_cg.intros(2))
          subgoal apply (subst merge_state_eval2)
            using assms(1,2) by auto
          apply (rule sync_gassn.intros) apply auto
              apply (rule interrupt_solInf_cg.intros(4)[of i _ _ e' Q'])
          by auto
        done
      done
    done
  done

(*
lemma sync_gassn_interrupt_solInf_out:
  shows
  "sync_gassn chs pns1 pns2 (interrupt_solInf_cg p rdy specs)
                            (wait_out_cg
*)

lemma ex1b:
  "spec_of_global
    (Parallel (Single ''a'' ex1a)
              {ch1, ch2}
              (Single ''b'' ex1b))
   Q"
  (* Stage 1: merge ex1a_sp and ex1b_sp *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule spec_of_single) apply (rule ex1a_sp)
     apply (rule spec_of_single) apply (rule ex1b_sp)
  (* Stage 2: rewrite the assertions *)
    apply auto subgoal for s0
    apply (auto simp: single_assn_wait_in single_assn_wait single_assn_wait_out
                      single_assn_init single_assn_interrupt_solInf single_assn_disj updg_subst2)
  (* Stage 3: merge the assertions *)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_disj2)
      apply (rule sync_gassn_out_in) apply auto
     apply (rule sync_gassn_out_in) apply auto
    apply (rule entails_g_trans)
     apply (rule entails_g_disj2)
      apply (rule sync_gassn_subst_right) apply auto
     apply (rule sync_gassn_subst_right) apply auto
    apply (rule entails_g_trans)
     apply (rule entails_g_disj2)
      apply (rule updg_mono)
      apply (rule sync_gassn_interrupt_solInf_wait)
        apply auto
     apply (rule updg_mono)
     apply (rule sync_gassn_interrupt_solInf_wait)
       apply auto


end
