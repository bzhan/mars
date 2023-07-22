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
                               ({}, {ch2})
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
                               ({}, {dh})
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
        (\<lambda>d. interrupt_solInf_c (\<lambda>s0 t. (rpart s0)(X := val s0 X + 2 * t)) ({}, {ch2})
                                [InSpec2 ch2 (\<lambda>d v s. init (upd (upd s X (val s X + 2 * d)) Y v))]) \<or>\<^sub>a
       wait_out_c ch1 (\<lambda>_. 2)
        (\<lambda>d. interrupt_solInf_c (\<lambda>s0 t. (rpart s0)(X := val s0 X + t)) ({}, {ch2})
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
  "ex1b = (Cm (ch2[?]Y); Wait (\<lambda>s. val s Y); Cm (ch2[!](\<lambda>_. 0)))"

lemma ex1b_sp:
  "spec_of ex1b
           (wait_in_c ch2 (\<lambda>d v.
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
| OutSpecg2 cname pname "'a eexp" "real \<Rightarrow> 'a gassn2"

text \<open>Mapping from path on a single state to path on general states\<close>
definition single_path :: "pname \<Rightarrow> ('a estate \<Rightarrow> real \<Rightarrow> state) \<Rightarrow> 'a gstate \<Rightarrow> real \<Rightarrow> 'a gstate" where
  "single_path pn p gs t = gs (pn \<mapsto> updr (the (gs pn)) (p (the (gs pn)) t))"

lemma single_path_State:
  "single_path pn p (State pn s) t = State pn (updr s (p s t))"
  unfolding single_path_def
  by (auto simp add: State_def)

text \<open>Mapping from specification on single state to specification
  on general states.
\<close>
fun gassn_of :: "pname \<Rightarrow> 'a comm_spec2 \<Rightarrow> 'a comm_specg2" where
  "gassn_of pn (InSpec2 ch Q) = InSpecg2 ch (\<lambda>d v. single_assn pn (Q d v))"
| "gassn_of pn (OutSpec2 ch e Q) = OutSpecg2 ch pn e (\<lambda>d. single_assn pn (Q d))"

inductive interrupt_solInf_cg :: "('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow>
  'a comm_specg2 list \<Rightarrow> 'a gassn2" where
  "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   Q 0 v gs0 gs tr \<Longrightarrow> interrupt_solInf_cg p rdy specs gs0 gs (InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d v gs0 gs tr \<Longrightarrow>
   interrupt_solInf_cg p rdy specs gs0 gs (WaitBlockP d (\<lambda>\<tau>\<in>{0..d}. p gs0 \<tau>) rdy # InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch pn e Q \<Longrightarrow>
   v = e (the (gs0 pn)) \<Longrightarrow>
   Q 0 gs0 gs tr \<Longrightarrow> interrupt_solInf_cg p rdy specs gs0 gs (OutBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch pn e Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d gs0 gs tr \<Longrightarrow>
   v = e (the (p gs0 d pn)) \<Longrightarrow>
   interrupt_solInf_cg p rdy specs gs0 gs (WaitBlockP d (\<lambda>\<tau>\<in>{0..d}. p gs0 \<tau>) rdy # OutBlockP ch v # tr)"

lemma single_assn_interrupt_solInf:
  "single_assn pn (interrupt_solInf_c p rdy specs) =
   interrupt_solInf_cg (single_path pn p) rdy (map (gassn_of pn) specs)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0' s' tr'
        apply (elim interrupt_solInf_c.cases) apply auto
        subgoal for i ch Q v tr'' a b
          apply (rule interrupt_solInf_cg.intros(1)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch Q d v tr'' a b
        proof -
          have 1: "(\<lambda>\<tau>\<in>{0..d}. State pn (if 0 \<le> \<tau> \<and> \<tau> \<le> d then updr s0' (p s0' \<tau>) else undefined)) =
                   (\<lambda>\<tau>\<in>{0..d}. single_path pn p (State pn s0') \<tau>)"
            unfolding single_path_State by auto
          show ?thesis
            unfolding 1
            apply (rule interrupt_solInf_cg.intros(2)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
            using pre by (auto intro: single_assn.intros)
        qed
        subgoal for i ch e Q tr'' a b
          apply (rule interrupt_solInf_cg.intros(3)[of i _ _ pn e "(\<lambda>d. single_assn pn (Q d))" ])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch e Q d tr'' a b
        proof -
          have 1: "(\<lambda>\<tau>\<in>{0..d}. State pn (if 0 \<le> \<tau> \<and> \<tau> \<le> d then updr s0' (p s0' \<tau>) else undefined)) =
                   (\<lambda>\<tau>\<in>{0..d}. single_path pn p (State pn s0') \<tau>)"
            unfolding single_path_State by auto
          show ?thesis
            unfolding 1
            apply (rule interrupt_solInf_cg.intros(4)[of i _ _ pn e "(\<lambda>d. single_assn pn (Q d))"])
            using pre by (auto intro: single_assn.intros simp: single_path_State)
        qed
        done
      done
    subgoal apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for i ch Q v tr' a b
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
          apply (rule interrupt_solInf_c.intros(2)[of i _ _ Q']) by auto
        done
      subgoal for i ch pn e Q tr' a b
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          apply (subst ptrace_of.simps[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(3)[of i _ _ _ Q']) by auto
        done
      subgoal for i ch pn e Q d tr' a b
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          unfolding single_path_State
          apply (subst ptrace_of.simps[symmetric])
          apply (subst ptrace_of_simp3[symmetric])
          apply (rule single_assn.intros)
          apply (rule interrupt_solInf_c.intros(4)[of i _ _ _ Q']) by auto
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


end
