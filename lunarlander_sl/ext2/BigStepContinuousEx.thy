theory BigStepContinuousEx
  imports BigStepContinuous
begin

definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"
definition ch1 :: cname where "ch1 = ''ch1''"
definition ch2 :: cname where "ch2 = ''ch2''"

subsection \<open>Basic tests\<close>

lemma test_ode_unique:
  assumes "spec_of c Q"
  shows
  "spec_of (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. val s X < 1); c)
           (wait_sol_c (\<lambda>s t. upd s X (val s X + t)) (\<lambda>s. 1 - val s X)
                       (\<lambda>d s. Q (upd s X (val s X + d))))"
proof -
  have 1: "paramODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>s. val s X < 1)
                       (\<lambda>s t. (rpart s)(X := val s X + t)) (\<lambda>s. 1 - val s X)"
    unfolding paramODEsol_def apply clarify
    subgoal for s
      apply (rule conjI)
      subgoal apply (cases s)
        by (auto simp add: rpart.simps val.simps)
      apply (cases "val s X < 1")
      subgoal apply auto
        subgoal
          unfolding ODEsol_def solves_ode_def has_vderiv_on_def
          apply auto
          apply (rule exI[where x="1"])
          apply auto
          apply (rule has_vector_derivative_projI)
          apply (auto simp add: state2vec_def)
          apply (rule has_vector_derivative_eq_rhs)
           apply (auto intro!: derivative_intros)[1]
          by simp
        subgoal for t
          apply (cases s) by (auto simp add: updr.simps val.simps)
        subgoal 
          apply (cases s) by (auto simp add: updr.simps val.simps)
        done
      subgoal by auto
      done
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
  show ?thesis
    apply (rule spec_of_post)
     apply (rule Valid_cont_unique_sp)
    apply (rule assms)
      apply (rule 1) apply (rule 2)
    apply clarify apply (simp only: updr_rpart_simp1)
    apply (rule wait_sol_mono) subgoal for _ d' s
      by (rule entails_triv)
    done
qed

lemma test_interrupt_unique:
  "spec_of (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. val s X < 1)
                      [(dh[?]Y, Skip)])
           (interrupt_sol_c (\<lambda>s t. upd s X (val s X + t)) (\<lambda>s. 1 - val s X)
                            (\<lambda>d s. init (upd s X (val s X + d)))
                            [InSpec2 dh (\<lambda>d v s. init (upd (upd s X (val s X + d)) Y v))])"
proof -
  have 1: "paramODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>s. val s X < 1)
                       (\<lambda>s0 t. (rpart s0)(X := val s0 X + t)) (\<lambda>s0. 1 - val s0 X)"
    unfolding paramODEsol_def apply clarify
    subgoal for s
      apply (rule conjI)
      subgoal apply (cases s)
        by (auto simp add: rpart.simps val.simps)
      apply (cases "val s X < 1")
      subgoal apply auto
        subgoal
          unfolding ODEsol_def solves_ode_def has_vderiv_on_def
          apply auto
          apply (rule exI[where x="1"])
          apply auto
          apply (rule has_vector_derivative_projI)
          apply (auto simp add: state2vec_def)
          apply (rule has_vector_derivative_eq_rhs)
           apply (auto intro!: derivative_intros)[1]
          by simp
        subgoal for t
          apply (cases s) by (auto simp add: updr.simps val.simps)
        subgoal 
          apply (cases s) by (auto simp add: updr.simps val.simps)
        done
      subgoal by auto
      done
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
     apply (rule spec_of_interrupt_unique[where specs="?specs"])
        apply (rule 1) apply (rule 2)
      apply auto apply (rule spec_of_es.intros)
     apply (rule spec_of_skip)
    subgoal for s0
      apply (simp only: updr_rpart_simp1)
      apply (rule interrupt_sol_mono)
      subgoal by (rule entails_triv)
      subgoal by auto
      subgoal for i
        apply auto apply (intro spec2_entails.intros)
        subgoal for d v s0 apply (simp only: updr_rpart_simp2)
          by (rule entails_triv)
        done
      done
    done
qed

subsection \<open>Examples\<close>

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
           (interrupt_solInf_c (\<lambda>s t. upd s X (val s X + 2 * t))
                               [InSpec2 ch2 (\<lambda>d v. init {{Y := (\<lambda>_. v)}} {{X := (\<lambda>s. val s X + 2 * d)}})])"
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
      apply (simp only: updr_rpart_simp1)
      apply (rule interrupt_solInf_mono)
       apply auto
      apply (intro spec2_entails.intros)
      subgoal for d v s0
        apply (cases s0)
        apply (auto simp add: subst_assn2_def updr.simps rpart.simps val.simps upd.simps)
        by (rule entails_triv)
      done
    done
qed

lemma ex1a_ode2:
  "spec_of (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
                      [(dh[?]Y, Skip)])
           (interrupt_solInf_c (\<lambda>s t. upd s X (val s X + t))
                               [InSpec2 dh (\<lambda>d v. init {{Y := (\<lambda>_. v)}} {{X := (\<lambda>s. val s X + d)}})])"
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
      apply (simp only: updr_rpart_simp1)
      apply (rule interrupt_solInf_mono)
       apply auto
      apply (intro spec2_entails.intros)
      subgoal for d v s0
        apply (cases s0)
        apply (auto simp add: subst_assn2_def updr.simps rpart.simps val.simps upd.simps)
        by (rule entails_triv)
      done
    done
qed

lemma ex1a_sp:
  "spec_of ex1a
     ((wait_out_c ch1 (\<lambda>_. 1)
        (\<lambda>d. interrupt_solInf_c (\<lambda>s t. upd s X (val s X + 2 * t))
                                [InSpec2 ch2 (\<lambda>d v. init {{Y := (\<lambda>_. v)}} {{X := (\<lambda>s. val s X + 2 * d)}})]) \<or>\<^sub>a
       wait_out_c ch1 (\<lambda>_. 2)
        (\<lambda>d. interrupt_solInf_c (\<lambda>s t. upd s X (val s X + t))
                                [InSpec2 ch2 (\<lambda>d v. init {{Y := (\<lambda>_. v)}} {{X := (\<lambda>s. val s X + d)}})]))
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

lemma ex1':
  "spec_of_global
    (Parallel (Single ''a'' ex1a)
              {ch1, ch2}
              (Single ''b'' ex1b))
   ((wait_sol_cg
      (merge_path {''a''} {''b''} (single_path ''a'' (\<lambda>s t. upd s X (val s X + 2 * t))) id_path)
      ''b'' (\<lambda>s. val s Y)
      (\<lambda>d. (init_single {''b'', ''a''} {{Y := (\<lambda>_. 0)}}\<^sub>g at ''a'')
                                       {{X := (\<lambda>s. val s X + 2 * d)}}\<^sub>g at ''a'')
        {{Y := (\<lambda>_. 1)}}\<^sub>g at ''b'' \<or>\<^sub>g
     wait_sol_cg
      (merge_path {''a''} {''b''} (single_path ''a'' (\<lambda>s t. upd s X (val s X + t))) id_path)
      ''b'' (\<lambda>s. val s Y)
      (\<lambda>d. (init_single {''b'', ''a''} {{Y := (\<lambda>_. 0)}}\<^sub>g at ''a'')
                                       {{X := (\<lambda>s. val s X + d)}}\<^sub>g at ''a'')
        {{Y := (\<lambda>_. 2)}}\<^sub>g at ''b'') {{X := (\<lambda>_. 0)}}\<^sub>g at ''a'')"
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
    apply (rule updg_mono)
    apply (rule sync_gassn_disj2)
    (* Left branch *)
    subgoal
      apply (rule entails_g_trans)
       apply (rule sync_gassn_out_in) apply auto
      apply (rule entails_g_trans)
       apply (rule sync_gassn_subst_right) apply auto
      apply (rule updg_mono)
      apply (rule entails_g_trans)
       apply (rule sync_gassn_interrupt_solInf_wait) apply auto
      apply (rule wait_sol_cg_mono)
      apply (rule entails_g_trans)
       apply (rule sync_gassn_interrupt_solInf_out) apply auto
      apply (rule entails_g_trans)
       apply (rule sync_gassn_subst_left) apply auto
      apply (rule updg_mono)
      apply (rule entails_g_trans)
       apply (rule sync_gassn_subst_left) apply auto
      apply (rule updg_mono)
      apply (rule entails_g_trans)
      apply (rule sync_gassn_emp) apply auto
      by (rule entails_g_triv)
    (* Right branch *)
    subgoal
      apply (rule entails_g_trans)
       apply (rule sync_gassn_out_in) apply auto
      apply (rule entails_g_trans)
       apply (rule sync_gassn_subst_right) apply auto
      apply (rule updg_mono)
      apply (rule entails_g_trans)
       apply (rule sync_gassn_interrupt_solInf_wait) apply auto
      apply (rule wait_sol_cg_mono)
      apply (rule entails_g_trans)
       apply (rule sync_gassn_interrupt_solInf_out) apply auto
      apply (rule entails_g_trans)
       apply (rule sync_gassn_subst_left) apply auto
      apply (rule updg_mono)
      apply (rule entails_g_trans)
       apply (rule sync_gassn_subst_left) apply auto
      apply (rule updg_mono)
      apply (rule entails_g_trans)
      apply (rule sync_gassn_emp) apply auto
      by (rule entails_g_triv)
    done
  done

lemma ex1_merge1:
  assumes "proc_set s0 = {''a'', ''b''}"
  shows
  "merge_path {''a''} {''b''} (single_path ''a'' (\<lambda>s t. upd s X (val s X + 2 * t))) id_path s0 =
   (\<lambda>t. updg s0 ''a'' X (valg s0 ''a'' X + 2 * t))"
  apply (rule merge_state_elim[of s0 "{''a''}" "{''b''}"])
  using assms apply auto[2]
  apply simp apply (rule ext)
  apply (subst merge_path_eval) apply auto[3]
  by (simp add: single_path_def valg_def[symmetric] updg_def[symmetric]
      merge_state_updg_left valg_merge_state_left)

lemma ex1_merge2:
  assumes "proc_set s0 = {''a'', ''b''}"
  shows
  "merge_path {''a''} {''b''} (single_path ''a'' (\<lambda>s t. upd s X (val s X + t))) id_path s0 =
   (\<lambda>t. updg s0 ''a'' X (valg s0 ''a'' X + t))"
  apply (rule merge_state_elim[of s0 "{''a''}" "{''b''}"])
  using assms apply auto[2]
  apply simp apply (rule ext)
  apply (subst merge_path_eval) apply auto[3]
  by (simp add: single_path_def valg_def[symmetric] updg_def[symmetric]
      merge_state_updg_left valg_merge_state_left)

lemma ex1'':
  assumes "proc_set s0 = {''a'', ''b''}"
  shows
  "((wait_sol_cg
      (merge_path {''a''} {''b''} (single_path ''a'' (\<lambda>s t. upd s X (val s X + 2 * t))) id_path)
      ''b'' (\<lambda>s. val s Y)
      (\<lambda>d. (init_single {''b'', ''a''} {{Y := (\<lambda>_. 0)}}\<^sub>g at ''a'')
                                       {{X := (\<lambda>s. val s X + 2 * d)}}\<^sub>g at ''a'')
        {{Y := (\<lambda>_. 1)}}\<^sub>g at ''b'' \<or>\<^sub>g
     wait_sol_cg
      (merge_path {''a''} {''b''} (single_path ''a'' (\<lambda>s t. upd s X (val s X + t))) id_path)
      ''b'' (\<lambda>s. val s Y)
      (\<lambda>d. (init_single {''b'', ''a''} {{Y := (\<lambda>_. 0)}}\<^sub>g at ''a'')
                                       {{X := (\<lambda>s. val s X + d)}}\<^sub>g at ''a'')
        {{Y := (\<lambda>_. 2)}}\<^sub>g at ''b'') {{X := (\<lambda>_. 0)}}\<^sub>g at ''a'') s0 \<Longrightarrow>\<^sub>g
    (wait_inv_cg (\<lambda>gs. valg gs ''a'' X \<in> {0..2})
        (\<lambda>s0. \<exists>\<^sub>gs1. !\<^sub>g[(valg s1 ''a'' X = 2)] \<and>\<^sub>g init_single {''b'', ''a''} s1)) s0"
  apply (rule entails_g_trans)
   apply (rule gassn_subst)
  apply (rule entails_g_disj)
  subgoal
    (* Left branch *)
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule wait_inv_cgI[where d=1 and I="\<lambda>gs. valg gs ''a'' X \<in> {0..2}"])
       apply (simp only: valg_def[symmetric]) apply auto[1]
      apply auto[1]
    subgoal apply (subst ex1_merge1)
      using assms by auto
    apply (rule entails_g_trans)
     apply (rule wait_inv_cg_state)
    apply (rule entails_g_trans)
     apply (rule wait_inv_cg_state)
    apply (rule wait_inv_cg_mono)
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (simp only: valg_def[symmetric]) apply auto
    apply (rule exists_gassn_intro)
    apply (rule exI[where x="updg (updg (updg (updg s0 ''a'' X 0) ''b'' Y 1) ''a'' X 2) ''a'' Y 0"])
    apply (rule conj_gassn_intro)
     apply (rule pure_gassn_intro)
    by (auto simp add: entails_g_def X_def Y_def)
  subgoal
    (* Right branch *)
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule wait_inv_cgI[where d=2 and I="\<lambda>gs. valg gs ''a'' X \<in> {0..2}"])
       apply (simp only: valg_def[symmetric]) apply auto[1]
      apply auto[1]
    subgoal apply (subst ex1_merge2)
      using assms by auto
    apply (rule entails_g_trans)
     apply (rule wait_inv_cg_state)
    apply (rule entails_g_trans)
     apply (rule wait_inv_cg_state)
    apply (rule wait_inv_cg_mono)
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (simp only: valg_def[symmetric]) apply auto
    apply (rule exists_gassn_intro)
    apply (rule exI[where x="updg (updg (updg (updg s0 ''a'' X 0) ''b'' Y 2) ''a'' X 2) ''a'' Y 0"])
    apply (rule conj_gassn_intro)
     apply (rule pure_gassn_intro)
    by (auto simp add: entails_g_def X_def Y_def)
  done

lemma ex1:
  assumes "proc_set s0 = {''a'', ''b''}"
  shows
  "\<Turnstile>\<^sub>p {init_global s0}
        (Parallel (Single ''a'' ex1a)
                  {ch1, ch2}
                  (Single ''b'' ex1b))
      {(wait_inv_cg (\<lambda>gs. valg gs ''a'' X \<in> {0..2})
        (\<lambda>s0. \<exists>\<^sub>gs1. !\<^sub>g[(valg s1 ''a'' X = 2)] \<and>\<^sub>g init_single {''b'', ''a''} s1)) s0}"
  apply (rule weaken_post_global)
   apply (rule spec_of_globalE[OF ex1'])
  apply (rule ex1'')
  using assms by auto

end
