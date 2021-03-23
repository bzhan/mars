theory Velocity
  imports BigStepParallel
begin


subsection \<open>Case study: velocity control\<close>

definition V :: char where "V = CHR ''v''"
definition A :: char where "A = CHR ''a''"
definition T :: char where "T = CHR ''t''"

lemma [simp]: "V \<noteq> A" "A \<noteq> V" "V \<noteq> T" "T \<noteq> V" "A \<noteq> T" "T \<noteq> A"
  by (auto simp add: V_def A_def T_def)

text \<open>
  plant ::= (t := 0; \<langle>v_dot = a, t_dot = 1 & t < 1\<rangle>; p2c!v; c2p?a)*
\<close>
definition plant :: proc where
  "plant = Rep (T ::= (\<lambda>_. 0);
                Cont (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s A), T := (\<lambda>_. 1)))) (\<lambda>s. s T < 1);
                Cm (''p2c''[!](\<lambda>s. s V));
                Cm (''c2p''[?]A))"

text \<open>
  control ::= (p2c?v; if v < 10 then c2p!1 else c2p!(-1))*
\<close>
definition control :: proc where
  "control = Rep (Cm (''p2c''[?]V);
                  IF (\<lambda>s. s V < 10) THEN Cm (''c2p''[!](\<lambda>_. 1))
                  ELSE Cm (''c2p''[!](\<lambda>_. -1)) FI)"

text \<open>
  system ::= plant || control
\<close>
definition system :: pproc where
  "system = Parallel (Single plant) {''p2c'', ''c2p''} (Single control)"

text \<open>
  Analysis of the ODE for plant. This involves checking the solution and
  showing that the ODE satisfies the Lipschitz condition (and hence has
  unique solutions).
\<close>
lemma plant_ODE:
  "\<Turnstile> {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0, A := a0, T := 0) \<and> P tr}
        Cont (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s A), T := (\<lambda>_. 1)))) (\<lambda>s. s T < 1)
      {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0 + a0 * 1, A := a0, T := 1) \<and>
              (P @\<^sub>t Wait\<^sub>t 1 (\<lambda>t. State ((\<lambda>_. 0)(V := v0 + a0 * t, A := a0, T := t))) ({}, {})) tr}"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s A), T := (\<lambda>_. 1))))
                  (\<lambda>t. (\<lambda>_. 0)(V := v0 + a0 * t, A := a0, T := t)) 1"
    unfolding ODEsol_def has_vderiv_on_def
    apply auto
    apply(rule exI[where x=1])
    apply auto
    apply (rule has_vector_derivative_projI)
    apply (auto simp add: state2vec_def A_def V_def T_def)
     apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1] apply simp
    subgoal for x i
      apply (cases "i = CHR ''a''") by auto
    done
  have 2: "local_lipschitz {- (1::real)<..} UNIV (\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(V := \<lambda>s. s A, T := \<lambda>_. 1))) (vec2state v))"
  proof -
    show ?thesis
      unfolding state2vec_def vec2state_def fun_upd_def
      apply (rule c1_implies_local_lipschitz[where f'="(\<lambda>(t,v). Blinfun(\<lambda>(v::vec) . \<chi> x. if x = V then (v$A) else if x = T then 0 else 0))"])
         apply auto
      subgoal for t x
        apply (subst bounded_linear_Blinfun_apply)
        subgoal
          apply (rule bounded_linearI')
          by (auto simp add: vec_lambda_unique[symmetric])
        unfolding has_derivative_def
        apply auto
          apply (rule bounded_linearI')
        apply (auto simp add: vec_lambda_unique[symmetric])
        apply (rule vec_tendstoI)
        by (auto simp add: state2vec_def)
      done
  qed
  show ?thesis
    apply (rule Valid_ode_unique_solution_st[OF _ 1 _ _ _ 2])
    by auto
qed

text \<open>
  Trace invariant for plant. Here
   - v0, a0, t0 is the starting velocity, acceleration, and time.
   - as is the list of acceleration commands received from c2p.
\<close>
fun plant_inv :: "real \<times> real \<times> real \<Rightarrow> real list \<Rightarrow> tassn" where
  "plant_inv (v0, a0, t0) [] = emp\<^sub>t"
| "plant_inv (v0, a0, t0) (a # as) =
     Wait\<^sub>t 1 (\<lambda>t. State ((\<lambda>_. 0)(V := v0 + a0 * t, A := a0, T := t))) ({}, {}) @\<^sub>t
     Out\<^sub>t (State ((\<lambda>_. 0)(V := v0 + a0, A := a0, T := 1))) ''p2c'' (v0 + a0) @\<^sub>t
     In\<^sub>t (State ((\<lambda>_. 0)(V := v0 + a0, A := a0, T := 1))) ''c2p'' a @\<^sub>t
     plant_inv (v0 + a0, a, 1) as"

text \<open>
  Final state given the initial v0, a0, t0 and acceleration commands as.
\<close>
fun plant_end_state :: "real \<times> real \<times> real \<Rightarrow> real list \<Rightarrow> state" where
  "plant_end_state (v0, a0, t0) [] = ((\<lambda>_. 0)(V := v0, A := a0, T := t0))"
| "plant_end_state (v0, a0, t0) (a # as) =
   plant_end_state (v0 + a0, a, 1) as"

lemma plant_end_state_rw:
  "(plant_end_state (v0, a0, t0) as)(T := 0) =
   (\<lambda>_. 0)(V := plant_end_state (v0, a0, t0) as V,
           A := plant_end_state (v0, a0, t0) as A,
           T := 0)"
  apply (induct as arbitrary: v0 a0 t0) by auto

lemma plant_end_state_snoc:
  "plant_end_state (v0, a0, t0) (as @ [a]) =
   (\<lambda>_. 0)(V := plant_end_state (v0, a0, t0) as V + plant_end_state (v0, a0, t0) as A, T := 1, A := a)"
  apply (induct as arbitrary: v0 a0 t0) by auto

lemma plant_inv_snoc:
  "plant_inv (v0, a0, t0) (xs @ [a]) =
  (plant_inv (v0, a0, t0) xs @\<^sub>t
   Wait\<^sub>t 1 (\<lambda>t. State ((\<lambda>_. 0)(V := plant_end_state (v0, a0, t0) xs V + plant_end_state (v0, a0, t0) xs A * t,
                               A := plant_end_state (v0, a0, t0) xs A, T := t))) ({}, {})) @\<^sub>t
   Out\<^sub>t (State ((\<lambda>_. 0)(V := plant_end_state (v0, a0, t0) xs V + plant_end_state (v0, a0, t0) xs A,
                        A := plant_end_state (v0, a0, t0) xs A, T := 1)))
       ''p2c'' (plant_end_state (v0, a0, t0) xs V + plant_end_state (v0, a0, t0) xs A) @\<^sub>t
   In\<^sub>t (State ((\<lambda>_. 0) (V := plant_end_state (v0, a0, t0) xs V + plant_end_state (v0, a0, t0) xs A,
                        A := plant_end_state (v0, a0, t0) xs A, T := 1)))
       ''c2p'' a"
proof (induct xs arbitrary: v0 a0 t0)
  case Nil
  have a: "(\<lambda>_. 0)(V := v0 + a0 * t, A := a0, T := t) =
        (\<lambda> a. if a = T then t else if a = A then a0 else if a = V then v0 + a0 * t else 0)" for t
    apply (rule ext) by auto
  have b: "(\<lambda>_. 0)(V := v0 + a0, A := a0, T := 1) =
        (\<lambda> a. if a = T then 1 else if a = A then a0 else if a = V then v0 + a0 else 0)"
    apply (rule ext) by auto
  show ?case
    by (auto simp add: a b)
next
  case (Cons a as)
  show ?case
    by (auto simp add: Cons join_assoc)
qed

lemma plant_prop:
  "\<Turnstile> {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0, A := a0, T := t0) \<and> emp\<^sub>t tr}
        plant
      {\<lambda>s tr. \<exists>as. s = plant_end_state (v0, a0, t0) as \<and>
                   plant_inv (v0, a0, t0) as tr}"
  unfolding plant_def
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for xs
    apply (rule Valid_seq)
    apply (rule Valid_assign_sp_st)
    apply (rule Valid_seq)
    unfolding plant_end_state_rw
     apply (rule plant_ODE)
    apply (rule Valid_seq)
     apply (rule Valid_send_sp_st)
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_receive_sp_st)
    apply (auto simp add: entails_def)
    subgoal for tr a
      apply (rule exI[where x="xs @ [a]"])
      by (auto simp add: plant_end_state_snoc plant_inv_snoc join_assoc)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by auto

text \<open>
  Trace invariant for control. Here
   - v0 is the initial value of velocity
   - vs is the list of velocity values received from p2c.
\<close>
fun control_inv :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "control_inv v0 [] = emp\<^sub>t"
| "control_inv v0 (v # vs) =
   In\<^sub>t (State ((\<lambda>_. 0)(V := v0))) ''p2c'' v @\<^sub>t
   Out\<^sub>t (State ((\<lambda>_. 0)(V := v))) ''c2p'' (if v < 10 then 1 else -1) @\<^sub>t
   control_inv v vs"

fun control_end_state :: "real \<Rightarrow> real list \<Rightarrow> state" where
  "control_end_state v0 [] = ((\<lambda>_. 0)(V := v0))"
| "control_end_state v0 (v # vs) = control_end_state v vs"

lemma control_end_state_snoc:
  "control_end_state v0 (vs @ [v]) = (control_end_state v0 vs)(V := v)"
  apply (induct vs arbitrary: v0) by auto

lemma control_inv_snoc:
  "control_inv v0 (vs @ [v]) =
   control_inv v0 vs @\<^sub>t In\<^sub>t (State (control_end_state v0 vs)) ''p2c'' v @\<^sub>t
                        Out\<^sub>t (State ((control_end_state v0 vs)(V := v))) ''c2p''
   (if v < 10 then 1 else -1)"
proof (induct vs arbitrary: v0)
  case Nil
  have a: "(\<lambda>_. 0)(V := v0) = (\<lambda>a. if a = V then v0 else 0)"
    apply (rule ext) by auto
  have aa: "(\<lambda>_. 0)(V := v) = (\<lambda>a. if a = V then v else if a = V then v0 else 0)"
    apply (rule ext) by auto
  show ?case
    by (auto simp add: a aa)
next
  case (Cons a vs v0)
  then show ?case
    by (auto simp add: join_assoc)
qed


lemma control_prop:
  "\<Turnstile> {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0) \<and> emp\<^sub>t tr}
        control
      {\<lambda>s tr. \<exists>vs. s = control_end_state v0 vs \<and>
                   control_inv v0 vs tr}"
  unfolding control_def
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for vs
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp_st)
    apply (rule Valid_ex_pre)
    subgoal for v
      apply (rule Valid_strengthen_post)
       prefer 2 apply (rule Valid_cond_sp)
        apply (rule Valid_send_sp)
      apply (rule Valid_send_sp)
      apply (auto simp add: entails_def)
      apply (rule exI[where x="vs @ [v]"])
       apply (auto simp add: control_end_state_snoc control_inv_snoc conj_assn_def pure_assn_def join_assoc)
      apply (rule exI[where x="vs @ [v]"])
      by (auto simp add: control_end_state_snoc control_inv_snoc join_assoc)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by auto

text \<open>
  Loop invariant:
   - velocity always stays in the interval [9, 11].
   - acceleration is 1 if v < 10, and -1 if otherwise.
\<close>
fun loop_inv :: "real \<times> real \<Rightarrow> bool" where
  "loop_inv (v, a) \<longleftrightarrow> (v \<ge> 9 \<and> v \<le> 11 \<and> a = (if v < 10 then 1 else -1))"

declare loop_inv.simps [simp del]

text \<open>
  Trace invariant for the whole system. Note it includes the
  invariant on velocity and acceleration.
\<close>
fun system_inv :: "nat \<Rightarrow> tassn" where
  "system_inv 0 = emp\<^sub>t"
| "system_inv (Suc n) = (\<exists>\<^sub>tv0 a0 v0'. \<up>(loop_inv (v0, a0)) \<and>\<^sub>t
     Wait\<^sub>t 1 (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0 + a0 * t, A := a0, T := t))) (State ((\<lambda>_. 0)(V := v0')))) ({}, {''p2c''}) @\<^sub>t
     IO\<^sub>t ''p2c'' (v0 + a0) @\<^sub>t
     IO\<^sub>t ''c2p'' (if v0 + a0 < 10 then 1 else -1) @\<^sub>t
     system_inv n)"

lemma combine:
  "loop_inv (v0, a0) \<Longrightarrow>
   combine_assn {''p2c'', ''c2p''}
    (plant_inv (v0, a0, t0) as) (control_inv v0' vs) \<Longrightarrow>\<^sub>t
     system_inv (length as)"
proof (induct as arbitrary: v0 a0 t0 v0' vs)
  case Nil
  note Nil1 = Nil
  then show ?case
  proof (cases vs)
    case Nil
    then show ?thesis
      using Nil1 by (auto simp add: conj_assn_def pure_assn_def)
  next
    case (Cons a list)
    then show ?thesis
      by (auto simp add: combine_assn_emp_in)
  qed
next
  case (Cons a as)
  note Cons1 = Cons
  then show ?case
  proof (cases vs)
    case Nil
    then show ?thesis
      apply auto
      apply (rule entails_tassn_trans)
      apply (rule combine_assn_wait_emp)
      by (rule false_assn_entails)
  next
    case (Cons v vs)
    show ?thesis
      apply (auto simp add: Cons split del: if_split)
      apply (rule entails_tassn_trans)
      apply (rule combine_assn_wait_in)
         apply (auto split del: if_split)
      apply (rule entails_tassn_exI[where x=v0])
      apply (rule entails_tassn_exI[where x=a0])
      apply (rule entails_tassn_exI[where x=v0'])
      apply (rule entails_tassn_conj)
      subgoal
        by (auto simp add: pure_assn_def Cons1(2) entails_tassn_def)
      apply (rule entails_tassn_cancel_left)
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_out_in)
       apply (auto split del: if_split)
      apply (rule entails_tassn_cancel_left)
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_in_out)
       apply (auto split del: if_split)
      apply (rule entails_tassn_cancel_left)
      apply (rule Cons1(1))
      using Cons1(2) by (auto simp add: loop_inv.simps)
  qed
qed

theorem system_prop:
  assumes "loop_inv (v0, a0)"
  shows "\<Turnstile>\<^sub>p
    {pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(V := v0, A := a0, T := t0)))
               (\<lambda>s. s = ((\<lambda>_. 0)(V := v0')))}
      system
    {\<exists>\<^sub>gn. trace_gassn (system_inv n)}"
  unfolding system_def
  apply (rule ParValid_conseq')
  apply (rule ParValid_Parallel')
  apply (rule plant_prop)
  apply (rule control_prop)
   apply (auto simp add: sing_gassn_split sing_gassn_ex)
  apply (rule sync_gassn_ex_pre_left)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for as vs
    unfolding sync_gassn_state_left sync_gassn_state_right
    apply (rule entails_ex_gassn)
    apply (rule exI[where x="length as"])
    apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
    apply (rule combine[OF assms])
    by (auto simp add: entails_tassn_def entails_gassn_def and_gassn_def)
  done


end
