theory ExampleContinuous
  imports BigStepParallel
begin

text \<open>Some common variables\<close>
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"

lemma vars_distinct [simp]: "X \<noteq> Y" "X \<noteq> Z" "Y \<noteq> Z" "Y \<noteq> X" "Z \<noteq> X" "Z \<noteq> Y"
  unfolding X_def Y_def Z_def by auto

subsection \<open>Examples of ODE\<close>

lemma example_ode:
  "\<Turnstile> {\<lambda>s tr. \<forall>s'. (ODE\<^sub>t (s(X := s X + 1)) ode b s' @- Q s') tr}
       X ::= (\<lambda>s. s X + 1); Cont ode b
      {Q}"
  apply (rule Valid_seq)
   prefer 2 apply (rule Valid_ode')
  by (rule Valid_assign)

lemma example_ode':
  "\<Turnstile> {\<lambda>s tr. s = st \<and> Q s tr}
        Cont ode b; X ::= (\<lambda>s. s X + 1)
      {\<lambda>s tr. \<exists>s'. s = s'(X := s' X + 1) \<and> (Q st @\<^sub>t ODE\<^sub>t st ode b s') tr}"
  apply (rule Valid_seq)
   apply (rule Valid_ode_sp_st)
  apply (rule Valid_strengthen_post)
   prefer 2 apply (rule Valid_assign_sp)
  apply (auto simp add: entails_def)
  subgoal for s tr x
    apply (rule exI[where x="s(X := x)"])
    by auto
  done


subsection \<open>Tests for ODE\<close>

text \<open>
  c ::= <x_dot = 1 & x < 1>
\<close>
lemma testHL12:
  assumes "a < 1"
  shows "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> Q tr}
      Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1)
    {\<lambda>s tr. s = ((\<lambda>_. 0)(X := 1)) \<and> (Q @\<^sub>t Wait\<^sub>t (1 - a) (\<lambda>t. State ((\<lambda>_. 0)(X := t + a))) ({}, {})) tr}"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + a)) (1 - a)"
     unfolding ODEsol_def solves_ode_def has_vderiv_on_def
     using assms apply auto
     apply (rule exI[where x="1"])
     apply auto
     apply (rule has_vector_derivative_projI)
     apply (auto simp add: state2vec_def)
     apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     by simp
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
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_ode_unique_solution_st[OF _ 1 _ _ _ 2])
    using assms by (auto simp add: entails_def)
qed


subsection \<open>Test with ODE, loop and parallel\<close>

text \<open>
  The system to be analyzed is c1 || c2, where
    c1 ::= (<x_dot = 1 & x < 1>; ch1!x; ch2?x>)*
    c2 ::= (ch1?y; ch2!(y-1))*
\<close>

text \<open>
  For the left side, there are two cases for analyzing the loop body:
   - if initial value of x is less than 1 (testHL13a') and
   - if initial value of x is not less than 1 (testHL13a'').
\<close>
lemma testHL13a':
  assumes "a < 1"
  shows "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> Q tr}
      Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
      Cm (''ch1''[!](\<lambda>s. s X));
      Cm (''ch2''[?]X)
    {\<lambda>s tr. \<exists>v. s = (\<lambda>_. 0)(X := v) \<and>
            (Q @\<^sub>t Wait\<^sub>t (1 - a) (\<lambda>t. State ((\<lambda>_. 0)(X := t + a))) ({}, {})
               @\<^sub>t Out\<^sub>t (State ((\<lambda>_. 0)(X := 1))) ''ch1'' 1
               @\<^sub>t In\<^sub>t (State ((\<lambda>_. 0)(X := 1))) ''ch2'' v) tr}"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + a)) (1 - a)"
     unfolding ODEsol_def solves_ode_def has_vderiv_on_def
     using assms apply auto
     apply (rule exI[where x="1"])
     apply auto
     apply (rule has_vector_derivative_projI)
     apply (auto simp add: state2vec_def)
     apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     by simp
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
    apply (rule Valid_seq)
     apply (rule Valid_ode_unique_solution_st[OF _ 1 _ _ _ 2])
        using assms apply auto apply (rule Valid_seq)
     apply (rule Valid_send_sp_st)
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_receive_sp_st)
    by (auto simp add: entails_def join_assoc)
qed

lemma testHL13a'':
  assumes "\<not>a < 1"
  shows "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> Q tr}
      Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
      Cm (''ch1''[!](\<lambda>s. s X));
      Cm (''ch2''[?]X)
    {\<lambda>s tr. \<exists>v. s = (\<lambda>_. 0)(X := v) \<and>
            (Q @\<^sub>t Out\<^sub>t (State ((\<lambda>_. 0)(X := a))) ''ch1'' a
               @\<^sub>t In\<^sub>t (State ((\<lambda>_. 0)(X := a))) ''ch2'' v) tr}"
  apply (rule Valid_seq)
   apply (rule Valid_ode_exit_st)
  using assms apply auto[1]
  apply (rule Valid_seq)
  apply (rule Valid_send_sp_st)
  apply (rule Valid_strengthen_post)
   prefer 2 apply (rule Valid_receive_sp_st)
  by (auto simp add: entails_def join_assoc)

text \<open>
  Trace invariant to be satisfied by the left side.
  Here
   - a is the initial value of variable x,
   - vs is the list of values received from channel ch2.
\<close>
fun left_blocks :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "left_blocks a [] = emp\<^sub>t"
| "left_blocks a (v # rest) =
    (if a < 1 then
       Wait\<^sub>t (1 - a) (\<lambda>t. State ((\<lambda>_. 0)(X := t + a))) ({}, {}) @\<^sub>t
       Out\<^sub>t (State ((\<lambda>_. 0)(X := 1))) ''ch1'' 1 @\<^sub>t
       In\<^sub>t (State ((\<lambda>_. 0)(X := 1))) ''ch2'' v @\<^sub>t left_blocks v rest
     else
       Out\<^sub>t (State ((\<lambda>_. 0)(X := a))) ''ch1'' a @\<^sub>t
       In\<^sub>t (State ((\<lambda>_. 0)(X := a))) ''ch2'' v @\<^sub>t left_blocks v rest)"

fun last_val :: "real \<Rightarrow> real list \<Rightarrow> real" where
  "last_val a [] = a"
| "last_val a (x # xs) = last_val x xs"

lemma last_val_snoc [simp]:
  "last_val a (xs @ [v]) = v"
  by (induct xs arbitrary: a, auto)

lemma left_blocks_snoc:
  "left_blocks a (vs @ [v]) =
    (if last_val a vs < 1 then
      left_blocks a vs @\<^sub>t
      Wait\<^sub>t (1 - last_val a vs) (\<lambda>t. State ((\<lambda>_. 0)(X := t + last_val a vs))) ({}, {}) @\<^sub>t
      Out\<^sub>t (State ((\<lambda>_. 0)(X := 1))) ''ch1'' 1 @\<^sub>t
      In\<^sub>t (State ((\<lambda>_. 0)(X := 1))) ''ch2'' v
    else
      left_blocks a vs @\<^sub>t
      Out\<^sub>t (State ((\<lambda>_. 0)(X := last_val a vs))) ''ch1'' (last_val a vs) @\<^sub>t
      In\<^sub>t (State ((\<lambda>_. 0)(X := last_val a vs))) ''ch2'' v)"
  apply (induct vs arbitrary: a)
  by (auto simp add: join_assoc)

lemma testHL13a:
  "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> emp\<^sub>t tr}
      Rep (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
           Cm (''ch1''[!](\<lambda>s. s X));
           Cm (''ch2''[?]X))
    {\<lambda>s tr. \<exists>vs. s = ((\<lambda>_. 0)(X := last_val a vs)) \<and> left_blocks a vs tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for vs
    apply (cases "last_val a vs < 1")
    apply (rule Valid_strengthen_post)
      prefer 2 apply (rule testHL13a') apply auto[1]
    subgoal apply (auto simp add: entails_def)
      subgoal for tr v apply (rule exI[where x="vs@[v]"])
        by (auto simp add: left_blocks_snoc)
      done
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule testHL13a'') apply auto[1]
    apply (auto simp add: entails_def)
    subgoal for tr v apply (rule exI[where x="vs@[v]"])
      by (auto simp add: left_blocks_snoc)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

text \<open>
  Trace invariant to be satisfied by the right side.
  Here
   - a is the initial value of variable y,
   - vs is the list of values received from channel ch1.
\<close>
fun right_blocks :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "right_blocks a [] = emp\<^sub>t"
| "right_blocks a (v # rest) =
    In\<^sub>t (State ((\<lambda>_. 0)(Y := a))) ''ch1'' v @\<^sub>t
    Out\<^sub>t (State ((\<lambda>_. 0)(Y := v))) ''ch2'' (v - 1) @\<^sub>t
    right_blocks v rest"

lemma right_blocks_snoc:
  "right_blocks a (vs @ [v]) =
    right_blocks a vs @\<^sub>t
    In\<^sub>t (State ((\<lambda>_. 0)(Y := last_val a vs))) ''ch1'' v @\<^sub>t
    Out\<^sub>t (State ((\<lambda>_. 0)(Y := v))) ''ch2'' (v - 1)"
  apply (induct vs arbitrary: a)
  by (auto simp add: join_assoc)

lemma testHL13b:
  "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(Y := a)) \<and> emp\<^sub>t tr}
      Rep (Cm (''ch1''[?]Y);
           Cm (''ch2''[!](\<lambda>s. s Y - 1)))
    {\<lambda>s tr. \<exists>ws. s = ((\<lambda>_. 0)(Y := last_val a ws)) \<and> right_blocks a ws tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for ws
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp_st)
    apply (rule Valid_ex_pre)
    subgoal for w
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_send_sp_st)
    apply (auto simp add: entails_def)
    subgoal for tr
      apply (rule exI[where x="ws@[w]"])
      by (auto simp add: right_blocks_snoc join_assoc)
    done
  done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

text \<open>
  Trace invariant for the overall system.
\<close>
fun tot_blocks :: "nat \<Rightarrow> tassn" where
  "tot_blocks 0 = emp\<^sub>t"
| "tot_blocks (Suc n) = (
    Wait\<^sub>t 1 (\<lambda>t. ParState (State ((\<lambda>_. 0)(X := t))) (State ((\<lambda>_. 0)(Y := 1)))) ({}, {''ch1''}) @\<^sub>t
    IO\<^sub>t ''ch1'' 1 @\<^sub>t IO\<^sub>t ''ch2'' 0 @\<^sub>t tot_blocks n)"

lemma combineHL13:
  "combine_assn {''ch1'', ''ch2''} (left_blocks 0 vs) (right_blocks 1 ws) \<Longrightarrow>\<^sub>t
   tot_blocks (length vs)"
proof (induct vs arbitrary: ws)
  case Nil
  then show ?case
  proof (cases ws)
    case Nil
    then show ?thesis by auto
  next
    case (Cons w ws')
    then show ?thesis
      by (auto simp add: combine_assn_emp_in)
  qed
next
  case (Cons a vs)
  note Cons1 = Cons
  then show ?case
  proof (cases ws)
    case Nil
    then show ?thesis
      apply auto
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_wait_emp)
      by (rule false_assn_entails)
  next
    case (Cons b list)
    show ?thesis
      apply (auto simp add: Cons)
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_wait_in)
         apply auto
      apply (rule entails_tassn_cancel_left)
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_out_in)
       apply auto apply (rule entails_tassn_cancel_left)
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_in_out)
       apply auto apply (rule entails_tassn_cancel_left)
      by (rule Cons1)
  qed
qed

lemma testHL13:
  "\<Turnstile>\<^sub>p
    {pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(X := 0))) (\<lambda>s. s = ((\<lambda>_. 0)(Y := 1)))}
      Parallel
       (Single (Rep (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
                Cm (''ch1''[!](\<lambda>s. s X));
                Cm (''ch2''[?]X)))) {''ch1'', ''ch2''}
       (Single (Rep (Cm (''ch1''[?]Y);
                Cm (''ch2''[!](\<lambda>s. s Y - 1)))))
    {\<exists>\<^sub>gn. trace_gassn (tot_blocks n)}"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
     apply (rule testHL13a)
    apply (rule testHL13b)
   apply (auto simp add: sing_gassn_ex sing_gassn_split)
  apply (rule sync_gassn_ex_pre_left)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for vs ws
    unfolding sync_gassn_state_left sync_gassn_state_right
    apply (rule entails_ex_gassn)
    apply (rule exI[where x="length vs"])
    apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
    apply (rule entails_tassn_trans)
     prefer 2 apply (rule combineHL13)
    apply (rule combine_assn_mono)
    by (auto simp add: entails_tassn_def entails_gassn_def and_gassn_def)
  done


subsection \<open>Test with interrupt, loop and parallel\<close>

text \<open>
  The system to be analyzed is c1 || c2, where
    c1 ::= (<x_dot = 1 & True> |> [](ch1!x -> skip); ch2?x)*
    c2 ::= (wait 1; ch1?y; ch2!(y-1))*
\<close>

text \<open>
  For the left side, first anlyze the ODE with interrupt.
\<close>
lemma testHL14o:
  "\<Turnstile>
    {\<lambda>s tr. s = (\<lambda>_. 0)(X := a) \<and> P tr}
      Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
                [(''ch1''[!](\<lambda>s. s X), Skip)]
    {\<lambda>s tr. \<exists>d. s = (\<lambda>_. 0)(X := d + a) \<and> (P @\<^sub>t WaitOut\<^sub>t d (\<lambda>t. (\<lambda>_. 0)(X := t + a)) ''ch1'' (\<lambda>s. s X) ({''ch1''}, {})) tr}"
proof -
  have 1: "ODEsolInf (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + a))"
     unfolding ODEsolInf_def solves_ode_def has_vderiv_on_def
     apply auto
     apply (rule exI[where x="1"])
     apply auto
     apply (rule has_vector_derivative_projI)
     apply (auto simp add: state2vec_def)
     apply (rule has_vector_derivative_eq_rhs)
      apply (auto intro!: derivative_intros)[1]
     by simp
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
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_ode_out_unique_solution[OF 1 _ _ 2])
    apply auto
     apply (rule Valid_skip) by auto
qed

text \<open>
  Trace invariant to be satisfied by the left side.
  Here
   - a is the initial value of variable x,
   - ps is a list of pairs (d, v), where d is delay and v is received value.
\<close>
fun ileft_blocks :: "real \<Rightarrow> (real \<times> real) list \<Rightarrow> tassn" where
  "ileft_blocks a [] = emp\<^sub>t"
| "ileft_blocks a ((d, v) # rest) =
   WaitOut\<^sub>t d (\<lambda>t. (\<lambda>_. 0)(X := t + a)) ''ch1'' (\<lambda>s. s X) ({''ch1''}, {}) @\<^sub>t
   In\<^sub>t (State ((\<lambda>_. 0)(X := a + d))) ''ch2'' v @\<^sub>t
   ileft_blocks v rest"

fun last_ileft_blocks :: "real \<Rightarrow> (real \<times> real) list \<Rightarrow> real" where
  "last_ileft_blocks a [] = a"
| "last_ileft_blocks a ((d, v) # rest) = last_ileft_blocks v rest"

lemma ileft_blocks_snoc:
  "ileft_blocks a (ps @ [(d, v)]) =
   ileft_blocks a ps @\<^sub>t
     WaitOut\<^sub>t d (\<lambda>t. (\<lambda>_. 0)(X := t + last_ileft_blocks a ps)) ''ch1'' (\<lambda>s. s X) ({''ch1''}, {}) @\<^sub>t
     In\<^sub>t (State ((\<lambda>_. 0)(X := d + last_ileft_blocks a ps))) ''ch2'' v"
  apply (induct ps arbitrary: a)
  by (auto simp add: join_assoc add.commute)

lemma last_ileft_blocks_snoc [simp]:
  "last_ileft_blocks a (ps @ [(d, v)]) = v"
  apply (induct ps arbitrary: a) by auto

lemma testHL14a:
  "\<Turnstile>
    {\<lambda>s tr. s = (\<lambda>_. 0)(X := a) \<and> emp\<^sub>t tr}
      Rep (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True) [(''ch1''[!](\<lambda>s. s X), Skip)];
           Cm (''ch2''[?]X))
    {\<lambda>s tr. \<exists>ps. s = (\<lambda>_. 0)(X := last_ileft_blocks a ps) \<and> ileft_blocks a ps tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for ps
    apply (rule Valid_seq)
     apply (rule testHL14o)
    apply (rule Valid_ex_pre)
    subgoal for d
      apply (rule Valid_strengthen_post)
       prefer 2 apply (rule Valid_receive_sp)
      apply (auto simp add: entails_def)
      subgoal for s tr x v
        apply (rule exI[where x="ps@[(d,v)]"])
        apply (auto simp add: conj_assn_def pure_assn_def ileft_blocks_snoc join_assoc)
        by (metis fun_upd_idem_iff fun_upd_upd)
      done
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

text \<open>
  Trace invariant to be satisfied by the right side.
  Here
   - a is the initial value of variable y,
   - vs is the list of values received from channel ch1.
\<close>
fun iright_blocks :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "iright_blocks a [] = emp\<^sub>t"
| "iright_blocks a (v # rest) =
   Wait\<^sub>t 1 (\<lambda>t. State ((\<lambda>_. 0)(Y := a))) ({}, {}) @\<^sub>t
   In\<^sub>t (State ((\<lambda>_. 0)(Y := a))) ''ch1'' v @\<^sub>t
   Out\<^sub>t (State ((\<lambda>_. 0)(Y := v))) ''ch2'' (v - 1) @\<^sub>t iright_blocks v rest"

fun last_iright_blocks :: "real \<Rightarrow> real list \<Rightarrow> real" where
  "last_iright_blocks a [] = a"
| "last_iright_blocks a (v # rest) = last_iright_blocks v rest"

lemma iright_blocks_snoc:
  "iright_blocks a (vs @ [v]) =
   iright_blocks a vs @\<^sub>t Wait\<^sub>t 1 (\<lambda>t. State ((\<lambda>_. 0)(Y := last_iright_blocks a vs))) ({}, {}) @\<^sub>t
   In\<^sub>t (State ((\<lambda>_. 0)(Y := last_iright_blocks a vs))) ''ch1'' v @\<^sub>t
   Out\<^sub>t (State ((\<lambda>_. 0)(Y := v))) ''ch2'' (v - 1)"
  apply (induct vs arbitrary: a)
  by (auto simp add: join_assoc)

lemma last_iright_blocks_snoc [simp]:
  "last_iright_blocks a (vs @ [v]) = v"
  apply (induct vs arbitrary: a) by auto

lemma testHL14b:
  "\<Turnstile>
    {\<lambda>s tr. s = (\<lambda>_. 0)(Y := a) \<and> emp\<^sub>t tr}
      Rep (Wait (\<lambda>_. 1); Cm (''ch1''[?]Y); Cm (''ch2''[!](\<lambda>s. s Y - 1)))
    {\<lambda>s tr. \<exists>vs. s = (\<lambda>_. 0)(Y := last_iright_blocks a vs) \<and> iright_blocks a vs tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for vs
    apply (rule Valid_seq)
    apply (rule Valid_wait_sp) apply simp
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp)
    apply (intro Valid_ex_pre)
    subgoal for x v
      apply (rule Valid_strengthen_post)
       prefer 2 apply (rule Valid_send_sp)
      apply (auto simp add: entails_def)
      apply (rule exI[where x="vs@[v]"])
      apply (auto simp add: conj_assn_def pure_assn_def iright_blocks_snoc join_assoc)
       apply (metis fun_upd_idem fun_upd_upd)
      by (metis fun_upd_triv fun_upd_upd)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

text \<open>
  Trace invariant for the overall system.
\<close>
fun tot_blocks2 :: "nat \<Rightarrow> tassn" where
  "tot_blocks2 0 = emp\<^sub>t"
| "tot_blocks2 (Suc n) = (
    Wait\<^sub>t 1 (\<lambda>t. ParState (State ((\<lambda>_. 0)(X := t))) (State ((\<lambda>_. 0)(Y := 1)))) ({''ch1''}, {}) @\<^sub>t
    IO\<^sub>t ''ch1'' 1 @\<^sub>t IO\<^sub>t ''ch2'' 0 @\<^sub>t tot_blocks2 n)"

lemma combineHL14:
  "combine_assn {''ch1'', ''ch2''} (ileft_blocks 0 ps) (iright_blocks 1 ws) \<Longrightarrow>\<^sub>t
   tot_blocks2 (length ps)"
proof (induct ps arbitrary: ws)
  case Nil
  then show ?case
  proof (cases ws)
    case Nil
    then show ?thesis by auto
  next
    case (Cons w ws')
    then show ?thesis
      apply auto
      apply (rule entails_tassn_trans)
      apply (rule combine_assn_emp_wait)
      by (rule false_assn_entails)
  qed
next
  case (Cons p ps')
  note Cons1 = Cons
  then show ?case
  proof (cases p)
    case (Pair d v)
    then show ?thesis
    proof (cases ws)
      case Nil
      then show ?thesis
        apply (auto simp add: Pair)
        apply (rule entails_tassn_trans)
        apply (rule combine_assn_waitout_emp)
        by auto
    next
      case (Cons a list)
      then show ?thesis
        apply (auto simp add: Pair)
        apply (rule entails_tassn_trans)
        apply (rule combine_assn_waitout_wait)
         apply auto
        apply (rule entails_tassn_cancel_left)
        apply (rule entails_tassn_trans)
        apply (rule combine_assn_waitout_in)
        apply auto
        apply (rule entails_tassn_cancel_left)
        apply (rule entails_tassn_trans)
         apply (rule combine_assn_in_out)
         apply auto
        apply (rule entails_tassn_cancel_left)
        by (rule Cons1)
    qed
  qed
qed

lemma testHL14:
  "\<Turnstile>\<^sub>p
    {pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(X := 0))) (\<lambda>s. s = ((\<lambda>_. 0)(Y := 1)))}
     Parallel
      (Single (Rep (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True) [(''ch1''[!](\<lambda>s. s X), Skip)];
               Cm (''ch2''[?]X)))) {''ch1'', ''ch2''}
      (Single (Rep (Wait (\<lambda>_. 1); Cm (''ch1''[?]Y); Cm (''ch2''[!](\<lambda>s. s Y - 1)))))
    {\<exists>\<^sub>g n. trace_gassn (tot_blocks2 n)}"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
     apply (rule testHL14a)
    apply (rule testHL14b)
   apply (auto simp add: sing_gassn_ex sing_gassn_split)
  apply (rule sync_gassn_ex_pre_left)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for ps vs
    unfolding sync_gassn_state_left sync_gassn_state_right
    apply (rule entails_ex_gassn)
    apply (rule exI[where x="length ps"])
    apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
    apply (rule entails_tassn_trans)
    prefer 2 apply (rule combineHL14)
    apply (rule combine_assn_mono)
    by (auto simp add: entails_tassn_def entails_gassn_def and_gassn_def)
  done

end
