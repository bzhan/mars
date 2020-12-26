theory ExampleContinuous
  imports BigStepContinuous ExampleSimple
begin

subsection \<open>Tests for ODE\<close>

lemma testHL12:
  assumes "a < 1"
  shows "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> Q tr)
    (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := 1)) \<and> (Q @\<^sub>t WaitS\<^sub>A (1 - a) (\<lambda>t. (\<lambda>_. 0)(X := t + a))) tr)"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + a)) (1 - a)"
     unfolding ODEsol_def solves_ode_def has_vderiv_on_def
     using assms apply auto
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
     prefer 2 apply (rule Valid_ode_unique_solution'[OF _ 1 _ _ _ 2])
    using assms by (auto simp add: entails_def)
qed


subsection \<open>Test with ODE, loop and parallel\<close>

lemma testHL13a':
  assumes "a < 1"
  shows "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> Q tr)
    (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
     Cm (''ch1''[!](\<lambda>s. s X));
     Cm (''ch2''[?]X))
    (\<lambda>s tr. \<exists>v. s = (\<lambda>_. 0)(X := v) \<and>
            (Q @\<^sub>t WaitS\<^sub>A (1 - a) (\<lambda>t. (\<lambda>_. 0)(X := t + a))
               @\<^sub>t Out\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch1'' 1
               @\<^sub>t In\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch2'' v) tr)"
proof -
  have 1: "ODEsol (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + a)) (1 - a)"
     unfolding ODEsol_def solves_ode_def has_vderiv_on_def
     using assms apply auto
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
     apply (rule Valid_ode_unique_solution'[OF _ 1 _ _ _ 2])
        using assms apply auto apply (rule Valid_seq)
     apply (rule Valid_send_sp)
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_receive_sp)
    by (auto simp add: entails_def join_assoc)
qed

lemma testHL13a'':
  assumes "\<not>a < 1"
  shows "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> Q tr)
    (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
     Cm (''ch1''[!](\<lambda>s. s X));
     Cm (''ch2''[?]X))
    (\<lambda>s tr. \<exists>v. s = (\<lambda>_. 0)(X := v) \<and>
            (Q @\<^sub>t Out\<^sub>A ((\<lambda>_. 0)(X := a)) ''ch1'' a
               @\<^sub>t In\<^sub>A ((\<lambda>_. 0)(X := a)) ''ch2'' v) tr)"
  apply (rule Valid_seq)
   apply (rule Valid_ode_exit)
  using assms apply auto[1]
  apply (rule Valid_seq)
  apply (rule Valid_send_sp)
  apply (rule Valid_strengthen_post)
   prefer 2 apply (rule Valid_receive_sp)
  by (auto simp add: entails_def join_assoc)


text \<open>a is the initial value of X\<close>
fun left_blocks :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "left_blocks a [] = emp\<^sub>A"
| "left_blocks a (v # rest) =
    (if a < 1 then
       WaitS\<^sub>A (1 - a) (\<lambda>t. (\<lambda>_. 0)(X := t + a)) @\<^sub>t
       Out\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch1'' 1 @\<^sub>t
       In\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch2'' v @\<^sub>t left_blocks v rest
     else
       Out\<^sub>A ((\<lambda>_. 0)(X := a)) ''ch1'' a @\<^sub>t
       In\<^sub>A ((\<lambda>_. 0)(X := a)) ''ch2'' v @\<^sub>t left_blocks v rest)"

lemma left_blocks_snoc:
  "left_blocks a (vs @ [v]) =
    (if last_val a vs < 1 then
      left_blocks a vs @\<^sub>t
      WaitS\<^sub>A (1 - last_val a vs) (\<lambda>t. (\<lambda>_. 0)(X := t + last_val a vs)) @\<^sub>t
      Out\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch1'' 1 @\<^sub>t
      In\<^sub>A ((\<lambda>_. 0)(X := 1)) ''ch2'' v
    else
      left_blocks a vs @\<^sub>t
      Out\<^sub>A ((\<lambda>_. 0)(X := last_val a vs)) ''ch1'' (last_val a vs) @\<^sub>t
      In\<^sub>A ((\<lambda>_. 0)(X := last_val a vs)) ''ch2'' v)"
  apply (induct vs arbitrary: a)
  by (auto simp add: join_assoc)

lemma testHL13a:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> emp\<^sub>A tr)
    (Rep (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
          Cm (''ch1''[!](\<lambda>s. s X));
          Cm (''ch2''[?]X)))
    (\<lambda>s tr. \<exists>vs. s = ((\<lambda>_. 0)(X := last_val a vs)) \<and> left_blocks a vs tr)"
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

fun right_blocks :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "right_blocks a [] = emp\<^sub>A"
| "right_blocks a (v # rest) =
    In\<^sub>A ((\<lambda>_. 0)(Y := a)) ''ch1'' v @\<^sub>t
    Out\<^sub>A ((\<lambda>_. 0)(Y := v)) ''ch2'' (v - 1) @\<^sub>t
    right_blocks v rest"

lemma right_blocks_snoc:
  "right_blocks a (vs @ [v]) =
    right_blocks a vs @\<^sub>t
    In\<^sub>A ((\<lambda>_. 0)(Y := last_val a vs)) ''ch1'' v @\<^sub>t
    Out\<^sub>A ((\<lambda>_. 0)(Y := v)) ''ch2'' (v - 1)"
  apply (induct vs arbitrary: a)
  by (auto simp add: join_assoc)

lemma testHL13b:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(Y := a)) \<and> emp\<^sub>A tr)
    (Rep (Cm (''ch1''[?]Y);
          Cm (''ch2''[!](\<lambda>s. s Y - 1))))
    (\<lambda>s tr. \<exists>ws. s = ((\<lambda>_. 0)(Y := last_val a ws)) \<and> right_blocks a ws tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for ws
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp)
    apply (rule Valid_ex_pre)
    subgoal for w
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_send_sp)
    apply (auto simp add: entails_def)
    subgoal for tr
      apply (rule exI[where x="ws@[w]"])
      by (auto simp add: right_blocks_snoc join_assoc)
    done
  done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

fun tot_blocks :: "nat \<Rightarrow> tassn" where
  "tot_blocks 0 = emp\<^sub>A"
| "tot_blocks (Suc n) = (
    Wait\<^sub>A 1 (\<lambda>t\<in>{0..1}. ParState (State ((\<lambda>_. 0)(X := t))) (State ((\<lambda>_. 0)(Y := 1)))) @\<^sub>t
    IO\<^sub>A ''ch1'' 1 @\<^sub>t IO\<^sub>A ''ch2'' 0 @\<^sub>t tot_blocks n)"

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
       apply auto[1]
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
  "ParValid
    (pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(X := 0))) (\<lambda>s. s = ((\<lambda>_. 0)(Y := 1))))
    (Parallel
       (Single (Rep (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1);
                Cm (''ch1''[!](\<lambda>s. s X));
                Cm (''ch2''[?]X)))) {''ch1'', ''ch2''}
       (Single (Rep (Cm (''ch1''[?]Y);
                Cm (''ch2''[!](\<lambda>s. s Y - 1))))))
    (\<exists>\<^sub>gn. trace_gassn (tot_blocks n))"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
     apply (rule testHL13a)
    apply (rule testHL13b)
   apply auto
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

lemma testHL14o:
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0)(X := a) \<and> P tr)
    (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
               [(''ch1''[!](\<lambda>s. s X), Skip)])
    (\<lambda>s tr. \<exists>d. s = (\<lambda>_. 0)(X := d + a) \<and> (P @\<^sub>t WaitOut\<^sub>A d (\<lambda>t. (\<lambda>_. 0)(X := t + a)) ''ch1'' (\<lambda>s. s X) ({''ch1''}, {})) tr)"
proof -
  have 1: "ODEsolInf (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (\<lambda>t. (\<lambda>_. 0)(X := t + a))"
     unfolding ODEsolInf_def solves_ode_def has_vderiv_on_def
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

fun ileft_blocks :: "real \<Rightarrow> (real \<times> real) list \<Rightarrow> tassn" where
  "ileft_blocks a [] = emp\<^sub>A"
| "ileft_blocks a ((d, v) # rest) =
   WaitOut\<^sub>A d (\<lambda>t. (\<lambda>_. 0)(X := t + a)) ''ch1'' (\<lambda>s. s X) ({''ch1''}, {}) @\<^sub>t
   In\<^sub>A ((\<lambda>_. 0)(X := a + d)) ''ch2'' v @\<^sub>t
   ileft_blocks v rest"

fun last_ileft_blocks :: "real \<Rightarrow> (real \<times> real) list \<Rightarrow> real" where
  "last_ileft_blocks a [] = a"
| "last_ileft_blocks a ((d, v) # rest) = last_ileft_blocks v rest"

lemma ileft_blocks_snoc:
  "ileft_blocks a (ps @ [(d, v)]) =
   ileft_blocks a ps @\<^sub>t
     WaitOut\<^sub>A d (\<lambda>t. (\<lambda>_. 0)(X := t + last_ileft_blocks a ps)) ''ch1'' (\<lambda>s. s X) ({''ch1''}, {}) @\<^sub>t
     In\<^sub>A ((\<lambda>_. 0)(X := d + last_ileft_blocks a ps)) ''ch2'' v"
  apply (induct ps arbitrary: a)
  by (auto simp add: join_assoc add.commute)

lemma last_ileft_blocks_snoc [simp]:
  "last_ileft_blocks a (ps @ [(d, v)]) = v"
  apply (induct ps arbitrary: a) by auto

lemma testHL14a:
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0)(X := a) \<and> emp\<^sub>A tr)
    (Rep (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True) [(''ch1''[!](\<lambda>s. s X), Skip)];
          Cm (''ch2''[?]X)))
    (\<lambda>s tr. \<exists>ps. s = (\<lambda>_. 0)(X := last_ileft_blocks a ps) \<and> ileft_blocks a ps tr)"
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
      subgoal for tr v
        apply (rule exI[where x="ps@[(d,v)]"])
        by (auto simp add: ileft_blocks_snoc join_assoc)
      done
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

fun iright_blocks :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "iright_blocks a [] = emp\<^sub>A"
| "iright_blocks a (v # rest) =
   WaitS\<^sub>A 1 (\<lambda>t. (\<lambda>_. 0)(Y := a)) @\<^sub>t
   In\<^sub>A ((\<lambda>_. 0)(Y := a)) ''ch1'' v @\<^sub>t
   Out\<^sub>A ((\<lambda>_. 0)(Y := v)) ''ch2'' (v - 1) @\<^sub>t iright_blocks v rest"

fun last_iright_blocks :: "real \<Rightarrow> real list \<Rightarrow> real" where
  "last_iright_blocks a [] = a"
| "last_iright_blocks a (v # rest) = last_iright_blocks v rest"

lemma iright_blocks_snoc:
  "iright_blocks a (vs @ [v]) =
   iright_blocks a vs @\<^sub>t WaitS\<^sub>A 1 (\<lambda>t. (\<lambda>_. 0)(Y := last_iright_blocks a vs)) @\<^sub>t
   In\<^sub>A ((\<lambda>_. 0)(Y := last_iright_blocks a vs)) ''ch1'' v @\<^sub>t
   Out\<^sub>A ((\<lambda>_. 0)(Y := v)) ''ch2'' (v - 1)"
  apply (induct vs arbitrary: a)
  by (auto simp add: join_assoc)

lemma last_iright_blocks_snoc [simp]:
  "last_iright_blocks a (vs @ [v]) = v"
  apply (induct vs arbitrary: a) by auto

lemma testHL14b:
  "Valid
    (\<lambda>s tr. s = (\<lambda>_. 0)(Y := a) \<and> emp\<^sub>A tr)
    (Rep (Wait 1; Cm (''ch1''[?]Y); Cm (''ch2''[!](\<lambda>s. s Y - 1))))
    (\<lambda>s tr. \<exists>vs. s = (\<lambda>_. 0)(Y := last_iright_blocks a vs) \<and> iright_blocks a vs tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for vs
    apply (rule Valid_seq)
    apply (rule Valid_wait_sp) apply simp
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp)
    apply (rule Valid_ex_pre)
    subgoal for v
      apply (rule Valid_strengthen_post)
       prefer 2 apply (rule Valid_send_sp)
      apply (auto simp add: entails_def)
      apply (rule exI[where x="vs@[v]"])
      by (auto simp add: iright_blocks_snoc join_assoc)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

lemma combine_assn_waitout_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (WaitOut\<^sub>A d p ch e rdy @\<^sub>t P) emp\<^sub>A \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def wait_out_assn.simps)
  using assms by (auto elim!: combine_blocks_elim2i combine_blocks_elim4b)

lemma combine_assn_waitout_wait:
  assumes "ch \<in> chs"
  shows "combine_assn chs (WaitOut\<^sub>A d p ch e rdy @\<^sub>t P) (Wait\<^sub>A d2 p2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         (\<up>(d \<ge> d2) \<and>\<^sub>t (Wait\<^sub>A d2 (\<lambda>t\<in>{0..d2}. ParState (State (p t)) (p2 t)) @\<^sub>t
                        combine_assn chs (WaitOut\<^sub>A (d - d2) (\<lambda>t\<in>{0..d-d2}. p (t + d2)) ch e rdy @\<^sub>t P) Q))"
  sorry

lemma combine_assn_waitout_in:
  assumes "ch \<in> chs"
  shows "combine_assn chs (WaitOut\<^sub>A d p ch e rdy @\<^sub>t P) (In\<^sub>A s ch v @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         (\<up>(d = 0) \<and>\<^sub>t \<up>(v = e (p 0)) \<and>\<^sub>t
          (IO\<^sub>A ch v @\<^sub>t combine_assn chs P Q))"
  sorry

lemma combineHL14:
  "combine_assn {''ch1'', ''ch2''} (ileft_blocks 0 ps) (iright_blocks 1 ws) \<Longrightarrow>\<^sub>t
   tot_blocks (length ps)"
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
  "ParValid
    (pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(X := 0))) (\<lambda>s. s = ((\<lambda>_. 0)(Y := 1))))
    (Parallel
      (Single (Rep (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True) [(''ch1''[!](\<lambda>s. s X), Skip)];
               Cm (''ch2''[?]X)))) {''ch1'', ''ch2''}
      (Single (Rep (Wait 1; Cm (''ch1''[?]Y); Cm (''ch2''[!](\<lambda>s. s Y - 1))))))
    (\<exists>\<^sub>g n. trace_gassn (tot_blocks n))"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
     apply (rule testHL14a)
    apply (rule testHL14b)
  apply auto
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
