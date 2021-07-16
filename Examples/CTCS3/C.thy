theory C
  imports HHLProver.ContinuousInv
    HHLProver.BigStepParallel
    HHLProver.Complementlemma
begin

locale C =
  fixes Stop_point :: real    \<comment> \<open>64000\<close>
  fixes V_limit :: real       \<comment> \<open>100\<close>
  fixes Next_V_limit :: real  \<comment> \<open>40\<close>
  fixes Period :: real        \<comment> \<open>0.125\<close>
  fixes A_minus :: real       \<comment> \<open>1\<close>
  fixes A_plus :: real        \<comment> \<open>1\<close>
  assumes Period[simp]: "Period > 0"
  assumes Stop_point[simp]: "Stop_point > 0"
  assumes V_limit: "V_limit > 0"
  assumes Next_V_limit: "Next_V_limit > 0"
  assumes A_minus: "A_minus > 0"
  assumes A_plus: "A_plus > 0"
begin

definition "Pull_curve_max_d = V_limit * V_limit / (2 * A_minus)"
definition "Pull_curve_coeff = sqrt (2 * A_minus)"

lemma Pull_curve_coeff_ge_zero [simp]:
  "Pull_curve_coeff > 0"
  unfolding Pull_curve_coeff_def using A_minus by auto

lemma Pull_curve_max_d_ge_zero [simp]:
  "Pull_curve_max_d > 0"
  unfolding Pull_curve_max_d_def using V_limit A_minus by auto

text \<open>Variables\<close>

definition A :: char where "A = CHR ''a''"
definition V :: char where "V = CHR ''b''"
definition S :: char where "S = CHR ''c''"
definition T :: char where "T = CHR ''k''"
definition Command_a :: char where "Command_a = CHR ''n''"

lemma train_vars_distinct [simp]: "A \<noteq> V" "A \<noteq> S" "A \<noteq> T" 
                                  "V \<noteq> A" "V \<noteq> S" "V \<noteq> T" 
                                  "S \<noteq> A" "S \<noteq> V" "S \<noteq> T"
                                  "T \<noteq> A" "T \<noteq> V" "T \<noteq> S"
  unfolding A_def V_def S_def T_def by auto

definition Plant :: proc where
  "Plant =
      Cm (''P2C''[!](\<lambda>s. s V));
      Cm (''P2C''[!](\<lambda>s. s S));
      Cm (''C2P''[?]A);
      Rep (
      Interrupt 
      (ODE ((\<lambda>_ _. 0)(S := (\<lambda>s. s V),
                      V := (\<lambda>s. s A))))(\<lambda> s. True)
      [(''P2C''[!](\<lambda>s. s V),
            Cm (''P2C''[!](\<lambda>s. s S));
            Cm (''C2P''[?]A))])"


fun Plant_inv :: "real \<times> real \<times> real \<Rightarrow> (real\<times>real)  list \<Rightarrow> tassn" where
  "Plant_inv (v0, s0, a0) [] = emp\<^sub>t"
| "Plant_inv (v0, s0, a0) ((T_t,a) # as) =
    WaitOut\<^sub>t T_t (\<lambda>t.  ((\<lambda>_. 0)(V := v0+a0*t, S := s0+v0*t+1/2*a0*t*t,
                                            A := a0))) ''P2C'' (\<lambda> s. s V) ({''P2C''},{})@\<^sub>t    
    (Out\<^sub>t (State ((\<lambda>_. 0)(V := v0+a0*T_t, S := s0+v0*T_t+1/2*a0*T_t*T_t, A := a0))) ''P2C'' (s0+v0*T_t+1/2*a0*T_t*T_t)) @\<^sub>t
    (In\<^sub>t (State ((\<lambda>_. 0)(V := v0+a0*T_t, S := s0+v0*T_t+1/2*a0*T_t*T_t, A := a0))) ''C2P'' a) @\<^sub>t
    Plant_inv (v0+a0*T_t, s0+v0*T_t+1/2*a0*T_t*T_t, a) (as)"

fun Plant_block :: "real \<times> real \<times> real \<Rightarrow> real \<Rightarrow> (real\<times>real)  list \<Rightarrow> tassn" where
"Plant_block (v0, s0, a00) a0 as =  
    (Out\<^sub>t (State ((\<lambda>_. 0)(V := v0, S := s0, A := a00))) ''P2C'' v0) @\<^sub>t    
    (Out\<^sub>t (State ((\<lambda>_. 0)(V := v0, S := s0, A := a00))) ''P2C'' s0) @\<^sub>t
    (In\<^sub>t (State ((\<lambda>_. 0)(V := v0, S := s0, A := a00))) ''C2P'' a0) @\<^sub>t 
    Plant_inv (v0, s0, a0) as"

fun Plant_end_state :: "real \<times> real \<times> real  \<Rightarrow> (real\<times>real)  list\<Rightarrow> state" where
  "Plant_end_state (v0, s0, a0) [] = ((\<lambda>_. 0)(V := v0, S := s0, A := a0))"
| "Plant_end_state (v0, s0, a0) ((T_t,a) # rest) =
   Plant_end_state (v0 + a0 * T_t, s0 + v0 * T_t + 
                          1/2 * a0 * T_t * T_t, a) rest"

lemma Plant_end_state_rw:
  "(Plant_end_state (v0, s0, a0) xs) =
   (\<lambda>_. 0)(V := Plant_end_state (v0, s0, a0) xs V,
           S := Plant_end_state (v0, s0, a0) xs S,
           A := Plant_end_state (v0, s0, a0) xs A)"
  apply (induct xs arbitrary: v0 s0 a0) by auto

definition Plant_ode_state :: "state \<Rightarrow> real \<Rightarrow> state" where
  "Plant_ode_state s T_t = (\<lambda>_. 0)(V := s V + s A * T_t,
           S := s S + s V * T_t + s A * T_t * T_t / 2,
           A := s A)"

lemma Plant_end_state_snoc:
  "Plant_end_state (v0, s0, a0) (xs @ [(T_t,a)]) =
   (Plant_ode_state (Plant_end_state (v0, s0, a0) (xs)) T_t) (A := a)"
  apply (induct xs arbitrary: v0 s0 a0 ) unfolding Plant_ode_state_def by auto


lemma Plant_inv_snoc:
  "Plant_inv (v0, s0, a0) (xs @ [(T_t,a)]) =
   Plant_inv (v0, s0, a0) xs @\<^sub>t
   WaitOut\<^sub>t T_t (\<lambda>t.  Plant_ode_state(Plant_end_state (v0, s0, a0) xs) t) ''P2C'' (\<lambda> s. s V) ({''P2C''},{})@\<^sub>t    
   Out\<^sub>t (State (Plant_ode_state(Plant_end_state (v0, s0, a0) xs) T_t)) ''P2C'' (Plant_end_state (v0, s0, a0) xs S  +
            Plant_end_state (v0, s0, a0) xs V * T_t  +
            (Plant_end_state (v0, s0, a0) xs A) * T_t  * T_t / 2) @\<^sub>t
   In\<^sub>t (State (Plant_ode_state(Plant_end_state (v0, s0, a0) xs) T_t)) ''C2P'' a 
   "
proof (induct xs arbitrary: v0 s0 a0 )
  case Nil
  then show ?case 
    unfolding Plant_ode_state_def apply (auto simp add: fun_upd_def)
    done
next
  case (Cons a xs)
  show ?case
    apply (cases a)
    subgoal for T_t' a'
      by (auto simp add: Cons join_assoc)
    done
qed

lemma Plant_block_snoc:
  "Plant_block (v0, s0, a00) a0 (xs @ [(T_t,a)]) =
   Plant_block (v0, s0, a00) a0  xs @\<^sub>t
   WaitOut\<^sub>t T_t (\<lambda>t.  Plant_ode_state(Plant_end_state (v0, s0, a0) xs) t) ''P2C'' (\<lambda> s. s V) ({''P2C''},{})@\<^sub>t    
   Out\<^sub>t (State (Plant_ode_state(Plant_end_state (v0, s0, a0) xs) T_t)) ''P2C'' (Plant_end_state (v0, s0, a0) xs S  +
            Plant_end_state (v0, s0, a0) xs V * T_t  +
            (Plant_end_state (v0, s0, a0) xs A) * T_t  * T_t / 2) @\<^sub>t
   In\<^sub>t (State (Plant_ode_state(Plant_end_state (v0, s0, a0) xs) T_t)) ''C2P'' a 
   "
  apply auto
  using Plant_inv_snoc[of v0 s0 a0 xs T_t a]
  by (auto simp add: join_assoc)

lemma Plant_prop:
  "\<Turnstile>
    {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0, S := s0, A := a00) \<and> emp\<^sub>t tr}
      Plant
    {\<lambda>s tr. \<exists>a0 xs. s = Plant_end_state (v0, s0, a0) xs \<and>
                 Plant_block (v0, s0, a00) a0 xs tr}"
  unfolding Plant_def
  apply(rule Valid_seq)
   apply (rule Valid_send_sp_st)
  apply(rule Valid_seq)
   apply (rule Valid_send_sp_st)
apply(rule Valid_seq)
   apply (rule Valid_receive_sp_st)
  apply(rule Valid_ex_pre)
  subgoal for a0
    apply(rule Valid_ex_post)
    apply(rule exI[where x= "a0"])
    apply(rule Valid_weaken_pre)
     prefer 2
     apply(rule Valid_rep)
     prefer 2
    subgoal
     apply(auto simp add: entails_def)
      apply(rule exI[where x= "[]"])
      by (auto simp add: join_assoc)
    apply(rule Valid_ex_pre)
    subgoal for xs
      apply(rule Valid_ode_out_unique_solution[where p="\<lambda> t. Plant_ode_state(Plant_end_state (v0, s0, a0) xs) t"])
          apply(auto simp add:Plant_ode_state_def ODEsolInf_def has_vderiv_on_def)
      subgoal
        apply (rule exI[where x="1"])
        apply auto
        apply (rule has_vector_derivative_projI)
        apply (auto simp add: state2vec_def)
         subgoal
       apply (rule has_vector_derivative_eq_rhs)
        apply (fast intro!: derivative_intros) by simp
     subgoal
      apply (rule has_vector_derivative_eq_rhs)
        apply (fast intro!: derivative_intros) by simp
     subgoal premises pre for x i
   proof-
     have eq: "i \<noteq> S \<Longrightarrow>
           i \<noteq> V \<Longrightarrow>
           (\<lambda>t. if i = A then Plant_end_state (v0, s0, a0) xs A
                 else ((\<lambda>_. 0)(V := Plant_end_state (v0, s0, a0) xs V + Plant_end_state (v0, s0, a0) xs A * t,
                               S := Plant_end_state (v0, s0, a0) xs S + Plant_end_state (v0, s0, a0) xs V * t + Plant_end_state (v0, s0, a0) xs A * t * t / 2))
                       i) = (\<lambda>t. if i = A then Plant_end_state (v0, s0, a0) xs A else 0)"
       by auto
     have 1: ?thesis if "i = A"
       using eq that by auto
     have 2: ?thesis if "i \<noteq> A"
       using eq that pre by auto 
     show ?thesis using 1 2 by linarith
       qed
       done
     subgoal using Plant_end_state_rw by auto
     subgoal
   proof-
    have bl:"bounded_linear (\<lambda>(v::vec) . \<chi> x. if x = V then (v$A) else if x = S then (v$V) else 0)"
      apply (rule bounded_linearI')
      using vec_lambda_unique by fastforce+
    show ?thesis
      unfolding state2vec_def vec2state_def fun_upd_def
      apply (rule c1_implies_local_lipschitz[where f'="(\<lambda>(t,v). Blinfun(\<lambda>(v::vec) . \<chi> x. if x = V then (v$A) else if x = S then (v$V) else 0))"])
         apply (auto simp add: bounded_linear_Blinfun_apply[OF bl])
      subgoal premises pre for t x
        unfolding has_derivative_def apply (auto simp add: bl)
        apply (rule vec_tendstoI)
        by (auto simp add: state2vec_def)
        done
    qed
    apply(rule Valid_ex_pre)
    subgoal for T_t
      apply(rule Valid_seq)
       apply (rule Valid_send_sp_st)
      apply(rule Valid_strengthen_post)
       prefer 2
       apply(rule Valid_receive_sp_st)
      apply(auto simp add:entails_def)
      subgoal for tr a
        apply(rule exI[where x="xs@[(T_t,a)]"])
        apply auto
        subgoal using Plant_end_state_snoc Plant_end_state_rw
          by(auto simp add: Plant_ode_state_def)
        using Plant_inv_snoc
        by(auto simp add: Plant_ode_state_def join_assoc)
      done
    done
  done
  done
     

definition fs :: "real \<Rightarrow> real" where
   "fs s =
      (let D = Stop_point - s in
        if D \<ge> Pull_curve_max_d then
          V_limit
        else if D \<ge> 0 then
          Pull_curve_coeff * sqrt(D)
        else 0)"

definition com_a :: "real \<Rightarrow> real \<Rightarrow> real" where
  "com_a s v =
      (let s1' = s + v * Period + A_plus * Period\<^sup>2 / 2 in
       let target_v1 = fs s1' in
         if v + A_plus * Period \<le> target_v1 then
           A_plus
         else let s2' = s + v * Period in
              let target_v2 = fs s2' in
                if v \<le> target_v2 then 0
                else -A_minus)"
lemma control_vars_distinct [simp]: "Command_a \<noteq> V" "Command_a \<noteq> S" 
                                  "V \<noteq> Command_a" "V \<noteq> S" 
                                  "S \<noteq> Command_a" "S \<noteq> V" 
 unfolding Command_a_def V_def S_def by auto

definition Control :: proc where
  "Control =
      Cm (''P2C''[?]V);
      Cm (''P2C''[?]S);
      Command_a ::= (\<lambda>s. com_a (s S) (s V));
      Cm (''C2P''[!](\<lambda>s. s Command_a));
    Rep(
      Wait (\<lambda> s. Period);
      Cm (''P2C''[?]V);
      Cm (''P2C''[?]S);
      Command_a ::= (\<lambda>s. com_a (s S) (s V));
      Cm (''C2P''[!](\<lambda>s. s Command_a)))"

fun Control_inv :: "real \<times> real \<times> real  \<Rightarrow> (real \<times> real) list \<Rightarrow> tassn" where
  "Control_inv (v0, s0, a0) [] = emp\<^sub>t"
| "Control_inv (v0, s0, a0) ((v, s) # rest) =
    Wait\<^sub>t Period (\<lambda> t. (State ((\<lambda>_. 0)(V := v0, S := s0, Command_a := a0)))) ({},{}) @\<^sub>t
    In\<^sub>t (State ((\<lambda>_. 0)(V := v0, S := s0, Command_a := a0))) ''P2C'' v @\<^sub>t
    In\<^sub>t (State ((\<lambda>_. 0)(V := v, S := s0, Command_a := a0))) ''P2C'' s @\<^sub>t
    Out\<^sub>t (State ((\<lambda>_. 0)(V := v, S := s, Command_a := com_a s v)))  ''C2P'' (com_a s v)  @\<^sub>t
    Control_inv (v,s,com_a s v) rest"


fun Control_block :: "real \<times> real \<times> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<times> real) list \<Rightarrow> tassn" where
  "Control_block (v0, s0, a0) v s rest  =
    In\<^sub>t (State ((\<lambda>_. 0)(V := v0, S := s0, Command_a := a0))) ''P2C'' v @\<^sub>t
    In\<^sub>t (State ((\<lambda>_. 0)(V := v, S := s0, Command_a := a0))) ''P2C'' s @\<^sub>t
    Out\<^sub>t (State ((\<lambda>_. 0)(V := v, S := s, Command_a := com_a s v)))  ''C2P'' (com_a s v)  @\<^sub>t
    Control_inv (v,s,com_a s v) rest"



fun Control_end_state :: "real \<times> real \<times> real  \<Rightarrow> (real \<times> real) list \<Rightarrow> state" where
  "Control_end_state (v0, s0, a0) [] = ((\<lambda>_. 0)(V := v0, S := s0, Command_a := a0))"
| "Control_end_state (v0, s0, a0) ((v, s) # rest) = Control_end_state (v, s, com_a s v) rest"

definition control_state :: "state \<Rightarrow> real \<Rightarrow> real \<Rightarrow> state" where
  "control_state state v s = state(V := v, S := s, Command_a := com_a s v)"

lemma Control_end_state_snoc:
  "Control_end_state (v0, s0, a0) (xs @ [(v, s)]) =
   control_state (Control_end_state (v0, s0, a0) xs) v s"
  apply (induct xs arbitrary: v0 s0 a0 ) 
  unfolding control_state_def by auto

lemma Control_end_state_rw:
  "Control_end_state (v0, s0, a0) xs =
   (\<lambda>_ . 0) (V := Control_end_state (v0, s0, a0) xs V, 
             S := Control_end_state (v0, s0, a0) xs S, 
             Command_a := Control_end_state (v0, s0, a0) xs Command_a)"
  apply (induct xs arbitrary: v0 s0 a0 ) 
  unfolding control_state_def by auto

lemma Control_state_end_state:
"control_state (Control_end_state (v0, s0, a0) xs) v s = (\<lambda>_ . 0) (V := v, 
             S := s, 
             Command_a := com_a s v)"
  apply(subst Control_end_state_rw[of v0 s0 a0 xs])
  unfolding control_state_def by auto


lemma Control_inv_snoc:
  "Control_inv (v0, s0, a0) (xs @ [(v, s)]) =
   Control_inv (v0, s0, a0) xs @\<^sub>t
   Wait\<^sub>t Period (\<lambda> t. (State ((Control_end_state (v0, s0, a0) xs)))) ({},{})@\<^sub>t
   In\<^sub>t (State ((Control_end_state (v0, s0, a0) xs))) ''P2C'' v @\<^sub>t
   In\<^sub>t (State ((Control_end_state (v0, s0, a0) xs)(V := v))) ''P2C'' s @\<^sub>t
   Out\<^sub>t (State (control_state (Control_end_state (v0, s0, a0) xs) v s)) ''C2P'' ((control_state (Control_end_state (v0, s0, a0) xs) v s) Command_a)"
  apply (induct xs arbitrary: v0 s0 a0 )
   apply (auto simp add: join_assoc Control_end_state_snoc control_state_def fun_upd_twist)[1]
  apply (auto simp add: join_assoc Control_end_state_snoc fun_upd_twist)
  done

lemma Control_prop:
  "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(V := v0, S := s0, Command_a := a0)) \<and> emp\<^sub>t tr}
      Control
    {\<lambda>s tr. \<exists>v' s' xs. s = Control_end_state (v', s', com_a s' v') xs 
                         \<and> Control_block (v0, s0, a0) v' s' xs tr}"
  unfolding Control_def
  apply(rule Valid_seq)
   apply(rule Valid_receive_sp_st)
  apply(rule Valid_ex_pre)
  subgoal for v'
    apply(rule Valid_seq)
     apply(rule Valid_receive_sp_st)
    apply(rule Valid_ex_pre)
    subgoal for s'
      apply(rule Valid_seq)
       apply(rule Valid_assign_sp_st)
      apply(rule Valid_seq)
       apply(rule Valid_send_sp_st)
      apply(rule Valid_weaken_pre)
       prefer 2
       apply(rule Valid_rep)
       prefer 2
      subgoal
        apply(auto simp add:entails_def)
        subgoal for tr
          apply(rule exI[where x="v'"])
          apply(rule exI[where x="s'"])
          apply(rule exI[where x="[]"])
          by (auto simp add:join_assoc fun_upd_twist)
        done
      apply(rule Valid_ex_pre)
      subgoal for v'
        apply(rule Valid_ex_pre)
        subgoal for s'
          apply(rule Valid_ex_pre)
          subgoal for xs
            apply(rule Valid_seq)
             apply(rule Valid_wait_sp_st)
            apply simp
            apply(rule Valid_seq)
             apply(rule Valid_receive_sp_st)
            apply(rule Valid_ex_pre)
            subgoal for v''
              apply(rule Valid_seq)
               apply(rule Valid_receive_sp_st)
              apply(rule Valid_ex_pre)
              subgoal for s''
                apply(rule Valid_seq)
                 apply(rule Valid_assign_sp_st)
                apply(rule Valid_strengthen_post)
                 prefer 2
                 apply(rule Valid_send_sp_st)
                apply(auto simp add:entails_def)
                apply(rule exI[where x="v'"])
                apply(rule exI[where x="s'"])
                apply(rule exI[where x="xs@[(v'',s'')]"])
                apply auto
                subgoal
                  using Control_end_state_snoc 
                  apply(auto simp add:control_state_def)
                  done
                using Control_inv_snoc 
                apply(auto simp add:control_state_def join_assoc)
                done
              done
            done
          done
        done
      done
    done
  done

lemma fs_at_least_zero:
  "fs s \<ge> 0"
  unfolding fs_def Let_def apply auto
  using V_limit apply auto
  using  Pull_curve_coeff_ge_zero
  by (simp add: dual_order.strict_implies_order)

lemma fs_at_most_limit:
  "fs s \<le> V_limit"
  unfolding fs_def Let_def
  apply auto
  subgoal premises pre
  proof-
    have "Stop_point - s < V_limit * V_limit / (2 * A_minus)"
        using pre unfolding Pull_curve_max_d_def Pull_curve_coeff_def by auto
      then have 31: "(Stop_point - s) * (2 * A_minus) < V_limit * V_limit"
        using A_minus
        by (metis lattice_ab_group_add_class.zero_less_double_add_iff_zero_less_single_add mult_2 pos_less_divide_eq)
      have 32: "sqrt (2 * A_minus) * sqrt (Stop_point - s) = sqrt ((Stop_point - s) * (2 * A_minus))"
        using A_minus pre by (simp add: real_sqrt_mult)
      have 33: "V_limit = sqrt (V_limit * V_limit)"
        using V_limit by auto
      show ?thesis 
        unfolding Pull_curve_max_d_def Pull_curve_coeff_def 32
        apply (subst 33) using 31 
        using real_sqrt_less_iff 
        using less_eq_real_def by blast
    qed
    subgoal using V_limit by auto
    done


lemma fs_prop1:
  assumes "v \<le> fs(s)"
    and "v \<ge> 0"
    and "s \<le> Stop_point"
  shows "v^2 \<le> 2 * A_minus * (Stop_point - s)"
proof-
  have 1: "v^2 \<le> 2 * A_minus * (Stop_point - s)" if "Stop_point - s \<ge> Pull_curve_max_d"
  proof-
    have 11: "v\<le>V_limit"
      using assms(1) that unfolding fs_def Let_def by auto
    then have 12: "v^2\<le>V_limit^2"
      using assms(2) V_limit by simp
    have 13:" V_limit^2 \<le>2 * A_minus * (Stop_point - s)" 
      using that A_minus unfolding Pull_curve_max_d_def
      by (auto simp add: power2_eq_square field_simps)
    then show ?thesis using 12 by auto
  qed
  have 2:"v^2 \<le> 2 * A_minus * (Stop_point - s)" if "Stop_point - s < Pull_curve_max_d"
  proof-
    have 21:"v \<le> Pull_curve_coeff * sqrt(Stop_point - s)"
      using assms that unfolding fs_def by auto
    then show ?thesis using assms A_minus unfolding Pull_curve_coeff_def 
      by (metis power2_eq_square real_sqrt_le_iff real_sqrt_mult real_sqrt_pow2)
  qed
  show ?thesis using 1 2 assms 
    by linarith
qed


fun loop_once :: "real \<times> real \<Rightarrow> real \<times> real" where
  "loop_once (s, v) = 
    (let a = com_a s v in
     let v' = v + a * Period in
     let s' = s + v * Period + a * Period * Period / 2 in
      (s', v'))"


declare loop_once.simps[simp del]


lemma loop_once_invariant:
  assumes "v \<le> fs s \<and> s \<le> Stop_point"
    and "(s', v') = loop_once (s, v)"
  shows "v' \<le> fs s' \<and> s' \<le> Stop_point"
proof -
  have case1:"v' \<le> fs s' \<and> s' \<le> Stop_point" if cond1:"v + A_plus * Period \<le> fs (s + v * Period + A_plus * Period\<^sup>2 / 2)"
  proof-
    have 1:"com_a s v = A_plus" 
      using that unfolding com_a_def by auto
    have 2:"(s', v') = (s + v * Period + A_plus * Period\<^sup>2 / 2,v + A_plus * Period )" 
      using assms 1  that loop_once.simps by (auto simp add: power2_eq_square)
    have 3:"v' \<le> fs s'" 
      using that 2
      unfolding fs_def Let_def by auto
    have 4:"s' \<le> Stop_point" 
    proof (cases "v' > 0")
      case True
      then show ?thesis 
        using 3 2 that apply(simp add: fs_def Let_def) apply auto 
        by (smt Pull_curve_max_d_ge_zero)
    next
      case False
      then show ?thesis 
      proof-
        have "v + A_plus * Period \<le> 0"
          using False 2 by auto
        then have "(v + A_plus * Period)*Period \<le> 0"
          by (meson Period eucl_less_le_not_le mult_le_0_iff)
        then have "v * Period + A_plus * Period\<^sup>2 \<le>0"
          by(auto simp add:power2_eq_square algebra_simps)
        then have "v * Period + A_plus * Period\<^sup>2 - A_plus * Period*Period/2 \<le>0"
          apply(subgoal_tac "A_plus * Period*Period/2 > 0")
           prefer 2 using A_plus apply simp
          by linarith
        then have "v * Period + A_plus * Period\<^sup>2/2 \<le>0"
          by(auto simp add: power2_eq_square)
        then have "s + v * Period + A_plus * Period\<^sup>2/2 \<le> Stop_point"
          using assms by auto
        then show ?thesis using 2 apply auto done
      qed
    qed
     show ?thesis using 3 4 by auto
  qed
  have case2:"v' \<le> fs s' \<and>  s' \<le> Stop_point" if cond2:
    "\<not> v + A_plus * Period \<le> fs (s + v * Period + A_plus * Period\<^sup>2 / 2)" 
    "v \<le> fs (s + v * Period)" 
  proof-
    have 1: "com_a s v = 0" using that unfolding com_a_def by auto
    have 2: "(s',v') = (s + v * Period, v)" using assms 1 loop_once.simps by auto
    have 3:"v' \<le> fs s'" 
      using 2 that
      unfolding fs_def Let_def by auto
    have 4:"s' \<le> Stop_point" 
    proof-
      have "v \<le> 0" if "s' > Stop_point"
        using 2 3 unfolding fs_def Let_def 
        using Pull_curve_max_d_ge_zero assms(1) that by auto
      then have"s\<ge>s'" if "s' > Stop_point" using 2 that
        by (smt Period old.prod.inject zero_less_mult_pos2)
      then show ?thesis using assms 
        using leI 2   by auto
    qed
    then show ?thesis using 3 4  by auto
  qed
  have case3:"v' \<le> fs s'  \<and> s' \<le> Stop_point" if cond3:
    "\<not> v + A_plus * Period \<le> fs (s + v * Period + A_plus * Period\<^sup>2 / 2)"
    "\<not> v \<le> fs (s + v * Period)" 
  proof-
    have 1: "com_a s v = -A_minus" using that unfolding com_a_def by auto
    have 2:"(s',v') = (s + v * Period - A_minus * Period\<^sup>2 / 2, v - A_minus  * Period)"
        using assms 1  cond3 loop_once.simps by (auto simp add: power2_eq_square)
    have 31:"s' \<le> Stop_point" if "v\<ge>0"
        using 2 apply auto
        subgoal premises pre
        proof-
          have "v^2 \<le> 2 * A_minus * (Stop_point - s)"
              using fs_prop1 assms that by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le> 
                      2 * A_minus * (Stop_point - s) - 2 * A_minus * v * Period + A_minus^2 * Period^2"
            by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le>
                      2 * A_minus * (Stop_point - s - v * Period + 1/2 * A_minus * Period^2)"
            by (auto simp add: algebra_simps power2_eq_square)
          then have "(v - A_minus * Period)^2 \<le> 2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2))"
            by (auto simp add: algebra_simps power2_eq_square)
          then have " 2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)) \<ge> 0"
            by (smt zero_le_power2)
          then have "(Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)) \<ge> 0"
            by (metis A_minus less_eq_real_def linordered_ab_group_add_class.double_add_le_zero_iff_single_add_le_zero mult_less_cancel_right not_one_le_zero not_real_square_gt_zero one_add_one zero_le_mult_iff zero_less_mult_iff)
          then show ?thesis by auto
            qed
            done
          have 32:"s' \<le> Stop_point" if "v<0"
            using 2 apply auto
            apply (subgoal_tac"s \<le> Stop_point")
             prefer 2 using assms apply auto
            apply (subgoal_tac"v * Period \<le> 0")
            prefer 2 using that Period 
             apply (smt cond3(2) fs_at_least_zero)
            apply (subgoal_tac" A_minus * Period\<^sup>2 / 2 \<ge> 0")
             prefer 2
            subgoal
              using A_minus by(auto simp add:power2_eq_square)
            by linarith
       have 41:"v' \<le> fs s'" if "v\<ge>0"
        using 2
        unfolding fs_def Let_def apply auto
        subgoal using assms(1) fs_at_most_limit A_minus Period 
          by (smt mult_diff_mult real_mult_less_iff1)
        subgoal premises pre
        proof-
          have "v^2 \<le> 2 * A_minus * (Stop_point - s)"
            using fs_prop1 assms that by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le> 
                      2 * A_minus * (Stop_point - s) - 2 * A_minus * v * Period + A_minus^2 * Period^2"
            by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le>
                      2 * A_minus * (Stop_point - s - v * Period + 1/2 * A_minus * Period^2)"
            by (auto simp add: algebra_simps power2_eq_square)
          then have "(v - A_minus * Period)^2 \<le> 2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2))"
            by (auto simp add: algebra_simps power2_eq_square)
          then have a:"sqrt((v - A_minus * Period)^2) \<le> sqrt(2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)))"
            using real_sqrt_le_iff by blast
          have b:"(v - A_minus * Period) <= sqrt((v - A_minus * Period)^2)" 
            by auto
          have c:"sqrt(2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2))) = sqrt(2 * A_minus) * sqrt((Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)))"
            by (simp add: real_sqrt_mult)
          show ?thesis using a b c unfolding Pull_curve_coeff_def by auto
        qed
        subgoal using assms fs_at_most_limit A_minus Period 
          using Pull_curve_max_d_ge_zero by linarith
        subgoal using 31 that by auto
        done
      have 42:"v' \<le> fs s'" if "v<0"
        using 2
        unfolding fs_def Let_def apply auto
        subgoal using assms(1) fs_at_most_limit A_minus Period 
          by (smt mult_diff_mult real_mult_less_iff1)
        subgoal 
          apply(subgoal_tac "s + v * Period - A_minus * Period\<^sup>2 / 2  \<le> s")
           prefer 2 subgoal
           apply (subgoal_tac"s \<le> Stop_point")
             prefer 2 using assms apply auto
            apply (subgoal_tac"v * Period \<le> 0")
            prefer 2 using that Period 
             apply (smt cond3(2) fs_at_least_zero)
            apply (subgoal_tac" A_minus * Period\<^sup>2 / 2 \<ge> 0")
             prefer 2
            subgoal
              using A_minus by(auto simp add:power2_eq_square)
            apply linarith
            done
            apply(subgoal_tac" \<not> Pull_curve_max_d \<le> Stop_point - s")
             prefer 2
             apply simp
            apply(subgoal_tac"v \<le> Pull_curve_coeff * sqrt (Stop_point - s)")
            prefer 2
            subgoal using assms unfolding fs_def Let_def by auto
            apply(subgoal_tac"v - A_minus * Period \<le> v")
            prefer 2 subgoal using A_minus 
              by (smt cond3(2) fs_at_least_zero that)
            apply(subgoal_tac"Pull_curve_coeff * sqrt (Stop_point - s)\<le>Pull_curve_coeff * sqrt (Stop_point - (s + v * Period - A_minus * Period\<^sup>2 / 2))")
             apply linarith
            by simp
          subgoal using assms fs_at_most_limit A_minus Period 
            using Pull_curve_max_d_ge_zero by linarith
          subgoal using that A_minus 
            using "32" by auto
          done
       show ?thesis using 31 32 41 42 
         using leI by blast
    qed
  show ?thesis
    using case1 case2 case3
    by linarith
qed


fun loop_invariant :: "real \<times> real \<Rightarrow> bool" where
  "loop_invariant (s, v) \<longleftrightarrow> v \<le> fs s \<and> s \<le> Stop_point"


lemma loop_once_invariant':
  assumes "loop_invariant (s,v)"
    and "(s', v') = loop_once (s, v)"
  shows "loop_invariant (s',v')"
  using loop_once_invariant assms
  using loop_invariant.simps by blast


fun tot_inv :: "real \<times> real \<Rightarrow> nat \<Rightarrow> tassn" where
  "tot_inv (s0, v0) 0 = emp\<^sub>t"
| "tot_inv (s0, v0) (Suc n) =
   (\<up>(loop_invariant (s0, v0)) \<and>\<^sub>t Wait\<^sub>t (Period) (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0 + com_a s0 v0 * t, S := s0 + v0 * t + com_a s0 v0 * t * t / 2, A := com_a s0 v0))) 
                    (State ((\<lambda>_. 0)(V := v0, S := s0, Command_a := com_a s0 v0)) )) ({''P2C''}, {})) @\<^sub>t
   IO\<^sub>t ''P2C'' (snd (loop_once (s0, v0))) @\<^sub>t
   IO\<^sub>t ''P2C'' (fst (loop_once (s0, v0))) @\<^sub>t
   IO\<^sub>t ''C2P'' (com_a (fst (loop_once (s0, v0))) (snd (loop_once (s0, v0)))) @\<^sub>t
   tot_inv (loop_once (s0, v0) ) n"



fun tot_block :: "real \<times> real \<Rightarrow> nat \<Rightarrow> tassn" where
"tot_block (s0, v0) n =   
   IO\<^sub>t ''P2C'' v0 @\<^sub>t
   IO\<^sub>t ''P2C'' s0 @\<^sub>t
   IO\<^sub>t ''C2P'' (com_a s0 v0) @\<^sub>t tot_inv (s0, v0) n "

lemma combine0:
  "loop_invariant (s0, v0) \<Longrightarrow> 
   combine_assn {''P2C'', ''C2P''}
     (Plant_inv (v0, s0, com_a s0 v0) as) (Control_inv (v0, s0, com_a s0 v0) vs) 
      \<Longrightarrow>\<^sub>t  tot_inv (s0,v0) (length as)"
proof (induct as arbitrary: vs s0 v0)
case Nil
  then show ?case 
  proof(cases vs)
    case Nil
    then show ?thesis 
      by auto
  next
    case (Cons vsp vsrest)
    then show ?thesis 
      apply auto
      subgoal
    proof (cases vsp)
      case (Pair v1 s1)
      then show ?thesis 
        apply auto
        apply (rule entails_tassn_trans)
       apply (rule combine_assn_emp_wait)
        apply simp by (rule false_assn_entails)
    qed
    done
  qed
next
  case (Cons asp asrest)
  note Cons1 = Cons
  then show ?case 
  proof (cases asp)
    case (Pair T1 a1)
    note Pair1 = Pair
    then show ?thesis 
    proof (cases vs)
      case Nil
      then show ?thesis 
        apply(auto simp add:Pair)
        apply (rule entails_tassn_trans)
       apply(rule combine_assn_waitout_emp)
         apply simp by (rule false_assn_entails)
next
  case (Cons vsp vsrest)
  then show ?thesis 
    subgoal
proof (cases vsp)
  case (Pair v1' s1')
  then show ?thesis 
    apply(auto simp add: Cons Pair1)
    apply (rule entails_tassn_trans)
      apply (rule combine_assn_waitout_wait)
       apply auto
    apply (rule entails_tassn_conj)
    subgoal 
      using Cons1(2) apply (auto simp add: pure_assn_def entails_tassn_def) 
      done
    apply (rule entails_tassn_cancel_left)
apply (rule entails_tassn_trans)
     apply (rule combine_assn_waitout_in)
      apply (auto simp add:loop_once.simps Let_def)
apply (rule entails_tassn_cancel_left)
    apply (rule entails_tassn_trans)
     apply (rule combine_assn_out_in)
    apply auto
    apply (rule entails_tassn_cancel_left)
 apply (rule entails_tassn_trans)
     apply (rule combine_assn_in_out)
     apply auto
    apply (rule entails_tassn_cancel_left)
    using Cons1(1)[of "s0 + v0 * Period + com_a s0 v0 * Period * Period / 2" "v0 + com_a s0 v0 * Period" "vsrest"] Cons1(2)
    using loop_once_invariant'[of s0 v0 "s0 + v0 * Period + com_a s0 v0 * Period * Period / 2" "v0 + com_a s0 v0 * Period"]
    by(auto simp add:loop_once.simps Let_def)
qed
  done
qed
  qed
qed

lemma combine:
  "loop_invariant (s0, v0) \<Longrightarrow> 
   combine_assn {''P2C'', ''C2P''}
     (Plant_block (v0, s0, a00) a0 as) (Control_block (v00', s00', a00') v0' s0' vs) 
      \<Longrightarrow>\<^sub>t  tot_block (s0,v0) (length as)"
  apply auto
apply (rule entails_tassn_trans)
     apply (rule combine_assn_out_in)
    apply auto
  apply (rule entails_tassn_cancel_left)
apply (rule entails_tassn_trans)
     apply (rule combine_assn_out_in)
    apply auto
  apply (rule entails_tassn_cancel_left)
apply (rule entails_tassn_trans)
     apply (rule combine_assn_in_out)
    apply auto
  apply (rule entails_tassn_cancel_left)
  apply(rule combine0)
  by auto

definition System :: pproc where
  "System = Parallel (Single Plant)
                     {''P2C'', ''C2P''}
                     (Single Control)"


lemma System_Prop:
  assumes "loop_invariant (s0, v0)"
  shows "\<Turnstile>\<^sub>p
    {pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(V := v0, S := s0, A := a00)))
               (\<lambda>s. s = ((\<lambda>_. 0)(V := v00', S := s00', Command_a := a00')))}
      System
    {\<exists>\<^sub>g n. trace_gassn (tot_block (s0,v0) n)}"
unfolding System_def
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
  apply (rule Plant_prop)
  apply (rule Control_prop)
  apply (auto simp add: sing_gassn_split sing_gassn_ex)
  apply (rule sync_gassn_ex_pre_left)
  apply (rule sync_gassn_ex_pre_left)
  subgoal for a0 as
  apply (rule sync_gassn_ex_pre_right)
  apply (rule sync_gassn_ex_pre_right)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for v' s' vs
    unfolding sync_gassn_state_left sync_gassn_state_right
    apply (rule entails_ex_gassn)
    apply (rule exI[where x="length as"])
    apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
     apply (rule entails_tassn_trans)
      prefer 2 apply(rule combine[OF assms])
     apply (rule combine_assn_mono)
    by (auto simp add: entails_tassn_def entails_gassn_def and_gassn_def)
  done
  done

end
end