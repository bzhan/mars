theory CTCS3p
  imports HHLProver.ContinuousInv
    HHLProver.BigStepParallel
    HHLProver.Complementlemma
begin

locale CTCS3 =
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
definition Level :: char where "Level = CHR ''l''"
definition Next_seg_v :: char where "Next_seg_v = CHR ''s''"

text \<open>Processes\<close>
lemma train_vars_distinct [simp]: "A \<noteq> V" "A \<noteq> S" "A \<noteq> T" 
                                  "V \<noteq> A" "V \<noteq> S" "V \<noteq> T" 
                                  "S \<noteq> A" "S \<noteq> V" "S \<noteq> T"
                                  "T \<noteq> A" "T \<noteq> V" "T \<noteq> S"
  unfolding A_def V_def S_def T_def by auto

definition Train :: proc where
  "Train =
    Rep (
      T ::= (\<lambda>_. 0);
      Cont (ODE ((\<lambda>_ _. 0)(S := (\<lambda>s. s V),
                           V := (\<lambda>s. s A), T := (\<lambda>_. 1))))
                ((\<lambda>s. s T < Period \<and> s V > 0));
      Wait (\<lambda>s. Period - s T);
      Cm (''Train2Control''[!](\<lambda>s. s V));
      Cm (''Train2Control''[!](\<lambda>s. s S));
      Cm (''Control2Train''[?]A)
    )"


text \<open>Running time of ODE\<close>
definition T_t :: "real \<Rightarrow> real \<Rightarrow> real" where
  "T_t v0 a = (if v0 \<le> 0 then 0
               else (if v0 + a * Period > 0 then Period
               else v0/(-a)))"

lemma T_t_prop1:
  "\<not>v0 \<le> 0 \<Longrightarrow> 0 < T_t v0 a"
  unfolding T_t_def using Period
  apply auto
  subgoal premises pre
  proof -
    have "a<0" using pre Period 
      by (smt mult_nonneg_nonneg)
    then show ?thesis using pre 
      by (simp add: divide_pos_neg)
  qed
  done

lemma T_t_prop2:
  "\<not>v0 \<le> 0 \<Longrightarrow> T_t v0 a \<le> Period"
  unfolding T_t_def
  apply auto
  by (metis Period add_nonneg_pos add_pos_nonneg leI linear linorder_neqE_linordered_idom
        mult.commute mult_pos_pos mult_zero_left neg_less_minus_divide_eq real_0_less_add_iff)

lemma T_t_prop3:
  "\<not>v0 \<le> 0 \<Longrightarrow> \<not> T_t v0 a < Period \<Longrightarrow> T_t v0 a = Period"
  using T_t_prop2 
  by (simp add: dual_order.antisym)

lemma linear_ge:
  assumes "(tmax::real)\<ge>0"
    and "(a::real) \<ge> (c::real)"
    and "a + (b::real)*tmax\<ge>c"
    and "(t::real) \<ge> 0"
    and "t \<le> tmax"
  shows "a+b*t \<ge> c"
proof (cases "b\<ge>0")
  case True
  then have "b*t \<ge>0"
    using assms by auto
  then have "a+b*t \<ge>a" 
    by auto 
  then show ?thesis using assms by auto 
next
  case False
  then have "b*t \<ge> b*tmax"
    using assms by auto
  then have "a+b*t \<ge> a+b*tmax"
    by auto
  then show ?thesis using assms by auto
qed

lemma linear_g:
  assumes "(tmax::real)\<ge>0"
    and "(a::real) > (c::real)"
    and "a + (b::real)*tmax>c"
    and "(t::real) \<ge> 0"
    and "t \<le> tmax"
  shows "a+b*t > c"
proof (cases "b\<ge>0")
  case True
  then have "b*t \<ge>0"
    using assms by auto
  then have "a+b*t \<ge>a" 
    by auto 
  then show ?thesis using assms by auto 
next
  case False
  then have "b*t \<ge> b*tmax"
    using assms by auto
  then have "a+b*t \<ge> a+b*tmax"
    by auto
  then show ?thesis using assms by auto
qed


definition T_tassn :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> tassn" where
  "T_tassn v0 s0 a =
    (if v0 \<le> 0 then
       emp\<^sub>t @\<^sub>t Wait\<^sub>t (Period) (\<lambda>t. State ((\<lambda>_. 0)(V := v0, S := s0,
                                            A := a, T := 0))) ({}, {})
     else
       Wait\<^sub>t (T_t v0 a) (\<lambda>t. State ((\<lambda>_. 0)(V := v0+a*t, S := s0+v0*t+1/2*a*t*t,
                                            A := a, T := t))) ({}, {}) 
    @\<^sub>t Wait\<^sub>t (Period - T_t v0 a) (\<lambda>t. State ((\<lambda>_. 0)(V := v0+a*(T_t v0 a), S := s0+v0*(T_t v0 a)+1/2*a*(T_t v0 a)*(T_t v0 a),
                                            A := a, T := (T_t v0 a)))) ({}, {}))"


fun Train_inv :: "real \<times> real \<times> real \<times> real\<Rightarrow> real list \<Rightarrow> tassn" where
  "Train_inv (v0, s0, a0, t0) [] = emp\<^sub>t"
| "Train_inv (v0, s0, a0, t0) (a # as) =
    T_tassn v0 s0 a0 @\<^sub>t
    (Out\<^sub>t (State ((\<lambda>_. 0)(V := v0+a0*(T_t v0 a0), S := s0+v0*(T_t v0 a0)+1/2*a0*(T_t v0 a0)*(T_t v0 a0), A := a0, T := (T_t v0 a0)))) ''Train2Control'' (v0+a0*(T_t v0 a0))) @\<^sub>t    
    (Out\<^sub>t (State ((\<lambda>_. 0)(V := v0+a0*(T_t v0 a0), S := s0+v0*(T_t v0 a0)+1/2*a0*(T_t v0 a0)*(T_t v0 a0), A := a0, T := (T_t v0 a0)))) ''Train2Control'' (s0+v0*(T_t v0 a0)+1/2*a0*(T_t v0 a0)*(T_t v0 a0))) @\<^sub>t
    (In\<^sub>t (State ((\<lambda>_. 0)(V := v0+a0*(T_t v0 a0), S := s0+v0*(T_t v0 a0)+1/2*a0*(T_t v0 a0)*(T_t v0 a0), A := a0, T := (T_t v0 a0)))) ''Control2Train'' a) @\<^sub>t
    Train_inv (v0+a0*(T_t v0 a0), s0+v0*(T_t v0 a0)+1/2*a0*(T_t v0 a0)*(T_t v0 a0), a, T_t v0 a0) (as)"

fun Train_end_state :: "real \<times> real \<times> real \<times> real \<Rightarrow> real list \<Rightarrow> state" where
  "Train_end_state (v0, s0, a0, t0) [] = ((\<lambda>_. 0)(V := v0, S := s0, A := a0, T := t0))"
| "Train_end_state (v0, s0, a0, t0) (a # rest) =
   Train_end_state (v0 + a0 * T_t v0 a0, s0 + v0 * (T_t v0 a0) + 
                          1/2 * a0 * (T_t v0 a0) * (T_t v0 a0), a, T_t v0 a0) rest"

lemma Train_end_state_rw:
  "(Train_end_state (v0, s0, a0, t0) xs)(T := 0) =
   (\<lambda>_. 0)(V := Train_end_state (v0, s0, a0, t0) xs V,
           S := Train_end_state (v0, s0, a0, t0) xs S,
           A := Train_end_state (v0, s0, a0, t0) xs A, T := 0)"
  apply (induct xs arbitrary: v0 s0 a0 t0) by auto

definition Train_ode_state :: "state \<Rightarrow> state" where
  "Train_ode_state s = (\<lambda>_. 0)(V := s V + s A * (T_t  (s V)  (s A)),
           S := s S + s V * (T_t  (s V)  (s A)) + s A * (T_t  (s V)  (s A)) * (T_t  (s V)  (s A)) / 2,
           A := s A, T := (T_t  (s V)  (s A)))"
  
lemma Train_end_state_snoc:
  "Train_end_state (v0, s0, a0, t0) (xs @ [a]) =
   (Train_ode_state (Train_end_state (v0, s0, a0, t0) (xs))) (A := a)"
  apply (induct xs arbitrary: v0 s0 a0 t0) unfolding Train_ode_state_def by auto

lemma Train_inv_snoc:
  "Train_inv (v0, s0, a0, t0) (xs @ [a]) =
   Train_inv (v0, s0, a0, t0) xs @\<^sub>t
   T_tassn (Train_end_state (v0, s0, a0, t0) xs V) (Train_end_state (v0, s0, a0, t0) xs S) (Train_end_state (v0, s0, a0, t0) xs A) @\<^sub>t
   Out\<^sub>t (State (Train_ode_state(Train_end_state (v0, s0, a0, t0) xs))) ''Train2Control'' (Train_end_state (v0, s0, a0, t0) xs V + (Train_end_state (v0, s0, a0, t0) xs A) * T_t (Train_end_state (v0, s0, a0, t0) xs V) (Train_end_state (v0, s0, a0, t0) xs A)) @\<^sub>t
   Out\<^sub>t (State (Train_ode_state(Train_end_state (v0, s0, a0, t0) xs))) ''Train2Control'' (Train_end_state (v0, s0, a0, t0) xs S  +
            Train_end_state (v0, s0, a0, t0) xs V * T_t (Train_end_state (v0, s0, a0, t0) xs V) (Train_end_state (v0, s0, a0, t0) xs A) +
            (Train_end_state (v0, s0, a0, t0) xs A) * T_t (Train_end_state (v0, s0, a0, t0) xs V) (Train_end_state (v0, s0, a0, t0) xs A) * T_t (Train_end_state (v0, s0, a0, t0) xs V) (Train_end_state (v0, s0, a0, t0) xs A) / 2) @\<^sub>t
   In\<^sub>t (State (Train_ode_state(Train_end_state (v0, s0, a0, t0) xs))) ''Control2Train'' a 
   "
proof (induct xs arbitrary: v0 s0 a0 t0)
  case Nil
  have "((\<lambda>_. 0)(V := v0 + a0 * T_t v0 a0, S := s0 + v0 * T_t v0 a0 + a0 * T_t v0 a0 * T_t v0 a0 / 2, A := a0, T := T_t v0 a0)) =
        (\<lambda>a. if a = T then T_t v0 a0
             else ((\<lambda>_. 0)
                   (V := v0 + a0 * T_t v0 a0, S := s0 + v0 * T_t v0 a0 + a0 * T_t v0 a0 * T_t v0 a0 / 2, A := a0))
                   a)"
    apply (rule ext) by auto
  then show ?case 
    unfolding Train_ode_state_def
    by auto
next
  case (Cons a xs)
  show ?case
    by (auto simp add: Cons join_assoc)
qed

lemma trainode:
  "\<Turnstile>
    {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0, S := s0, A := a, T := 0) \<and> P tr}
      Cont (ODE ((\<lambda>_ _. 0)(S := (\<lambda>s. s V), V := (\<lambda>s. s A), T := (\<lambda>_. 1))))
                (\<lambda>s. s T < Period \<and> s V > 0);
      Wait (\<lambda>s. Period - s T)
    {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0 + a * (T_t v0 a),
                        S := s0 + v0 * (T_t v0 a) + 1/2 * a * (T_t v0 a) * (T_t v0 a),
                        A := a, T := (T_t v0 a)) \<and>
            (P @\<^sub>t (T_tassn v0 s0 a)) tr}"
  proof (cases "v0 \<le> 0")
  case True
  then show ?thesis unfolding T_tassn_def T_t_def apply auto
    apply (rule Valid_seq)
    apply (rule Valid_ode_exit_st)
     apply auto
    apply(rule Valid_strengthen_post)
     prefer 2
     apply(rule Valid_wait_sp)
    apply(auto simp add:entails_def pure_assn_def conj_assn_def)
    done
next
case False
  then show ?thesis unfolding T_tassn_def apply auto
    apply(rule Valid_seq[where Q = "\<lambda> s tr .  s = (\<lambda>_. 0)
           (V := v0 + a * T_t v0 a, S := s0 + v0 * T_t v0 a + a * T_t v0 a * T_t v0 a / 2, A := a, T := T_t v0 a) \<and> (P @\<^sub>t
            Wait\<^sub>t (T_t v0 a) (\<lambda>t. State ((\<lambda>_. 0)(V := v0 + a * t, S := s0 + v0 * t + a * t * t / 2, A := a, T := t))) ({}, {})) tr"])
    subgoal
apply (rule Valid_ode_unique_solution_st)
    subgoal using T_t_prop1 by auto
    subgoal
      unfolding ODEsol_def has_vderiv_on_def
      apply auto 
    subgoal
      using T_t_prop1 
      by (meson not_le_imp_less order.asym)
    apply (rule exI[where x=1]) apply auto
    subgoal for x
    apply (rule has_vector_derivative_projI)
     apply (auto simp add: state2vec_def)
     unfolding power2_eq_square
     subgoal
       apply (rule has_vector_derivative_eq_rhs)
        apply (fast intro!: derivative_intros) by simp
     subgoal
      apply (rule has_vector_derivative_eq_rhs)
        apply (fast intro!: derivative_intros) by simp
     subgoal premises pre for i 
   proof-
     have eq: "i \<noteq> S \<Longrightarrow>
           i \<noteq> V \<Longrightarrow>
           i \<noteq> T \<Longrightarrow>
           (\<lambda>t. if i = A then a
                 else ((\<lambda>_. 0)(V := v0 + a * t, S := s0 + v0 * t + a * (t * t) / 2))
                       i) = (\<lambda>t. if i = A then a else 0)"
       by auto
     have 1: ?thesis if "i = A"
       using eq that by auto
     have 2: ?thesis if "i \<noteq> A"
       using eq that pre by auto 
     show ?thesis using 1 2 by linarith
       qed
       done
     done
   subgoal unfolding T_t_def apply auto
     subgoal for t
       using linear_g Period 
       by (smt mult_nonneg_nonneg mult_strict_left_mono_neg)
     subgoal for t 
       by (smt T_t_def T_t_prop2 minus_divide_right)
     subgoal for t
       by (metis add_strict_increasing mult.commute neg_less_minus_divide_eq not_less real_0_less_add_iff split_mult_pos_le)
     done
  subgoal unfolding T_t_def by auto
  subgoal by simp
  subgoal
   proof-
    have bl:"bounded_linear (\<lambda>(v::vec) . \<chi> x. if x = T then 0 else if x = V then (v$A) else if x = S then (v$V) else 0)"
      apply (rule bounded_linearI')
      using vec_lambda_unique by fastforce+
    show ?thesis
      unfolding state2vec_def vec2state_def fun_upd_def
      apply (rule c1_implies_local_lipschitz[where f'="(\<lambda>(t,v). Blinfun(\<lambda>(v::vec) . \<chi> x. if x = T then 0 else if x = V then (v$A) else if x = S then (v$V) else 0))"])
         apply (auto simp add: bounded_linear_Blinfun_apply[OF bl])
      subgoal premises pre for t x
        unfolding has_derivative_def apply (auto simp add: bl)
        apply (rule vec_tendstoI)
        by (auto simp add: state2vec_def)
        done
    qed
    done
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule Valid_wait_sp)
  by (auto simp add:entails_def pure_assn_def conj_assn_def join_assoc)
qed

lemma Valid_seq':
  "\<Turnstile> {P} c1;c2 {Q} \<Longrightarrow> \<Turnstile> {Q} c3 {R} \<Longrightarrow> \<Turnstile> {P} c1; c2; c3 {R}"
 unfolding Valid_def
  apply (auto elim!: seqE) 
  using seqB by fastforce

lemma Train_prop:
  "\<Turnstile>
    {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0, S := s0, A := a0, T := t0) \<and> emp\<^sub>t tr}
      Train
    {\<lambda>s tr. \<exists>xs. s = Train_end_state (v0, s0, a0, t0) xs \<and>
                 Train_inv (v0, s0, a0, t0) xs tr}"
  unfolding Train_def
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for xs
    apply (rule Valid_seq)
    apply (rule Valid_assign_sp_st)
    apply (rule Valid_seq')
     apply (subst Train_end_state_rw)
     apply (rule trainode)
    apply (rule Valid_seq)
apply (rule Valid_send_sp_st)
    apply (rule Valid_seq)
    apply (rule Valid_send_sp_st)
    apply (rule Valid_strengthen_post)
    prefer 2
    apply (rule Valid_receive_sp_st)
    apply (auto simp add :entails_def)
    subgoal for tr a
      apply (rule exI[where x="xs@[a]"])
      apply (auto simp add: Train_end_state_snoc Train_inv_snoc join_assoc Train_ode_state_def)
      done
    done
  apply(auto simp add:entails_def)
  subgoal for tr
    apply (rule exI[where x="[]"])
    apply auto
    done
  done
    


text \<open>Limit on velocity as a function of position and
  maximum velocity in the next segment.

\<close>
definition fs_gen :: "real \<Rightarrow> real \<Rightarrow> real" where
   "fs_gen s next_v =
      (let D = Stop_point - s in
        if D \<ge> Pull_curve_max_d then
          V_limit
        else if D \<ge> 0 then
          sqrt (next_v * next_v + 2 * A_minus * D)
        else 0)"

definition com_a_gen :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "com_a_gen s v next_v =
      (let s1' = s + v * Period + A_plus * Period\<^sup>2 / 2 in
       let target_v1 = fs_gen s1' next_v in
         if v + A_plus * Period \<le> target_v1 then
           A_plus
         else let s2' = s + v * Period in
              let target_v2 = fs_gen s2' next_v in
                if v \<le> target_v2 then 0
                else -A_minus)"

lemma control_vars_distinct [simp]: "Command_a \<noteq> V" "Command_a \<noteq> S" "Command_a \<noteq> Level" "Command_a \<noteq> Next_seg_v"
                                  "V \<noteq> Command_a" "V \<noteq> S" "V \<noteq> Level" "V \<noteq> Next_seg_v"
                                  "S \<noteq> Command_a" "S \<noteq> V" "S \<noteq> Level" "S \<noteq> Next_seg_v"
                                  "Level \<noteq> Command_a" "Level \<noteq> V" "Level \<noteq> S" "Level \<noteq> Next_seg_v"
                                  "Next_seg_v \<noteq> Command_a" "Next_seg_v \<noteq> V" "Next_seg_v \<noteq> S" "Next_seg_v \<noteq> Level"


  unfolding Command_a_def V_def S_def Level_def Next_seg_v_def by auto

definition Control :: proc where
  "Control =
    Level ::= (\<lambda>_. 2.5);Next_seg_v ::= (\<lambda>_. 0);
    Rep(
      Cm (''Train2Control''[?]V);
      Cm (''Train2Control''[?]S);
      (IF (\<lambda>s. s Level = 2.5 \<and> s S > Stop_point) THEN
          Level ::= (\<lambda>_. 3)
       ELSE Level ::= (\<lambda> s. s Level) FI);
      (IF (\<lambda>s. s Level = 3 \<and> s S < Stop_point / 2) THEN
          Next_seg_v ::= (\<lambda>_. Next_V_limit)
       ELSE Next_seg_v ::= (\<lambda> s. s Next_seg_v) FI);
      Command_a ::= (\<lambda>s. com_a_gen (s S) (s V) (s Next_seg_v));
      Cm (''Control2Train''[!](\<lambda>s. s Command_a)))"

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

lemma fs_gen_zero:
  "fs_gen s 0 = fs s"
  unfolding fs_gen_def fs_def Let_def Pull_curve_coeff_def
  by (auto simp add: real_sqrt_mult)

lemma com_a_zero:
  "com_a_gen s v 0 = com_a s v"
  unfolding com_a_gen_def com_a_def
  using fs_gen_zero by auto


fun Control_blocks :: "real \<times> real \<times> real \<times> real \<times> real \<Rightarrow> (real \<times> real) list \<Rightarrow> tassn" where
  "Control_blocks (v0, s0, a0, l0, n0) [] = emp\<^sub>t"
| "Control_blocks (v0, s0, a0, l0, n0) ((v, s) # rest) =
    In\<^sub>t (State ((\<lambda>_. 0)(V := v0, S := s0, Command_a := a0, Level := l0, Next_seg_v := n0))) ''Train2Control'' v @\<^sub>t
    In\<^sub>t (State ((\<lambda>_. 0)(V := v, S := s0, Command_a := a0, Level := l0, Next_seg_v := n0))) ''Train2Control'' s @\<^sub>t
    Out\<^sub>t (State ((\<lambda>_. 0)(V := v, S := s, Command_a := (com_a_gen s v (if l0 = 3 \<and> s < Stop_point/2  then Next_V_limit else n0)), Level := if l0 = 2.5 \<and> s > Stop_point then 3 else l0, Next_seg_v := if l0 = 3 \<and> s < Stop_point/2  then Next_V_limit else n0))) ''Control2Train'' (com_a_gen s v (if l0 = 3 \<and> s < Stop_point/2  then Next_V_limit else n0)) @\<^sub>t
    Control_blocks (v, s, (com_a_gen s v (if l0 = 3 \<and> s < Stop_point/2  then Next_V_limit else n0)), if l0 = 2.5 \<and> s > Stop_point then 3 else l0, if l0 = 3 \<and> s < Stop_point/2  then Next_V_limit else n0) rest"


fun Control_end_state :: "real \<times> real \<times> real \<times> real \<times> real  \<Rightarrow> (real \<times> real) list \<Rightarrow> state" where
  "Control_end_state (v0, s0, a0, l0, n0) [] = ((\<lambda>_. 0)(V := v0, S := s0, Command_a := a0, Level := l0, Next_seg_v := n0))"
| "Control_end_state (v0, s0, a0, l0, n0) ((v, s) # rest) = Control_end_state (v, s, (com_a_gen s v (if l0 = 3 \<and> s < Stop_point/2  then Next_V_limit else n0)), if l0 = 2.5 \<and> s > Stop_point then 3 else l0, if l0 = 3 \<and> s < Stop_point/2  then Next_V_limit else n0) rest"

definition control_state :: "state \<Rightarrow> real \<Rightarrow> real \<Rightarrow> state" where
  "control_state state v s = state(V := v, S := s, Command_a := (com_a_gen s v (if (state Level) = 3 \<and> s < Stop_point/2 then Next_V_limit else (state Next_seg_v))), Level := if (state Level) = 2.5 \<and> s > Stop_point then 3 else (state Level), Next_seg_v := if (state Level) = 3 \<and> s < Stop_point/2  then Next_V_limit else (state Next_seg_v))"

lemma Control_end_state_snoc:
  "Control_end_state (v0, s0, a0, l0, n0) (xs @ [(v, s)]) =
   control_state (Control_end_state (v0, s0, a0, l0, n0) xs) v s"
  apply (induct xs arbitrary: v0 s0 a0 l0 n0) 
  unfolding control_state_def by auto

lemma Control_blocks_snoc:
  "Control_blocks (v0, s0, a0, l0, n0) (xs @ [(v, s)]) =
   Control_blocks (v0, s0, a0, l0, n0) xs @\<^sub>t
   In\<^sub>t (State ((Control_end_state (v0, s0, a0, l0, n0) xs))) ''Train2Control'' v @\<^sub>t
   In\<^sub>t (State ((Control_end_state (v0, s0, a0, l0, n0) xs)(V := v))) ''Train2Control'' s @\<^sub>t
   Out\<^sub>t (State (control_state (Control_end_state (v0, s0, a0, l0, n0) xs) v s)) ''Control2Train'' ((control_state (Control_end_state (v0, s0, a0, l0, n0) xs) v s) Command_a)"
  apply (induct xs arbitrary: v0 s0 a0 l0 n0)
   apply (auto simp add: join_assoc Control_end_state_snoc control_state_def fun_upd_twist)[1]
  apply (auto simp add: join_assoc Control_end_state_snoc )
  done
  
    
lemma Control_prop:
  "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(V := v0, S := s0, Command_a := a0, 
                       Level := l0, Next_seg_v := n0 )) \<and> emp\<^sub>t tr}
      Control
    {\<lambda>s tr. \<exists>xs. s = Control_end_state (v0, s0, a0, 2.5, 0) xs 
                         \<and> Control_blocks (v0, s0, a0, 2.5, 0) xs tr}"
  unfolding Control_def
  apply (rule Valid_seq)
   apply (rule Valid_assign_sp_st)
  apply (rule Valid_seq)
  apply (rule Valid_assign_sp_st)
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for xs
    apply (rule Valid_seq)
    apply (rule Valid_receive_sp_st)
    apply (rule Valid_ex_pre)
        subgoal for v
      apply (rule Valid_seq)
      apply (rule Valid_receive_sp_st)
      apply (rule Valid_ex_pre)
       subgoal for s
         apply(rule Valid_seq)
          apply(rule Valid_cond_sp2)
           apply (rule Valid_assign_sp_st)
          apply(rule Valid_assign_sp_st)
         apply(rule Valid_seq)
          apply(rule Valid_if_split)
           apply(rule Valid_cond_sp2)
            apply (rule Valid_assign_sp_st)
           apply(rule Valid_assign_sp_st)
          apply(rule Valid_cond_sp2)
            apply (rule Valid_assign_sp_st)
          apply(rule Valid_assign_sp_st)
         apply(rule Valid_seq)
          apply(rule Valid_if_split)
           apply(rule Valid_if_split)
            apply (rule Valid_assign_sp_st)
           apply (rule Valid_assign_sp_st)
          apply(rule Valid_if_split)
           apply (rule Valid_assign_sp_st)
          apply (rule Valid_assign_sp_st)
         apply(rule Valid_strengthen_post)
          prefer 2
          apply(rule Valid_if_split)
           apply(rule Valid_if_split)
            apply(rule Valid_send_sp)
           apply(rule Valid_send_sp)
          apply(rule Valid_if_split)
            apply(rule Valid_send_sp)
          apply(rule Valid_send_sp)
         apply(auto simp add:entails_def)
         subgoal for sa tr
           apply (rule exI[where x="xs@[(v,s)]"])
           apply(auto simp add: pure_assn_def conj_assn_def join_assoc Control_end_state_snoc Control_blocks_snoc fun_upd_twist control_state_def)
           done
         subgoal 
           using Stop_point by linarith
         subgoal for sa tr
           apply (rule exI[where x="xs@[(v,s)]"])
           apply(auto simp add: pure_assn_def conj_assn_def join_assoc Control_end_state_snoc Control_blocks_snoc fun_upd_twist control_state_def)
           done
         subgoal for sa tr
           apply (rule exI[where x="xs@[(v,s)]"])
           apply(auto simp add: pure_assn_def conj_assn_def join_assoc Control_end_state_snoc Control_blocks_snoc fun_upd_twist control_state_def)
           done
         subgoal for sa tr
           apply (rule exI[where x="xs@[(v,s)]"])
           apply(auto simp add: pure_assn_def conj_assn_def join_assoc Control_end_state_snoc Control_blocks_snoc fun_upd_twist control_state_def)
           done
         subgoal for sa tr
           apply (rule exI[where x="xs@[(v,s)]"])
           apply(auto simp add: pure_assn_def conj_assn_def join_assoc Control_end_state_snoc Control_blocks_snoc fun_upd_twist control_state_def)
           done
         subgoal for sa tr
           apply (rule exI[where x="xs@[(v,s)]"])
           apply(auto simp add: pure_assn_def conj_assn_def join_assoc Control_end_state_snoc Control_blocks_snoc fun_upd_twist control_state_def)
           done
         done
       done
     done
   apply(auto simp add: entails_def)
   apply (rule exI[where x="[]"]) by auto




text \<open>Once through the loop. Input and output are s and v\<close>
fun loop_once :: "real \<times> real \<Rightarrow> real \<times> real" where
  "loop_once (s, v) = (if v \<le> 0 then (s, v) else
    (let a = com_a s v in
     let v' = v + a * Period in
     let s' = s + v * Period + a * Period\<^sup>2 / 2 in
      if v'> 0 then (s', v') else (s - v^2/(2*a), 0)))"
declare loop_once.simps[simp del]

lemma loop_once_prop1:
  assumes "v>0"
  shows " loop_once(s,v) = 
    (s + v * T_t v (com_a s v) + com_a s v * T_t v (com_a s v) * T_t v (com_a s v) / 2,
     v + com_a s v * T_t v (com_a s v))"
  using assms unfolding T_t_def
  apply auto
  unfolding Let_def loop_once.simps apply auto
   apply (simp add: power2_eq_square)
  by (simp add: power2_eq_square)


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

fun loop_invariant :: "real \<times> real \<Rightarrow> bool" where
  "loop_invariant (s, v) \<longleftrightarrow> v \<le> fs s \<and> v \<ge> 0 \<and> s \<le> Stop_point"


lemma loop_once_invariant:
  assumes "v \<le> fs s \<and> v \<ge> 0 \<and> s \<le> Stop_point"
    and "(s', v') = loop_once (s, v)"
  shows "v' \<le> fs s' \<and> v' \<ge> 0 \<and> s' \<le> Stop_point"
proof -
  have case0:"v' \<le> fs s' \<and> v' \<ge> 0 \<and> s' \<le> Stop_point" if cond0:"v \<le> 0" 
    using assms that loop_once.simps by auto
  have case1:"v' \<le> fs s' \<and> v' \<ge> 0 \<and> s' \<le> Stop_point" if cond1:"v + A_plus * Period \<le> fs (s + v * Period + A_plus * Period\<^sup>2 / 2)" "v>0"
  proof-
    have 1:"com_a s v = A_plus" 
      using that unfolding com_a_def by auto
    have 2:"v + A_plus * Period > 0" using assms A_plus Period 
      by (simp add: add_strict_increasing2)
    have 3:"(s', v') = (s + v * Period + A_plus * Period\<^sup>2 / 2,v + A_plus * Period )" 
      using assms 1  2 that loop_once.simps by auto
    have 4:"v' \<le> fs s'" 
      using that 3
      unfolding fs_def Let_def by auto
    have 5:"v' \<ge> 0" 
      using 3 that 2 by auto
    have 6:"s' \<le> Stop_point" 
      using 3 2 that apply(simp add: fs_def Let_def) apply auto 
      by (smt Pull_curve_max_d_ge_zero)
    show ?thesis using 4 5 6 by auto
  qed
  have case2:"v' \<le> fs s' \<and> v' \<ge> 0 \<and> s' \<le> Stop_point" if cond2:
    "\<not> v + A_plus * Period \<le> fs (s + v * Period + A_plus * Period\<^sup>2 / 2)" 
    "v \<le> fs (s + v * Period)" "v>0"
  proof-
    have 1: "com_a s v = 0" using that unfolding com_a_def by auto
    have 2: "(s',v') = (s + v * Period, v)" using assms 1 loop_once.simps by auto
    have 3:"v' \<le> fs s'" 
      using 2 that
      unfolding fs_def Let_def apply auto
      subgoal premises pre
      proof-
        have "v\<le>0" using pre 
          using Pull_curve_max_d_ge_zero by auto
        then show ?thesis using pre by auto
      qed
      done
    have 4:"v' \<ge> 0" 
      using 2 assms by auto
    have 5:"s' \<le> Stop_point" 
    proof-
      have "v = 0" if "s' > Stop_point"
        using 2 3 unfolding fs_def Let_def 
        using Pull_curve_max_d_ge_zero assms(1) that by auto
      then have"s=s'" if "s' > Stop_point" using 2 that by auto
      then show ?thesis using assms 
        using leI by blast
    qed
    then show ?thesis using 3 4 5 by auto
  qed
  have case3:"v' \<le> fs s' \<and> v' \<ge> 0 \<and> s' \<le> Stop_point" if cond3:
    "\<not> v + A_plus * Period \<le> fs (s + v * Period + A_plus * Period\<^sup>2 / 2)"
    "\<not> v \<le> fs (s + v * Period)" "v>0"
  proof-
    have 1: "com_a s v = -A_minus" using that unfolding com_a_def by auto
    have case31: "v' \<le> fs s' \<and> v' \<ge> 0 \<and> s' \<le> Stop_point" if cond31:"v -A_minus * Period >0"
    proof-
      have 2:"(s',v') = (s + v * Period - A_minus * Period\<^sup>2 / 2, v - A_minus  * Period)"
        using assms 1 cond31 cond3 loop_once.simps by auto
      have 3:"s' \<le> Stop_point"
        using 2 apply auto
        subgoal premises pre
        proof-
          have "v^2 \<le> 2 * A_minus * (Stop_point - s)"
              using fs_prop1 assms by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le> 
                      2 * A_minus * (Stop_point - s) - 2 * A_minus * v * Period + A_minus^2 * Period^2"
            by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le>
                      2 * A_minus * (Stop_point - s - v * Period + 1/2 * A_minus * Period^2)"
            by (auto simp add: algebra_simps power2_eq_square)
          then have "(v - A_minus * Period)^2 \<le> 2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2))"
            by (auto simp add: algebra_simps power2_eq_square)
          then have " 2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)) > 0"
            by (smt that zero_less_power)
          then show ?thesis using A_minus 
            by (smt mult_cancel_right1 mult_le_0_iff times_divide_eq_left)
        qed
        done
       have 4:"v' \<le> fs s'"
        using 2
        unfolding fs_def Let_def apply auto
        subgoal using assms(1) fs_at_most_limit A_minus Period 
          by (smt mult_diff_mult mult_less_iff1)
        subgoal premises pre
        proof-
          have "v^2 \<le> 2 * A_minus * (Stop_point - s)"
            using fs_prop1 assms by auto
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
          have b:"(v - A_minus * Period) = sqrt((v - A_minus * Period)^2)" 
            using cond31 by auto
          have c:"sqrt(2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2))) = sqrt(2 * A_minus) * sqrt((Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)))"
            by (simp add: real_sqrt_mult)
          show ?thesis using a b c unfolding Pull_curve_coeff_def by auto
        qed
        subgoal using assms fs_at_most_limit A_minus Period 
          using Pull_curve_max_d_ge_zero by linarith
        subgoal using 3 by auto
        done
      have 5:"v'\<ge>0"
        using 2 cond31 by auto
      show ?thesis using 3 4 5 by auto
    qed
    have case32: "v' \<le> fs s' \<and> v' \<ge> 0 \<and> s' \<le> Stop_point" if cond32:"v -A_minus * Period \<le> 0"
    proof-
      have 2:"(s',v') = (s + v^2/(2*A_minus), 0)"
        using 1 assms cond32 loop_once.simps by auto
      have 3:"s' \<le> Stop_point"
      proof-
        have "v\<^sup>2 \<le> 2 * A_minus * (Stop_point - s)"
          using 2 assms fs_prop1 by auto
        then have "v\<^sup>2 /(2* A_minus) \<le> Stop_point - s"
          using A_minus
          by (smt divide_divide_eq_left divide_less_cancel real_divide_square_eq)
        then have "s + v\<^sup>2 /(2* A_minus) \<le> Stop_point"
          by auto
        then show ?thesis
          using 2 by auto
      qed
      have 4: "v'\<le>fs s'"
        using 2 3 fs_at_least_zero by auto
      have 5: "v'\<ge> 0"
        using 2 by auto
      show ?thesis using 3 4 5 by auto
    qed
    show ?thesis
      using case31 case32 by linarith
  qed
  show ?thesis
    using case0 case1 case2 case3
    by linarith
qed

lemma loop_once_invariant':
  assumes "loop_invariant (s,v)"
    and "(s', v') = loop_once (s, v)"
  shows "loop_invariant (s',v')"
  using loop_once_invariant assms
  using loop_invariant.simps by blast



definition system :: pproc where
  "system = Parallel (Single Train)
                     {''Train2Control'', ''Control2Train''}
                     (Single Control)"


definition P_tassn :: "real \<Rightarrow> real \<Rightarrow> tassn " where
  "P_tassn v0 s0 =
   (\<up>(loop_invariant (s0, v0)) \<and>\<^sub>t
    (if v0 \<le> 0 then
       emp\<^sub>t @\<^sub>t Wait\<^sub>t (Period) (\<lambda>t. ParState (State ((\<lambda>_. 0)(V := v0, S := s0, A := com_a s0 v0, T := 0))) (State ((\<lambda>_. 0)(V := v0, S := s0, Command_a := com_a s0 v0, Level := 2.5, Next_seg_v := 0)) )) ({}, {''Train2Control''})
     else
       Wait\<^sub>t (T_t v0 (com_a s0 v0))
    (\<lambda>t. ParState
      (State ((\<lambda>_. 0)(V := v0 + com_a s0 v0 * t,
                      S := s0 + v0 * t + 1/2 * com_a s0 v0 * t * t,
                      A := com_a s0 v0, T := t)))
      (State ((\<lambda>_. 0)(V := v0, S := s0, Command_a := com_a s0 v0, Level := 2.5, Next_seg_v := 0)))) 
                      ({}, {''Train2Control''})
    @\<^sub>t Wait\<^sub>t (Period - T_t v0 (com_a s0 v0)) 
    (\<lambda>t. ParState 
      (State ((\<lambda>_. 0)(V := v0 + com_a s0 v0 * (T_t v0 (com_a s0 v0)),
                      S := s0 + v0 * (T_t v0 (com_a s0 v0)) + 1/2 * com_a s0 v0 * (T_t v0 (com_a s0 v0)) * (T_t v0 (com_a s0 v0)),
                      A := com_a s0 v0, T := T_t v0 (com_a s0 v0)))) 
      (State ((\<lambda>_. 0)(V := v0, S := s0, Command_a := com_a s0 v0, Level := 2.5, Next_seg_v := 0)) )) ({}, {''Train2Control''})
))"


fun tot_block :: "real \<times> real \<Rightarrow> nat \<Rightarrow> tassn" where
  "tot_block (s0, v0) 0 = emp\<^sub>t"
| "tot_block (s0, v0) (Suc n) =
   P_tassn v0 s0 @\<^sub>t
   IO\<^sub>t ''Train2Control'' (snd (loop_once (s0, v0))) @\<^sub>t
   IO\<^sub>t ''Train2Control'' (fst (loop_once (s0, v0))) @\<^sub>t
   IO\<^sub>t ''Control2Train'' (com_a (fst (loop_once (s0, v0))) (snd (loop_once (s0, v0)))) @\<^sub>t
   tot_block (loop_once (s0, v0) ) n"

fun tot_seq :: "real \<times> real \<Rightarrow> nat \<Rightarrow> (real \<times> real) list" where
  "tot_seq (v, s) 0 = []"
| "tot_seq (v, s) (Suc n) = (v, s) # tot_seq (loop_once (v, s)) n"



lemma combine:
  "loop_invariant (s0, v0) \<Longrightarrow> 
   combine_assn {''Train2Control'', ''Control2Train''}
     (Train_inv (v0, s0, com_a s0 v0, t0) as) (Control_blocks (v0, s0, com_a s0 v0, 2.5, 0) vs) 
      \<Longrightarrow>\<^sub>t  tot_block (s0,v0) (length as)"
proof (induct as arbitrary: vs v0 s0 t0)
  case Nil
  then show ?case 
  proof(cases vs)
    case Nil
    then show ?thesis by auto
  next
    case (Cons vsp rest)
    then show ?thesis 
      apply auto
        subgoal
        proof (cases vsp)
          case (Pair v s)
          then show ?thesis
            apply auto
            subgoal
            apply (rule entails_tassn_trans)
             apply (subst combine_assn_emp_in)
               apply auto
              by (rule false_assn_entails)
            apply (rule entails_tassn_trans)
             apply (subst combine_assn_emp_in)
               apply auto
            by (rule false_assn_entails)
        qed
        done
    qed
next
  case (Cons a as)
  note Cons1 = Cons
  then show ?case 
  proof (cases vs)
    case Nil
    then show ?thesis apply auto
      subgoal
        apply (rule entails_tassn_trans)
        unfolding T_tassn_def
        apply auto
         apply (rule combine_assn_wait_emp)
          apply auto
        apply(subst join_assoc)
        apply (rule combine_assn_wait_emp)
        using T_t_prop1 by auto
      done
    next
      case (Cons vsp rest)
    then show ?thesis 
       apply auto
       subgoal premises pre
     proof(cases vsp)
      case (Pair v s)
      then show ?thesis
        apply auto
        unfolding T_tassn_def P_tassn_def
         apply (auto simp add: pre)
        subgoal
           apply (rule entails_tassn_trans)
         apply (rule combine_assn_wait_in)
             apply auto
          apply (rule entails_tassn_conj)
        subgoal
            using Cons1(2) apply (auto simp add: pure_assn_def entails_tassn_def) 
            done
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
         apply (rule combine_assn_out_in)
           apply (auto simp add:T_t_def pre loop_once.simps)
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_out_in)
           apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_in_out)
           apply auto
          apply (subst com_a_zero)
          apply (rule entails_tassn_cancel_left)
          using Cons1(2) by auto
        subgoal
          apply (rule entails_tassn_trans)
          apply(subst join_assoc)
         apply (rule combine_assn_wait_in)
             apply auto
          apply (rule entails_tassn_conj)
          subgoal
            using Cons1(2) apply (auto simp add: pure_assn_def entails_tassn_def) 
            done
          apply(subst join_assoc)
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
         apply (rule combine_assn_wait_in)
            apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_out_in)
           apply auto
          apply (subst loop_once_prop1)
           apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_out_in)
           apply auto
          apply (subst loop_once_prop1)
           apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_in_out)
           apply auto
          apply (subst loop_once_prop1)
           apply auto
          apply (subst loop_once_prop1)
           apply auto
          apply (subst com_a_zero)
          apply (rule entails_tassn_cancel_left)
          apply (subst loop_once_prop1)
           apply auto
          subgoal premises pref 
          proof-
            have 1:"(s0 + v0 * T_t v0 (com_a s0 v0) + com_a s0 v0 * T_t v0 (com_a s0 v0) * T_t v0 (com_a s0 v0) / 2,v0 + com_a s0 v0 * T_t v0 (com_a s0 v0)) = loop_once(s0,v0)"
              using loop_once_prop1[of v0 s0] pref by auto
            have 2:"loop_invariant(s0,v0)"
              using Cons1 by auto
            have 3:"loop_invariant(s0 + v0 * T_t v0 (com_a s0 v0) + com_a s0 v0 * T_t v0 (com_a s0 v0) * T_t v0 (com_a s0 v0) / 2,v0 + com_a s0 v0 * T_t v0 (com_a s0 v0))"
              using loop_once_invariant'[OF 2 1] by auto
            then show ?thesis using pref unfolding loop_invariant.simps by auto
          qed
          done
        subgoal
          apply (rule entails_tassn_trans)
         apply (rule combine_assn_wait_in)
             apply auto
          apply (rule entails_tassn_conj)
          subgoal
            using Cons1(2) apply (auto simp add: pure_assn_def entails_tassn_def) 
            done
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_out_in)
           apply (auto simp add:T_t_def loop_once.simps)
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_out_in)
           apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_in_out)
           apply auto
          apply (subst com_a_zero)+
          apply (rule entails_tassn_cancel_left)
          using Cons1 by auto
        subgoal
          apply (rule entails_tassn_trans)
          apply(subst join_assoc)
         apply (rule combine_assn_wait_in)
             apply auto
          apply (rule entails_tassn_conj)
          subgoal
            using Cons1(2) apply (auto simp add: pure_assn_def entails_tassn_def) 
            done
          apply(subst join_assoc)
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
         apply (rule combine_assn_wait_in)
            apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_out_in)
           apply auto
          apply (subst loop_once_prop1)
           apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_out_in)
           apply auto
          apply (subst loop_once_prop1)
           apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply (rule combine_assn_in_out)
           apply auto
          apply (subst loop_once_prop1)
           apply auto
          apply (subst loop_once_prop1)
           apply auto
          apply (subst com_a_zero)+
          apply (rule entails_tassn_cancel_left)
          apply (subst loop_once_prop1)
           apply auto
subgoal premises pref 
          proof-
            have 1:"(s0 + v0 * T_t v0 (com_a s0 v0) + com_a s0 v0 * T_t v0 (com_a s0 v0) * T_t v0 (com_a s0 v0) / 2,v0 + com_a s0 v0 * T_t v0 (com_a s0 v0)) = loop_once(s0,v0)"
              using loop_once_prop1[of v0 s0] pref by auto
            have 2:"loop_invariant(s0,v0)"
              using Cons1 by auto
            have 3:"loop_invariant(s0 + v0 * T_t v0 (com_a s0 v0) + com_a s0 v0 * T_t v0 (com_a s0 v0) * T_t v0 (com_a s0 v0) / 2,v0 + com_a s0 v0 * T_t v0 (com_a s0 v0))"
              using loop_once_invariant'[OF 2 1] by auto
            then show ?thesis using Cons1 by auto
          qed
          done
        done
    qed
    done
qed
qed
          
lemma system_Prop:
  assumes "loop_invariant (s0, v0)"
  shows "\<Turnstile>\<^sub>p
    {pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(V := v0, S := s0, A := com_a s0 v0, T := t0)))
               (\<lambda>s. s = ((\<lambda>_. 0)(V := v0, S := s0, Command_a := com_a s0 v0, 
                                                   Level := 2.5, Next_seg_v := 0)))}
      system
    {\<exists>\<^sub>g n. trace_gassn (tot_block (s0,v0) n)}"
  unfolding system_def
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
  apply (rule Train_prop)
  apply (rule Control_prop)
  apply (auto simp add: sing_gassn_split sing_gassn_ex)
  apply (rule sync_gassn_ex_pre_left)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for xs as
    unfolding sync_gassn_state_left sync_gassn_state_right
    apply (rule entails_ex_gassn)
    apply (rule exI[where x="length xs"])
    apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
     apply (rule entails_tassn_trans)
      prefer 2 apply(rule combine[OF assms])
     apply (rule combine_assn_mono)
    by (auto simp add: entails_tassn_def entails_gassn_def and_gassn_def)
  done


          

         
          


          
          
          
end
end
