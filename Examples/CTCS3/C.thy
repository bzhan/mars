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

fun loop_once :: "real \<times> real \<Rightarrow> real \<times> real" where
  "loop_once (s, v) = 
    (let a = com_a s v in
     let v' = v + a * Period in
     let s' = s + v * Period + a * Period\<^sup>2 / 2 in
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
      using assms 1   that loop_once.simps by auto
    have 21:"s' = s + v * Period + A_plus * Period\<^sup>2 / 2"
      using 2 by auto
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
        then show ?thesis using 
            assms 21 by auto 
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
    have 5:"s' \<le> Stop_point" 
    proof-
      have "v \<le> 0" if "s' > Stop_point"
        using 2 3 unfolding fs_def Let_def 
        using Pull_curve_max_d_ge_zero assms(1) that by auto
      then have"s\<ge>s'" if "s' > Stop_point" using 2 that
        by (smt Period old.prod.inject zero_less_mult_pos2)
      then show ?thesis using assms 
        using leI 
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
          by (smt mult_diff_mult real_mult_less_iff1)
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
end
end