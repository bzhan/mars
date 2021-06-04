theory CTCS3
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
  assumes Period: "Period > 0"
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

definition Train :: proc where
  "Train =
    Rep (
      T ::= (\<lambda>_. 0);
      Cont (ODE ((\<lambda>_ _. 0)(S := (\<lambda>s. s V),
                           V := (\<lambda>s. s A), T := (\<lambda>_. 1))))
                ((\<lambda>s. s T < Period \<and> s V > 0));
      Wait (\<lambda>s. Period - s T);
      Cm (''Train2MCU''[!](\<lambda>s. s V));
      Cm (''Train2MCU''[!](\<lambda>s. s S));
      Cm (''MCU2Train''[?]A)
    )"

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
    
definition Control :: proc where
  "Control =
    Level ::= (\<lambda>_. 2.5);
    Next_seg_v ::= (\<lambda>_. 0);
    Rep (
      Cm (''Train2MCU''[?]V);
      Cm (''Train2MCU''[?]S);
      Command_a ::= (\<lambda>s. com_a_gen (s S) (s V) (s Next_seg_v));
      (IF (\<lambda>s. s Level = 2.5 \<and> s S > Stop_point) THEN
         Level ::= (\<lambda>_. 3)
       ELSE Skip FI);
      (IF (\<lambda>s. s Level = 3 \<and> s S < Stop_point / 2) THEN
         Next_seg_v ::= (\<lambda>_. Next_V_limit)
       ELSE Skip FI);
      Cm (''MCU2Train''[!](\<lambda>s. s Command_a))
    )"

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


end
