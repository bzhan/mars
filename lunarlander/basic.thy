theory basic
  imports HOL.NthRoot HHL_SL invGen
begin


definition x :: exp where
  "x == RVar ''parx''"


definition y :: exp where
  "y == RVar ''pary''"

definition Assignment :: proc where 
  "Assignment == x := ((Con Real 1) [+] x)"

lemma B01:
  "{x[\<ge>](Con Real 0)} x := ((Con Real 1) [+] x) {x[\<ge>](Con Real 1); elE 0}"
  unfolding x_def
  apply (rule AssignRRule, auto, fold x_def)
proof -
  fix s
  assume a: "(x[\<ge>]Con Real 0) s"
  obtain c where evalx: "evalE x s = Real c"
    using a[unfolded fGreaterEqual_def]
    apply (cases "evalE x s") by auto
  show "(x[\<ge>]Con Real 1) (\<lambda>(y, i). if y = ''parx'' \<and> i = R then evalE (Con Real 1 [+] x) s else s (y, i))" 
  proof -
    have eval0: "evalE (Con Real 0) s = Real 0"
      by auto
    from a[unfolded fGreaterEqual_def] evalx eval0
    have nonneg_c: "0 \<le> c" by auto
    have evalx': "s (''parx'', R) = Real c"
      using evalx unfolding x_def evalE.simps(2) by auto
    show ?thesis
      unfolding fGreaterEqual_def x_def evalE.simps(2) evalE.simps(1)
      by (simp add: evalx' nonneg_c)
  qed
qed

lemma B02:
  "{x[\<ge>](Con Real 0)}
    (x :=((Con Real 1) [+] x ));
    (x :=((Con Real 1) [+] x ))*&& x[\<ge>](Con Real 1)
   {x[\<ge>](Con Real 1);elE 0}"

apply (cut_tac p="x[\<ge>](Con Real 0)"
           and P="(x :=((Con Real 1) [+] x ))" 
           and m="x[\<ge>](Con Real 1)"
           and Q="(x :=((Con Real 1) [+] x ))*&& x[\<ge>](Con Real 1)" 
           and q="x[\<ge>](Con Real 1)"
           and H="elE 0"
           and G="elE 0"
            in  SequentialRule_aux,auto)
    apply (cut_tac B01,auto)
   defer
   apply (simp add:chop_def)
  apply (simp add: Valid_def)
apply (cut_tac I="x[\<ge>](Con Real 1)"
           and P="x :=((Con Real 1) [+] x )" 
           and H="elE 0" 
            in  RepetitionRule,auto)
apply (simp add:chop_def) 
defer
apply (simp add:dOr_def )
apply (cut_tac p="x[\<ge>](Con Real 1)" 
           and q="x[\<ge>](Con Real 1)" 
           and H="elE 0" 
           and x="''parx''" 
           and f="((Con Real 1) [+] x )" in  AssignRRule,auto)
defer apply (simp add:x_def)

proof-
  fix s
  assume a:"(x[\<ge>]Con Real 1) s"
  obtain c where evalx: "evalE x s = Real c"
     using a[unfolded fGreaterEqual_def]
     apply (cases "evalE x s") by auto
   show "(x[\<ge>]Con Real 1)
          (\<lambda>(y, i). if y = ''parx'' \<and> i = R then evalE (Con Real 1 [+] x) s else s (y, i))"
proof -
    have eval1: "evalE (Con Real 1) s = Real 1"
      by auto
    from a[unfolded fGreaterEqual_def] evalx eval1
    have nonneg_c1: "1 \<le> c" by auto
    have nonneg_c0: "0 \<le> c" using nonneg_c1 by linarith
    have evalx': "s (''parx'', R) = Real c"
      using evalx unfolding x_def evalE.simps(2) by auto
    show ?thesis
      unfolding fGreaterEqual_def x_def evalE.simps(2) evalE.simps(1)
      by (simp add: evalx' nonneg_c0)
  qed
qed


lemma B03:
  "{x[\<ge>](Con Real 0)}
    (x :=((Con Real 1) [+] x ));
    (x :=((Con Real 1) [+] x )) [[ (y :=((Con Real 1) [+] y ))
   {x[\<ge>](Con Real 1);elE 0}"
apply (cut_tac p="x[\<ge>](Con Real 0)"
           and P="(x :=((Con Real 1) [+] x ))" 
           and m="x[\<ge>](Con Real 1)"
           and Q="(x :=((Con Real 1) [+] x )) [[ (y :=((Con Real 1) [+] y ))" 
           and q="x[\<ge>](Con Real 1)"
           and H="elE 0"
           and G="elE 0"
            in  SequentialRule_aux,auto)
    apply (cut_tac B01,auto)
   defer
   apply (simp add:chop_def)
  apply (simp add: Valid_def)
  apply (cut_tac P="(x :=((Con Real 1) [+] x )) "
           and Q="(y :=((Con Real 1) [+] y ))" 
           and p="x[\<ge>](Con Real 1)" 
           and m="x[\<ge>](Con Real 1)" 
           and q="x[\<ge>](Con Real 1)" 
           and H="elE 0" 
           and G="elE 0"  in JoinRule,auto)
defer
defer
apply (simp add:fOr_def )
apply (simp add:dOr_def )
apply (cut_tac p="x[\<ge>](Con Real 1)" 
           and q="x[\<ge>](Con Real 1)" 
           and H="elE 0" 
           and x="''parx''" 
           and f="((Con Real 1) [+] x )" in  AssignRRule,auto)
    defer 
    apply (simp add:x_def)
apply (cut_tac p="x[\<ge>](Con Real 1)" 
           and q="x[\<ge>](Con Real 1)" 
           and H="elE 0" 
           and x="''pary''" 
           and f="((Con Real 1) [+] y )" in  AssignRRule,auto)
    defer
    apply (simp add:y_def)
  
proof-
  fix s
  assume a:"(x[\<ge>]Con Real 1) s"
  obtain c where evalx: "evalE x s = Real c"
     using a[unfolded fGreaterEqual_def]
     apply (cases "evalE x s") by auto
   show "(x[\<ge>]Con Real 1)
          (\<lambda>(y, i). if y = ''parx'' \<and> i = R then evalE (Con Real 1 [+] x) s else s (y, i))"
proof -
    have eval1: "evalE (Con Real 1) s = Real 1"
      by auto
    from a[unfolded fGreaterEqual_def] evalx eval1
    have nonneg_c1: "1 \<le> c" by auto
    have nonneg_c0: "0 \<le> c" using nonneg_c1 by linarith
    have evalx': "s (''parx'', R) = Real c"
      using evalx unfolding x_def evalE.simps(2) by auto
    show ?thesis
      unfolding fGreaterEqual_def x_def evalE.simps(2) evalE.simps(1)
      by (simp add: evalx' nonneg_c0)
  qed
  assume a:"(x[\<ge>]Con Real 1) s"
  obtain c where evalx: "evalE x s = Real c"
     using a[unfolded fGreaterEqual_def]
     apply (cases "evalE x s") by auto
   show "(x[\<ge>]Con Real 1)
          (\<lambda>(ya, i). if ya = ''pary'' \<and> i = R then evalE (Con Real 1 [+] y) s else s (ya, i)) "
proof -
    have eval1: "evalE (Con Real 1) s = Real 1"
      by auto
    from a[unfolded fGreaterEqual_def] evalx eval1
    have nonneg_c1: "1 \<le> c" by auto
    have evalx': "s (''parx'', R) = Real c"
      using evalx unfolding x_def evalE.simps(2) by auto
    show ?thesis
      unfolding fGreaterEqual_def x_def y_def evalE.simps(2) evalE.simps(1)
      by (simp add: evalx' nonneg_c1)
qed
qed





end
