theory basic
  imports HOL.NthRoot HHL_SL invGen
begin


definition x :: exp where
  "x == RVar ''parx''"

definition y :: exp where
  "y == RVar ''pary''"

definition z :: exp where
  "z == RVar ''parz''"

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

consts Inv :: fform

definition cons11:: fform where "cons11 \<equiv>  (x [\<ge>] Con Real 1) [\<longrightarrow>] Inv "
definition cons12:: fform where "cons12 \<equiv>  Inv [\<longrightarrow>] (x [\<ge>] Con Real 1) "
definition cons13:: fform where "cons13 \<equiv>  exeFlow(<[(''x'', R)]: [(Con Real 2)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"
lemma allcons1:"\<forall> s. ( cons11 [&] cons12 [&] cons13 ) s"
apply (simp add:cons11_def cons12_def cons13_def)
  sorry
lemma ODE1:"{x[\<ge>](Con Real 0)}
    (x :=((Con Real 1) [+] x )); <[(''x'', R)]: [(Con Real 2)] && Inv & fTrue>
           {x[\<ge>](Con Real 1); (elE 0 [[|]] (almost (x[\<ge>](Con Real 1))))}"
apply (cut_tac p="x[\<ge>](Con Real 0)"
           and P="(x :=((Con Real 1) [+] x ))" 
           and m="x[\<ge>](Con Real 1)"
           and Q="<[(''x'', R)]: [(Con Real 2)] && Inv & fTrue>" 
           and q="x[\<ge>](Con Real 1)"
           and H="elE 0"
           and G="(elE 0 [[|]] (almost (x[\<ge>](Con Real 1))))"
            in  SequentialRule_aux,auto)
    apply (cut_tac B01,auto)
   defer 
   apply (simp add:chop_def dOr_def Valid_def)
  apply (cut_tac allcons1)
apply (simp add:cons11_def cons12_def cons13_def)
  apply (cut_tac p="x[\<ge>](Con Real 1)"
             and q="x[\<ge>](Con Real 1)"
             and b="fTrue"
             and Inv="Inv"
             and H="(elE 0 [[|]] (almost (x[\<ge>](Con Real 1))))"
             in ContinuousRuleGT,auto)
  apply (simp add: fAnd_def fImp_def)
     apply (simp add: fAnd_def fImp_def)
    apply (simp add: fAnd_def fImp_def)
   apply (simp add:dOr_def)
  apply (simp add:dOr_def fAnd_def fImp_def)
  by (metis (no_types, lifting) almostmono)

ML{*
val t =@{term "((x [\<ge>] Con Real 1 [\<longrightarrow>] Inv) 
            [&] (Inv [\<longrightarrow>] x [\<ge>] Con Real 1) 
            [&] (exeFlow (<[(''x'', R)]:[Con Real 2]&&Inv&\<lambda>s. True>) Inv [\<longrightarrow>] Inv)) 
       "}

val res = trans_goal t
*}
definition cons21:: fform where "cons21 \<equiv>  ((x [\<ge>] Con Real 0)[&](y [\<ge>] Con Real 0)[&](z [\<ge>] Con Real 0)) [\<longrightarrow>] Inv "
definition cons22:: fform where "cons22 \<equiv>  Inv [\<longrightarrow>] (x [\<ge>] Con Real 0) "
definition cons23:: fform where "cons23 \<equiv>  exeFlow(<[(''x'', R),(''y'', R)]: [y,z] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"
lemma allcons2:"\<forall> s. ( cons21 [&] cons22 [&] cons23 ) s"
apply (simp add:cons21_def cons22_def cons23_def)
  sorry
lemma ODE2:"{x [\<ge>] Con Real 0 [&] y [\<ge>] Con Real 0 [&] z [\<ge>] Con Real 0}
           <[(''x'', R), (''y'', R)]:[y, z]&&Inv&\<lambda>s. True>
            {x [\<ge>] Con Real 0; (elE 0 [[|]] (almost (x[\<ge>](Con Real 0))))}"
  sorry

ML{*
val t =@{term "((x [\<ge>] Con Real 0 [&] y [\<ge>] Con Real 0 [&] z [\<ge>] Con Real 0 [\<longrightarrow>] Inv) 
            [&](Inv [\<longrightarrow>] x [\<ge>] Con Real 0) 
            [&](exeFlow (<[(''x'', R), (''y'', R)]:[y, z]&&Inv&\<lambda>s. True>) Inv [\<longrightarrow>] Inv)) 
       "}

val res = trans_goal t
*}
definition cons31:: fform where "cons31 \<equiv>  (x [\<ge>] Con Real 0) [\<longrightarrow>] Inv "
definition cons32:: fform where "cons32 \<equiv>  Inv [\<longrightarrow>] (x [\<ge>] Con Real 0) "
definition cons33:: fform where "cons33 \<equiv>  exeFlow(<[(''x'', R)]: [(Con Real 5)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"
definition cons34:: fform where "cons34 \<equiv>  exeFlow(<[(''x'', R)]: [(Con Real 2)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"
definition cons35:: fform where "cons35 \<equiv>  exeFlow(<[(''x'', R)]: [x] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"
lemma allcons3:"\<forall> s. ( cons31 [&] cons32 [&] cons33 [&] cons34 [&] cons35) s"
apply (simp add:cons31_def cons32_def cons33_def cons34_def cons35_def)
  sorry
lemma ODE3:"{x [\<ge>] Con Real 0 }
           <[(''x'', R)]: [(Con Real 5)] && Inv & fTrue>;
           <[(''x'', R)]: [(Con Real 2)] && Inv & fTrue>;
           <[(''x'', R)]: [x] && Inv & fTrue>
            {x [\<ge>] Con Real 0; (elE 0 [[|]] (almost (x[\<ge>](Con Real 0))))}"
  sorry
ML{*
val t =@{term "((x [\<ge>] Con Real 0  [\<longrightarrow>] Inv) 
            [&](Inv [\<longrightarrow>] x [\<ge>] Con Real 0) 
            [&](exeFlow (<[(''x'', R)]:[Con Real 5]&&Inv&\<lambda>s. True>) Inv [\<longrightarrow>] Inv) 
            [&](exeFlow (<[(''x'', R)]:[Con Real 2]&&Inv&\<lambda>s. True>) Inv [\<longrightarrow>] Inv) 
            [&](exeFlow (<[(''x'', R)]:[x]&&Inv&\<lambda>s. True>) Inv [\<longrightarrow>] Inv)) 
       "}
*}
end
