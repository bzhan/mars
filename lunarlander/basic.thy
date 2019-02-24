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

definition cons11 :: fform where "cons11 \<equiv> (x [\<ge>] Con Real 1) [\<longrightarrow>] Inv"
definition cons12 :: fform where "cons12 \<equiv> Inv [\<longrightarrow>] (x [\<ge>] Con Real 1)"
definition cons13 :: fform where "cons13 \<equiv> exeFlow(<[(''parx'', R)]: [(Con Real 2)] && Inv & fTrue>) Inv [\<longrightarrow>] Inv"

lemma allcons1: "\<forall>s. (cons11 [&] cons12 [&] cons13) s"
  apply (simp only: cons11_def cons12_def cons13_def x_def)
  sorry

lemma ODE1:
  "{x [\<ge>] (Con Real 0)}  \<comment> \<open>x >= 0\<close>
    (x := ((Con Real 1) [+] x));  \<comment> \<open>x := 1 + x\<close>
    <[(''parx'', R)]: [(Con Real 2)] && Inv & fTrue>  \<comment> \<open>x' = 2 & True\<close>
   {x[\<ge>](Con Real 1); (elE 0 [[|]] (almost (x[\<ge>](Con Real 1))))}"  \<comment> \<open>x >= 1\<close>
  apply (rule SequentialRule[where m="x[\<ge>](Con Real 1)" and H="elE 0" and G="elE 0 [[|]] (almost (x[\<ge>](Con Real 1)))"])
  apply (rule B01)
  prefer 2 subgoal
    by (simp add:chop_def dOr_def Valid_def)
  apply (rule ContinuousRuleGT)
  using allcons1 apply (auto simp add: cons11_def cons12_def cons13_def fAnd_def fImp_def dOr_def)
  by (metis (no_types, lifting) almostmono)

ML{*
trans_goal @{term "\<forall>s. ((RVar ''parx'' [\<ge>] Con Real 1 [\<longrightarrow>] Inv) [&] (Inv [\<longrightarrow>] RVar ''parx'' [\<ge>] Con Real 1) [&]
         (exeFlow (<[(''parx'', R)]:[Con Real 2]&&Inv&fTrue>) Inv [\<longrightarrow>] Inv))
         s"} |> writeln
*}

definition cons21:: fform where "cons21 \<equiv>  ((x [\<ge>] Con Real 0)[&](y [\<ge>] Con Real 0)[&](z [\<ge>] Con Real 0)) [\<longrightarrow>] Inv "
definition cons22:: fform where "cons22 \<equiv>  Inv [\<longrightarrow>] (x [\<ge>] Con Real 0) "
definition cons23:: fform where "cons23 \<equiv>  exeFlow(<[(''parx'', R),(''pary'', R)]: [y,z] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"

lemma allcons2:"\<forall> s. ( cons21 [&] cons22 [&] cons23 ) s"
  apply (simp only:cons21_def cons22_def cons23_def x_def y_def z_def)
  sorry

lemma ODE2:"{x [\<ge>] Con Real 0 [&] y [\<ge>] Con Real 0 [&] z [\<ge>] Con Real 0}
           <[(''parx'', R), (''pary'', R)]:[y, z]&&Inv&\<lambda>s. True>
            {x [\<ge>] Con Real 0; (elE 0 [[|]] (almost (x[\<ge>](Con Real 0))))}"
  apply (rule ContinuousRuleGT) 
  using allcons2 apply (auto simp add:cons21_def cons22_def cons23_def x_def y_def z_def fAnd_def fImp_def dOr_def)
  by (smt almostmono)


ML {*
trans_goal @{term " \<forall>s. ((RVar ''parx'' [\<ge>] Con Real 0 [&] RVar ''pary'' [\<ge>] Con Real 0 [&] RVar ''parz'' [\<ge>] Con Real 0 [\<longrightarrow>] Inv) [&]
         (Inv [\<longrightarrow>] RVar ''parx'' [\<ge>] Con Real 0) [&]
         (exeFlow (<[(''parx'', R), (''pary'', R)]:[RVar ''pary'', RVar ''parz'']&&Inv&fTrue>) Inv [\<longrightarrow>] Inv))
         s"} |> writeln
*}

definition cons31:: fform where "cons31 \<equiv>  (x [\<ge>] Con Real 0) [\<longrightarrow>] Inv "
definition cons32:: fform where "cons32 \<equiv>  Inv [\<longrightarrow>] (x [\<ge>] Con Real 0) "
definition cons33:: fform where "cons33 \<equiv>  exeFlow(<[(''parx'', R)]: [(Con Real 5)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"
definition cons34:: fform where "cons34 \<equiv>  exeFlow(<[(''parx'', R)]: [(Con Real 2)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"
definition cons35:: fform where "cons35 \<equiv>  exeFlow(<[(''parx'', R)]: [x] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"

lemma allcons3:"\<forall> s. ( cons31 [&] cons32 [&] cons33 [&] cons34 [&] cons35) s"
  apply (simp only:cons31_def cons32_def cons33_def cons34_def cons35_def
          x_def )
  sorry

lemma ODE3:"{x [\<ge>] Con Real 0 }
           <[(''parx'', R)]: [(Con Real 5)] && Inv & fTrue>;
           <[(''parx'', R)]: [(Con Real 2)] && Inv & fTrue>;
           <[(''parx'', R)]: [x] && Inv & fTrue>
            {x [\<ge>] Con Real 0; (elE 0 [[|]] (almost (x[\<ge>](Con Real 0))))}"
  apply (rule SequentialRule[where m="x[\<ge>](Con Real 0)" and H="elE 0 [[|]] (almost (x[\<ge>](Con Real 0)))" and G="elE 0 [[|]] (almost (x[\<ge>](Con Real 0)))"]) 
  apply (rule ContinuousRuleGT) 
  using allcons3 apply (simp add:cons31_def cons32_def cons33_def cons34_def cons35_def
          x_def fAnd_def fImp_def dOr_def )
    apply (smt almostmono)
   apply (rule SequentialRule[where m="x[\<ge>](Con Real 0)" and H="elE 0 [[|]] (almost (x[\<ge>](Con Real 0)))" and G="elE 0 [[|]] (almost (x[\<ge>](Con Real 0)))"]) 
   apply (rule ContinuousRuleGT) 
  using allcons3 apply (simp add:cons31_def cons32_def cons33_def cons34_def cons35_def
          x_def fAnd_def fImp_def dOr_def )
    apply (smt almostmono)
   apply (rule ContinuousRuleGT) 
  using allcons3 apply (simp add:cons31_def cons32_def cons33_def cons34_def cons35_def
          x_def fAnd_def fImp_def dOr_def )
    apply (smt almostmono)
  using chopfor apply blast
  using chopfor apply blast
  done

ML{*
trans_goal @{term "\<forall>s. ((RVar ''parx'' [\<ge>] Con Real 0 [\<longrightarrow>] Inv) [&] (Inv [\<longrightarrow>] RVar ''parx'' [\<ge>] Con Real 0) [&]
         (exeFlow (<[(''x'', R)]:[Con Real 5]&&Inv&fTrue>) Inv [\<longrightarrow>] Inv) [&]
         (exeFlow (<[(''x'', R)]:[Con Real 2]&&Inv&fTrue>) Inv [\<longrightarrow>] Inv) [&]
         (exeFlow (<[(''x'', R)]:[RVar ''parx'']&&Inv&fTrue>) Inv [\<longrightarrow>] Inv))
         s"} |> writeln
*}

definition exp41:: exp where
  "exp41 \<equiv> ((Con Real 0 [-] x [-] ((Con Real 1117 [*] y) [div] Con Real 500)) [+]
   ((Con Real 439 [*] y [**] 3) [div] Con Real 200 ))[-]((Con Real 333 [*] y [**] 5) [div] Con Real 500) "

definition exp42:: exp where
  "exp42 \<equiv> ((x [+]((Con Real 617 [*] y) [div] Con Real 500)) [-]
   ((Con Real 439 [*] y [**] 3) [div] Con Real 200 ))[+]((Con Real 333 [*] y [**] 5) [div] Con Real 500)"

definition cons41:: fform where
  "cons41 \<equiv>  (x[**]2 [\<le>] Con Real (1/2) [&] y[**]2 [\<le>] Con Real (1/3)) [\<longrightarrow>] Inv "

definition cons42:: fform where
  "cons42 \<equiv>  Inv [\<longrightarrow>] (x [-] Con Real 4 [*] y [<] Con Real 8) "

definition cons43:: fform where
  "cons43 \<equiv>  exeFlow(<[(''parx'', R),(''pary'', R)]: [(exp41),(exp42)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"

lemma allcons4:"\<forall> s. ( cons41 [&] cons42 [&] cons43 ) s"
  apply (simp only:cons41_def cons42_def cons43_def exp41_def exp42_def
          x_def y_def)
  apply (inv_check_oracle "parx^2 + parx*pary + pary^2 - 111/59")
  sorry

lemma ODE4:"{x[**]2 [\<le>] Con Real (1/2) [&] y[**]2 [\<le>] Con Real (1/3)}
           <[(''parx'', R),(''pary'', R)]: [(exp41),(exp42)] && Inv & fTrue>
            {x [-] Con Real 4 [*] y [<] Con Real 8;elE 0 [[|]] (almost (x [-] Con Real 4 [*] y [<] Con Real 8))}"
apply (rule ContinuousRuleGT) 
  using allcons4 apply (simp add:cons41_def cons42_def cons43_def 
          x_def y_def  fAnd_def fImp_def dOr_def )
  by (smt almostmono)

ML{*
trans_goal @{term "\<forall>s. ((RVar ''parx'' [**] 2 [\<le>] Con Real (1 / 2) [&] RVar ''pary'' [**] 2 [\<le>] Con Real (1 / 3) [\<longrightarrow>] Inv) [&]
         (Inv [\<longrightarrow>] RVar ''parx'' [-] Con Real 4 [*] RVar ''pary'' [<] Con Real 8) [&]
         (exeFlow
           (<[(''parx'', R),
              (''pary'',
               R)]:[(Con Real 0 [-] RVar ''parx'' [-] (Con Real 1117 [*] RVar ''pary'') [div] Con Real 500) [+]
                    (Con Real 439 [*] RVar ''pary'' [**] 3) [div] Con Real 200 [-]
                    (Con Real 333 [*] RVar ''pary'' [**] 5) [div] Con Real 500,
                    (RVar ''parx'' [+] ((Con Real 617 [*] RVar ''pary'') [div] Con Real 500 [-]
                     (Con Real 439 [*] RVar ''pary'' [**] 3) [div] Con Real 200)) [+]
                    (Con Real 333 [*] RVar ''pary'' [**] 5) [div] Con Real 500]&&Inv&fTrue>)
           Inv [\<longrightarrow>]
          Inv))
         s"} |> writeln
*}

definition cons51:: fform where
  "cons51 \<equiv>  (x[**]2 [\<le>] Con Real (1/2) [&] y[**]2 [\<le>] Con Real (1/3)) [\<longrightarrow>] Inv"

definition cons52:: fform where
  "cons52 \<equiv>  Inv [\<longrightarrow>] ((x [-] Con Real 1) [**]2 [+] (y [-] Con Real (3/2)) [**]2 [>] Con Real (1/4)) "

definition cons53:: fform where
  "cons53 \<equiv>  exeFlow(<[(''parx'', R),(''pary'', R)]: [((y[-]x)[-]x[**]3),((y[**]2[-]x)[-]y)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"

lemma allcons5:"\<forall> s. ( cons51 [&] cons52 [&] cons53 ) s"
  apply (simp only:cons51_def cons52_def cons53_def 
          x_def y_def)
  sorry

lemma ODE5:"{x[**]2 [\<le>] Con Real (1/2) [&] y[**]2 [\<le>] Con Real (1/3)}
           <[(''parx'', R),(''pary'', R)]: [((y[-]x)[-]x[**]3),((y[**]2[-]x)[-]y)] && Inv & fTrue>
            {(x [-] Con Real 1) [**]2 [+] (y [-] Con Real (3/2)) [**]2 [>] Con Real (1/4);elE 0 [[|]] (almost ((x [-] Con Real 1) [**]2 [+] (y [-] Con Real (3/2)) [**]2 [>] Con Real (1/4)))}"
apply (rule ContinuousRuleGT) 
  using allcons5 apply (simp add:cons51_def cons52_def cons53_def 
          x_def y_def  fAnd_def fImp_def dOr_def )
  by (smt almostmono)

ML{*
trans_goal @{term "\<forall>s. ((RVar ''parx'' [**] 2 [\<le>] Con Real (1 / 2) [&] RVar ''pary'' [**] 2 [\<le>] Con Real (1 / 3) [\<longrightarrow>]
          Inv) [&]
         (Inv [\<longrightarrow>]
          (RVar ''parx'' [-] Con Real 1) [**] 2 [+] (RVar ''pary'' [-] Con Real (3 / 2)) [**] 2 [>]
          Con Real (1 / 4)) [&]
         (exeFlow
           (<[(''x'', R),
              (''y'',
               R)]:[RVar ''pary'' [-] RVar ''parx'' [-] RVar ''parx'' [**] 3,
                    RVar ''pary'' [**] 2 [-] RVar ''parx'' [-] RVar ''pary'']&&Inv&fTrue>)
           Inv [\<longrightarrow>]
          Inv))
         s"} |> writeln
*}


definition cons61:: fform where
  "cons61 \<equiv>  (x[**]2 [=] Con Real 1 [&] y[**]2 [=] Con Real 1 [&] z[**]2 [=] Con Real 1 ) [\<longrightarrow>] Inv "

definition cons62:: fform where
  "cons62 \<equiv>  Inv [\<longrightarrow>] (([\<not>]x[=]Con Real 0) [&] ([\<not>]y[=]Con Real 0) [&] ([\<not>]z[=]Con Real 0)) "

definition cons63:: fform where
  "cons63 \<equiv>  exeFlow(<[(''parx'', R),(''pary'', R),(''parz'',R)]: [(x[*]y[-]x[*]z),(y[*]z[-]y[*]x),(z[*]x[-]z[*]y)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"

lemma allcons6:"\<forall> s. ( cons61 [&] cons62 [&] cons63 ) s"
  apply (simp only:cons61_def cons62_def cons63_def 
          x_def y_def z_def)
  sorry


lemma ODE6:"{x[**]2 [=] Con Real 1 [&] y[**]2 [=] Con Real 1 [&] z[**]2 [=] Con Real 1}
           <[(''parx'', R),(''pary'', R),(''parz'',R)]: [(x[*]y[-]x[*]z),(y[*]z[-]y[*]x),(z[*]x[-]z[*]y)] && Inv & fTrue>
            {([\<not>]x[=]Con Real 0) [&] ([\<not>]y[=]Con Real 0) [&] ([\<not>]z[=]Con Real 0);elE 0 [[|]] (almost (([\<not>]x[=]Con Real 0) [&] ([\<not>]y[=]Con Real 0) [&] ([\<not>]z[=]Con Real 0)))}"
apply (rule ContinuousRuleGT) 
  using allcons6 apply (simp add:cons61_def cons62_def cons63_def 
          x_def y_def  fAnd_def fImp_def dOr_def )
  by (smt almostmono)

ML{*
trans_goal @{term " \<forall>s. ((RVar ''parx'' [**] 2 [=] Con Real 1 [&]
          RVar ''pary'' [**] 2 [=] Con Real 1 [&] RVar ''parz'' [**] 2 [=] Con Real 1 [\<longrightarrow>]
          Inv) [&]
         (Inv [\<longrightarrow>]
          [\<not>]RVar ''parx'' [=] Con Real 0 [&]
          [\<not>]RVar ''pary'' [=] Con Real 0 [&] [\<not>]RVar ''parz'' [=] Con Real 0) [&]
         (exeFlow
           (<[(''x'', R), (''y'', R),
              (''z'',
               R)]:[RVar ''parx'' [*] RVar ''pary'' [-] RVar ''parx'' [*] RVar ''parz'',
                    RVar ''pary'' [*] RVar ''parz'' [-] RVar ''pary'' [*] RVar ''parx'',
                    RVar ''parz'' [*] RVar ''parx'' [-] RVar ''parz'' [*] RVar ''pary'']&&Inv&fTrue>)
           Inv [\<longrightarrow>]
          Inv))
         s"} |> writeln
*}

definition Inv1 :: fform where
"Inv1 == Inv"
definition Inv2 :: fform where
"Inv2 == Inv"

ML {*
trans_goal @{term "\<forall>s. ((RVar ''plant_t'' [\<ge>] Con Real 0 [&] RVar ''plant_t'' [\<le>] Con Real (16 / 125) [&] Inv [\<longrightarrow>]
          RVar ''plant_v1_1'' [+] Con Real 2 [<] Con Real (1 / 20) [&]
          RVar ''plant_v1_1'' [+] Con Real 2 [>] Con Real - (1 / 20)) [&]
         (RVar ''plant_v1_1'' [=] Con Real - 2 [&]
          RVar ''plant_m1_1'' [=] Con Real 1250 [&]
          RVar ''control_1'' [=] Con Real (4055 / 2) [&] RVar ''plant_t'' [=] Con Real 0 [\<longrightarrow>]
          Inv) [&]
         (RVar ''plant_t'' [=] Con Real (16 / 125) [&] Inv [\<longrightarrow>] Inv\<lbrakk>Con Real 0,''plant_t'',R\<rbrakk>) [&]
         (Inv [\<longrightarrow>]
          Inv\<lbrakk>RVar ''plant_m1_1'' [*]
              (Con Real (811 / 500) [-]
               Con Real (1 / 100) [*]
               (RVar ''control_1'' [div] RVar ''plant_m1_1'' [-] Con Real (811 / 500)) [-]
               Con Real (3 / 5) [*] (RVar ''plant_v1_1'' [+] Con Real 2)),''control_1'',R\<rbrakk>) [&]
         (exeFlow
           (<[(''plant_v1_1'', R), (''plant_m1_1'', R), (''plant_r1_1'', R),
              (''plant_t'',
               R)]:[RVar ''control_1'' [div] RVar ''plant_m1_1'' [-] Con Real (811 / 500),
                    Con Real 0 [-] RVar ''control_1'' [div] Con Real 2548, RVar ''plant_v1_1'',
                    Con Real 1]&&Inv1&RVar ''plant_t'' [<] Con Real (16 / 125)>)
           Inv [\<longrightarrow>]
          Inv) [&]
         (exeFlow
           (<[(''plant_v1_1'', R), (''plant_m1_1'', R), (''plant_r1_1'', R),
              (''plant_t'',
               R)]:[RVar ''control_1'' [div] RVar ''plant_m1_1'' [-] Con Real (811 / 500),
                    Con Real 0 [-] RVar ''control_1'' [div] Con Real 2842, RVar ''plant_v1_1'',
                    Con Real 1]&&Inv2&RVar ''plant_t'' [<] Con Real (16 / 125)>)
           Inv [\<longrightarrow>]
          Inv))
         s"} |> writeln
*}

end
