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
  "Assignment == x := ((Real 1) [+] x)"

lemma B01:
  "{x[\<ge>](Real 0)} x := ((Real 1) [+] x) {x[\<ge>](Real 1); elE 0}"
  unfolding x_def
  apply (rule AssignRRule, auto, fold x_def)
proof -
  fix s
  assume a: "(x[\<ge>]Real 0) s"
  obtain c where evalx: "evalE x s = c"
    using a[unfolded fGreaterEqual_def] by auto
  show "(x[\<ge>]Real 1) (\<lambda>y. if y = ''parx'' then evalE (Real 1 [+] x) s else s y)" 
  proof -
    have eval0: "evalE (Real 0) s = 0"
      by auto
    from a[unfolded fGreaterEqual_def] evalx eval0
    have nonneg_c: "0 \<le> c" by auto
    have evalx': "s ''parx'' = c"
      using evalx unfolding x_def evalE.simps(2) by auto
    show ?thesis
      unfolding fGreaterEqual_def x_def evalE.simps(2) evalE.simps(1)
      by (simp add: evalx' nonneg_c)
  qed
qed

lemma B02:
  "{x[\<ge>](Real 0)}
    (x :=((Real 1) [+] x ));
    (x :=((Real 1) [+] x ))*&& x[\<ge>](Real 1)
   {x[\<ge>](Real 1);elE 0}"

apply (cut_tac p="x[\<ge>](Real 0)"
           and P="(x :=((Real 1) [+] x ))" 
           and m="x[\<ge>](Real 1)"
           and Q="(x :=((Real 1) [+] x ))*&& x[\<ge>](Real 1)" 
           and q="x[\<ge>](Real 1)"
           and H="elE 0"
           and G="elE 0"
            in  SequentialRule_aux,auto)
    apply (cut_tac B01,auto)
   defer
   apply (simp add:chop_def)
  apply (simp add: Valid_def)
apply (cut_tac I="x[\<ge>](Real 1)"
           and P="x :=((Real 1) [+] x )" 
           and H="elE 0" 
            in  RepetitionRule,auto)
apply (simp add:chop_def) 
defer
apply (simp add:dOr_def )
apply (cut_tac p="x[\<ge>](Real 1)" 
           and q="x[\<ge>](Real 1)" 
           and H="elE 0" 
           and x="''parx''" 
           and f="((Real 1) [+] x )" in  AssignRRule,auto)
defer apply (simp add:x_def)

proof-
  fix s
  assume a:"(x[\<ge>]Real 1) s"
  obtain c where evalx: "evalE x s = c"
     using a[unfolded fGreaterEqual_def] by auto
   show "(x[\<ge>]Real 1)
          (\<lambda>y. if y = ''parx'' then evalE (Real 1 [+] x) s else s y)"
proof -
    have eval1: "evalE (Real 1) s = 1"
      by auto
    from a[unfolded fGreaterEqual_def] evalx eval1
    have nonneg_c1: "1 \<le> c" by auto
    have nonneg_c0: "0 \<le> c" using nonneg_c1 by linarith
    have evalx': "s ''parx'' = c"
      using evalx unfolding x_def evalE.simps(2) by auto
    show ?thesis
      unfolding fGreaterEqual_def x_def evalE.simps(2) evalE.simps(1)
      by (simp add: evalx' nonneg_c0)
  qed
qed


lemma B03:
  "{x[\<ge>](Real 0)}
    (x :=((Real 1) [+] x ));
    (x :=((Real 1) [+] x )) [[ (y :=((Real 1) [+] y ))
   {x[\<ge>](Real 1);elE 0}"
apply (cut_tac p="x[\<ge>](Real 0)"
           and P="(x :=((Real 1) [+] x ))" 
           and m="x[\<ge>](Real 1)"
           and Q="(x :=((Real 1) [+] x )) [[ (y :=((Real 1) [+] y ))" 
           and q="x[\<ge>](Real 1)"
           and H="elE 0"
           and G="elE 0"
            in  SequentialRule_aux,auto)
    apply (cut_tac B01,auto)
   defer
   apply (simp add:chop_def)
  apply (simp add: Valid_def)
  apply (cut_tac P="(x :=((Real 1) [+] x )) "
           and Q="(y :=((Real 1) [+] y ))" 
           and p="x[\<ge>](Real 1)" 
           and m="x[\<ge>](Real 1)" 
           and q="x[\<ge>](Real 1)" 
           and H="elE 0" 
           and G="elE 0"  in JoinRule,auto)
defer
defer
apply (simp add:fOr_def )
apply (simp add:dOr_def )
apply (cut_tac p="x[\<ge>](Real 1)" 
           and q="x[\<ge>](Real 1)" 
           and H="elE 0" 
           and x="''parx''" 
           and f="((Real 1) [+] x )" in  AssignRRule,auto)
    defer 
    apply (simp add:x_def)
apply (cut_tac p="x[\<ge>](Real 1)" 
           and q="x[\<ge>](Real 1)" 
           and H="elE 0" 
           and x="''pary''" 
           and f="((Real 1) [+] y )" in  AssignRRule,auto)
    defer
    apply (simp add:y_def)
  
proof-
  fix s
  assume a:"(x[\<ge>]Real 1) s"
  obtain c where evalx: "evalE x s = c"
     using a[unfolded fGreaterEqual_def] by auto
   show "(x[\<ge>]Real 1)
          (\<lambda>y. if y = ''parx'' then evalE (Real 1 [+] x) s else s y)"
proof -
    have eval1: "evalE (Real 1) s = 1"
      by auto
    from a[unfolded fGreaterEqual_def] evalx eval1
    have nonneg_c1: "1 \<le> c" by auto
    have nonneg_c0: "0 \<le> c" using nonneg_c1 by linarith
    have evalx': "s ''parx'' = c"
      using evalx unfolding x_def evalE.simps(2) by auto
    show ?thesis
      unfolding fGreaterEqual_def x_def evalE.simps(2) evalE.simps(1)
      by (simp add: evalx' nonneg_c0)
  qed
  assume a:"(x[\<ge>]Real 1) s"
  obtain c where evalx: "evalE x s = c"
     using a[unfolded fGreaterEqual_def] by auto
   show "(x[\<ge>]Real 1)
          (\<lambda>ya. if ya = ''pary'' then evalE (Real 1 [+] y) s else s ya) "
proof -
    have eval1: "evalE (Real 1) s = 1"
      by auto
    from a[unfolded fGreaterEqual_def] evalx eval1
    have nonneg_c1: "1 \<le> c" by auto
    have evalx': "s ''parx'' = c"
      using evalx unfolding x_def evalE.simps(2) by auto
    show ?thesis
      unfolding fGreaterEqual_def x_def y_def evalE.simps(2) evalE.simps(1)
      by (simp add: evalx' nonneg_c1)
qed
qed

consts Inv :: fform

definition cons11 :: fform where "cons11 \<equiv> (x [\<ge>] Real 1) [\<longrightarrow>] Inv"
definition cons12 :: fform where "cons12 \<equiv> Inv [\<longrightarrow>] (x [\<ge>] Real 1)"
definition cons13 :: fform where "cons13 \<equiv> exeFlow(<[''parx'']: [(Real 2)] && Inv & fTrue>) Inv [\<longrightarrow>] Inv"

lemma allcons1: "\<forall>s. (cons11 [&] cons12 [&] cons13) s"
  apply (simp only: cons11_def cons12_def cons13_def x_def)
  by (inv_check_oracle "parx-1>=0")

lemma ODE1:
  "{x [\<ge>] (Real 0)}  \<comment> \<open>x >= 0\<close>
    (x := ((Real 1) [+] x));  \<comment> \<open>x := 1 + x\<close>
    <[''parx'']: [(Real 2)] && Inv & fTrue>  \<comment> \<open>x' = 2 & True\<close>
   {x[\<ge>](Real 1); (elE 0 [[|]] (almost (x[\<ge>](Real 1))))}"  \<comment> \<open>x >= 1\<close>
  apply (rule SequentialRule[where m="x[\<ge>](Real 1)" and H="elE 0" and G="elE 0 [[|]] (almost (x[\<ge>](Real 1)))"])
  apply (rule B01)
  prefer 2 subgoal
    by (simp add:chop_def dOr_def Valid_def)
  apply (rule ContinuousRuleGT)
  using allcons1 apply (auto simp add: cons11_def cons12_def cons13_def fAnd_def fImp_def dOr_def)
  by (metis (no_types, lifting) almostmono)

definition cons21:: fform where "cons21 \<equiv>  ((x [\<ge>] Real 0)[&](y [\<ge>] Real 0)[&](z [\<ge>] Real 0)) [\<longrightarrow>] Inv "
definition cons22:: fform where "cons22 \<equiv>  Inv [\<longrightarrow>] (x [\<ge>] Real 0) "
definition cons23:: fform where "cons23 \<equiv>  exeFlow(<[''parx'', ''pary'']: [y,z] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"

lemma allcons2:"\<forall> s. ( cons21 [&] cons22 [&] cons23 ) s"
  apply (simp only:cons21_def cons22_def cons23_def x_def y_def z_def)
  by (inv_check_oracle "parz >= 0 & pary >= 0 & parx >= 0 ")

lemma ODE2:"{x [\<ge>] Real 0 [&] y [\<ge>] Real 0 [&] z [\<ge>] Real 0}
           <[''parx'', ''pary'']:[y, z]&&Inv&\<lambda>s. True>
            {x [\<ge>] Real 0; (elE 0 [[|]] (almost (x[\<ge>](Real 0))))}"
  apply (rule ContinuousRuleGT) 
  using allcons2 apply (auto simp add:cons21_def cons22_def cons23_def x_def y_def z_def fAnd_def fImp_def dOr_def)
  by (smt almostmono)

definition cons31:: fform where "cons31 \<equiv>  (x [\<ge>] Real 0) [\<longrightarrow>] Inv "
definition cons32:: fform where "cons32 \<equiv>  Inv [\<longrightarrow>] (x [\<ge>] Real 0) "
definition cons33:: fform where "cons33 \<equiv>  exeFlow(<[''parx'']: [(Real 5)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"
definition cons34:: fform where "cons34 \<equiv>  exeFlow(<[''parx'']: [(Real 2)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"
definition cons35:: fform where "cons35 \<equiv>  exeFlow(<[''parx'']: [x] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"

lemma allcons3:"\<forall> s. ( cons31 [&] cons32 [&] cons33 [&] cons34 [&] cons35) s"
  apply (simp only:cons31_def cons32_def cons33_def cons34_def cons35_def
          x_def )
  by (inv_check_oracle "parx>=0")

lemma ODE3:"{x [\<ge>] Real 0 }
           <[''parx'']: [(Real 5)] && Inv & fTrue>;
           <[''parx'']: [(Real 2)] && Inv & fTrue>;
           <[''parx'']: [x] && Inv & fTrue>
            {x [\<ge>] Real 0; (elE 0 [[|]] (almost (x[\<ge>](Real 0))))}"
  apply (rule SequentialRule[where m="x[\<ge>](Real 0)" and H="elE 0 [[|]] (almost (x[\<ge>](Real 0)))" and G="elE 0 [[|]] (almost (x[\<ge>](Real 0)))"]) 
  apply (rule ContinuousRuleGT) 
  using allcons3 apply (simp add:cons31_def cons32_def cons33_def cons34_def cons35_def
          x_def fAnd_def fImp_def dOr_def )
    apply (smt almostmono)
   apply (rule SequentialRule[where m="x[\<ge>](Real 0)" and H="elE 0 [[|]] (almost (x[\<ge>](Real 0)))" and G="elE 0 [[|]] (almost (x[\<ge>](Real 0)))"]) 
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

definition exp41:: exp where
  "exp41 \<equiv> ((Real 0 [-] x [-] ((Real 1117 [*] y) [div] Real 500)) [+]
   ((Real 439 [*] y [**] 3) [div] Real 200 ))[-]((Real 333 [*] y [**] 5) [div] Real 500) "

definition exp42:: exp where
  "exp42 \<equiv> ((x [+]((Real 617 [*] y) [div] Real 500)) [-]
   ((Real 439 [*] y [**] 3) [div] Real 200 ))[+]((Real 333 [*] y [**] 5) [div] Real 500)"

definition cons41:: fform where
  "cons41 \<equiv>  (x[**]2 [\<le>] Real (1/2) [&] y[**]2 [\<le>] Real (1/3)) [\<longrightarrow>] Inv "

definition cons42:: fform where
  "cons42 \<equiv>  Inv [\<longrightarrow>] (x [-] Real 4 [*] y [<] Real 8) "

definition cons43:: fform where
  "cons43 \<equiv>  exeFlow(<[''parx'', ''pary'']: [(exp41),(exp42)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"

lemma allcons4:"\<forall> s. ( cons41 [&] cons42 [&] cons43 ) s"
  apply (simp only:cons41_def cons42_def cons43_def exp41_def exp42_def
          x_def y_def)
  (*apply (inv_oracle_SOS)
 done*)
by (inv_check_oracle "parx^2 + parx*pary + pary^2 - 111/59 <= 0") 

lemma ODE4:"{x[**]2 [\<le>] Real (1/2) [&] y[**]2 [\<le>] Real (1/3)}
           <[''parx'', ''pary'']: [(exp41),(exp42)] && Inv & fTrue>
            {x [-] Real 4 [*] y [<] Real 8;elE 0 [[|]] (almost (x [-] Real 4 [*] y [<] Real 8))}"
  apply (rule ContinuousRuleGT) 
  using allcons4 apply (simp add: cons41_def cons42_def cons43_def x_def y_def fAnd_def fImp_def dOr_def )
  by (smt almostmono)

definition cons51:: fform where
  "cons51 \<equiv>  (x[**]2 [\<le>] Real (1/2) [&] (y [+] Real 2)[**]2 [\<le>] Real (1/3)) [\<longrightarrow>] Inv"

definition cons52:: fform where
  "cons52 \<equiv>  Inv [\<longrightarrow>] ((x [-] Real 1) [**]2 [+] (y [-] Real (3/2)) [**]2 [>] Real (1/4)) "

definition cons53:: fform where
  "cons53 \<equiv>  exeFlow(<[''parx'', ''pary'']: [((y[-]x)[-]x[**]3),((y[**]2[-]x)[-]y)] && Inv & fTrue>) (Inv)  [\<longrightarrow>]  Inv"

lemma allcons5:"\<forall> s. ( cons51 [&] cons52 [&] cons53 ) s"
  apply (simp only: cons51_def cons52_def cons53_def x_def y_def)
  by (inv_check_oracle "2*(parx^2) + (pary+3/2)^2 - 4 <= 0")

lemma ODE5:"{x[**]2 [\<le>] Real (1/2) [&] (y [+] Real 2) [**]2 [\<le>] Real (1/3)}
           <[''parx'', ''pary'']: [((y[-]x)[-]x[**]3),((y[**]2[-]x)[-]y)] && Inv & fTrue>
            {(x [-] Real 1) [**]2 [+] (y [-] Real (3/2)) [**]2 [>] Real (1/4);elE 0 [[|]] (almost ((x [-] Real 1) [**]2 [+] (y [-] Real (3/2)) [**]2 [>] Real (1/4)))}"
apply (rule ContinuousRuleGT) 
  using allcons5 apply (simp add:cons51_def cons52_def cons53_def 
          x_def y_def  fAnd_def fImp_def dOr_def )
  by (smt almostmono)





end
