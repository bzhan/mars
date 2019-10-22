theory nonlinear
  imports HOL.NthRoot HHL_SL invGen
begin


definition x :: exp where
  "x == RVar ''parx''"

definition y :: exp where
  "y == RVar ''pary''"

definition z :: exp where
  "z == RVar ''parz''"

definition a :: exp where
  "a == RVar ''para''"

consts Inv :: fform

definition cons11 :: fform where "cons11 \<equiv> (x[**]2 [\<le>] Real (1/2) [&] y[**]2 [\<le>] Real (1/3)) [\<longrightarrow>] Inv"
definition cons12 :: fform where "cons12 \<equiv> Inv [\<longrightarrow>] (x[-]Real 4[*]y [<] Real 8)"
definition cons13 :: fform where "cons13 \<equiv> exeFlow(<[''parx'',''pary'']: [(Real 0 [-] x [-](Real 1117[*]y)[div]Real 500 [+] (Real 439[*]y[**]3)[div]Real 200 [-] (Real 333[*]y[**]5)[div]Real 500),(x [+](Real 617[*]y)[div]Real 500 [-] (Real 439[*]y[**]3)[div]Real 200 [+] (Real 333[*]y[**]5)[div]Real 500)] && Inv & fTrue>) Inv [\<longrightarrow>] Inv"
lemma allcons1: "\<forall>s. (cons11 [&] cons12 [&] cons13) s"
  apply (simp only: cons11_def cons12_def cons13_def x_def y_def)
  by (inv_check_oracle "parx^2 + parx*pary + pary^2 - 111/59 <=0")

lemma N1:"{(x[**]2 [\<le>] Real (1/2) [&] y[**]2 [\<le>] Real (1/3))}
         <[''parx'',''pary'']: [(Real 0 [-] x [-](Real 1117[*]y)[div]Real 500 [+] (Real 439[*]y[**]3)[div]Real 200 [-] (Real 333[*]y[**]5)[div]Real 500),(x [+](Real 617[*]y)[div]Real 500 [-] (Real 439[*]y[**]3)[div]Real 200 [+] (Real 333[*]y[**]5)[div]Real 500)] && Inv & fTrue>
          {(x[-]Real 4[*]y [<] Real 8);elE 0 [[|]] almost(x[-]Real 4[*]y [<] Real 8)}"
apply (rule ContinuousRuleGT )
  apply auto
      apply (cut_tac allcons1)
      apply (simp add:fAnd_def fImp_def cons11_def)
     apply (cut_tac allcons1)
     apply (simp add:fAnd_def fImp_def cons12_def)
apply (cut_tac allcons1)
    apply (simp add:fAnd_def fImp_def cons13_def)
   apply (simp add:dOr_def)
  apply(cut_tac allcons1)
  apply (simp add:fAnd_def fImp_def dOr_def almost_def cons12_def)
  done


definition cons21 :: fform where "cons21 \<equiv> (x[**]2 [\<le>] Real (1/2) [&] (y[+]Real 2)[**]2 [\<le>] Real (1/3)) [\<longrightarrow>] Inv"
definition cons22 :: fform where "cons22 \<equiv> Inv [\<longrightarrow>] ((x[-]Real 1)[**]2[+](y[-]Real (3/2))[**]2 [>] Real (1/4))"
definition cons23 :: fform where "cons23 \<equiv> exeFlow(<[''parx'',''pary'']: [(Real 0 [-] x [+] y [-]x[**]3),(Real 0 [-] x [-] y [+] y[**]2)] && Inv & fTrue>) Inv [\<longrightarrow>] Inv"
lemma allcons2: "\<forall>s. (cons21 [&] cons22 [&] cons23) s"
  apply (simp only: cons21_def cons22_def cons23_def x_def y_def)
  by (inv_check_oracle"2*parx^2 + (pary + 3/2)^2 - 4<= 0") 
lemma N2:"{ (x[**]2 [\<le>] Real (1/2) [&] (y[+]Real 2)[**]2 [\<le>] Real (1/3))}
         <[''parx'',''pary'']: [(Real 0 [-] x [+] y [-]x[**]3),(Real 0 [-] x [-] y [+] y[**]2)] && Inv & fTrue>
          { ((x[-]Real 1)[**]2[+](y[-]Real (3/2))[**]2 [>] Real (1/4));elE 0 [[|]] almost ((x[-]Real 1)[**]2[+](y[-]Real (3/2))[**]2 [>] Real (1/4))}"
apply (rule ContinuousRuleGT )
  apply auto
      apply (cut_tac allcons2)
      apply (simp add:fAnd_def fImp_def cons21_def)
     apply (cut_tac allcons2)
     apply (simp add:fAnd_def fImp_def cons22_def)
apply (cut_tac allcons2)
    apply (simp add:fAnd_def fImp_def cons23_def)
   apply (simp add:dOr_def)
  apply(cut_tac allcons2)
  apply (simp add:fAnd_def fImp_def dOr_def almost_def cons22_def)
  done

definition cons31 :: fform where "cons31 \<equiv> (x[**]2 [\<le>] Real (1/2) [&] y[**]2 [\<le>] Real (1/3)) [\<longrightarrow>] Inv"
definition cons32 :: fform where "cons32 \<equiv> Inv [\<longrightarrow>] ((x[-]Real 2)[**]2[+](y[-]Real 3)[**]2 [>] Real (1/4))"
definition cons33 :: fform where "cons33 \<equiv> exeFlow(<[''parx'',''pary'']: [(y [-](x[**]7)[*](x[**]4[+]Real 2[*]y[**]2[-]Real 10)),(Real 0 [-] x[**]3 [-]Real 3[*] y[**]5[*](x[**]4[+]Real 2[*]y[**]2[-]Real 10))] && Inv & fTrue>) Inv [\<longrightarrow>] Inv"
lemma allcons3: "\<forall>s. (cons31 [&] cons32 [&] cons33) s"
  apply (simp only: cons31_def cons32_def cons33_def x_def y_def)
by (inv_check_oracle"parx^4 + 2*pary^2 - 19 <= 0")
lemma N3:"{ (x[**]2 [\<le>] Real (1/2) [&] y[**]2 [\<le>] Real (1/3))}
         <[''parx'',''pary'']: [(y [-](x[**]7)[*](x[**]4[+]Real 2[*]y[**]2[-]Real 10)),(Real 0 [-] x[**]3 [-]Real 3[*] y[**]5[*](x[**]4[+]Real 2[*]y[**]2[-]Real 10))] && Inv & fTrue>
          { ((x[-]Real 2)[**]2[+](y[-]Real 3)[**]2 [>] Real (1/4));elE 0 [[|]] almost ((x[-]Real 2)[**]2[+](y[-]Real 3)[**]2 [>] Real (1/4))}"
apply (rule ContinuousRuleGT )
  apply auto
      apply (cut_tac allcons3)
      apply (simp add:fAnd_def fImp_def cons31_def)
     apply (cut_tac allcons3)
     apply (simp add:fAnd_def fImp_def cons32_def)
apply (cut_tac allcons3)
    apply (simp add:fAnd_def fImp_def cons33_def)
   apply (simp add:dOr_def)
  apply(cut_tac allcons3)
  apply (simp add:fAnd_def fImp_def dOr_def almost_def cons32_def)
  done



definition cons41 :: fform where "cons41 \<equiv> (x [=] Real 1 [&] y [=] Real 0 [&] z [=] Real 0) [\<longrightarrow>] Inv"
definition cons42 :: fform where "cons42 \<equiv> Inv [&] close(x[**]2[+]y[**]2[+]z[**]2[=] Real 1)[\<longrightarrow>] (x [\<le>] Real 1 [&] z[\<le>] Real 0)"
definition cons43 :: fform where "cons43 \<equiv> exeFlow(<[''parx'',''pary'',''parz'']: [x[*]z,y[*]z,Real 0[-]x[**]2[-]y[**]2] && Inv & (x[**]2[+]y[**]2[+]z[**]2[=] Real 1)>) Inv [\<longrightarrow>] Inv"
lemma allcons4: "\<forall>s. (cons41 [&] cons42 [&] cons43) s"
  apply (simp add: cons41_def cons42_def cons43_def x_def y_def z_def)
 by (inv_check_oracle "parz <= 0")
lemma N4:"{(x [=] Real 1 [&] y [=] Real 0 [&] z [=] Real 0)}
         <[''parx'',''pary'',''parz'']: [x[*]z,y[*]z,Real 0[-]x[**]2[-]y[**]2] && Inv & (x[**]2[+]y[**]2[+]z[**]2[=] Real 1)>
          {x [\<le>] Real 1 [&] z[\<le>] Real 0;elE 0 [[|]] almost (x [\<le>] Real 1 [&] z[\<le>] Real 0)}"
  apply (rule ContinuousRuleGT )
apply auto
  apply(simp add:fAnd_def fImp_def fEqual_def)
      apply (cut_tac allcons4)
      apply (simp add:fAnd_def fImp_def cons41_def)
     apply (cut_tac allcons4)
     apply (simp add:fAnd_def fImp_def cons42_def)
apply (cut_tac allcons4)
    apply (simp add:fAnd_def fImp_def cons43_def)
   apply (simp add:dOr_def)
  apply(cut_tac allcons4)
  apply (simp add:fAnd_def fImp_def dOr_def almost_def cons42_def)
  done

definition cons51 :: fform where "cons51 \<equiv> (x [=] Real 0 [&] y [=] Real (0-1) [&] y[*]a[**]2[=]Real -1) [\<longrightarrow>] Inv"
definition cons52 :: fform where "cons52 \<equiv> Inv [\<longrightarrow>] ( y[\<le>] Real 0 )"
definition cons53 :: fform where "cons53 \<equiv> exeFlow(<[''parx'',''pary'',''para'']: [x,y[**]2,Real (1/2)[div]a] && Inv & fTrue>) Inv [\<longrightarrow>] Inv"
lemma allcons5: "\<forall>s. (cons51 [&] cons52 [&] cons53) s"
apply (simp only: cons51_def cons52_def cons53_def x_def y_def a_def)
 by (inv_check_oracle "pary*para^2+1=0")

lemma N5le:"{(x [=] Real 0 [&] y [=] Real (0-1) [&] y[*]a[**]2[=]Real -1)}
         <[''parx'',''pary'',''para'']: [x,y[**]2,Real (1/2)[div]a] && Inv & fTrue>
          {( y[\<le>] Real 0 );elE 0 [[|]] almost ( y[\<le>] Real 0 )}"
  apply (rule ContinuousRuleGT )
apply auto
      apply (cut_tac allcons5)
      apply (simp add:fAnd_def fImp_def cons51_def)
     apply (cut_tac allcons5)
     apply (simp add:fAnd_def fImp_def cons52_def)
apply (cut_tac allcons5)
    apply (simp add:fAnd_def fImp_def cons53_def)
   apply (simp add:dOr_def)
  apply(cut_tac allcons5)
  apply (simp add:fAnd_def fImp_def dOr_def almost_def cons52_def)
  done
lemma N5:"{(x [=] Real 0 [&] y [=] Real (0-1) )}
         <[''parx'',''pary'']: [x,y[**]2] && Inv & fTrue>
          {( y[\<le>] Real 0);elE 0 [[|]] almost ( y[\<le>] Real 0)}"
apply (rule GhostRule[where w="''para''"
                          and F="Real (1/2)[div]a"
                          and pre="x [=] Real 0 [&] y [=] Real (0-1) [&] y[*]a[**]2[=]Real -1"
                          and post="( y[\<le>] Real 0 )"
                          and HF="(elE 0)[[|]]almost (( y[\<le>] Real 0 ))"])
         apply auto
apply(simp add: fAnd_def  fEqual_def  not_in_fform_def x_def y_def )
   apply(simp add: fLessEqual_def fOr_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def ) 
  apply(simp add:dOr_def   fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_dform_def x_def y_def  almost_def)
  apply(subgoal_tac "{(x [=] Real 0 [&] y [=] Real (0-1) [&] y[*]a[**]2[=]Real -1)}
         <[''parx'',''pary'',''para'']: [x,y[**]2,Real (1/2)[div]a] && Inv & fTrue>
          {( y[\<le>] Real 0 );elE 0 [[|]] almost ( y[\<le>] Real 0 )}")
  apply(simp add: dOr_def)
     apply (rule N5le)
  subgoal for s
  proof -
    have not_a: "not_in_fform ''para'' (x [=] Real 0 [&] y [=] Real - 1)"
      by (simp add: fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def )
    have eq: "(x [=] Real 0 [&] y [=] Real - 1) (\<lambda>y. if y \<noteq> ''para'' then s y else  sqrt ( -1/s ''pary'')) \<longleftrightarrow> (x [=] Real 0 [&] y [=] Real - 1) s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="sqrt ( -1/s ''pary'')"] )
      apply (auto simp add: eq fAnd_def   fEqual_def fLess_def   x_def y_def  a_def)
      done
  qed
 subgoal for s
   proof -
     have not_a: "not_in_fform ''para'' (y [\<le>] Real 0)"
       by(simp add:  fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def )
     have eq: "(y [\<le>] Real 0) (\<lambda>y. if y \<noteq> ''para'' then s y else sqrt ( -s ''pary'')) \<longleftrightarrow> (y [\<le>] Real 0) s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="sqrt ( -s ''pary'')"])
      apply ( simp add: eq fAnd_def  fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def  a_def)
      done
  qed
  subgoal for h n d
    apply(simp add:dOr_def almost_def fAnd_def a_def )
    apply (case_tac "n=d")
    apply auto
    apply (case_tac "n>d")
     apply auto
    apply (case_tac "n<d")
     apply auto
    apply (rule exI[where x="\<lambda>t y. sqrt(- (h t  ''pary''))"])
    apply auto
      apply (subgoal_tac "not_in_fform ''para'' (y [\<le>] Real 0)")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:  fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def )
    apply(simp add:  fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def )
    done
  done

end