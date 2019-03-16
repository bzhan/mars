theory nonlinear
  imports HOL.NthRoot HHL_SL invGen
begin


definition x :: exp where
  "x == RVar ''parx''"

definition y :: exp where
  "y == RVar ''pary''"

definition z :: exp where
  "z == RVar ''parz''"


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





end