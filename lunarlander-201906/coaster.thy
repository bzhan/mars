theory coaster
  imports HOL.NthRoot HHL_SL invGen
begin

consts dyLo :: real

consts dyHi :: real 

consts g :: real

consts cy :: real

consts cx :: real

consts yG :: real

consts dy0 :: real

consts dx0 :: real

consts vLo :: real

consts vHi :: real

consts centLo :: real

consts centHi :: real

consts cent :: real

consts tanLo :: real

consts tanHi :: real

consts tan :: real

consts r :: real

consts y0 :: real

consts x0 :: real

consts y1 :: real

consts x1 :: real

consts v0 :: real

consts c :: real

definition y :: exp where
"y == RVar ''pary''"

definition x :: exp where
"x == RVar ''parx''"

definition dy :: exp where
"dy == RVar ''pardy''"

definition dx :: exp where
"dx == RVar ''pardx''"

definition v :: exp where
"v == RVar ''parv''"

definition a :: exp where
"a == RVar ''para''"
consts Inv :: fform

definition pre1 :: fform where
"pre1 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
      [&] (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)
      [&]((Real dy0[\<le>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0) 
        [\<longrightarrow>](v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real (dyLo*g)[\<le>] Real (-dy0*g)[&]Real (-dy0*g)[\<le>]Real (dyHi*g)[&] Real dx0[*]y [=] Real dy0[*]x [+] Real (dx0*c)))
      [&](Real dy0[\<le>]Real 0)
      [&]((x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](Real dx0[*]v[**]2[>]Real (2*dy0*g)[*](Real x1[-]x)))
      [&](Real x1[>]Real x0)
      [&](Real (dx0^2+dy0^2)[=]Real 1)
      [&](Real dx0[>]Real 0)"

definition post1 :: fform where
"post1 == (v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
      [&](x[\<le>]Real x1 [&] x[\<ge>]Real x0)
      [&](Real dx0[*]y [=] Real dy0[*]x [+] Real (dx0*c))"


definition cons11 :: fform where
"cons11 == pre1 [\<longrightarrow>] Inv"
definition cons12 :: fform where
"cons12 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>]post1"
definition cons13 :: fform where
"cons13 ==  (exeFlow(<[''parx'', ''pary'', ''parv'']: [(v[*]Real dx0),(v[*]Real dy0),(Real (-dy0*g))] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>) (Inv)  [\<longrightarrow>]  Inv )"
lemma allcons1: "\<forall>s. (cons11[&]cons12 [&] cons13 ) s"
  apply (simp add: cons11_def cons12_def cons13_def  x_def y_def v_def pre1_def post1_def)
  by (inv_check_oracle "g > 0 & dy0 <= 0 & parv > 0 & parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 & dx0*pary - dy0*parx - dx0*c = 0 ")

lemma linedown:"{pre1}
             <[''parx'', ''pary'', ''parv'']: [(v[*]Real dx0),(v[*]Real dy0),(Real (-dy0*g))] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
              {post1;(elE 0 [[|]] (almost post1))}"
  apply (rule ContinuousRuleGT )
  apply auto
   apply (simp add:fAnd_def )
       apply (simp add:pre1_def post1_def fAnd_def fImp_def)
      apply (cut_tac allcons1)
      apply (simp add:fAnd_def cons11_def fImp_def)
       apply (subgoal_tac "\<forall>s. cons12 s")
      apply (simp add: cons12_def fImp_def)
      apply (simp add:fAnd_def)
     apply (cut_tac allcons1)
     apply (simp add:fAnd_def)
    apply (cut_tac allcons1)
    apply (simp add:fAnd_def cons13_def fImp_def )
   apply (simp add:dOr_def)
  apply (subgoal_tac "\<forall>s. cons12 s")
   apply (simp add: cons12_def fImp_def dOr_def)
   apply (simp add: almost_def)
apply (cut_tac allcons1)
     apply (simp add:fAnd_def)
  done



definition pre2 :: fform where
"pre2 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
      [&] (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)
      [&]((Real dy0[\<ge>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0) 
        [\<longrightarrow>](v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real (dyLo*g)[\<le>] Real (-dy0*g)[&]Real (-dy0*g)[\<le>]Real (dyHi*g)[&] Real dx0[*]y [=] Real dy0[*]x [+] Real (dx0*c)))
      [&](Real dy0[\<ge>]Real 0)
      [&]((x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](Real dx0[*]v[**]2[>]Real (2*dy0*g)[*](Real x1[-]x)))
      [&](Real x1[>]Real x0)
      [&](Real (dx0^2+dy0^2)[=]Real 1)
      [&](Real dx0[>]Real 0)
          "

definition post2 :: fform where
"post2 == (v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
      [&]x[\<le>]Real x1 [&] x[\<ge>]Real x0
      [&]Real dx0[*]y [=] Real dy0[*]x [+] Real (dx0*c)
      "
definition cons21 :: fform where
"cons21 == pre2[&](v[*](a[**]2)[=]Real 1) [\<longrightarrow>] Inv"
definition cons22 :: fform where
"cons22 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>]post2[&](v[*](a[**]2)[=]Real 1) "
definition cons23 :: fform where
"cons23 ==  (exeFlow(<[''parx'', ''pary'', ''parv'', ''para'']: [(v[*]Real dx0),(v[*]Real dy0),(Real (-dy0*g)),(Real (dy0 * g/2) [*] a [div] v)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>) (Inv)  [\<longrightarrow>]  Inv )"

lemma allcons2: "\<forall>s. (cons21[&]cons22[&] cons23 ) s"
  apply (simp add: cons21_def cons22_def cons23_def  x_def y_def v_def a_def pre2_def post2_def)
by (inv_check_oracle "parv*para^2 - 1 = 0 & parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 & parv > 0 & dx0*pary - dy0*parx -dx0*c = 0")





lemma lineuple:"{pre2[&](v[*](a[**]2)[=]Real 1)}
              <[''parx'', ''pary'', ''parv'', ''para'']: [(v[*]Real dx0),(v[*]Real dy0),(Real (-dy0*g)),(Real (dy0 * g/2) [*] a [div] v)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
              {post2[&](v[*](a[**]2)[=]Real 1);(elE 0)[[|]]almost (post2[&](v[*](a[**]2)[=]Real 1))}"
  apply (rule ContinuousRuleGT )
  apply auto
 apply (simp add:fAnd_def )
       apply (simp add:pre2_def post1_def fAnd_def fImp_def)
 apply (cut_tac allcons2)
      apply (simp add:fAnd_def cons21_def fImp_def)
apply (subgoal_tac "\<forall>s. cons22 s")
      apply (simp add: cons22_def fImp_def)
      apply (simp add:fAnd_def)
     apply (cut_tac allcons2)
     apply (simp add:fAnd_def)
apply (cut_tac allcons2)
    apply (simp add:fAnd_def cons23_def fImp_def)
  apply (simp add: dOr_def)
 apply (subgoal_tac "\<forall>s. cons22 s")
   apply (simp add: cons22_def fImp_def dOr_def)
   apply (simp add: almost_def)
apply (cut_tac allcons2)
  apply (simp add:fAnd_def)
  done
lemma lineup:"{pre2}
              <[''parx'', ''pary'', ''parv'']: [(v[*]Real dx0),(v[*]Real dy0),(Real (-dy0*g))] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
              {post2;(elE 0)[[|]]almost post2}"
  apply (rule GhostRule[where w="''para''"
                          and F="(Real (dy0 * g/2) [*] a [div] v)"
                          and pre="pre2[&](v[*](a[**]2)[=]Real 1)"
                          and post="post2[&](v[*](a[**]2)[=]Real 1)"
                          and HF="(elE 0)[[|]]almost (post2[&](v[*](a[**]2)[=]Real 1))"])
         apply auto
  apply(simp add:pre2_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def)
   apply(simp add:post2_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def) 
  apply(simp add:dOr_def post2_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_dform_def x_def y_def v_def almost_def)
  apply(subgoal_tac "{pre2[&](v[*](a[**]2)[=]Real 1)}
              <[''parx'', ''pary'', ''parv'', ''para'']: [(v[*]Real dx0),(v[*]Real dy0),(Real (-dy0*g)),(Real (dy0 * g/2) [*] a [div] v)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
              {post2[&](v[*](a[**]2)[=]Real 1);(elE 0)[[|]]almost (post2[&](v[*](a[**]2)[=]Real 1))}")
  apply(simp add: dOr_def)
     apply (rule lineuple)
  subgoal for s
  proof -
    have not_a: "not_in_fform ''para'' pre2"
      by (simp add:pre2_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def)
    have eq: "pre2 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> pre2 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "pre2 s"
      then have "s ''parv'' > 0"
        unfolding pre2_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
   subgoal for s
   proof -
     have not_a: "not_in_fform ''para'' post2"
       by(simp add:post2_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def)
     have eq: "post2 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> post2 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "post2 s"
      then have "s ''parv'' > 0"
        unfolding post2_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
  subgoal for h n d
    apply(simp add:dOr_def almost_def fAnd_def a_def v_def)
    apply (case_tac "n=d")
    apply auto
    apply (case_tac "n>d")
     apply auto
    apply (case_tac "n<d")
     apply auto
    apply (rule exI[where x="\<lambda>t y. 1/sqrt(evalE v (h t))"])
    apply auto
      apply (subgoal_tac "not_in_fform ''para'' post2")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post2_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def)
     apply(subgoal_tac"(h t ''parv'') > 0")
      apply(simp add:fEqual_def v_def)
    apply (simp add: power_divide)
     apply(simp add:post2_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def)
    apply auto
    apply (subgoal_tac "not_in_fform ''para'' post2")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post2_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def)
    done
  done
definition pre3 :: fform where
"pre3 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (v0^2)[+]Real (2*g*yG))
      [&]((Real dy0[\<le>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)
       [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<ge>] Real cx[&] y[\<ge>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<le>]Real 0)
      [&](dx[*]Real r [=](y[-]Real cy))
      [&](dy[*]Real r [=](Real cx[-]x))
      [&](Real x1[>]Real x0)
      [&](Real y1[<]Real y0)
      [&](Real cy[\<le>]Real y1)
      [&](Real cx[\<le>]Real x0)
      [&](Real r[>]Real 0) 
      [&]((x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1))"

definition post3 :: fform where
"post3 == (dx[*]Real r [=](y[-]Real cy))
       [&](dy[*]Real r [=](Real cx[-]x))
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)
       [&](y[\<ge>]Real cy)"
       

definition cons31 :: fform where
"cons31 == pre3 [\<longrightarrow>] Inv"
definition cons32 :: fform where
"cons32 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)[\<longrightarrow>]post3"
definition cons33 :: fform where
"cons33 ==  (exeFlow(<[''parx'', ''pary'', ''parv'', ''pardx'',  ''pardy'']: [(v[*]dx),(v[*]dy),(dy[*]Real -g),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>) (Inv)  [\<longrightarrow>]  Inv )"
lemma allcons3: "\<forall>s. (cons31[&]cons32[&]cons33 ) s"
apply (simp add: cons31_def cons32_def cons33_def  x_def y_def v_def dx_def dy_def pre3_def post3_def)
  by (inv_check_oracle
   " r>0 &
     pardx*r - pary + cy = 0 &
     pardy*r - cx + parx = 0 &
     y1 - cy >= 0 & x0 - cx >= 0 &
     parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 &
     g > 0 & parv > 0 &
     (parx-cx)^2+(pary-cy)^2-r^2 = 0"
   "y1" "x0")




lemma q1:"{pre3}
         <[''parx'', ''pary'', ''parv'', ''pardx'', ''pardy'']: [(v[*]dx),(v[*]dy),(dy[*]Real -g),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>
          {post3;(elE 0 [[|]] (almost post3))}"
  apply (rule ContinuousRuleGT )
  apply auto
       apply(simp add:pre3_def fAnd_def)
      apply (cut_tac allcons3)
      apply (simp add:cons31_def fAnd_def fImp_def)
     apply (subgoal_tac "\<forall>s. cons32 s")
      apply (simp add:cons32_def fImp_def )
      apply (simp add:fAnd_def)
     apply (cut_tac allcons3)
     apply (simp add:fAnd_def )
apply (cut_tac allcons3)
    apply (simp add:cons33_def fAnd_def fImp_def)
   apply (simp add:dOr_def)
apply (subgoal_tac "\<forall>s. cons32 s")
   apply (simp add:cons32_def fImp_def )
   apply (simp add:dOr_def almost_def)
 apply (cut_tac allcons3)
  apply (simp add:fAnd_def )
  done




definition pre4 :: fform where
"pre4 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (v0^2)[+]Real (2*g*yG))
      [&]((Real dy0[\<ge>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)
         [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<ge>] Real cx[&] y[\<ge>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<ge>]Real 0)
      [&](dx[*]Real r[=](Real cy[-]y))
      [&](dy[*]Real r[=](x[-]Real cx))
      [&](Real x1[>]Real x0)
      [&](Real y1[<]Real y0)
      [&](Real r[>]Real 0)
      [&](Real cy[\<le>]Real y1)
      [&](Real cx[\<le>]Real x0)
      [&]((x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)[\<longrightarrow>](v[**]2)[div]Real 2[>]Real g[*](Real y0[-]y))
      [&](x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)"
      
definition post4 :: fform where
"post4 == (dx[*]Real r[=](Real cy[-]y))
       [&](dy[*]Real r[=](x[-]Real cx))
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real (v0^2)[+]Real (2*g*yG))
       [&](y[\<ge>]Real cy)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"


definition cons41 :: fform where
"cons41 == pre4[&](v[*](a[**]2)[=]Real 1) [\<longrightarrow>] Inv"
definition cons42 :: fform where
"cons42 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)[\<longrightarrow>](post4[&](v[*](a[**]2)[=]Real 1))"
definition cons43 :: fform where
"cons43 == (exeFlow(<[''parx'', ''pary'', ''parv'', ''pardx'',  ''pardy'', ''para'']: [(v[*]dx),(v[*]dy),(dy[*](Real -g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>) (Inv)  [\<longrightarrow>]  Inv )"


lemma allcons4: "\<forall>s. (cons41[&]cons42[&]cons43 ) s"
  apply (simp add: cons41_def cons42_def cons43_def pre4_def post4_def x_def y_def v_def dx_def dy_def a_def)
  by (inv_check_oracle "
       parv*(para^2)- 1  =0 & 
       parv > 0 & 
       pardx*r + pary - cy = 0 &
       pardy*r + cx - parx = 0 &
       parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 &
      (parx-cx)^2+(pary-cy)^2-r^2 = 0 &
       y1 - cy >= 0" "y1")



lemma q1cwle:"{pre4[&](v[*](a[**]2)[=]Real 1)}
         <[''parx'', ''pary'', ''parv'', ''pardx'',  ''pardy'', ''para'']: [(v[*]dx),(v[*]dy),(dy[*](Real -g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>
          {post4[&](v[*](a[**]2)[=]Real 1);(elE 0 [[|]] (almost (post4[&](v[*](a[**]2)[=]Real 1))))}"
   apply (rule ContinuousRuleGT )
  apply auto
       apply(simp add:pre4_def fAnd_def)
      apply (cut_tac allcons4)
      apply (simp add:cons41_def fAnd_def fImp_def)
     apply (subgoal_tac "\<forall>s. cons42 s")
      apply (simp add:cons42_def fImp_def )
      apply (simp add:fAnd_def)
     apply (cut_tac allcons4)
     apply (simp add:fAnd_def )
apply (cut_tac allcons4)
    apply (simp add:cons43_def fAnd_def fImp_def)
   apply (simp add:dOr_def)
apply (subgoal_tac "\<forall>s. cons42 s")
   apply (simp add:cons42_def fImp_def )
   apply (simp add:dOr_def almost_def)
 apply (cut_tac allcons4)
  apply (simp add:fAnd_def )
  done
lemma q1cw:"{pre4}
         <[''parx'', ''pary'', ''parv'', ''pardx'',  ''pardy'']: [(v[*]dx),(v[*]dy),(dy[*](Real -g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>
          {post4;(elE 0 [[|]] (almost (post4)))}"
apply (rule GhostRule[where w="''para''"
                          and F="(((a[*]dy[*]Real g)[div](Real 2))[div]v)"
                          and pre="pre4[&](v[*](a[**]2)[=]Real 1)"
                          and post="post4[&](v[*](a[**]2)[=]Real 1)"
                          and HF="(elE 0)[[|]]almost (post4[&](v[*](a[**]2)[=]Real 1))"])
         apply auto
  apply(simp add:pre4_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
   apply(simp add:post4_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def) 
  apply(simp add:dOr_def post4_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_dform_def x_def y_def v_def dx_def dy_def almost_def)
  apply(subgoal_tac "{pre4[&](v[*](a[**]2)[=]Real 1)}
         <[''parx'', ''pary'', ''parv'', ''pardx'',  ''pardy'', ''para'']: [(v[*]dx),(v[*]dy),(dy[*](Real -g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>
          {post4[&](v[*](a[**]2)[=]Real 1);(elE 0 [[|]] (almost (post4[&](v[*](a[**]2)[=]Real 1))))}")
  apply(simp add: dOr_def)
     apply (rule q1cwle)
  subgoal for s
  proof -
    have not_a: "not_in_fform ''para'' pre4"
      by (simp add:pre4_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    have eq: "pre4 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> pre4 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "pre4 s"
      then have "s ''parv'' > 0"
        unfolding pre4_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
   subgoal for s
   proof -
     have not_a: "not_in_fform ''para'' post4"
       by(simp add:post4_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
     have eq: "post4 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> post4 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "post4 s"
      then have "s ''parv'' > 0"
        unfolding post4_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
  subgoal for h n d
    apply(simp add:dOr_def almost_def fAnd_def a_def v_def)
    apply (case_tac "n=d")
    apply auto
    apply (case_tac "n>d")
     apply auto
    apply (case_tac "n<d")
     apply auto
    apply (rule exI[where x="\<lambda>t y. 1/sqrt(evalE v (h t))"])
    apply auto
      apply (subgoal_tac "not_in_fform ''para'' post4")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post4_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
     apply(subgoal_tac"(h t ''parv'') > 0")
      apply(simp add:fEqual_def v_def)
    apply (simp add: power_divide)
     apply(simp add:post4_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    apply auto
    apply (subgoal_tac "not_in_fform ''para'' post4")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post4_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    done
  done

definition pre5 :: fform where
"pre5 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (v0^2)[+]Real (2*g*yG))
      [&]((Real dy0[\<ge>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)
         [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<le>] Real cx[&] y[\<ge>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<ge>]Real 0)
      [&](dx[*]Real r[=](y[-]Real cy))
      [&](dy[*]Real r[=](Real cx[-]x))
      [&](Real x1[>]Real x0)
      [&](Real y1[>]Real y0)
      [&](Real cy[\<le>]Real y0)
      [&](Real x1[\<le>]Real cx)
      [&](Real r[>]Real 0)
      [&]((x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](v[**]2)[div]Real 2[>]Real g[*](Real y1[-]y))
      [&](x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)"
     
definition post5 :: fform where
"post5 == (dx[*]Real r[=](y[-]Real cy))
       [&](dy[*]Real r[=](Real cx[-]x))
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
       [&](x[\<le>]Real cx)
       [&](Real cy[\<le>]y)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"

definition cons51 :: fform where
"cons51 == pre5[&](v[*](a[**]2)[=]Real 1) [\<longrightarrow>] Inv"
definition cons52 :: fform where
"cons52 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](post5[&](v[*](a[**]2)[=]Real 1))"
definition cons53 :: fform where
"cons53 == (exeFlow(<[''parx'',''pary'',''parv'',''pardx'',''pardy'',''para'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>) (Inv)  [\<longrightarrow>]  Inv )"

lemma allcons5:"\<forall>s. (cons51[&]cons52[&]cons53 ) s"
  apply (simp add: cons51_def cons52_def cons53_def pre5_def post5_def x_def y_def v_def dx_def dy_def a_def)
  by (inv_check_oracle "parv*(para^2)-1=0 & 
                        parv>0 & 
                        pardx*r-pary+cy=0 &
                        pardy*r-cx+parx=0 &
                        parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 &
                        (parx-cx)^2+(pary-cy)^2-r^2 = 0 &
                        x1-cx<=0 &
                        cy-y0<=0" "x1" "y0" )

lemma q2le:"{pre5[&](v[*](a[**]2)[=]Real 1)}
           <[''parx'',''pary'',''parv'',''pardx'',''pardy'',''para'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
            {post5[&](v[*](a[**]2)[=]Real 1);(elE 0  [[|]] (almost (post5[&](v[*](a[**]2)[=]Real 1))))}"
apply (rule ContinuousRuleGT )
  apply auto
       apply(simp add:pre5_def fAnd_def)
      apply (cut_tac allcons5)
      apply (simp add:cons51_def fAnd_def fImp_def)
     apply (subgoal_tac "\<forall>s. cons52 s")
      apply (simp add:cons52_def fImp_def )
      apply (simp add:fAnd_def)
     apply (cut_tac allcons5)
     apply (simp add:fAnd_def )
apply (cut_tac allcons5)
    apply (simp add:cons53_def fAnd_def fImp_def)
   apply (simp add:dOr_def)
apply (subgoal_tac "\<forall>s. cons52 s")
   apply (simp add:cons52_def fImp_def )
   apply (simp add:dOr_def almost_def)
 apply (cut_tac allcons5)
  apply (simp add:fAnd_def )
  done



lemma q2:"{pre5}
         <[''parx'', ''pary'', ''parv'', ''pardx'', ''pardy'']: [(v[*]dx),(v[*]dy),(dy[*]Real -g),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
          {post5;(elE 0 [[|]] (almost post5))}"
 apply (rule GhostRule[where w="''para''"
                          and F="(((a[*]dy[*]Real g)[div](Real 2))[div]v)"
                          and pre="pre5[&](v[*](a[**]2)[=]Real 1)"
                          and post="post5[&](v[*](a[**]2)[=]Real 1)"
                          and HF="(elE 0)[[|]]almost (post5[&](v[*](a[**]2)[=]Real 1))"])
         apply auto
  apply(simp add:pre5_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
   apply(simp add:post5_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def) 
  apply(simp add:dOr_def post5_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_dform_def x_def y_def v_def dx_def dy_def almost_def)
  apply(subgoal_tac "{pre5[&](v[*](a[**]2)[=]Real 1)}
           <[''parx'',''pary'',''parv'',''pardx'',''pardy'',''para'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
            {post5[&](v[*](a[**]2)[=]Real 1);(elE 0  [[|]] (almost (post5[&](v[*](a[**]2)[=]Real 1))))}")
  apply(simp add: dOr_def)
     apply (rule q2le)
  subgoal for s
  proof -
    have not_a: "not_in_fform ''para'' pre5"
      by (simp add:pre5_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    have eq: "pre5 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> pre5 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "pre5 s"
      then have "s ''parv'' > 0"
        unfolding pre5_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
   subgoal for s
   proof -
     have not_a: "not_in_fform ''para'' post5"
       by(simp add:post5_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
     have eq: "post5 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> post5 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "post5 s"
      then have "s ''parv'' > 0"
        unfolding post5_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
  subgoal for h n d
    apply(simp add:dOr_def almost_def fAnd_def a_def v_def)
    apply (case_tac "n=d")
    apply auto
    apply (case_tac "n>d")
     apply auto
    apply (case_tac "n<d")
     apply auto
    apply (rule exI[where x="\<lambda>t y. 1/sqrt(evalE v (h t))"])
    apply auto
      apply (subgoal_tac "not_in_fform ''para'' post5")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post5_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
     apply(subgoal_tac"(h t ''parv'') > 0")
      apply(simp add:fEqual_def v_def)
    apply (simp add: power_divide)
     apply(simp add:post5_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    apply auto
    apply (subgoal_tac "not_in_fform ''para'' post5")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post5_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    done
  done

definition pre6 :: fform where
"pre6 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (v0^2)[+]Real (2*g*yG))
      [&]((Real dy0[\<le>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)
         [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<le>] Real cx[&] y[\<ge>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<le>]Real 0)
      [&](dx[*]Real r[=](Real cy[-]y))
      [&](dy[*]Real r[=](x[-]Real cx))
      [&](Real x1[>]Real x0)
      [&](Real y1[<]Real y0)
      [&](Real cy[\<le>]Real y1)
      [&](Real x1[\<le>]Real cx)
      [&](Real r[>]Real 0)
      [&](x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)"
     
definition post6 :: fform where
"post6 == (dx[*]Real r[=](Real cy[-]y))
       [&](dy[*]Real r[=](x[-]Real cx))
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
       [&](x[\<le>]Real cx)
       [&](Real cy[\<le>]y)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"

definition cons61 :: fform where
"cons61 == pre6 [\<longrightarrow>] Inv"
definition cons62 :: fform where
"cons62 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)[\<longrightarrow>](post6)"
definition cons63 :: fform where
"cons63 == (exeFlow(<[''parx'',''pary'',''parv'',''pardx'',''pardy'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>) (Inv)  [\<longrightarrow>]  Inv )"

lemma allcons6:"\<forall>s. (cons61[&]cons62[&]cons63 ) s"
  apply (simp add: cons61_def cons62_def cons63_def pre6_def post6_def x_def y_def v_def dx_def dy_def a_def)
  by (inv_check_oracle "pardx*r-cy+pary=0 &
                        pardy*r-parx+cx=0 &
                        parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 &
                       (parx-cx)^2+(pary-cy)^2-r^2 = 0 &
                        cx-x1>=0 &
                        y1-cy>=0 &
                        r>0 &
                        g>0 &
                        parv>0 " "x1" "y1")

lemma q2cw:"{pre6}
           <[''parx'',''pary'',''parv'',''pardx'',''pardy'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>
            {post6;(elE 0 [[|]] (almost post6))}"
apply (rule ContinuousRuleGT )
  apply auto
       apply(simp add:pre6_def fAnd_def)
      apply (cut_tac allcons6)
      apply (simp add:cons61_def fAnd_def fImp_def)
     apply (subgoal_tac "\<forall>s. cons62 s")
      apply (simp add:cons62_def fImp_def )
      apply (simp add:fAnd_def)
     apply (cut_tac allcons6)
     apply (simp add:fAnd_def )
apply (cut_tac allcons6)
    apply (simp add:cons63_def fAnd_def fImp_def)
   apply (simp add:dOr_def)
apply (subgoal_tac "\<forall>s. cons62 s")
   apply (simp add:cons62_def fImp_def )
   apply (simp add:dOr_def almost_def)
 apply (cut_tac allcons6)
  apply (simp add:fAnd_def )
  done

definition pre7 :: fform where
"pre7 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (v0^2)[+]Real (2*g*yG))
      [&]((Real dy0[\<le>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)
         [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<le>] Real cx[&] y[\<le>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<le>]Real 0)
      [&](dx[*]Real r[=](Real cy[-]y))
      [&](dy[*]Real r[=](x[-]Real cx))
      [&](Real x1[>]Real x0)
      [&](Real y1[<]Real y0)
      [&](Real cy[\<ge>]Real y0)
      [&](Real x1[\<le>]Real cx)
      [&](Real r[>]Real 0)
      [&](x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)"
     
definition post7 :: fform where
"post7 == (dx[*]Real r[=](Real cy[-]y))
       [&](dy[*]Real r[=](x[-]Real cx))
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
       [&](x[\<le>]Real cx)
       [&](Real cy[\<ge>]y)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"

definition cons71 :: fform where
"cons71 == pre7 [\<longrightarrow>] Inv"
definition cons72 :: fform where
"cons72 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)[\<longrightarrow>](post7)"
definition cons73 :: fform where
"cons73 == (exeFlow(<[''parx'',''pary'',''parv'',''pardx'',''pardy'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>) (Inv)  [\<longrightarrow>]  Inv )"

lemma allcons7:"\<forall>s. (cons71[&]cons72[&]cons73 ) s"
  apply (simp add: cons71_def cons72_def cons73_def pre7_def post7_def x_def y_def v_def dx_def dy_def a_def)
  by (inv_check_oracle "pardx*r-cy+pary=0 &
                        pardy*r-parx+cx=0 &
                        parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 &
                       (parx-cx)^2+(pary-cy)^2-r^2 = 0 &
                        cx-x1>=0 &
                        cy-y0>=0 &
                        r>0 &
                        g>0 &
                        parv>0 " "x1" "y0")

lemma q3:"{pre7}
           <[''parx'',''pary'',''parv'',''pardx'',''pardy'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>
            {post7;(elE 0 [[|]] (almost post7))}"
apply (rule ContinuousRuleGT )
  apply auto
       apply(simp add:pre7_def fAnd_def)
      apply (cut_tac allcons7)
      apply (simp add:cons71_def fAnd_def fImp_def)
     apply (subgoal_tac "\<forall>s. cons72 s")
      apply (simp add:cons72_def fImp_def )
      apply (simp add:fAnd_def)
     apply (cut_tac allcons7)
     apply (simp add:fAnd_def )
apply (cut_tac allcons7)
    apply (simp add:cons73_def fAnd_def fImp_def)
   apply (simp add:dOr_def)
apply (subgoal_tac "\<forall>s. cons72 s")
   apply (simp add:cons72_def fImp_def )
   apply (simp add:dOr_def almost_def)
 apply (cut_tac allcons7)
  apply (simp add:fAnd_def )
  done




definition pre8 :: fform where
"pre8 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (v0^2)[+]Real (2*g*yG))
      [&]((Real dy0[\<ge>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)
         [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<le>] Real cx[&] y[\<le>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<ge>]Real 0)
      [&](dx[*]Real r[=](y[-]Real cy))
      [&](dy[*]Real r[=](Real cx[-]x))
      [&](Real x1[>]Real x0)
      [&](Real y1[>]Real y0)
      [&](Real cy[\<ge>]Real y1)
      [&](Real x1[\<le>]Real cx)
      [&](Real r[>]Real 0)
      [&]((x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](v[**]2)[div]Real 2[>]Real g[*](Real y1[-]y))
      [&](x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)"
     
definition post8 :: fform where
"post8 == (dx[*]Real r[=](y[-]Real cy))
       [&](dy[*]Real r[=](Real cx[-]x))
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
       [&](x[\<le>]Real cx)
       [&](Real cy[\<ge>]y)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"

definition cons81 :: fform where
"cons81 == pre8[&](v[*](a[**]2)[=]Real 1) [\<longrightarrow>] Inv"
definition cons82 :: fform where
"cons82 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](post8[&](v[*](a[**]2)[=]Real 1))"
definition cons83 :: fform where
"cons83 == (exeFlow(<[''parx'',''pary'',''parv'',''pardx'',''pardy'',''para'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>) (Inv)  [\<longrightarrow>]  Inv )"

lemma allcons8:"\<forall>s. (cons81[&]cons82[&]cons83 ) s"
  apply (simp add: cons81_def cons82_def cons83_def pre8_def post8_def x_def y_def v_def dx_def dy_def a_def)
  by (inv_check_oracle "parv*(para^2)-1=0 & 
                        parv>0 & 
                        pardx*r-pary+cy=0 &
                        pardy*r-cx+parx=0 &
                        parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 &
                        (parx-cx)^2+(pary-cy)^2-r^2 = 0 &
                        x1-cx<=0 &
                        cy-y1>=0" "x1" "y1" )

lemma q3cwle:"{pre8[&](v[*](a[**]2)[=]Real 1)}
           <[''parx'',''pary'',''parv'',''pardx'',''pardy'',''para'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
            {post8[&](v[*](a[**]2)[=]Real 1);(elE 0  [[|]] (almost (post8[&](v[*](a[**]2)[=]Real 1))))}"
apply (rule ContinuousRuleGT )
  apply auto
       apply(simp add:pre8_def fAnd_def)
      apply (cut_tac allcons8)
      apply (simp add:cons81_def fAnd_def fImp_def)
     apply (subgoal_tac "\<forall>s. cons82 s")
      apply (simp add:cons82_def fImp_def )
      apply (simp add:fAnd_def)
     apply (cut_tac allcons8)
     apply (simp add:fAnd_def )
apply (cut_tac allcons8)
    apply (simp add:cons83_def fAnd_def fImp_def)
   apply (simp add:dOr_def)
apply (subgoal_tac "\<forall>s. cons82 s")
   apply (simp add:cons82_def fImp_def )
   apply (simp add:dOr_def almost_def)
 apply (cut_tac allcons8)
  apply (simp add:fAnd_def )
  done



lemma q3cw:"{pre8}
         <[''parx'', ''pary'', ''parv'', ''pardx'', ''pardy'']: [(v[*]dx),(v[*]dy),(dy[*]Real -g),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
          {post8;(elE 0 [[|]] (almost post8))}"
 apply (rule GhostRule[where w="''para''"
                          and F="(((a[*]dy[*]Real g)[div](Real 2))[div]v)"
                          and pre="pre8[&](v[*](a[**]2)[=]Real 1)"
                          and post="post8[&](v[*](a[**]2)[=]Real 1)"
                          and HF="(elE 0)[[|]]almost (post8[&](v[*](a[**]2)[=]Real 1))"])
         apply auto
  apply(simp add:pre8_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
   apply(simp add:post8_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def) 
  apply(simp add:dOr_def post8_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_dform_def x_def y_def v_def dx_def dy_def almost_def)
  apply(subgoal_tac "{pre8[&](v[*](a[**]2)[=]Real 1)}
           <[''parx'',''pary'',''parv'',''pardx'',''pardy'',''para'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
            {post8[&](v[*](a[**]2)[=]Real 1);(elE 0  [[|]] (almost (post8[&](v[*](a[**]2)[=]Real 1))))}")
  apply(simp add: dOr_def)
     apply (rule q3cwle)
  subgoal for s
  proof -
    have not_a: "not_in_fform ''para'' pre8"
      by (simp add:pre8_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    have eq: "pre8 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> pre8 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "pre8 s"
      then have "s ''parv'' > 0"
        unfolding pre8_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
   subgoal for s
   proof -
     have not_a: "not_in_fform ''para'' post8"
       by(simp add:post8_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
     have eq: "post8 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> post8 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "post8 s"
      then have "s ''parv'' > 0"
        unfolding post8_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
  subgoal for h n d
    apply(simp add:dOr_def almost_def fAnd_def a_def v_def)
    apply (case_tac "n=d")
    apply auto
    apply (case_tac "n>d")
     apply auto
    apply (case_tac "n<d")
     apply auto
    apply (rule exI[where x="\<lambda>t y. 1/sqrt(evalE v (h t))"])
    apply auto
      apply (subgoal_tac "not_in_fform ''para'' post8")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post8_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
     apply(subgoal_tac"(h t ''parv'') > 0")
      apply(simp add:fEqual_def v_def)
    apply (simp add: power_divide)
     apply(simp add:post8_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    apply auto
    apply (subgoal_tac "not_in_fform ''para'' post8")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post8_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    done
  done


definition pre9 :: fform where
"pre9 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (v0^2)[+]Real (2*g*yG))
      [&]((Real dy0[\<ge>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)
         [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<ge>] Real cx[&] y[\<le>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<ge>]Real 0)
      [&](dx[*]Real r[=](Real cy[-]y))
      [&](dy[*]Real r[=](x[-]Real cx))
      [&](Real x1[>]Real x0)
      [&](Real y1[>]Real y0)
      [&](Real cy[\<ge>]Real y1)
      [&](Real x0[\<ge>]Real cx)
      [&](Real r[>]Real 0)
      [&]((x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](v[**]2)[div]Real 2[>]Real g[*](Real y1[-]y))
      [&](x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)"
     
definition post9 :: fform where
"post9 == (dx[*]Real r[=](Real cy[-]y))
       [&](dy[*]Real r[=](x[-]Real cx))
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
       [&](x[\<ge>]Real cx)
       [&](Real cy[\<ge>]y)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"

definition cons91 :: fform where
"cons91 == pre9[&](v[*](a[**]2)[=]Real 1) [\<longrightarrow>] Inv"
definition cons92 :: fform where
"cons92 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](post9[&](v[*](a[**]2)[=]Real 1))"
definition cons93 :: fform where
"cons93 == (exeFlow(<[''parx'',''pary'',''parv'',''pardx'',''pardy'',''para'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>) (Inv)  [\<longrightarrow>]  Inv )"

lemma allcons9:"\<forall>s. (cons91[&]cons92[&]cons93 ) s"
  apply (simp add: cons91_def cons92_def cons93_def pre9_def post9_def x_def y_def v_def dx_def dy_def a_def)
  by (inv_check_oracle "parv*(para^2)-1=0 & 
                        parv>0 & 
                        pardx*r+pary-cy=0 &
                        pardy*r+cx-parx=0 &
                        parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 &
                        (parx-cx)^2+(pary-cy)^2-r^2 = 0 &
                        x0-cx>=0 &
                        cy-y1>=0" "x0" "y1" )

lemma q4le:"{pre9[&](v[*](a[**]2)[=]Real 1)}
           <[''parx'',''pary'',''parv'',''pardx'',''pardy'',''para'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
            {post9[&](v[*](a[**]2)[=]Real 1);(elE 0  [[|]] (almost (post9[&](v[*](a[**]2)[=]Real 1))))}"
apply (rule ContinuousRuleGT )
  apply auto
       apply(simp add:pre9_def fAnd_def)
      apply (cut_tac allcons9)
      apply (simp add:cons91_def fAnd_def fImp_def)
     apply (subgoal_tac "\<forall>s. cons92 s")
      apply (simp add:cons92_def fImp_def )
      apply (simp add:fAnd_def)
     apply (cut_tac allcons9)
     apply (simp add:fAnd_def )
apply (cut_tac allcons9)
    apply (simp add:cons93_def fAnd_def fImp_def)
   apply (simp add:dOr_def)
apply (subgoal_tac "\<forall>s. cons92 s")
   apply (simp add:cons92_def fImp_def )
   apply (simp add:dOr_def almost_def)
 apply (cut_tac allcons9)
  apply (simp add:fAnd_def )
  done



lemma q4:"{pre9}
         <[''parx'', ''pary'', ''parv'', ''pardx'', ''pardy'']: [(v[*]dx),(v[*]dy),(dy[*]Real -g),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
          {post9;(elE 0 [[|]] (almost post9))}"
 apply (rule GhostRule[where w="''para''"
                          and F="(((a[*]dy[*]Real g)[div](Real 2))[div]v)"
                          and pre="pre9[&](v[*](a[**]2)[=]Real 1)"
                          and post="post9[&](v[*](a[**]2)[=]Real 1)"
                          and HF="(elE 0)[[|]]almost (post9[&](v[*](a[**]2)[=]Real 1))"])
         apply auto
  apply(simp add:pre9_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
   apply(simp add:post9_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def) 
  apply(simp add:dOr_def post9_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_dform_def x_def y_def v_def dx_def dy_def almost_def)
  apply(subgoal_tac "{pre9[&](v[*](a[**]2)[=]Real 1)}
           <[''parx'',''pary'',''parv'',''pardx'',''pardy'',''para'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r),(((a[*]dy[*]Real g)[div](Real 2))[div]v)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
            {post9[&](v[*](a[**]2)[=]Real 1);(elE 0  [[|]] (almost (post9[&](v[*](a[**]2)[=]Real 1))))}")
  apply(simp add: dOr_def)
     apply (rule q4le)
  subgoal for s
  proof -
    have not_a: "not_in_fform ''para'' pre9"
      by (simp add:pre9_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    have eq: "pre9 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> pre9 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "pre9 s"
      then have "s ''parv'' > 0"
        unfolding pre9_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
   subgoal for s
   proof -
     have not_a: "not_in_fform ''para'' post9"
       by(simp add:post9_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
     have eq: "post9 (\<lambda>y. if y \<noteq> ''para'' then s y else 1 / sqrt (evalE v s)) \<longleftrightarrow> post9 s"
      by (simp add: not_in_fform_update[OF not_a])
    show ?thesis
      apply (rule exI[where x="1/sqrt(evalE v s)"])
      apply (auto simp add: eq fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def  x_def y_def v_def a_def)
    proof -
      assume "post9 s"
      then have "s ''parv'' > 0"
        unfolding post9_def fAnd_def fGreater_def fLessEqual_def fOr_def fEqual_def fLess_def fNot_def
        v_def evalE.simps by auto
      then show "s ''parv'' * (1 / sqrt (s ''parv''))\<^sup>2 = 1"
        by (smt divide_cancel_right nonzero_mult_div_cancel_left one_power2 power_divide
                real_sqrt_pow2)
    qed
  qed
  subgoal for h n d
    apply(simp add:dOr_def almost_def fAnd_def a_def v_def)
    apply (case_tac "n=d")
    apply auto
    apply (case_tac "n>d")
     apply auto
    apply (case_tac "n<d")
     apply auto
    apply (rule exI[where x="\<lambda>t y. 1/sqrt(evalE v (h t))"])
    apply auto
      apply (subgoal_tac "not_in_fform ''para'' post9")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post9_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
     apply(subgoal_tac"(h t ''parv'') > 0")
      apply(simp add:fEqual_def v_def)
    apply (simp add: power_divide)
     apply(simp add:post9_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    apply auto
    apply (subgoal_tac "not_in_fform ''para'' post9")
       apply(simp add:not_in_fform_def)
       apply smt
    apply(simp add:post9_def fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fImp_def fEqual_def fLess_def fGreater_def fNot_def not_in_fform_def x_def y_def v_def dx_def dy_def)
    done
  done
definition pre10 :: fform where
"pre10 == (Real g[>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (v0^2)[+]Real (2*g*yG))
      [&]((Real dy0[\<le>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)
         [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<ge>] Real cx[&] y[\<le>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<le>]Real 0)
      [&](dx[*]Real r[=](y[-]Real cy))
      [&](dy[*]Real r[=](Real cx[-]x))
      [&](Real x1[>]Real x0)
      [&](Real y1[>]Real y0)
      [&](Real cy[\<ge>]Real y1)
      [&](Real x0[\<ge>]Real cx)
      [&](Real r[>]Real 0)
      [&](x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)"
     
definition post10 :: fform where
"post10 == (dx[*]Real r[=](y[-]Real cy))
       [&](dy[*]Real r[=](Real cx[-]x))
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real(v0^2)[+]Real (2*g*yG))
       [&](x[\<ge>]Real cx)
       [&](Real cy[\<ge>]y)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"

definition cons101 :: fform where
"cons101 == pre10 [\<longrightarrow>] Inv"
definition cons102 :: fform where
"cons102 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](post10)"
definition cons103 :: fform where
"cons103 == (exeFlow(<[''parx'',''pary'',''parv'',''pardx'',''pardy'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>) (Inv)  [\<longrightarrow>]  Inv )"

lemma allcons10:"\<forall>s. (cons101[&]cons102[&]cons103 ) s"
  apply (simp add: cons101_def cons102_def cons103_def pre10_def post10_def x_def y_def v_def dx_def dy_def a_def)
  by (inv_check_oracle "pardx*r+cy-pary=0 &
                        pardy*r+parx-cx=0 &
                        parv^2 + 2*g*pary -v0^2- 2*g*yG = 0 &
                       (parx-cx)^2+(pary-cy)^2-r^2 = 0 &
                        cx-x0<=0 &
                        cy-y1>=0 &
                        r>0 &
                        g>0 &
                        parv>0 " "x0" "y1")

lemma q4cw:"{pre10}
           <[''parx'',''pary'',''parv'',''pardx'',''pardy'']:[(v[*]dx),(v[*]dy),(dy[*]Real(-g)),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r)]&& Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
            {post10;(elE 0 [[|]] (almost post10))}"
apply (rule ContinuousRuleGT )
  apply auto
       apply(simp add:pre10_def fAnd_def)
      apply (cut_tac allcons10)
      apply (simp add:cons101_def fAnd_def fImp_def)
     apply (subgoal_tac "\<forall>s. cons102 s")
      apply (simp add:cons102_def fImp_def )
      apply (simp add:fAnd_def)
     apply (cut_tac allcons10)
     apply (simp add:fAnd_def )
apply (cut_tac allcons10)
    apply (simp add:cons103_def fAnd_def fImp_def)
   apply (simp add:dOr_def)
apply (subgoal_tac "\<forall>s. cons102 s")
   apply (simp add:cons102_def fImp_def )
   apply (simp add:dOr_def almost_def)
 apply (cut_tac allcons10)
  apply (simp add:fAnd_def )
  done



end