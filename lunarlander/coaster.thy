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
"pre1 == (Real g[\<ge>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
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
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
      [&](x[\<le>]Real x1 [&] x[\<ge>]Real x0)
      [&](Real dx0[*]y [=] Real dy0[*]x [+] Real (dx0*c))"

definition Inv1 :: fform where
"Inv1 == (v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
      [&]Real dx0[*]y [=] Real dy0[*]x [+] Real (dx0*c)"



definition cons11 :: fform where
"cons11 == pre1 [\<longrightarrow>] Inv"
definition cons12 :: fform where
"cons12 == Inv[&]close(x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>]post1"
definition cons13 :: fform where
"cons13 ==  (exeFlow(<[''parx'', ''pary'', ''parv'']: [(v[*]Real dx0),(v[*]Real dy0),(Real (-dy0*g))] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>) (Inv)  [\<longrightarrow>]  Inv )"
lemma allcons1: "\<forall>s. (cons11[&]cons12 [&] cons13 ) s"
  apply (simp add: cons11_def cons12_def cons13_def  x_def y_def v_def pre1_def post1_def)
  by (inv_check_oracle "g > 0 & dy0 <= 0 & parv > 0 & parv^2 + 2*g*pary - 2*g*yG = 0 & dx0*pary - dy0*parx - dx0*c = 0 ")

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
"pre2 == (Real g[\<ge>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
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
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
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
by (inv_check_oracle "parv*para^2 - 1 = 0 & v^2 + 2*g*y - 2*g*yG = 0 & v > 0 & dx0*y - dy0*x -dx0*c = 0")
lemma lineuple:"{pre2[&](v[*](a[**]2)[=]Real 1)}
              <[''parx'', ''pary'', ''parv'', ''para'']: [(v[*]Real dx0),(v[*]Real dy0),(Real (-dy0*g)),(Real (dy0 * g/2) [*] a [div] v)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
              {post2[&](v[*](a[**]2)[=]Real 1);(elE 0)[[|]]almost (post2[&](v[*](a[**]2)[=]Real 1))}"
  sorry
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
"pre3 == (Real g[\<ge>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
      [&]((Real dy0[\<le>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)
       [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<ge>] Real cx[&] y[\<ge>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<le>]Real 0)
      [&](dx[=](y[-]Real cy)[div]Real r)
      [&](dy[=](Real cx[-]x)[div]Real r)
      [&](Real x1[>]Real x0)
      [&](Real y1[<]Real y0)
      [&](Real cy[\<le>]Real y1)
      [&](Real cx[\<le>]Real x0)
      [&](Real r[>]Real 0) "

definition post3 :: fform where
"post3 == (dx[=] (y[-]Real cy)[div]Real r)
       [&](dy[=] (Real cx[-]x)[div]Real r)
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
       [&](y[>]Real cy)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"

definition Inv3 :: fform where
"Inv3 == Inv"


lemma q1:"{pre3}
         <[''x'', ''y'', ''v'', ''dx'', ''dy'']: [(v[*]dx),(v[*]dy),(dy[*]Real -g),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>
          {post3;(elE 0 [[|]] (almost post3))}"
  sorry

definition pre4 :: fform where
"pre4 == (Real g[\<ge>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
      [&]((Real dy0[\<ge>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)
         [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<ge>] Real cx[&] y[\<ge>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<ge>]Real 0)
      [&](dx[=](Real cy[-]y)[div]Real r)
      [&](dy[=](x[-]Real cx)[div]Real r)
      [&](Real x1[>]Real x0)
      [&](Real y1[<]Real y0)
      [&](Real r[>]Real 0)
      [&](Real cy[\<le>]Real y1)
      [&](Real cx[\<le>]Real x0)
      [&]((x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)[\<longrightarrow>](v[**]2)[div]Real 2[>]Real g[*](Real y0[-]y))"
      
definition post4 :: fform where
"post4 == (dx[=](Real cy[-]y)[div]Real r)
       [&](dy[=](x[-]Real cx)[div]Real r)
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
       [&](y[>]Real cy)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"

definition Inv4 :: fform where
"Inv4 == Inv"


lemma q1cw:"{pre4}
         <[''x'', ''y'', ''v'', ''dx'', ''dy'']: [(v[*]dx),(v[*]dy),(dy[*]Real -g),((Real 0[-]dy[*]v)[div]Real r),((dx[*]v)[div]Real r)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y0 [&] y[\<ge>] Real y1)>
          {post4;(elE 0 [[|]] (almost post4))}"
  sorry


definition pre5 :: fform where
"pre5 == (Real g[\<ge>] Real 0)
      [&](v[>]Real 0)
      [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
      [&]((Real dy0[\<ge>]Real 0 [&] x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)
         [\<longrightarrow>](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2 [&] x[\<le>] Real cx[&] y[\<ge>] Real cy[&]v[**]2[\<ge>]Real vLo [&] v[**]2[\<le>]Real vHi [&] Real centLo[\<le>] Real cent[&]Real cent [\<le>]Real centHi [&] Real tanLo[\<le>]Real tan[&] Real tan[\<le>] Real tanHi))
      [&](Real dy0[\<ge>]Real 0)
      [&](dx[=](y[-]Real cy)[div]Real r)
      [&](dy[=](Real cx[-]x)[div]Real r)
      [&](Real x1[>]Real x0)
      [&](Real y1[>]Real y0)
      [&](Real cy[\<le>]Real y0)
      [&](Real x1[\<le>]Real cx)
      [&](Real r[>]Real 0)
      [&]((x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)[\<longrightarrow>](v[**]2)[div]Real 2[>]Real g[*](Real y1[-]y))"

definition post5 :: fform where
"post5 == (dx[=](y[-]Real cy)[div]Real r)
       [&](dy[=](Real cx[-]x)[div]Real r)
       [&](v[>]Real 0)
       [&](v[**]2 [+] Real (2*g) [*] y [=]Real (2*g*yG))
       [&](x[\<le>]Real cx)
       [&](Real cy[\<le>]y)
       [&](((x[-]Real cx)[**]2[+](y[-]Real cy)[**]2) [=] Real r [**]2)"

definition Inv5 :: fform where
"Inv5 == Inv"


lemma q2:"{pre5}
         <[''x'', ''y'', ''v'', ''dx'', ''dy'']: [(v[*]dx),(v[*]dy),(dy[*]Real -g),((dy[*]v)[div]Real r),((Real 0[-]dx[*]v)[div]Real r)] && Inv & (x[\<le>]Real x1 [&] x[\<ge>]Real x0 [&] y[\<le>] Real y1 [&] y[\<ge>] Real y0)>
          {post5;(elE 0 [[|]] (almost post5))}"
  sorry




end