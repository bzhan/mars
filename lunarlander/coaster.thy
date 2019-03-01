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
"y == RVar ''y''"

definition x :: exp where
"x == RVar ''x''"

definition dy :: exp where
"dy == RVar ''dy''"

definition dx :: exp where
"dx == RVar ''dx''"

definition v :: exp where
"v == RVar ''v''"

consts Inv :: fform

definition pre1 :: fform where
"pre1 == (Con Real g[\<ge>] Con Real 0)
      [&](v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&] (x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)
      [&]((Con Real dy0[\<le>]Con Real 0 [&] x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0) 
        [\<longrightarrow>](v[**]2[\<ge>]Con Real vLo [&] v[**]2[\<le>]Con Real vHi [&] Con Real (dyLo*g)[\<le>] Con Real (-dy0*g)[&]Con Real (-dy0*g)[\<le>]Con Real (dyHi*g)[&] Con Real dx0[*]y [=] Con Real dy0[*]x [+] Con Real (dx0*c)))
      [&](Con Real dy0[\<le>]Con Real 0)
      [&]((x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)[\<longrightarrow>](Con Real dx0[*]v[**]2[>]Con Real (2*dy0*g)[*](Con Real x1[-]x)))
      [&](Con Real x1[>]Con Real x0)
      [&](Con Real (dx0^2+dy0^2)[=]Con Real 1)
      [&](Con Real dx0[>]Con Real 0)"

definition post1 :: fform where
"post1 == (v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&](x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0)
      [&](Con Real dx0[*]y [=] Con Real dy0[*]x [+] Con Real (dx0*c))"

definition Inv1 :: fform where
"Inv1 == (v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&]Con Real dx0[*]y [=] Con Real dy0[*]x [+] Con Real (dx0*c)"

definition cons11 :: fform where
"cons11 ==  (exeFlow(<[(''x'', R),(''y'',R),(''v'',R)]: [(v[*]Con Real dx0),(v[*]Con Real dy0),(Con Real (-dy0*g))] && Inv1 & (x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)>) (Inv)  [\<longrightarrow>]  Inv )"

definition cons12 :: fform where
"cons12 == pre1 [\<longrightarrow>] Inv"

lemma allcons1: "\<forall>s. (cons12 [&] cons11 ) s"
  apply (simp only: cons11_def cons12_def  x_def y_def v_def pre1_def )
  by (inv_check_oracle "v > 0")

lemma linedown:"{pre1}
             <[(''x'', R),(''y'',R),(''v'',R)]: [(v[*]Con Real dx0),(v[*]Con Real dy0),(Con Real (-dy0*g))] && Inv1 & (x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)>
              {post1;(elE 0 [[|]] (almost post1))}"
    apply (rule ContinuousRuleGT )
   apply (simp add:fAnd_def )
  apply (simp add:pre1_def post1_def fAnd_def fImp_def)
definition pre2 :: fform where
"pre2 == (Con Real g[\<ge>] Con Real 0)
      [&](v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&]((dy[\<ge>]Con Real 0 [&] x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0) 
        [\<longrightarrow>](v[**]2[\<ge>]Con Real vLo [&] v[**]2[\<le>]Con Real vHi [&] Con Real (dyLo*g)[\<le>] Con Real (-dy0*g)[&]Con Real (-dy0*g)[\<le>]Con Real (dyHi*g)[&] Con Real dx0[*]y [=] Con Real dy0[*]x [+] Con Real (dx0*c)))
      [&](dy[\<ge>]Con Real 0)
      [&]((x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)[\<longrightarrow>](Con Real dx0[*]v[**]2[>]Con Real (2*dy0*g)[*](Con Real x1[-]x)))
      [&](Con Real x1[>]Con Real x0)
      [&](Con Real (dx0^2+dy0^2)[=]Con Real 1)
      [&](Con Real dx0[>]Con Real 0)     "

definition post2 :: fform where
"post2 == (v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&]x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0
      [&]Con Real dx0[*]y [=] Con Real dy0[*]x [+] Con Real (dx0*c)"

definition Inv2 :: fform where
"Inv2 == Inv"

lemma lineup:"{pre2}
             <[(''x'', R),(''y'',R),(''v'',R)]: [(v[*]Con Real dx0),(v[*]Con Real dy0),(Con Real (-dy0*g))] && Inv & (x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)>
              {post2;(elE 0 [[|]] (almost post2))}"
  sorry



definition pre3 :: fform where
"pre3 == (Con Real g[\<ge>] Con Real 0)
      [&](v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&]((Con Real dy0[\<le>]Con Real 0 [&] x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y0 [&] y[\<ge>] Con Real y1)
       [\<longrightarrow>](((x[-]Con Real cx)[**]2[+](y[-]Con Real cy)[**]2) [=] Con Real r [**]2 [&] x[\<ge>] Con Real cx[&] y[\<ge>] Con Real cy[&]v[**]2[\<ge>]Con Real vLo [&] v[**]2[\<le>]Con Real vHi [&] Con Real centLo[\<le>] Con Real cent[&]Con Real cent [\<le>]Con Real centHi [&] Con Real tanLo[\<le>]Con Real tan[&] Con Real tan[\<le>] Con Real tanHi))
      [&](Con Real dy0[\<le>]Con Real 0)
      [&](dx[=](y[-]Con Real cy)[div]Con Real r)
      [&](dy[=](Con Real cx[-]x)[div]Con Real r)
      [&](Con Real x1[>]Con Real x0)
      [&](Con Real y1[<]Con Real y0)
      [&](Con Real cy[\<le>]Con Real y1)
      [&](Con Real cx[\<le>]Con Real x0)
      [&](Con Real r[>]Con Real 0) "

definition post3 :: fform where
"post3 == (dx[=] (y[-]Con Real cy)[div]Con Real r)
       [&](dy[=] (Con Real cx[-]x)[div]Con Real r)
       [&](v[>]Con Real 0)
       [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
       [&](y[>]Con Real cy)
       [&](((x[-]Con Real cx)[**]2[+](y[-]Con Real cy)[**]2) [=] Con Real r [**]2)"

definition Inv3 :: fform where
"Inv3 == Inv"


lemma q1:"{pre3}
         <[(''x'', R),(''y'',R),(''v'',R),(''dx'',R),(''dy'',R)]: [(v[*]dx),(v[*]dy),(dy[*]Con Real -g),((dy[*]v)[div]Con Real r),((Con Real 0[-]dx[*]v)[div]Con Real r)] && Inv & (x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y0 [&] y[\<ge>] Con Real y1)>
          {post3;(elE 0 [[|]] (almost post3))}"
  sorry

definition pre4 :: fform where
"pre4 == (Con Real g[\<ge>] Con Real 0)
      [&](v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&]((Con Real dy0[\<ge>]Con Real 0 [&] x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y0 [&] y[\<ge>] Con Real y1)
         [\<longrightarrow>](((x[-]Con Real cx)[**]2[+](y[-]Con Real cy)[**]2) [=] Con Real r [**]2 [&] x[\<ge>] Con Real cx[&] y[\<ge>] Con Real cy[&]v[**]2[\<ge>]Con Real vLo [&] v[**]2[\<le>]Con Real vHi [&] Con Real centLo[\<le>] Con Real cent[&]Con Real cent [\<le>]Con Real centHi [&] Con Real tanLo[\<le>]Con Real tan[&] Con Real tan[\<le>] Con Real tanHi))
      [&](Con Real dy0[\<ge>]Con Real 0)
      [&](dx[=](Con Real cy[-]y)[div]Con Real r)
      [&](dy[=](x[-]Con Real cx)[div]Con Real r)
      [&](Con Real x1[>]Con Real x0)
      [&](Con Real y1[<]Con Real y0)
      [&](Con Real r[>]Con Real 0)
      [&](Con Real cy[\<le>]Con Real y1)
      [&](Con Real cx[\<le>]Con Real x0)
      [&]((x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y0 [&] y[\<ge>] Con Real y1)[\<longrightarrow>](v[**]2)[div]Con Real 2[>]Con Real g[*](Con Real y0[-]y))"
      
definition post4 :: fform where
"post4 == (dx[=](Con Real cy[-]y)[div]Con Real r)
       [&](dy[=](x[-]Con Real cx)[div]Con Real r)
       [&](v[>]Con Real 0)
       [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
       [&](y[>]Con Real cy)
       [&](((x[-]Con Real cx)[**]2[+](y[-]Con Real cy)[**]2) [=] Con Real r [**]2)"

definition Inv4 :: fform where
"Inv4 == Inv"


lemma q1cw:"{pre4}
         <[(''x'', R),(''y'',R),(''v'',R),(''dx'',R),(''dy'',R)]: [(v[*]dx),(v[*]dy),(dy[*]Con Real -g),((Con Real 0[-]dy[*]v)[div]Con Real r),((dx[*]v)[div]Con Real r)] && Inv & (x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y0 [&] y[\<ge>] Con Real y1)>
          {post4;(elE 0 [[|]] (almost post4))}"
  sorry


definition pre5 :: fform where
"pre5 == (Con Real g[\<ge>] Con Real 0)
      [&](v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&]((Con Real dy0[\<ge>]Con Real 0 [&] x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)
         [\<longrightarrow>](((x[-]Con Real cx)[**]2[+](y[-]Con Real cy)[**]2) [=] Con Real r [**]2 [&] x[\<le>] Con Real cx[&] y[\<ge>] Con Real cy[&]v[**]2[\<ge>]Con Real vLo [&] v[**]2[\<le>]Con Real vHi [&] Con Real centLo[\<le>] Con Real cent[&]Con Real cent [\<le>]Con Real centHi [&] Con Real tanLo[\<le>]Con Real tan[&] Con Real tan[\<le>] Con Real tanHi))
      [&](Con Real dy0[\<ge>]Con Real 0)
      [&](dx[=](y[-]Con Real cy)[div]Con Real r)
      [&](dy[=](Con Real cx[-]x)[div]Con Real r)
      [&](Con Real x1[>]Con Real x0)
      [&](Con Real y1[>]Con Real y0)
      [&](Con Real cy[\<le>]Con Real y0)
      [&](Con Real x1[\<le>]Con Real cx)
      [&](Con Real r[>]Con Real 0)
      [&]((x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)[\<longrightarrow>](v[**]2)[div]Con Real 2[>]Con Real g[*](Con Real y1[-]y))"

definition post5 :: fform where
"post5 == (dx[=](y[-]Con Real cy)[div]Con Real r)
       [&](dy[=](Con Real cx[-]x)[div]Con Real r)
       [&](v[>]Con Real 0)
       [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
       [&](x[\<le>]Con Real cx)
       [&](Con Real cy[\<le>]y)
       [&](((x[-]Con Real cx)[**]2[+](y[-]Con Real cy)[**]2) [=] Con Real r [**]2)"

definition Inv5 :: fform where
"Inv5 == Inv"


lemma q2:"{pre5}
         <[(''x'', R),(''y'',R),(''v'',R),(''dx'',R),(''dy'',R)]: [(v[*]dx),(v[*]dy),(dy[*]Con Real -g),((dy[*]v)[div]Con Real r),((Con Real 0[-]dx[*]v)[div]Con Real r)] && Inv & (x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)>
          {post5;(elE 0 [[|]] (almost post5))}"
  sorry




end