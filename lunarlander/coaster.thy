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

consts centLi :: real

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
      [&](dy [\<le>] Con Real 0)
      [&]((dy[\<le>]Con Real 0 [&] x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0) 
        [\<longrightarrow>](v[**]2[\<ge>]Con Real vLo [&] v[**]2[\<le>]Con Real vHi [&] Con Real (dyLo*g)[\<le>] Con Real (-dy0*g)[&]Con Real (-dy0*g)[\<le>]Con Real (dyHi*g)[&] Con Real dx0[*]y [=] Con Real dy0[*]x [+] Con Real (dx0*c)))
      [&](dy[\<le>]Con Real 0)
      [&]((x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0 [&] y[\<le>] Con Real y1 [&] y[\<ge>] Con Real y0)[\<longrightarrow>](Con Real dx0[*]v[**]2[>]Con Real (2*dy0*g)[*](Con Real x1[-]x)))
      [&](Con Real x1[>]Con Real x0)
      [&](Con Real (dx0^2+dy0^2)[=]Con Real 1)
      [&](Con Real dx0[>]Con Real 0)     "

definition post1 :: fform where
"post1 == (v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&]x[\<le>]Con Real x1 [&] x[\<ge>]Con Real x0
      [&]Con Real dx0[*]y [=] Con Real dy0[*]x [+] Con Real (dx0*c)"

definition Inv1 :: fform where
"Inv1 == Inv"

lemma linedown:"{pre1}
             <[(''x'', R),(''y'',R),(''v'',R)]: [(v[*]Con Real dx0),(v[*]Con Real dy0),(Con Real (-dy0*g))] && Inv & fTrue>
              {post1;(elE 0 [[|]] (almost post1))}"
  sorry


definition pre2 :: fform where
"pre2 == (Con Real g[\<ge>] Con Real 0)
      [&](v[>]Con Real 0)
      [&](v[**]2 [+] Con Real (2*g) [*] y [=]Con Real (2*g*yG))
      [&](dy [\<le>] Con Real 0)
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
             <[(''x'', R),(''y'',R),(''v'',R)]: [(v[*]Con Real dx0),(v[*]Con Real dy0),(Con Real (-dy0*g))] && Inv & fTrue>
              {post2;(elE 0 [[|]] (almost post2))}"
  sorry












end