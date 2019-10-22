section {* Isollete abstract model in HCSP*}

theory isollete_simp
  imports HHL_SL
begin 

consts q :: string
consts c :: string
consts x0 :: string
consts x0' :: string 
consts Inv :: fform
consts x1 :: string
consts x2 :: string
consts ch :: string
consts dh :: string 
consts t :: string
consts diff :: string 

definition  babybox_Init :: proc where
"babybox_Init == (((RVar q) := (Real 98.5)); ((RVar c) := (Real 98.5)); ((RVar x0) := (Real 1)))"

definition babybox_ode1 :: proc where
"babybox_ode1 == (<[q, c]: [(Real (-1)), ((RVar c [-] RVar q) [*] (Real -0.026))] && Inv & fTrue>)"


definition babybox_ode2 :: proc where
"babybox_ode2 == (<[q, c]: [(Real 1), ((RVar c [-] RVar q) [*] (Real -0.026))] && Inv & fTrue>)"

definition babybox_Intr1 :: proc where
"babybox_Intr1 == (babybox_ode1 [[ (ch!!(RVar c)) \<rightarrow> Skip)"

definition babybox_Intr2 :: proc where
"babybox_Intr2 == (babybox_ode2 [[ (ch!!(RVar c)) \<rightarrow> Skip)"

definition babybox_Intr3 :: proc where
"babybox_Intr3 == (babybox_ode1 [[ (dh??(RVar x0)) \<rightarrow> Skip)"

definition babybox_Intr4 :: proc where
"babybox_Intr4 == (babybox_ode2 [[ (dh??(RVar x0)) \<rightarrow> Skip)"

definition bf :: fform where
"bf == ((RVar x0) [\<le>] (Real 0))"

definition bf' :: fform where
"bf' == ((RVar x0) [>] (Real 0))"

definition cf :: fform where
"cf == (((RVar x1) [>] (Real 98.5)))"

definition babybox :: proc where
"babybox == (babybox_Init; IF (bf) babybox_Intr1; IF ([\<not>]bf) babybox_Intr2; (RVar x0') := (RVar x0);
            IF bf babybox_Intr3; IF (bf') babybox_Intr4)"

definition waitone :: proc where
"waitone ==  ((RVar t) := (Real 0); <[t]: [Real 1]&&fTrue& (fTrue)>)"

definition control :: proc where
"control == waitone; Cm (ch ?? (RVar x1)); 
                 ((RVar diff) := ((Real 10) [*] ((RVar x1) [-] (Real 98.5))));
                 IF ((RVar diff) [>] (Real 0)) (RVar x2) := (Real -1);
                 IF ((RVar diff) [\<le>] (Real 0)) (RVar x2) := (Real 1);
                 Cm (dh !! (RVar x2))"
  
                 
definition isollete :: procP where 
"isollete == (babybox || control)"

definition safe :: fform where 
"safe == ((RVar q [\<ge>] (Real 97)) [&] (RVar q [<] (Real 100)))"

lemma isollete_safe : "{fTrue, fTrue} isollete {safe, fTrue; almost safe, almost fTrue}"
  sorry




end 