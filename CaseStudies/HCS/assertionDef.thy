theory assertionDef
	imports "varDef"
begin

(*Define consts for processes definition.*)
consts expInv :: exp
definition Inv :: fform where
"Inv == expInv[>=](Real 0)"
definition Inv1 :: fform where
"Inv1 == Inv"
definition Inv2 :: fform where
"Inv2 == Inv"

definition assertion1 :: mid where
"assertion1 == ((plant_v1_1[=](Real -2)),l[=](Real 0))"
definition assertion2 :: mid where
"assertion2 == ((plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250)),l[=](Real 0))"
definition assertion3 :: mid where
"assertion3 == ((t[=](Real 0.128) [|] (control_1[<=](Real 3000)[&]t[=](Real 0))) [&] Inv,((l[=](Real 0) [|] (high Inv))))"
definition assertion4 :: mid where
"assertion4 == assertion2"
definition assertion5 :: mid where
"assertion5 == ((plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250) [&] control_1[=](Real 2027.5)),l[=](Real 0))"
definition assertion6 :: mid where
"assertion6 == ((plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250) [&] control_1[=](Real 2027.5) [&] t[=](Real 0)),l[=](Real 0))"
definition assertion7 :: mid where
"assertion7 == (t[=](Real 0.128) [&] Inv,((l[=](Real 0) [|] (high (t [<=] Real 16 / 125 [&] Inv)))))"
definition assertion8 :: mid where
"assertion8 == (substF
        ([(control_1,
           plant_m1_1 [*]
           (Real 811 / 500 [-]
            Real 1 / 100 [*]
            (control_1 [**] plant_m1_1 [-]
             Real 811 / 500) [-]
            Real 3 / 5 [*] (plant_v1_1 [+] Real 2)))],
         Inv [&] t[=](Real 0)),l[=](Real 0))"

definition assertion33 :: mid where
"assertion33 == (control_1 [>] Real 3000 [&] (t[=](Real 0.128)) [&] Inv,((l[=](Real 0) [|] (high (t [<=] Real 16 / 125 [&] Inv)))))"

end
