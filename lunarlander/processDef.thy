theory processDef
	imports "assertionDef"
begin

(*Define continuous processes*)
definition PC_Init :: proc where
"PC_Init ==  plant_v1_1 := (Con Real -2); 
               plant_m1_1 := (Con Real 1250); 
                  plant_r1_1:=(Con Real 30)"


definition PC_Diff11 :: proc where
"PC_Diff11 ==  <[(''plant_v1_1'', R), (''plant_m1_1'', R), (''plant_r1_1'', R), (''plant_t'', R)]: 
[((control_1 [div] plant_m1_1) [-] (Con Real 1.622)), ((Con Real 0) [-](control_1[div] (Con Real 2548))), plant_v1_1, (Con Real 1)] && Inv1&
((t [<] (Con Real 0.128)))>"

 
definition PC_Diff22 :: proc where
"PC_Diff22 ==  <[(''plant_v1_1'', R), (''plant_m1_1'', R), (''plant_r1_1'', R), (''plant_t'', R)]: 
[((control_1 [div] plant_m1_1) [-] (Con Real 1.622)), ((Con Real 0) [-](control_1[div] (Con Real 2842))), plant_v1_1, (Con Real 1)] && Inv2&
((t [<] (Con Real 0.128)))>"

 
definition PC_Difff :: proc where
"PC_Difff == IFELSE (control_1[>](Con Real 3000)) PC_Diff11 PC_Diff22"

(*Define discrete processes*)
definition PD_Init :: proc where
"PD_Init ==  control_1 := (Con Real 2027.5)"
definition PD_Rep :: proc where
"PD_Rep == control_1 := (plant_m1_1[*]((Con Real 1.622) [-] (Con Real 0.01)[*](control_1[div]plant_m1_1[-](Con Real 1.622)) [-] (Con Real 0.6)[*](plant_v1_1[+](Con Real 2))))"

(*Define the whole process.*)
(*We can see where Inv1, Inv2, and  Inv3 occur.*)
definition PP :: proc where
"PP == (PC_Init; PD_Init; t:=(Con Real 0));(PC_Difff; t:=(Con Real 0); PD_Rep)*&&Inv3"

end
