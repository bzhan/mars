theory processDef
	imports "assertionDef"
begin

(*Define continuous processes*)
definition PC_Init :: proc where
"PC_Init ==  plant_v1_1 := (Real -2);assertion1;
  plant_m1_1 := (Real 1250);assertion2;
 plant_r1_1:=(Real 30)"

(*Diff:  diff(plant_v1_1) == (control_1/plant_m1_1) - (Real 1.622), diff(plant_m1_1) == - (control_1/(Real 2548)),diff(plant_r1_1)==plant_v1_1*)
definition PC_Diff1 :: proc where
"PC_Diff1 == <(%'' plant_v1_1 , plant_m1_1 ,plant_r1_1,t'', '' (control_1/plant_m1_1) - ( 1.622), - (control_1/( 2548)),plant_v1_1,1''%) && Inv1 && ((control_1[>](Real 3000))[&] t [<] (Real 0.128))>: WTrue"

(*Diff:  diff(plant_v1_1) == (control_1/plant_m1_1) - (Real 1.622), diff(plant_m1_1) == - (control_1/(Real 2842)),diff(plant_r1_1)==plant_v1_1*)
definition PC_Diff2 :: proc where
"PC_Diff2 == <(%'' plant_v1_1 , plant_m1_1 ,plant_r1_1,t'', '' (control_1/plant_m1_1) - ( 1.622), - (control_1/( 2842)),plant_v1_1,1''%) && Inv2 && ((control_1[<=](Real 3000))[&] t [<] (Real 0.128))>: WTrue"

definition PC_Diff :: proc where
"PC_Diff == PC_Diff1;assertion3;PC_Diff2"

(*Define discrete processes*)
definition PD_Init :: proc where
"PD_Init ==  control_1 := (Real 2027.5)"
definition PD_Rep :: proc where
"PD_Rep == control_1 := (plant_m1_1[*]((Real 1.622) [-] (Real 0.01)[*](control_1[**]plant_m1_1[-](Real 1.622)) [-] (Real 0.6)[*](plant_v1_1[+](Real 2))))"

(*Define the whole process.*)
definition P :: proc where
"P == (PC_Init;assertion4;PD_Init;assertion5;t:=(Real 0));assertion6;(PC_Diff;assertion7;t:=(Real 0);assertion8;PD_Rep)*"
end
