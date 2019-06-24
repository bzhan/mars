theory processDef
	imports "assertionDef"
begin

(*Define continuous processes*)
definition PC1_1 :: proc where
"PC1_1 ==  plant_v1_1 := (Real -2);assertion1;
  plant_m1_1 := (Real 1250);assertion2;
 plant_r1_1:=(Real 30)
"
definition commI1 :: proc where
"commI1 == Ch_plant_v1_1_1!!plant_v1_1
 [[ Ch_control_1_0??control_1_0 [[ Ch_plant_m1_1_1!!plant_m1_1"
definition PC1_2 :: proc where
"PC1_2 == (<WTrue && WTrue>:WTrue) [[> (commI1);assertion3;
(<WTrue && WTrue>:WTrue) [[> (commI1)"
definition domain1 :: fform where
"domain1 ==  ((control_1_0[>](Real 3000)))"
definition PC1_3 :: proc where
"PC1_3 == (<inv1 && domain1>:rg1)
	[[>commI1"
definition domain2 :: fform where
"domain2 ==  ((control_1_0[<=](Real 3000)))"
definition PC1_4 :: proc where
"PC1_4 == (<inv2 && domain2>:rg2)
	[[>commI1"
definition PC1_init :: proc where
"PC1_init == PC1_1;assertion4;PC1_2"
definition PC1_rep :: proc where
"PC1_rep == PC1_3;assertion5;PC1_4"
definition PC1 :: proc where
"PC1 == PC1_init;assertion6;(PC1_rep)*"

(*Define discrete processes*)
definition PD1_1 :: proc where
"PD1_1 == t1:=(Real 0);assertion7;
 control_1 := (Real 2027.5)"
definition PD1_2 :: proc where
"PD1_2 == 
Ch_control_1_0!!control_1;assertion8;
Ch_plant_v1_1_1??plant_v1_1_1;assertion9;
 Ch_plant_m1_1_1??plant_m1_1_1"
definition PD1_3 :: proc where
"PD1_3 == 
 control_1 := (plant_m1_1_1[*]((Real 1.622) [-] (Real 0.01)[*](control_1[**]plant_m1_1_1[-](Real 1.622)) [-] (Real 0.6)[*](plant_v1_1_1[+](Real 2))))"
definition PD1_4 :: proc where
"PD1_4 == temp1:=t1;assertion10; <(WTrue) && (t1[<]temp1[+](Real 0.128))>:(l[=](Real 0.128))"
definition PD1_5 :: proc where
"PD1_5 == Ch_plant_v1_1_1??plant_v1_1_1;assertion11;
 Ch_plant_m1_1_1??plant_m1_1_1"
definition PD1_6 :: proc where
"PD1_6 == 
 control_1 := (plant_m1_1_1[*]((Real 1.622) [-] (Real 0.01)[*](control_1[**]plant_m1_1_1[-](Real 1.622)) [-] (Real 0.6)[*](plant_v1_1_1[+](Real 2))))"
definition PD1_7 :: proc where
"PD1_7 == 
Ch_control_1_0!!control_1"
definition PD1_init1 :: proc where
"PD1_init1 == PD1_1"
definition PD1_init2 :: proc where
"PD1_init2 == PD1_2"
definition PD1_init3 :: proc where
"PD1_init3 == PD1_3"
definition PD1_init :: proc where
"PD1_init == PD1_init1;assertion12;PD1_init2;assertion13;PD1_init3"
definition PD1_rep1 :: proc where
"PD1_rep1 == PD1_4"
definition PD1_rep2 :: proc where
"PD1_rep2 == PD1_5"
definition PD1_rep3 :: proc where
"PD1_rep3 == PD1_6"
definition PD1_rep4 :: proc where
"PD1_rep4 == PD1_7"
definition PD1_rep :: proc where
"PD1_rep == PD1_rep1;assertion14;PD1_rep2;assertion15;PD1_rep3;assertion16;PD1_rep4"
definition PD1 :: proc where
"PD1 == PD1_init;assertion17;(PD1_rep)*"

(*Define the whole process.*)
definition P :: proc where
"P == PC1||PD1"
end
