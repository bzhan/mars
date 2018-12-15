theory processDef
	imports "assertionDef"
begin

(*Define continuous processes*)
definition PC1_1 :: proc where
"PC1_1 ==  plant_1 := (Real 5)
"
definition commI1 :: proc where
"commI1 == Ch_plant_1_1!!plant_1
 [[ Ch_control_1_0??control_1_0"
definition PC1_2 :: proc where
"PC1_2 == (<WTrue && WTrue>:WTrue) [[> (commI1)"
definition domain1 :: fform where
"domain1 ==  ( )"
definition PC1_3 :: proc where
"PC1_3 == (<inv1 && domain1>:rg1)
	[[>commI1"
definition PC1_init :: proc where
"PC1_init == PC1_1;assertion1;PC1_2"
definition PC1_rep :: proc where
"PC1_rep == PC1_3"
definition PC1 :: proc where
"PC1 == PC1_init;assertion2;(PC1_rep)*"

(*Define discrete processes*)
definition PD1_1 :: proc where
"PD1_1 == t1:=(Real 0);assertion3;
 control_1 := (Real 1)"
definition PD1_2 :: proc where
"PD1_2 == 
Ch_control_1_0!!control_1;assertion4;
Ch_plant_1_1??plant_1_1"
definition PD1_3 :: proc where
"PD1_3 == 
 plant_1_1[>=](Real 5.9) -> control_1 := (Real 0) , plant_1_1[<=](Real 4.1) -> control_1 := (Real 1) , plant_1_1[>](Real 4.1)&&plant_1_1[<](Real 5.9)-> control_1 := control_1[+]0"
definition PD1_4 :: proc where
"PD1_4 == temp1:=t1;assertion5; <(WTrue) && (t1[<]temp1[+](Real 1))>:(l[=](Real 1))"
definition PD1_5 :: proc where
"PD1_5 == Ch_plant_1_1??plant_1_1"
definition PD1_6 :: proc where
"PD1_6 == 
 plant_1_1[>=](Real 5.9) -> control_1 := (Real 0) , plant_1_1[<=](Real 4.1) -> control_1 := (Real 1) , plant_1_1[>](Real 4.1)&&plant_1_1[<](Real 5.9)-> control_1 := control_1[+]0"
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
"PD1_init == PD1_init1;assertion6;PD1_init2;assertion7;PD1_init3"
definition PD1_rep1 :: proc where
"PD1_rep1 == PD1_4"
definition PD1_rep2 :: proc where
"PD1_rep2 == PD1_5"
definition PD1_rep3 :: proc where
"PD1_rep3 == PD1_6"
definition PD1_rep4 :: proc where
"PD1_rep4 == PD1_7"
definition PD1_rep :: proc where
"PD1_rep == PD1_rep1;assertion8;PD1_rep2;assertion9;PD1_rep3;assertion10;PD1_rep4"
definition PD1 :: proc where
"PD1 == PD1_init;assertion11;(PD1_rep)*"

(*Define the whole process.*)
definition P :: proc where
"P == PC1||PD1"
end
