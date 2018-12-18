theory varDef
	imports "../../HHLProver/HHL"
begin

(*Define channel names.*)
definition Ch_plant_v1_1_1 :: cname where
"Ch_plant_v1_1_1 == ''Ch_plant_v1_1_1''"
definition Ch_plant_m1_1_1 :: cname where
"Ch_plant_m1_1_1 == ''Ch_plant_m1_1_1''"
definition Ch_control_1_0 :: cname where
"Ch_control_1_0 == ''Ch_control_1_0''"

(*Define receiving variables.*)
definition plant_v1_1_1 :: exp where
"plant_v1_1_1 == RVar ''plant_v1_1_1''"
definition plant_m1_1_1 :: exp where
"plant_m1_1_1 == RVar ''plant_m1_1_1''"
definition control_1_0 :: exp where
"control_1_0 == RVar ''control_1_0''"

(*Define local and sending variables.*)
definition t0 :: exp where
"t0 == RVar ''t0''"
definition temp0 :: exp where
"temp0 == RVar ''temp0''"
definition t1 :: exp where
"t1 == RVar ''t1''"
definition temp1 :: exp where
"temp1 == RVar ''temp1''"
definition plant_v1_1 :: exp where
"plant_v1_1 == RVar ''plant_v1_1''"
definition plant_m1_1 :: exp where
"plant_m1_1 == RVar ''plant_m1_1''"
definition control_1 :: exp where
"control_1 == RVar ''control_1''"
definition plant_r1_1 :: exp where
"plant_r1_1 == RVar ''plant_r1_1''"

end
