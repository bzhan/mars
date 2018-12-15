theory varDef
	imports "/home/yangg/MARS/MARS_v1.1/HHLProver/HHL"
begin

(*Define channel names.*)
definition Ch_plant_1_1 :: cname where
"Ch_plant_1_1 == ''Ch_plant_1_1''"
definition Ch_control_1_0 :: cname where
"Ch_control_1_0 == ''Ch_control_1_0''"

(*Define receiving variables.*)
definition plant_1_1 :: exp where
"plant_1_1 == RVar ''plant_1_1''"
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
definition plant_1 :: exp where
"plant_1 == RVar ''plant_1''"
definition control_1 :: exp where
"control_1 == RVar ''control_1''"

end
