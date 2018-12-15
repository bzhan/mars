theory varDef
	imports "/home/yangg/MARS/MARS_v1.1/HHLProver/HHL"
begin

(*Define local and sending variables.*)
definition t :: exp where
"t == RVar ''t''"
definition plant_v1_1 :: exp where
"plant_v1_1 == RVar ''plant_v1_1''"
definition plant_m1_1 :: exp where
"plant_m1_1 == RVar ''plant_m1_1''"
definition control_1 :: exp where
"control_1 == RVar ''control_1''"
definition plant_r1_1 :: exp where
"plant_r1_1 == RVar ''plant_r1_1''"

end
