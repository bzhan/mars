theory varDef
	imports "HHL_SL"
begin

(*Define local and sending variables.*)
definition t :: exp where
"t == RVar ''plant_t''"
definition plant_v1_1 :: exp where
"plant_v1_1 == RVar ''plant_v1_1''"
definition plant_m1_1 :: exp where
"plant_m1_1 == RVar ''plant_m1_1''"
definition control_1 :: exp where
"control_1 == RVar ''control_1''"
definition plant_r1_1 :: exp where
"plant_r1_1 == RVar ''plant_r1_1''"


declare t_def [simp]
declare plant_v1_1_def [simp] 
declare plant_m1_1_def [simp]
declare control_1_def [simp]
declare plant_r1_1_def [simp]
end
