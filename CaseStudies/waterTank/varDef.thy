theory varDef
	imports "/home/wangjian/Projects/MARS_v1.0/HHLProver/HHL"
begin

(*Define local and sending variables.*)
definition t :: exp where
"t == RVar ''t''"
definition plant_1 :: exp where
"plant_1 == RVar ''plant_1''"
definition control_1 :: exp where
"control_1 == RVar ''control_1''"

end
