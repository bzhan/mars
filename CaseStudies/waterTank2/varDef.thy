theory varDef
	imports "null/HHLProver/HHL"
begin

(*Define channel names.*)
definition Ch_Add_1_1 :: cname where
"Ch_Add_1_1 == ''Ch_Add_1_1''"
definition Ch_Integrator_1_2 :: cname where
"Ch_Integrator_1_2 == ''Ch_Integrator_1_2''"
definition Ch_Integrator_1_0 :: cname where
"Ch_Integrator_1_0 == ''Ch_Integrator_1_0''"
definition Ch_Chart_1_0 :: cname where
"Ch_Chart_1_0 == ''Ch_Chart_1_0''"

(*Define receiving variables.*)
definition Add_1_1 :: exp where
"Add_1_1 == RVar ''Add_1_1''"
definition Integrator_1_2 :: exp where
"Integrator_1_2 == RVar ''Integrator_1_2''"
definition Integrator_1_0 :: exp where
"Integrator_1_0 == RVar ''Integrator_1_0''"
definition Chart_1_0 :: exp where
"Chart_1_0 == RVar ''Chart_1_0''"

(*Define local and sending variables.*)
definition t0 :: exp where
"t0 == RVar ''t0''"
definition temp0 :: exp where
"temp0 == RVar ''temp0''"
definition t1 :: exp where
"t1 == RVar ''t1''"
definition temp1 :: exp where
"temp1 == RVar ''temp1''"
definition t2 :: exp where
"t2 == RVar ''t2''"
definition temp2 :: exp where
"temp2 == RVar ''temp2''"
definition t3 :: exp where
"t3 == RVar ''t3''"
definition temp3 :: exp where
"temp3 == RVar ''temp3''"
definition Add_1 :: exp where
"Add_1 == RVar ''Add_1''"
definition product_1 :: exp where
"product_1 == RVar ''product_1''"
definition hehe_1 :: exp where
"hehe_1 == RVar ''hehe_1''"
definition chacha_1 :: exp where
"chacha_1 == RVar ''chacha_1''"
definition shabi_1 :: exp where
"shabi_1 == RVar ''shabi_1''"
definition Integrator_1 :: exp where
"Integrator_1 == RVar ''Integrator_1''"
definition cheng_1 :: exp where
"cheng_1 == RVar ''cheng_1''"
definition Chart_1 :: exp where
"Chart_1 == RVar ''Chart_1''"

end
