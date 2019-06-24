theory ChartVarDef
	imports "assertionDef"
begin

(*Define channel names.*)
definition BC_1 :: cname where
"BC_1 == ''BC_1''"
definition BR_1 :: cname where
"BR_1 == ''BR_1''"
definition BO_1 :: cname where
"BO_1 == ''BO_1''"
definition VO1 :: cname where
"VO1 == ''VO1''"
definition VI1 :: cname where
"VI1 == ''VI1''"
definition vBO1 :: exp where
"vBO1 == SVar ''vBO1''"
definition Ch_Chart_1 :: cname where
"Ch_Chart_1 == ''Ch_Chart_1''"

(*Define event variables assistent.*)
consts eL :: "exp list"
consts nL :: "exp list"
(*Define event variables.*)
definition E1 :: exp where
"E1 == SVar ''E1''"
definition done1 :: exp where
"done1 == RVar ''done1''"
definition SE :: exp where
"SE == SVar ''E''"
definition num :: exp where
"num == RVar ''num''"
definition EL :: exp where
"EL == List eL"
definition NL :: exp where
"NL == List nL"
(*Define local and sending variables.*)
definition sfTemp1 :: exp where
"sfTemp1 == RVar ''sfTemp1''"
definition p :: exp where
"p == RVar ''p''"
definition v :: exp where
"v == RVar ''v''"
definition p_out :: exp where
"p_out == RVar ''p_out''"
definition v_out :: exp where
"v_out == RVar ''v_out''"
definition actFalling :: exp where
"actFalling == RVar ''actFalling''"
(*Define input variables.*)
(*Define output variables.*)
definition p_out1 :: exp where
"p_out1 == RVar ''p_out1''"
definition v_out1 :: exp where
"v_out1 == RVar ''v_out1''"
(*Define local variables.*)
definition p1 :: exp where
"p1 == RVar ''p1''"
definition v1 :: exp where
"v1 == RVar ''v1''"

end
