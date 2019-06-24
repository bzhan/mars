theory Writer2_2VarDef
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
definition Ch_Writer2_2_1 :: cname where
"Ch_Writer2_2_1 == ''Ch_Writer2_2_1''"

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
definition ResponseDelay :: exp where
"ResponseDelay == RVar ''ResponseDelay''"
definition re_changes :: exp where
"re_changes == RVar ''re_changes''"
definition cansend :: exp where
"cansend == RVar ''cansend''"
definition ACKNACK :: exp where
"ACKNACK == RVar ''ACKNACK''"
definition flag :: exp where
"flag == RVar ''flag''"
definition event :: exp where
"event == RVar ''event''"
definition event1 :: exp where
"event1 == RVar ''event1''"
definition actrepairing :: exp where
"actrepairing == RVar ''actrepairing''"
definition actwaiting :: exp where
"actwaiting == RVar ''actwaiting''"
definition actmust_repair :: exp where
"actmust_repair == RVar ''actmust_repair''"
(*Define input variables.*)
definition cansend1 :: exp where
"cansend1 == RVar ''cansend1''"
definition ACKNACK1 :: exp where
"ACKNACK1 == RVar ''ACKNACK1''"
(*Define output variables.*)
definition flag1 :: exp where
"flag1 == RVar ''flag1''"
(*Define local variables.*)
definition re_changes1 :: exp where
"re_changes1 == RVar ''re_changes1''"

end
