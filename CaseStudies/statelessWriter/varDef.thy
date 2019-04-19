theory varDef
	imports "/Users/BEAR/Projects/mars/CaseStudies/statelessWriter/../../HHLProver/HHL"
begin

(*Define channel names.*)

(*Define receiving variables.*)

(*Define local and sending variables.*)
definition t0 :: exp where
"t0 == RVar ''t0''"
definition temp0 :: exp where
"temp0 == RVar ''temp0''"
definition t1 :: exp where
"t1 == RVar ''t1''"
definition temp1 :: exp where
"temp1 == RVar ''temp1''"
definition Writer2_2_1 :: exp where
"Writer2_2_1 == RVar ''Writer2_2_1''"

end
