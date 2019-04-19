theory varDef
	imports "/Users/BEAR/Projects/mars/CaseStudies/TwoBalls../../HHLProver/HHL"
begin

(*Define channel names.*)
definition Ch_First_1_0 :: cname where
"Ch_First_1_0 == ''Ch_First_1_0''"

(*Define receiving variables.*)
definition First_1_0 :: exp where
"First_1_0 == RVar ''First_1_0''"

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
definition Second_1 :: exp where
"Second_1 == RVar ''Second_1''"
definition First_1 :: exp where
"First_1 == RVar ''First_1''"

(*Definitions in comments, including extra functions defined by user or used during translation.*)
definition max :: "exp => exp => exp"
where "max(a,b) == if formT(a[<]b) then b else a"
end
