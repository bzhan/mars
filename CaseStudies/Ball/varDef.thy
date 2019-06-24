theory varDef
	imports "../../HHLProver/HHL"
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
definition Chart_1 :: exp where
"Chart_1 == RVar ''Chart_1''"

(*Definitions in comments, including extra functions defined by user or used during translation.*)
definition max :: "exp => exp => exp"
where "max(a,b) == if formT(a[<]b) then b else a"
end
