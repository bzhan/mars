theory varDef
	imports "/home/wangjian/Projects/MARS_v1.0/HHLProver/HHL"
begin

(*Define local and sending variables.*)
definition t :: exp where
"t == RVar ''t''"
definition Chart_1 :: exp where
"Chart_1 == RVar ''Chart_1''"

(*Definitions in comments, including extra functions defined by user or used during translation.*)
definition max :: "exp => exp => exp"
where "max(a,b) == if formT(a[<]b) then b else a"
end
