theory processDef
	imports "FirstPDef"
begin

(*Define discrete processes*)
definition PD1_1 :: proc where
"PD1_1 == fbuf(Cbi_First_1_0??bFirst_1,Cbo_First_1_0!!bFirst_1,1,1)"
definition PD1_init1 :: proc where
"PD1_init1 =="
definition PD1_init :: proc where
"PD1_init == PD1_init1"
definition PD1_rep1 :: proc where
"PD1_rep1 == PD1_1"
definition PD1_rep :: proc where
"PD1_rep == PD1_rep1"
definition PD1 :: proc where
"PD1 == PD1_init;assertion1;(PD1_rep)*"

(*Define the whole process.*)
definition P :: proc where
"P == PC1||PD1||PSecond||PFirst"
end
