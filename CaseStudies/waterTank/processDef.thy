theory processDef
	imports "assertionDef"
begin

(*Define continuous processes*)
definition PC_Init :: proc where
"PC_Init ==  plant_1 := (Real 5)"

(*Diff:  diff(plant_1) == (control_1*(Real 0.8))-(Real 0.0314)*(sqrt((Real 19.6)*plant_1))*)
definition PC_Diff1 :: proc where
"PC_Diff1 == <(%'' plant_1 ,t'', '' (control_1*( 0.8))-( 0.0314)*(sqrt(( 19.6)*plant_1)),1''%) && Inv1 && ( [&] t [<] (Real 1))>: WTrue"

definition PC_Diff :: proc where
"PC_Diff == PC_Diff1"

(*Define discrete processes*)
definition PD_Init :: proc where
"PD_Init ==  control_1 := (Real 1)"
definition PD_Rep :: proc where
"PD_Rep ==  plant_1[>=](Real 5.9) -> control_1 := (Real 0) , plant_1[<=](Real 4.1) -> control_1 := (Real 1) , plant_1[>](Real 4.1)&&plant_1[<](Real 5.9)-> control_1 := control_1[+]0"

(*Define the whole process.*)
definition P :: proc where
"P == (PC_Init;assertion1;PD_Init;assertion2;t:=(Real 0));assertion3;(PC_Diff;assertion4;t:=(Real 0);assertion5;PD_Rep)*"
end
