theory assertionDef
	imports "varDef"
begin

(*Define consts for processes definition.*)
consts
 diff :: "exp => exp" 

definition assertion1 :: mid where
"assertion1 == (WTrue,l[=](Real 0))"



end
