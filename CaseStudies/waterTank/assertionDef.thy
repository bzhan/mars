theory assertionDef
	imports "varDef"
begin

(*Define consts for processes definition.*)
consts diff :: "exp => exp" 

definition assertion1 :: mid where
"assertion1 == (WTrue,l[=](Real 0))"
definition assertion2 :: mid where
"assertion2 == (WTrue,l[=](Real 0))"
definition assertion3 :: mid where
"assertion3 == (WTrue,l[=](Real 0))"
definition assertion4 :: mid where
"assertion4 == (WTrue,l[=](Real 0))"
definition assertion5 :: mid where
"assertion5 == (WTrue,l[=](Real 0))"


definition Inv1 :: fform where
"Inv1 == WTrue"

end
