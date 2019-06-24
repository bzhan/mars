theory assertionDef
	imports "varDef"
begin

(*Define consts for processes definition.*)
consts
 diff :: "exp => exp" 

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
definition assertion6 :: mid where
"assertion6 == (WTrue,l[=](Real 0))"
definition assertion7 :: mid where
"assertion7 == (WTrue,l[=](Real 0))"
definition assertion8 :: mid where
"assertion8 == (WTrue,l[=](Real 0))"
definition assertion9 :: mid where
"assertion9 == (WTrue,l[=](Real 0))"
definition assertion10 :: mid where
"assertion10 == (WTrue,l[=](Real 0))"
definition assertion11 :: mid where
"assertion11 == (WTrue,l[=](Real 0))"
definition assertion12 :: mid where
"assertion12 == (WTrue,l[=](Real 0))"
definition assertion13 :: mid where
"assertion13 == (WTrue,l[=](Real 0))"
definition assertion14 :: mid where
"assertion14 == (WTrue,l[=](Real 0))"
definition assertion15 :: mid where
"assertion15 == (WTrue,l[=](Real 0))"
definition assertion16 :: mid where
"assertion16 == (WTrue,l[=](Real 0))"
definition assertion17 :: mid where
"assertion17 == (WTrue,l[=](Real 0))"

definition rg1 :: fform where
"rg1 == (l[=](Real 0))"
definition rg2 :: fform where
"rg2 == (l[=](Real 0))"

definition inv1 :: fform where
"inv1 == WTrue"
definition inv2 :: fform where
"inv2 == WTrue"

end
