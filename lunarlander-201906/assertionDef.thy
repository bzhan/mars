theory assertionDef
	imports "varDef"
begin


(*We assume the differential invariants for the two different differential equations are the same, then we solve
if such invariant exists or not. *)
consts Inv :: fform
definition Inv1 :: fform where
"Inv1 == Inv"
definition Inv2 :: fform where
"Inv2 == Inv"

(*The loop invariants can be deduced easily from the goal we need to prove. *)
definition Inv3 :: fform where
"Inv3 == Inv [&] RVar ''plant_t''[=] Real 0 [&] RVar ''plant_t''[\<le>] Real (16 / 125)"

end
