theory goal
	imports "processDef"
begin

(*Assistance for defining goal, user may need to modify it for proof.*)
consts 
pre :: fform 
post :: fform 
H :: fform 

(*Goal for the whole process.*)
lemma goal : "{pre} P {post; H}"
sorry

end
