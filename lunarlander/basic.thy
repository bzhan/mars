theory basic
   imports NthRoot  HHL_SL
begin

definition x :: exp where
"x == RVar ''parx''"


definition Assignment :: proc where 
"Assignment == x :=((Con Real 1) [+] x )"

lemma B01:"{x[\<ge>](Con Real 0)}x :=((Con Real 1) [+] x ){x[\<ge>](Con Real 1);elE 0}"






apply (cut_tac p="x[\<ge>](Con Real 0)" 
           and q="x[\<ge>](Con Real 1)" 
           and H="elE 0" 
           and x="''parx''" 
           and f="((Con Real 1) [+] x )" in  AssignRRule,auto)



defer apply (simp add:x_def)
apply (simp add:fGreaterEqual_def)
apply (simp add:fNot_def)
apply (simp add:fLess_def)
apply (simp add:x_def)


sorry
lemma B02:"{x[\<ge>](Con Real 1)} (x :=((Con Real 1) [+] x ))*&& x[\<ge>](Con Real 1) {x[\<ge>](Con Real 1);elE 0}"
apply (cut_tac Inv="x[\<ge>](Con Real 1)" 
           and P="x :=((Con Real 1) [+] x )" 
           and H="elE 0" 
            in  RepetitionRule,auto)
apply (simp add:chop_def) 
defer
apply (simp add:dOr_def )
apply (cut_tac p="x[\<ge>](Con Real 1)" 
           and q="x[\<ge>](Con Real 1)" 
           and H="elE 0" 
           and x="''parx''" 
           and f="((Con Real 1) [+] x )" in  AssignRRule,auto)
defer apply (simp add:x_def)
apply (simp add:fGreaterEqual_def)
apply (simp add:fNot_def)
apply (simp add:fLess_def)
apply (simp add:x_def)
sorry

lemma B03:"{x[\<ge>](Con Real 1)}( x := (x [+] Con Real 1)) [[ ( y := (y [+] Con Real 1) ) {x[\<ge>](Con Real 1);elE 0}"
apply (cut_tac P="(x := (x [+] Con Real 1))" 
           and Q="(y := (y [+] Con Real 1))" 
           and p="x[\<ge>](Con Real 1)" 
           and m="x[\<ge>](Con Real 1)" 
           and q="x[\<ge>](Con Real 1)" 
           and H="elE 0" 
           and G="elE 0"  in JoinRule,auto)
defer
defer
apply (simp add:fOr_def )
apply (simp add:dOr_def )
sorry




end
