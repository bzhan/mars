theory State_SL
  imports Syntax_SL 
begin

type_synonym now = real
type_synonym history = "time \<Rightarrow> state"

definition semf :: "state \<Rightarrow> fform \<Rightarrow> bool" ("_ |= _" 50) where
  "semf s f \<equiv> f s"

end
