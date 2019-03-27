theory goaltest 
  imports  invGen
begin
definition t :: exp where
"t == RVar ''t''"
definition v :: exp where
"v == RVar ''v''"
definition w :: exp where
"w == RVar ''w''"


declare t_def [simp]
declare v_def [simp] 
declare w_def [simp]

consts Inv :: fform



definition safeProp :: fform where
"safeProp == (v [+](Real 2)) [<] (Real 0.05) [&] (v [+] (Real 2)) [>] (Real -0.05)"



definition PC_Diff11 :: proc where
"PC_Diff11 ==  <[''t'', ''v'', ''w'']: 
[(Real 1), (w [-] (Real 1.622)), (w[**]2 [div] (Real 2548))] && Inv&
((t[\<ge>]Real 0)[&](t [<] (Real 0.128)))>"

 
definition PC_Diff22 :: proc where
"PC_Diff22 ==  <[''t'', ''v'', ''w'']: 
[(Real 1), (w [-] (Real 1.622)), (w[**]2 [div] (Real 2842))] && Inv&
((t[\<ge>]Real 0)[&](t [<] (Real 0.128)))>"

definition cons1 :: fform where 
"cons1 \<equiv> ((Inv [&] t [\<ge>]Real 0 [&] t [\<le>] Real 0.128 ) [\<longrightarrow>]  safeProp)"


definition cons2 :: fform where 
"cons2 \<equiv> ((v[=](Real -2) [&] w[=](Real (4055/2500)) [&] t[=](Real 0)) [\<longrightarrow>] Inv)"

definition cons3 :: fform where
"cons3 == (((Inv [&] t [=](Real (16 / 125))) ) [\<longrightarrow>] ((Inv \<lbrakk>(Real 0), ''t''\<rbrakk>)\<lbrakk> (Real (811 / 500) [-] Real (1 / 100) [*] (w [-] Real (811 / 500)) [-]
                                    Real (3 / 5) [*] (v [+] Real 2)), ''w''\<rbrakk>))"

definition cons4 :: fform where 
"cons4 \<equiv>  exeFlow(PC_Diff11) (Inv)  [\<longrightarrow>]  Inv"
definition cons5 :: fform where 
"cons5 \<equiv>  exeFlow(PC_Diff22) (Inv)  [\<longrightarrow>]  Inv"


lemma allCons: "\<forall> s. ( cons1 [&] cons2 [&] cons3 [&] cons4 [&] cons5) s"
apply (simp add: cons1_def)
apply (simp add: cons2_def cons3_def)
apply (simp add: cons4_def)
apply (simp add: cons5_def)
  apply (simp add: safeProp_def)
  apply (simp add:PC_Diff11_def PC_Diff22_def)
apply inv_oracle_SOS


end