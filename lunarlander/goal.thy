theory goal 
  imports processDef invGen
begin

(*The safety property to prove.*)
definition safeProp :: fform where
"safeProp == (plant_v1_1 [+](Real 2)) [<] (Real 0.05) [&] (plant_v1_1 [+] (Real 2)) [>] (Real -0.05)"

(*The system clock is always positive.*)
axiomatization where
Clock : "\<forall> s. (t [\<ge>] Real 0) s"


(*The following lists the constraints for solving the differential invariants for the 
differential equations.*)
(*The invariant guarantees the postcondition.*)
definition cons1 :: fform where 
"cons1 \<equiv> ((t [\<ge>]Real 0 [&] t [\<le>] Real 0.128 [&] Inv) [\<longrightarrow>]  safeProp)"
(*Initialization:the initial state guarantees the invariant;
and Computation: the computation guarantees the invariant.*)
definition cons2 :: fform where 
"cons2 \<equiv> ((plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250) 
    [&] control_1[=](Real (4055/2)) [&] t[=](Real 0)) [\<longrightarrow>] Inv)"
(*The core parts: the discrete computation and differential equations garantee the invariants. *)
definition cons31 :: fform where
"cons31 == (((t [=](Real (16 / 125))) [&] Inv) [\<longrightarrow>] (Inv \<lbrakk>(Real 0), ''plant_t''\<rbrakk>))"

definition cons31_aux :: fform where
"cons31_aux == \<lambda> s. ((t [=]Real (16 / 125) [&] Inv) s \<longrightarrow> Inv (\<lambda>y. if y = ''plant_t'' then evalE (Real 0) s else s y))" 


definition cons32 :: fform where
"cons32 == (Inv [\<longrightarrow>] (Inv \<lbrakk>(plant_m1_1 [*]
                                   (Real (811 / 500) [-] Real (1 / 100) [*] (control_1 [div] plant_m1_1 [-] Real (811 / 500)) [-]
                                    Real (3 / 5) [*] (plant_v1_1 [+] Real 2))), ''control_1''\<rbrakk>))"
 

definition cons32_aux :: fform where
"cons32_aux == \<lambda> s. (Inv s \<longrightarrow>
               Inv (\<lambda>y. if y = ''control_1''
                       then (evalE (plant_m1_1 [*]
                                   (Real (811 / 500) [-] Real (1 / 100) [*] (control_1 [div] plant_m1_1 [-] Real (811 / 500)) [-]
                                    Real (3 / 5) [*] (plant_v1_1 [+] Real 2)))
                             s)
                       else s y))" 
definition cons4 :: fform where 
"cons4 \<equiv>  exeFlow(PC_Diff11) (Inv)  [\<longrightarrow>]  Inv"
definition cons5 :: fform where 
"cons5 \<equiv>  exeFlow(PC_Diff22) (Inv)  [\<longrightarrow>]  Inv"

lemma cons31_fact: "cons31 s \<Longrightarrow> cons31_aux s"
  apply (simp add:cons31_def cons31_aux_def fSubForm_def fImp_def)
  done 


lemma cons32_fact: "cons32 s \<Longrightarrow> cons32_aux s"
  apply (simp add:cons32_def cons32_aux_def fSubForm_def fImp_def)
  by (metis control_1_def plant_m1_1_def plant_v1_1_def)

(*Put this whole constraint to the differential invariant generator.*)
lemma allCons: "\<forall> s. ( cons1 [&] cons2 [&] cons31 [&] cons32 [&] cons4 [&] cons5) s"
apply (simp add: cons1_def)
apply (simp add: cons2_def cons31_def cons32_def)
apply (simp add: cons4_def)
apply (simp add: cons5_def)
  apply (simp add: safeProp_def)
  apply (simp add:PC_Diff11_def PC_Diff22_def)

apply inv_oracle_SOS
done
*)
(**You can uncomment the above lines, if you have  Mathematica, Matlab, Yalmip and SDPT3 installed. "Sorry" will go away.**)
sorry

lemma constraint11: "\<forall> s. (t [\<ge>] Real 0 [&] t [\<le>] Real (16 / 125) [&] Inv) s \<longrightarrow> safeProp s"
apply (cut_tac allCons)
apply (simp add:cons1_def)
by (metis fAnd_def fImp_def)


lemma constraint1: "\<forall> s. (t [\<le>]Real (16 / 125) [&] Inv) s \<longrightarrow> safeProp s"
apply (cut_tac allCons)
apply (cut_tac Clock)
by (metis constraint11 fAnd_def)




lemma constraint2: "\<forall> s. (plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250) 
    [&] control_1[=](Real (4055/2)) [&] t[=](Real 0)) s \<longrightarrow> Inv s"
apply (cut_tac allCons)
apply (simp add:cons2_def)
by (metis fAnd_def fImp_def)


lemma constraint31: "\<forall> s. ((t [=]Real (16 / 125) [&] Inv) s \<longrightarrow> Inv (\<lambda>y. if y = ''plant_t'' then evalE (Real 0) s else s y))"
apply (cut_tac allCons)
  apply (simp add:cons31_def) 
proof -
  { fix vv :: "char list \<Rightarrow> real"
    have "cons31_aux vv"
      by (metis allCons cons31_fact fAnd_def)
    then have "\<not> (RVar ''plant_t''[=]Real (16 / 125) [&] Inv) vv \<or> Inv (\<lambda>cs. if cs = ''plant_t'' then evalE (Real 0) vv else vv cs)"
      by (simp add: cons31_aux_def) }
  then show "\<forall>f. (RVar ''plant_t''[=]Real (16 / 125) [&] Inv) f \<longrightarrow> Inv (\<lambda>cs. if cs = ''plant_t'' then evalE (Real 0) f else f cs)"
    by meson
qed





lemma constraint32: "\<forall> s. (Inv s \<longrightarrow>
               Inv (\<lambda>y. if y = ''control_1''
                       then (evalE (plant_m1_1 [*]
                                   (Real (811 / 500) [-] Real (1 / 100) [*] (control_1 [div] plant_m1_1 [-] Real (811 / 500)) [-]
                                    Real (3 / 5) [*] (plant_v1_1 [+] Real 2)))
                             s)
                       else s y))"
  apply (cut_tac allCons)
  apply (simp add:fAnd_def, auto)  
  apply (simp add:cons32_def fImp_def fSubForm_def)
  apply (drule_tac x = s in spec, auto)
  by (metis case_prod_conv cond_case_prod_eta control_1_def plant_m1_1_def plant_v1_1_def)

lemma constraint4: "\<forall> s.  exeFlow(PC_Diff11) (Inv) s  \<longrightarrow>  Inv s"
apply (cut_tac allCons)
apply (simp add:cons4_def)
by (metis fAnd_def fImp_def)


lemma constraint5: "\<forall> s.  exeFlow(PC_Diff22) (Inv) s  \<longrightarrow>  Inv s"
apply (cut_tac allCons)
apply (simp add:cons5_def)
by (metis fAnd_def fImp_def)


declare elE_def [simp del]


lemma factLess: "(RVar x [\<le>] Real r) s \<Longrightarrow>
  (RVar x [\<ge>] Real r) s \<Longrightarrow>  (RVar x [=] Real r) s"
  by (simp add:fLessEqual_def fGreaterEqual_def fLess_def fEqual_def fOr_def)


(*Goal for the whole process.*)
lemma goal : "{fTrue} PP {safeProp; (elE 0 [[|]] (almost safeProp))}"
(*mono*)
apply (cut_tac px="fTrue" and qx="t [\<le>] Real (16 / 125) [&] Inv" and Hx="(elE 0 [[|]] (almost (t [\<le>] Real (16 / 125) [&] Inv)))" in ConsequenceRule, auto)
prefer 2
apply (cut_tac constraint1, auto)
prefer 2
apply (cut_tac constraint1, auto)
apply (simp add:dOr_def almost_def, auto)
apply (simp add:PP_def PC_Init_def PD_Init_def)
(*separate into intialization and repetitive control*)
apply (cut_tac m = "((plant_v1_1[=](Real -2)) [&] (plant_m1_1[=](Real 1250)) [&] (control_1[=](Real 2027.5)) [&] (t[=](Real 0)))" 
           and  H = "elE 0"  and  G="(elE 0 [[|]] (almost (t [\<le>] Real (16 / 125) [&] Inv)))"  in SequentialRule, auto)
(*Init*)
apply (cut_tac m = "((plant_v1_1[=] (Real -2)) [&] (plant_m1_1[=] (Real 1250)))" 
     and  H = "elE 0"  and  G = "elE 0" in SequentialRule, auto)
apply (cut_tac m = "plant_v1_1[=]Real - 2"  and  H = "elE 0" and  G = "elE 0" in SequentialRule, auto)
apply (rule AssignRRule, auto) apply (simp add:fEqual_def)
apply (cut_tac m = "plant_v1_1[=]Real - 2 [&] plant_m1_1[=]Real 1250" 
   and  H = "elE 0" and  G = "elE 0" in SequentialRule, auto)
apply (rule AssignRRule, auto) apply (simp add:fAnd_def fEqual_def)
apply (rule AssignRRule, auto) apply (simp add:fAnd_def fEqual_def)
apply (simp add:elE_def chop_def)+
apply (cut_tac m = "((plant_v1_1[=](Real -2)) [&] (plant_m1_1[=](Real 1250)) [&] (control_1[=](Real 2027.5)))" 
           and  H = "elE 0" and  G = "elE 0" in SequentialRule, auto)
apply (rule AssignRRule, auto) apply (simp add:fAnd_def fEqual_def)
apply (rule AssignRRule, auto) apply (simp add:fAnd_def fEqual_def)
apply (simp add:elE_def chop_def)+
prefer 2
apply (simp add:elE_def dOr_def chop_def)
(*Rep Part*)
apply (cut_tac px="Inv [&] t[=](Real 0) [&] t [\<le>] Real (16 / 125)" and qx="Inv [&] t[=](Real 0) [&] t [\<le>] Real (16 / 125)" and Hx="(elE 0 [[|]] (almost (t [\<le>] Real (16 / 125) [&] Inv)))" in ConsequenceRule,auto)
prefer 2
apply (cut_tac constraint2, auto) apply (simp add:fAnd_def fLessEqual_def fOr_def fLess_def fEqual_def)
prefer 2
apply (simp add:fAnd_def fLessEqual_def fOr_def fLess_def)
prefer 2
apply (simp add:elE_def dOr_def)
apply (simp add:Inv3_def)
apply (cut_tac I = "Inv [&] RVar ''plant_t''[=]Real 0 [&]
     RVar ''plant_t''[\<le>]Real (16 / 125)" and
     P = "(PC_Difff; (RVar ''plant_t'') := (Real 0); PD_Rep)" and 
  H = "elE 0 [[|]] almost (RVar ''plant_t''[\<le>]Real (16 / 125) [&] Inv)" in RepetitionRule_a, auto)
apply (cut_tac P = "(RVar ''plant_t''[\<le>]Real (16 / 125) [&] Inv)"
      and h = h and n = n and nd = m in chopfor, auto)
prefer 2
apply (cut_tac px = "Inv [&] RVar ''plant_t''[=]Real 0 [&]
     RVar ''plant_t''[\<le>]Real (16 /125)" and 
     qx = "Inv [&] RVar ''plant_t''[=]Real 0 [&]
           RVar ''plant_t''[\<le>]Real (16 / 125)" and 
     Hx = "elE 0 [[|]] (elE 0 [[|]] almost (RVar ''plant_t''[\<le>]Real (16 / 125) [&] Inv))" in ConsequenceRule, auto)
apply (simp add: dOr_def)
apply (cut_tac m = "t [=] Real (16 / 125) [&] Inv" and
    H = "(elE 0 [[|]] (almost (t [\<le>] Real (16 / 125) [&] Inv)))" and  
  G= "elE 0" in  SequentialRule, auto)
prefer 2
apply (simp add: PD_Rep_def)
apply (cut_tac m = "t [=] Real 0 [&] Inv" and 
    H = "elE 0" and  G= "elE 0" in  SequentialRule, auto)
apply (rule AssignRRule, auto)
apply (cut_tac constraint31, auto)
 apply (simp add:fAnd_def fLessEqual_def fOr_def fLess_def fEqual_def)
apply (rule AssignRRule, auto)
apply (cut_tac constraint32)
 apply (simp add:fAnd_def fLessEqual_def fOr_def fLess_def fEqual_def)
using control_1_def plant_m1_1_def plant_v1_1_def 
apply presburger
apply (simp add:elE_def chop_def)
prefer 2 
apply (simp add: chop_def elE_def)
(*Plant Part*)
apply (simp add:PC_Difff_def)
apply (rule ConditionGRule, auto) 
apply (simp add:PC_Diff11_def Inv1_def)
apply (rule ContinuousRuleGT, auto)
apply (simp add:fLess_def fAnd_def fEqual_def) 
apply (simp add:fAnd_def)
apply (simp add:fAnd_def, auto)
apply (cut_tac e = "RVar ''plant_t''" and f = "Real (16 / 125)" in Lessc)
apply (rule factLess, auto) 
apply (cut_tac constraint4)
apply (simp add:PC_Diff11_def Inv1_def)
apply (simp add:elE_def dOr_def)
apply (simp add:dOr_def)
apply (simp add:fAnd_def almost_def) 
apply (simp add:PC_Diff22_def Inv2_def)
apply (rule ContinuousRuleGT, auto)
apply (simp add:fLess_def fAnd_def fEqual_def) 
apply (simp add:fAnd_def)
apply (simp add:fAnd_def, auto)
apply (cut_tac e = "RVar ''plant_t''" and f = "Real (16 / 125)" in Lessc)
apply (rule factLess, auto) 
apply (cut_tac constraint5)
apply (simp add:PC_Diff22_def Inv2_def)
apply (simp add:elE_def dOr_def)
apply (simp add:dOr_def)
apply (simp add:fAnd_def almost_def) 
done




end
