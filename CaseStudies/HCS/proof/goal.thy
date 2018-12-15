theory goal
	imports "invGen"
begin

(*The safety property to prove.*)
definition safeProp :: fform where
"safeProp == (plant_v1_1 [+] Real 2) [<] Real 0.05 [&] (plant_v1_1 [+] Real 2) [>] Real -0.05"

(*The system clock is always positive.*)
axiomatization where
Clock : "|-t [>=] Real 0"

(*Some lemmas to be used in proving goal.*)
lemma constraint0a: "close(Inv) |- Inv"
apply (simp add: Inv_def equal_greater_def)
apply (rule Trans1, auto)
done

lemma constraint0b: "~ inPairForm
       ([(t, Real 0)],
        substF
         ([(control_1,
            plant_m1_1 [*]
            (Real 811 / 500 [-]
             Real 1 / 100 [*]
             (control_1 [**] plant_m1_1 [-] Real 811 / 500) [-]
             Real 3 / 5 [*] (plant_v1_1 [+] Real 2)))],
          Inv [&] t[=](Real 0)))"
apply (simp add: t_def control_1_def Inv_def equal_greater_def)
done

lemma constraint0c: "~ inPairForm
       ([(control_1,
          plant_m1_1 [*]
          (Real 811 / 500 [-]
           Real 1 / 100 [*] (control_1 [**] plant_m1_1 [-] Real 811 / 500) [-]
           Real 3 / 5 [*] (plant_v1_1 [+] Real 2)))],
        Inv [&] t [=] Real 0)"
apply (simp add: t_def control_1_def Inv_def equal_greater_def)
done



(*The following lists the constraints for solving the differential invariants for the 
differential equations.*)
(*The invariant guarantees the postcondition.*)
definition cons1 :: fform where "cons1 \<equiv> ((t [>=] Real 0 [&] t [<=] Real 0.128 [&] Inv) [-->]  safeProp)"
(*Initialization:the initial state guarantees the invariant;
and Computation: the computation guarantees the invariant.*)
definition cons2 :: fform where "cons2 \<equiv> ((plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250) [&] control_1[=](Real 4055/2) [&] t[=](Real 0)) [-->] Inv)"
definition cons3 :: fform where "cons3 \<equiv> (((t[=](Real 16/125)) [&] Inv) [-->] (substF([(t, Real 0)], substF
        ([(control_1,
           plant_m1_1 [*]
           (Real 811 / 500 [-]
            Real 1 / 100 [*]
            (control_1 [**] plant_m1_1 [-]
             Real 811 / 500) [-]
            Real 3 / 5 [*] (plant_v1_1 [+] Real 2)))],
         Inv))))"
(*The core parts: the differential equations garantee the invariants. *)
definition cons4 :: fform where "cons4 \<equiv>  exeFlow(%'' plant_v1_1 , plant_m1_1 ,plant_r1_1,t'','' (control_1/plant_m1_1) - ( 1.622), - (control_1/( 2548)),plant_v1_1,1''%, t [<] Real 16 / 125, Inv) [-->] Inv"
definition cons5 :: fform where "cons5 \<equiv>  exeFlow(%'' plant_v1_1 , plant_m1_1 ,plant_r1_1,t'','' (control_1/plant_m1_1) - ( 1.622), - (control_1/( 2842)),plant_v1_1,1''%, t [<] Real 16 / 125, Inv) [-->] Inv"

(*Put this whole constraint to the differential invariant generator.*)
lemma allCons: "|- cons1 [&] cons2 [&] cons3 [&] cons4 [&] cons5"
apply (simp add: cons1_def)
apply (simp add: cons2_def)
apply (simp add: cons3_def)
apply (simp add: cons4_def)
apply (simp add: cons5_def)
apply (simp add: safeProp_def)
apply (simp add: t_def)
apply (simp add: plant_v1_1_def)
apply (simp add: plant_m1_1_def)
apply (simp add: control_1_def)
apply inv_oracle_SOS
done

lemma constraint11: "t [>=] Real 0 [&] t [<=] Real 16 / 125 [&] Inv |- safeProp"
apply (rule backwards_impR)
apply (cut_tac allCons)
apply (simp add:cons1_def)
apply (rule conjunct1, auto)
done

lemma constraint1: "t [<=] Real 16 / 125 [&] Inv |- safeProp"
apply (cut_tac P = "t [>=] Real 0 [&] t [<=] Real 16 / 125 [&] Inv" in cut, auto)
apply (rule thinR, rule conjR, rule thinL)
apply (rule Clock)
apply fast
apply (rule thinL, rule constraint11)
done



lemma constraint2: "(plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250) [&] control_1[=](Real 4055/2) [&] t[=](Real 0)) |- Inv"
apply (rule backwards_impR)
apply (subgoal_tac "|- cons2 [&] cons3 [&] cons4 [&] cons5")
apply (simp add:cons2_def)
apply (rule conjunct1, auto)
apply (cut_tac allCons)
apply (rule conjunct2, auto)
done 

lemma constraint3: "(t[=](Real 16/125)) [&] Inv |- substF([(t, Real 0)], substF
        ([(control_1,
           plant_m1_1 [*]
           (Real 811 / 500 [-]
            Real 1 / 100 [*]
            (control_1 [**] plant_m1_1 [-]
             Real 811 / 500) [-]
            Real 3 / 5 [*] (plant_v1_1 [+] Real 2)))],
         Inv))"
apply (rule backwards_impR)
apply (subgoal_tac "|- cons3 [&] cons4 [&] cons5")
apply (simp add:cons3_def)
apply (rule conjunct1, auto)
apply (cut_tac allCons)
apply (rule conjunct2)
apply (rule conjunct2)
apply assumption
done 



lemma constraint4: " exeFlow(%'' plant_v1_1 , plant_m1_1 ,plant_r1_1,t'','' (control_1/plant_m1_1) - ( 1.622), - (control_1/( 2548)),plant_v1_1,1''%, t [<] Real 16 / 125, Inv) |- Inv"
apply (rule backwards_impR)
apply (subgoal_tac "|- cons4 [&] cons5")
apply (simp add:cons4_def)
apply (rule conjunct1, auto)
apply (cut_tac allCons)
apply (rule conjunct2)
apply (rule conjunct2)
apply (rule conjunct2)
apply assumption
done 

lemma constraint5: " exeFlow(%'' plant_v1_1 , plant_m1_1 ,plant_r1_1,t'','' (control_1/plant_m1_1) - ( 1.622), - (control_1/( 2842)),plant_v1_1,1''%, t [<] Real 16 / 125, Inv) |- Inv"
apply (rule backwards_impR)
apply (subgoal_tac "|- cons5")
apply (simp add:cons5_def)
apply (cut_tac allCons)
apply (rule conjunct2)
apply (rule conjunct2)
apply (rule conjunct2)
apply (rule conjunct2)
apply assumption
done 



(*Goal for the whole process.*)
lemma goal : "{WTrue} P {safeProp; (l[=](Real 0) [|] (high safeProp))}"
(*mono*)
apply (cut_tac px="WTrue" and qx="t [<=] Real 16 / 125 [&] Inv" and Hx="(l[=](Real 0)) [^] (l[=](Real 0) [|] (high (t [<=] Real 16 / 125 [&] Inv)))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)
apply (rule conjR, rule impR, rule constraint1)
apply (rule impR, rule LL3a)
apply (rule disjL, rule disjR, rule basic)
apply (rule disjR, rule thinR, cut_tac Q="safeProp" in DCM, auto)
apply (rule basic)
apply (rule constraint1)
(*separate into intialization and repetitive control*)
apply (simp add: P_def)
apply (simp add: assertion6_def)
apply (rule Sequence)
(*Init*)
apply (simp add: assertion4_def assertion2_def)
apply (cut_tac px="WTrue" and qx="(plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250) [&] control_1[=](Real 2027.5) [&] t[=](Real 0))" and Hx="(l[=](Real 0)) [^] (l[=](Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (simp add: PC_Init_def assertion1_def assertion2_def)
apply (cut_tac px="WTrue" and qx="(plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250))" and Hx="(l[=](Real 0)) [^] (l[=](Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: plant_v1_1_def)
apply (simp add: plant_v1_1_def, rule Trans, auto)
apply (cut_tac px="plant_v1_1[=](Real -2)" and qx="(plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250))" and Hx="(l[=](Real 0)) [^] (l[=](Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: plant_v1_1_def)
apply (simp add: plant_v1_1_def plant_m1_1_def, rule Trans, auto)
apply (rule Assign)
apply (simp add: plant_v1_1_def plant_m1_1_def plant_r1_1_def)
apply (simp add: plant_v1_1_def plant_m1_1_def plant_r1_1_def, rule Trans, auto)
apply (simp add: PD_Init_def assertion5_def)
apply (cut_tac px="(plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250))" and qx="(plant_v1_1[=](Real -2) [&] plant_m1_1[=](Real 1250) [&] control_1[=](Real 2027.5) [&] t[=](Real 0))" and Hx="(l[=](Real 0)) [^] (l[=](Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: plant_v1_1_def plant_m1_1_def plant_r1_1_def control_1_def)
apply (simp add: plant_v1_1_def plant_m1_1_def plant_r1_1_def control_1_def, rule Trans, auto)
apply (rule Assign)
apply (simp add: plant_v1_1_def plant_m1_1_def plant_r1_1_def control_1_def t_def)
apply (simp add: plant_v1_1_def plant_m1_1_def plant_r1_1_def control_1_def t_def, rule Trans, auto)
(*Rep*)
apply (cut_tac px="Inv [&] t[=](Real 0) [&] t [<=] Real 16 / 125" and qx="Inv [&] t[=](Real 0) [&] t [<=] Real 16 / 125" and Hx="(l[=](Real 0) [|] (high (t [<=] Real 16 / 125 [&] Inv)))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR)
apply (rule conjR, rule constraint2)
apply (rule conjL)+ apply (rule thinL, rule thinL, rule thinL)
apply (simp add:t_def equal_less_def, rule Trans1, auto)
apply (rule conjR) apply fast
apply fast
apply (rule Rep)
prefer 2
apply (rule impR, rule LT1, rule LL3a, rule basic)
apply (rule LT1a, rule LL4, rule disjR, rule basic)
apply (rule disjR, rule thinR)
apply (rule DCR3, rule basic)
(*core of Rep*)
(*seperate Rep into two parts, 
the first part is a sequence of differential equations,
the second part is a sequence of control which does not consume any time.*)
apply (cut_tac px="Inv [&] t[=](Real 0)  [&] t [<=] Real 16 / 125" 
   and qx="Inv [&] t[=](Real 0) [&] t [<=] Real 16 / 125" and
     Hx="((l[=](Real 0) [|] (high (t [<=] Real 16 / 125 [&] Inv)))) [^] (l[=](Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assertion7_def)
apply (rule Sequence)
(*Deal with control part*)
prefer 2
apply (cut_tac px="t[=](Real 16/125) [&] Inv" and qx="Inv [&] t[=](Real 0)" and Hx="(l[=](Real 0)) [^] (l[=](Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule conjR, rule impR, rule conjR)
apply fast apply (simp add: t_def equal_less_def, rule Trans1, auto)
apply (rule impR, rule LL4, rule basic)
apply (unfold assertion8_def)
apply (rule Sequence)
apply (rule Assign)
apply (rule constraint0b)
apply (rule conjR)
apply (subgoal_tac "((t[=](Real 16/125)) [&] Inv) |- substF([(t, Real 0)], substF
        ([(control_1,
           plant_m1_1 [*]
           (Real 811 / 500 [-]
            Real 1 / 100 [*]
            (control_1 [**] plant_m1_1 [-]
             Real 811 / 500) [-]
            Real 3 / 5 [*] (plant_v1_1 [+] Real 2)))],
         Inv))")
prefer 2
apply (rule constraint3)
apply (simp add: t_def control_1_def)
apply (rule impR, rule conjR, simp)
apply (rule thinL, rule Trans, simp)
apply (rule impR, rule basic)
apply (simp add: PD_Rep_def)
apply (rule Assign)
apply (rule constraint0c)
apply (simp add: t_def control_1_def)
apply (rule conjR, rule impR, rule basic)
apply (rule impR, rule basic)
apply (simp add: PC_Diff_def)
apply (cut_tac px="Inv [&] t[=](Real 0) [&] t [<=] Real 16 / 125" and qx="(t[=](Real 16/125))[&]Inv" and Hx="((l[=](Real 0) [|] (high (t [<=] Real 16 / 125 [&] Inv)))) [^] (l[=](Real 0) [|] (high (t [<=] Real 16 / 125 [&] Inv)))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LT1, rule LL3a, rule basic)
apply (rule LT1a, rule LL4, rule disjR, rule basic)
apply (rule disjR, rule thinR)
apply (rule DCR3, rule basic)
(*Deal with plant part*)
apply (cut_tac b="control_1[>](Real 3000)" in Case, auto)
apply (cut_tac m="control_1[>](Real 3000) [&] t[=](Real 0.128) [&] Inv" and H="((l[=](Real 0) [|] (high (t [<=] Real 16 / 125 [&] Inv))))" in Sequence1, auto)
(*1*)
apply (simp add: PC_Diff1_def)
apply (rule Continue2T)
apply (rule conjR, rule impR)
apply (simp add: Inv1_def t_def, rule Trans1, auto)
apply (rule conjR, rule impR)
apply (rule conjR, simp add: Inv1_def t_def control_1_def, rule Trans1, auto)+
apply (cut_tac P="close(Inv)" in cut, auto)
apply (rule conjL)+
apply (simp add: Inv1_def, rule basic)
apply (rule thinL, rule constraint0a)
apply (rule conjR, rule impR, rule conjL, rule disjL, rule disjR, rule basic)
apply (cut_tac Q="t [<=] Real 16 / 125 [&] Inv" in DCM,auto)
apply (rule disjR, rule basic, simp add:Inv1_def equal_less_def)
apply (cut_tac P="t [<=] Real 16 / 125 [&] close(Inv)" in cut, auto)
apply (simp add:equal_less_def)
apply fast apply (rule conjR) apply fast
apply (rule thinL, rule thinL, rule conjL, rule thinL)
apply (rule constraint0a)
apply (simp add:Inv1_def, rule impR)
apply (rule constraint4)
(*2*) 
apply (simp add:PC_Diff2_def)
apply (rule Continue2F)
apply (rule conjR, rule impR, rule Trans1, simp add:t_def)
apply (rule conjR, rule impR) apply fast+
(*The case for control_1 [<=] Real 3000*)
apply (cut_tac m="([~]control_1[>](Real 3000) [&] t[=](Real 0)) [&] Inv" and H="((l[=](Real 0) [|] (high (t [<=] Real 16 / 125 [&] Inv))))" in Sequence1, auto)
apply (simp add:PC_Diff1_def)
apply (rule Continue2F)
apply (rule conjR) apply fast
apply (rule conjR) apply fast+
apply (simp add:PC_Diff2_def)
apply (rule Continue2T)
apply (rule conjR, rule impR)
apply (simp add:equal_less_def Inv2_def)
apply (simp add:t_def, rule Trans1, auto)
apply (rule conjR, rule impR, rule conjL, rule conjL, rule conjL, rule thinL, rule thinL)
apply (rule conjR, rule thinL, rule Trans1, simp add:t_def, auto)
apply (simp add:Inv2_def)
apply (cut_tac P="close(Inv)" in cut, auto) apply fast
apply (rule thinL, rule thinL, rule constraint0a)
apply (rule conjR, rule impR, simp add:Inv2_def)
apply (rule conjL, simp add:equal_less_def) apply (rule disjL) apply fast
apply (rule disjR, rule thinR, rule exchL, rule thinL, rule DC18) apply fast
apply (simp add:Inv2_def)
apply (rule impR, rule constraint5)
done


end
