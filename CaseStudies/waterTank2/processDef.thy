theory processDef
	imports "ChartPDef"
begin

(*Define continuous processes*)
definition PC1_1 :: proc where
"PC1_1 == Integrator_1:=(Real 4.5)
"
definition commI1 :: proc where
"commI1 == Ch_Add_1_1??Add_1_1
 [[ Ch_Integrator_1_2!!Integrator_1
 [[ Ch_Integrator_1_0!!Integrator_1"
definition domain1 :: fform where
"domain1 == <(diff(Integrator_1)[=]Add_1_1)"
definition PC1_2 :: proc where
"PC1_2 == (<inv1 && domain1>:rg1)
	[[>commI1"
definition PC1_init :: proc where
"PC1_init == PC1_1"
definition PC1_rep :: proc where
"PC1_rep == PC1_2"
definition PC1 :: proc where
"PC1 == PC1_init;assertion1;(PC1_rep)*"

(*Define discrete processes*)
definition PD1_1 :: proc where
"PD1_1 == definition PD1_2 :: proc where
"PD1_2 == fbuf(Cbi_Chart_1_0??bChart_1,Cbo_Chart_1_0!!bChart_1,1,0.001)"
definition PD1_init1 :: proc where
"PD1_init1 == PD1_1"
definition PD1_init :: proc where
"PD1_init == PD1_init1"
definition PD1_rep1 :: proc where
"PD1_rep1 == PD1_2"
definition PD1_rep :: proc where
"PD1_rep == PD1_rep1"
definition PD1 :: proc where
"PD1 == PD1_init;assertion2;(PD1_rep)*"

definition PD2_1 :: proc where
"PD2_1 == t0:=(Real 0)"
definition PD2_2 :: proc where
"PD2_2 == 
Cbo_Chart_1_0??Chart_1_0;assertion3;
Ch_Integrator_1_0??Integrator_1_0;assertion4;
product_1:=((Real 1)[*]Chart_1_0[*](Real 2))"
definition PD2_3 :: proc where
"PD2_3 == 
chacha_1:=((Real 1)[*](Real 19.6)[*]Integrator_1_0);assertion5;
hehe_1:=((Real 1)[*](Real 0.18)[*](Real 0.18));assertion6;
cheng_1:=((Real 1)[*](Real 3.14)[*]hehe_1);assertion7;
shabi_1:=((Real 1)[*]cheng_1[*]chacha_1);assertion8;
Add_1:=((Real 0)[+]product_1[-]shabi_1)"
definition PD2_4 :: proc where
"PD2_4 == 
Ch_Add_1_1!!Add_1"
definition PD2_5 :: proc where
"PD2_5 == temp0:=t0;assertion9; <(WTrue) && (t0[<]temp0[+](Real 0.001))>:(l[=](Real 0.001))"
definition PD2_6 :: proc where
"PD2_6 == Cbo_Chart_1_0??Chart_1_0;assertion10;
Ch_Integrator_1_0??Integrator_1_0;assertion11;
product_1:=((Real 1)[*]Chart_1_0[*](Real 2))"
definition PD2_7 :: proc where
"PD2_7 == 
chacha_1:=((Real 1)[*](Real 19.6)[*]Integrator_1_0);assertion12;
hehe_1:=((Real 1)[*](Real 0.18)[*](Real 0.18));assertion13;
cheng_1:=((Real 1)[*](Real 3.14)[*]hehe_1);assertion14;
shabi_1:=((Real 1)[*]cheng_1[*]chacha_1);assertion15;
Add_1:=((Real 0)[+]product_1[-]shabi_1)"
definition PD2_8 :: proc where
"PD2_8 == 
Ch_Add_1_1!!Add_1"
definition PD2_init1 :: proc where
"PD2_init1 == PD2_1"
definition PD2_init2 :: proc where
"PD2_init2 == PD2_2"
definition PD2_init3 :: proc where
"PD2_init3 == PD2_3"
definition PD2_init4 :: proc where
"PD2_init4 == PD2_4"
definition PD2_init :: proc where
"PD2_init == PD2_init1;assertion16;PD2_init2;assertion17;PD2_init3;assertion18;PD2_init4"
definition PD2_rep1 :: proc where
"PD2_rep1 == PD2_5"
definition PD2_rep2 :: proc where
"PD2_rep2 == PD2_6"
definition PD2_rep3 :: proc where
"PD2_rep3 == PD2_7"
definition PD2_rep4 :: proc where
"PD2_rep4 == PD2_8"
definition PD2_rep :: proc where
"PD2_rep == PD2_rep1;assertion19;PD2_rep2;assertion20;PD2_rep3;assertion21;PD2_rep4"
definition PD2 :: proc where
"PD2 == PD2_init;assertion22;(PD2_rep)*"

(*Define the whole process.*)
definition P :: proc where
"P == PC1||PD1||PD2||PChart"
end
