theory Trans_State2State
  imports Send_Total_ML 
begin

definition Chart_On :: State where " Chart_On = state [''On'']
  (print1 ''Entry_On'' )
  (print1 ''During_On'' )
  (print1 ''Exit_On'' )
  []
  [Trans (P [''On'']) (S [''E_one'']) (Bc True) (SKIP) (send1 ''E_one'' True) (P [''Off''])]
  No_Composition"

definition Chart_Off :: State where " Chart_Off = state [''Off'']
  (print1 ''Entry_Off'' )
  (print1 ''During_Off'' )
  (print1 ''Exit_Off'' )
  []
  [Trans (P [''Off'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (P [''On''])]
  No_Composition"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''On'' then Chart_On else 
if str = ''Off'' then Chart_Off else 
No_State )"

definition Root :: Composition where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''On''])])
 (False) (f_Chart)"

definition g :: path2trans where 
" g = (λ str. [])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) ([],[]) "

definition Chart :: Path_Info where 
"Chart str = (if str = [''On''] then (Info False None None) else
if str = [''Off''] then (Info False None None) else
if str = [] then (Info False (Some []) (Some [])) else
(Info False None None))"

text‹EXECUTION PROOF›
schematic_goal "root_execution_for_times Root '''' (2::int) Chart v g ?Chart2 ?v2"
  unfolding Chart_On_def Chart_Off_def f_Chart_def Root_def g_def v_def Chart_def 

  apply simp
  by stateflow_execution2

end