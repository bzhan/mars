theory Trans_State2State
  imports Final_ML 
begin

definition Chart_On :: state where " Chart_On = State [''On'']
  (print1 ''Entry_On'' )
  (print1 ''During_On'' )
  (print1 ''Exit_On'' )
  []
  [Trans (P [''On'']) (S [''E_one'']) (Bc True) (SKIP) (send1 ''E_one'' True) (P [''Off''])]
  (No_Composition)"

definition Chart_Off :: state where " Chart_Off = State [''Off'']
  (print1 ''Entry_Off'' )
  (print1 ''During_Off'' )
  (print1 ''Exit_Off'' )
  []
  [Trans (P [''Off'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (P [''On''])]
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''On'' then Chart_On else 
if str = ''Off'' then Chart_Off else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''On''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. [])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) ([],[]) "

definition I :: ctxt where 
"I str = (Info False [] [])"
definition fe::fenv where " 
fe str = ((SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text‹EXECUTION PROOF›
schematic_goal "Root_Exec_for_times env ''E_one'' (2::int) s ?s"
  unfolding Chart_On_def Chart_Off_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def 
  by stateflow_execution2

end