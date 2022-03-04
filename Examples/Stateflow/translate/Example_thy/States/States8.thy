theory States8
  imports Final_ML 
begin

definition Chart_add :: state where " Chart_add = State [''add'']
  (SKIP)
  (print1 ''du'' )
  (SKIP)
  []
  [Trans (P [''add'']) (S []) ((V ''i'') [<=] (N 5)) ((''i'' ::= Plus (V ''i'') (N 1)); (print1 ''loop'' )) (SKIP) (P [''add''])]
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''add'' then Chart_add else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''i'' ::= N 1) (SKIP) (P [''add''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. [])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) ([],[]) "

definition I :: ctxt where 
"I str = (Info False [] [])"
definition fe::fenv where " 
fe str = (if str = ''f'' then (print1 ''test'' ,
([[V ''s'', No_Expr]]),
No_Expr) else 
(SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text‹EXECUTION PROOF›
schematic_goal "Root_Exec_for_times env '''' (7::int) s ?s"
  unfolding Chart_add_def f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def 
s_def
  by stateflow_execution2

end