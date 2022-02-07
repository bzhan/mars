theory Function1
  imports Final_ML 
begin

definition Chart_A :: state where " Chart_A = State [''A'']
  ((print1 ''en_A''); ((([[V '''', No_Expr]])::= ''compute''<([[N 3, No_Expr]])>)) )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'']) (S []) ((V '''') [==] (N 15)) (SKIP) (SKIP) (P [''B''])]
  (No_Composition)"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''en_B'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''B'' then Chart_B else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. [])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) ([],[]) "

definition I :: ctxt where 
"I str = (Info False [] [])"
definition fe::fenv where " 
fe str = (if str = ''compute'' then ((''y'' ::= Plus (V ''x'') (N 1)); ((''z'' ::= Multiply (V ''y'') (V ''y'')); (''y'' ::= Minus (V ''z'') (N 1))),
([[V ''x'', No_Expr]]),
([[V ''y'', No_Expr]])) else 
if str = ''f'' then (print1 ''test'' ,
([[V ''s'', No_Expr]]),
No_Expr) else 
(SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text‹EXECUTION PROOF›
schematic_goal "Root_Exec_for_times env '''' (2::int) s ?s"
  unfolding Chart_A_def Chart_B_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def 
  by stateflow_execution2

end