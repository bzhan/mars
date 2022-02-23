theory Temporal4
  imports "../../Final_ML"
begin

definition Chart_A :: state where " Chart_A = State [''A'']
  ((print1 ''en_A'') ;''x'' ::= N 1)
  ((print1 ''du_A'') ;''x'' ::= Plus (V ''x'') (N 1))
  (SKIP)
  []
  [Trans (P [''A'']) (T1 (Before (''tick'') (N 4))) ((V ''x'') [>=] (N 3)) (SKIP) (SKIP) (P [''B''])]
  (No_Composition)"

definition Chart_B :: state where " Chart_B = State [''B'']
  ((print1 ''en_B'') ;''x'' ::= N 1)
  ((print1 ''du_B'') ;''x'' ::= Plus (V ''x'') (N 1))
  (SKIP)
  []
  [Trans (P [''B'']) (T1 (Before (''tick'') (N 4))) ((V ''x'') [>=] (N 4)) (SKIP) (SKIP) (P [''A''])]
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
fe str = (if str = ''f'' then (print1 ''test'' ,
([[V ''s'', No_Expr]]),
No_Expr) else 
(SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text‹EXECUTION PROOF›
schematic_goal "Root_Exec_for_times env '''' (11::int) s ?s"
  unfolding Chart_A_def Chart_B_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def
  by stateflow_execution2

end