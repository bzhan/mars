theory SelfLoop
  imports "../../Final_ML"
begin

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''Entry A'' )
  (print1 ''During A'' )
  (print1 ''Exit A'' )
  []
  [Trans (P [''A'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (J [''3''])]
  (No_Composition)"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''Entry B'' )
  (print1 ''During B'' )
  (print1 ''Exit B'' )
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''B'' then Chart_B else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''x'' ::= N 0) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''3''] then [Trans (J [''3'']) (S []) ((V ''x'') [>] (N 3)) (SKIP) (print1 ''Transition Action1'' ) (P [''B'']),
Trans (J [''3'']) (S []) (Bc True) (SKIP) (''x'' ::= Plus (V ''x'') (N 1)) (P [''A''])] else 
[])"

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
schematic_goal "Root_Exec_for_times env ''E_one'' (6::int) s ?s"
  unfolding Chart_A_def Chart_B_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def
  by stateflow_execution2

end