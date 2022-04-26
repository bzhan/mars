theory FlowChartNotation
  imports "../Final_ML" 
begin

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (print1 ''Entry A1'' )
  (print1 ''During A1'' )
  (print1 ''Exit A1'' )
  []
  []
  (No_Composition)"

definition Chart_A_A2 :: state where " Chart_A_A2 = State [''A'', ''A2'']
  (print1 ''Entry A2'' )
  (print1 ''During A2'' )
  (print1 ''Exit A2'' )
  []
  []
  (No_Composition)"

definition Chart_A_A3 :: state where " Chart_A_A3 = State [''A'', ''A3'']
  (print1 ''Entry A3'' )
  (print1 ''During A3'' )
  (print1 ''Exit A3'' )
  []
  []
  (No_Composition)"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. if str = ''A1'' then Chart_A_A1 else 
if str = ''A2'' then Chart_A_A2 else 
if str = ''A3'' then Chart_A_A3 else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''Entry A'' )
  (print1 ''During A'' )
  (print1 ''Exit A'' )
  [Trans (P [''A'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (J [''A'', ''3''])]
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (J [''A'', ''3''])])
 (False) (f_Chart_A))"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''x'' ::= N 0) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''A'', ''3''] then [Trans (J [''A'', ''3'']) (S []) (Bc True) (''x'' ::= Plus (V ''x'') (N 1)) (SKIP) (J [''A'', ''9''])] else 
if str = [''A'', ''9''] then [Trans (J [''A'', ''9'']) (S []) ((V ''x'') [<] (N 3)) (''x'' ::= Plus (V ''x'') (N 1)) (SKIP) (J [''A'', ''9'']),
Trans (J [''A'', ''9'']) (S []) (Bc True) (SKIP) (SKIP) (J [''A'', ''10''])] else 
if str = [''A'', ''10''] then [Trans (J [''A'', ''10'']) (S []) ((V ''x'') [>] (N 6)) (SKIP) (SKIP) (P [''A'', ''A1'']),
Trans (J [''A'', ''10'']) (S []) ((V ''x'') [>] (N 4)) (SKIP) (SKIP) (P [''A'', ''A3'']),
Trans (J [''A'', ''10'']) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A2''])] else 
[])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) (λx. []) ([],[]) "

definition I :: ctxt where 
"I str = (Info False [] [])"
definition fe::fenv where " 
fe str = ((SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text\<open>EXECUTION PROOF\<close>
schematic_goal "Root_Exec_for_times env [''E_one'', ''E_one'', ''E_one''] (3::int) s
 (Status (Vals ?v1 ?v2 ?v3 ?v4 ([''Entry A'', ''Entry A2'', ''During A'', ''Exit A2'', ''Entry A2'', ''During A'', ''Exit A2'', ''Entry A3''], ?o2)) (?I))"
  unfolding Chart_A_A1_def Chart_A_A2_def Chart_A_A3_def f_Chart_A_def Chart_A_def 
f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end