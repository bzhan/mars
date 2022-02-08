theory HistoryJunction1
  imports Final_ML 
begin

definition Chart_B_B1 :: state where " Chart_B_B1 = State [''B'', ''B1'']
  (print1 ''Entry B1'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'', ''B1'']) (S []) (Bc True) (''x'' ::= Plus (V ''x'') (N 1)) (SKIP) (P [''B'', ''B2''])]
  (No_Composition)"

definition Chart_B_B2 :: state where " Chart_B_B2 = State [''B'', ''B2'']
  (print1 ''Entry B2'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'', ''B2'']) (S []) (Bc True) (''x'' ::= Plus (V ''x'') (N 1)) (SKIP) (P [''B'', ''B4''])]
  (No_Composition)"

definition Chart_B_B3 :: state where " Chart_B_B3 = State [''B'', ''B3'']
  (print1 ''Entry B3'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'', ''B3'']) (S []) (Bc True) (''x'' ::= Plus (V ''x'') (N 1)) (SKIP) (P [''B'', ''B1''])]
  (No_Composition)"

definition Chart_B_B4 :: state where " Chart_B_B4 = State [''B'', ''B4'']
  (print1 ''Entry B4'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'', ''B4'']) (S []) (Bc True) (''x'' ::= Plus (V ''x'') (N 1)) (SKIP) (P [''B'', ''B3''])]
  (No_Composition)"

definition f_Chart_B :: string2state where 
" f_Chart_B = 
(λstr. if str = ''B1'' then Chart_B_B1 else 
if str = ''B2'' then Chart_B_B2 else 
if str = ''B3'' then Chart_B_B3 else 
if str = ''B4'' then Chart_B_B4 else 
No_State )"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''Entry B'' )
  (print1 ''During B'' )
  (print1 ''Exit B'' )
  []
  [Trans (P [''B'']) (S []) ((V ''x'') [>] (N 1)) (SKIP) (SKIP) (P [''A''])]
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''B'', ''B1''])])
 (True) (f_Chart_B))"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''Entry A'' )
  (print1 ''During A'' )
  (print1 ''Exit A'' )
  []
  [Trans (P [''A'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (P [''B''])]
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''B'' then Chart_B else 
if str = ''A'' then Chart_A else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''x'' ::= N 0) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''B'', ''14''] then [] else 
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
  unfolding Chart_B_B1_def Chart_B_B2_def Chart_B_B3_def Chart_B_B4_def f_Chart_B_def 
Chart_B_def Chart_A_def f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def 
s_def 
  apply simp
  by stateflow_execution2

end