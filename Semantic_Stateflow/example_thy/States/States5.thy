theory States5
  imports "../../Final_ML"
begin

definition Chart_A_A2 :: state where " Chart_A_A2 = State [''A'', ''A2'']
  (print1 ''enA2'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'', ''A2'']) (S []) (Bc True) (''x'' ::= Plus (V ''x'') (N 1)) (SKIP) (P [''A'', ''A1''])]
  (No_Composition)"

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (print1 ''enA1'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'', ''A1'']) (S []) (Bc True) (''x'' ::= Plus (V ''x'') (N 1)) (SKIP) (P [''A'', ''A2''])]
  (No_Composition)"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. if str = ''A2'' then Chart_A_A2 else 
if str = ''A1'' then Chart_A_A1 else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'']) (S []) ((V ''x'') [>=] (N 1)) (SKIP) (SKIP) (P [''B''])]
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A1''])])
 (True) (f_Chart_A))"

definition Chart_B_B2 :: state where " Chart_B_B2 = State [''B'', ''B2'']
  (print1 ''enB2'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'', ''B2'']) (S []) (Bc True) (''x'' ::= Minus (V ''x'') (N 1)) (SKIP) (P [''B'', ''B1''])]
  (No_Composition)"

definition Chart_B_B1 :: state where " Chart_B_B1 = State [''B'', ''B1'']
  (print1 ''enB1'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'', ''B1'']) (S []) (Bc True) (''x'' ::= Minus (V ''x'') (N 1)) (SKIP) (P [''B'', ''B2''])]
  (No_Composition)"

definition f_Chart_B :: string2state where 
" f_Chart_B = 
(λstr. if str = ''B2'' then Chart_B_B2 else 
if str = ''B1'' then Chart_B_B1 else 
No_State )"

definition Chart_B :: state where " Chart_B = State [''B'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'']) (S []) ((V ''x'') [<=] (N 0)) (SKIP) (SKIP) (P [''A''])]
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''B'', ''B1''])])
 (False) (f_Chart_B))"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''B'' then Chart_B else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''x'' ::= N 0) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''A'', ''31''] then [] else 
[])"

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
schematic_goal "Root_Exec_for_times env '''' (10::int) s ?s"
  unfolding Chart_A_A2_def Chart_A_A1_def f_Chart_A_def Chart_A_def Chart_B_B2_def 
Chart_B_B1_def f_Chart_B_def Chart_B_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def
  apply simp
  by stateflow_execution2

end