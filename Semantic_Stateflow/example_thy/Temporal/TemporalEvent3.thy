theory TemporalEvent3
  imports "../Final_ML" 
begin

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (print1 ''Entry A1'' )
  (SKIP)
  (print1 ''Exit A1'' )
  []
  [Trans (P [''A'', ''A1'']) (S []) (Bc True) (SKIP) (SKIP) (J [''B'', ''6''])]
  (No_Composition)"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. if str = ''A1'' then Chart_A_A1 else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''Entry A'' )
  (print1 ''During A'' )
  (print1 ''Exit A'' )
  []
  [Trans (P [''A'']) (T1 (After (''E'') (N 3))) (Bc True) (SKIP) (SKIP) (P [''B''])]
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A1''])])
 (False) (f_Chart_A))"

definition f_Chart_B :: string2state where 
" f_Chart_B = 
(λstr. No_State )"

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

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''B'', ''6''] then [Trans (J [''B'', ''6'']) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A1''])] else 
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
schematic_goal "Root_Exec_for_times env [''E'', ''E'', ''E'', ''E''] (4::int) s
 (Status (Vals ?v1 ?v2 ?v3 ?v4 ([''Entry A'', ''Entry A1'', ''During A'', ''Exit A1'', ''Exit A'', ''Entry A'', ''Entry A1'', ''During A'', ''Exit A1'', ''Exit A'', ''Entry A'', ''Entry A1'', ''During A'', ''Exit A1'', ''Exit A'', ''Entry A'', ''Entry A1''], ?o2)) (?I))"
  unfolding Chart_A_A1_def f_Chart_A_def Chart_A_def f_Chart_B_def Chart_B_def f_Chart_def 
Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end