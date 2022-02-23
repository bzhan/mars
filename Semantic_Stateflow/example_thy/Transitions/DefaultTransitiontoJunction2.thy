theory DefaultTransitiontoJunction2
  imports "../../Final_ML"
begin

definition Chart_B_B1_B1a :: state where " Chart_B_B1_B1a = State [''B'', ''B1'', ''B1a'']
  (print1 ''Entry B1a'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_B_B1 :: string2state where 
" f_Chart_B_B1 = 
(λstr. if str = ''B1a'' then Chart_B_B1_B1a else 
No_State )"

definition Chart_B_B1 :: state where " Chart_B_B1 = State [''B'', ''B1'']
  (print1 ''Entry B1'' )
  (SKIP)
  (SKIP)
  []
  []
  (Or ([])
 (False) (f_Chart_B_B1))"

definition Chart_B_B2_B2b :: state where " Chart_B_B2_B2b = State [''B'', ''B2'', ''B2b'']
  (print1 ''Entry B2b'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart_B_B2_B2a :: state where " Chart_B_B2_B2a = State [''B'', ''B2'', ''B2a'']
  (print1 ''Entry B2a'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'', ''B2'', ''B2a'']) (S []) ((V ''x'') [>] (N (-1))) (SKIP) (SKIP) (P [''B'', ''B1'', ''B1a''])]
  (No_Composition)"

definition f_Chart_B_B2 :: string2state where 
" f_Chart_B_B2 = 
(λstr. if str = ''B2b'' then Chart_B_B2_B2b else 
if str = ''B2a'' then Chart_B_B2_B2a else 
No_State )"

definition Chart_B_B2 :: state where " Chart_B_B2 = State [''B'', ''B2'']
  (print1 ''Entry B2'' )
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''B'', ''B2'', ''B2b''])])
 (False) (f_Chart_B_B2))"

definition f_Chart_B :: string2state where 
" f_Chart_B = 
(λstr. if str = ''B1'' then Chart_B_B1 else 
if str = ''B2'' then Chart_B_B2 else 
No_State )"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''Entry B'' )
  (print1 ''During B'' )
  (print1 ''Exit B'' )
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (J [''B'', ''5''])])
 (False) (f_Chart_B))"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''Entry A'' )
  (print1 ''During A'' )
  (print1 ''Exit A'' )
  []
  [Trans (P [''A'']) (S []) ((V ''x'') [>] (N (-5))) (SKIP) (SKIP) (P [''B''])]
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''B'' then Chart_B else 
if str = ''A'' then Chart_A else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''x'' ::= N 0) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''B'', ''5''] then [Trans (J [''B'', ''5'']) (S []) ((V ''x'') [>] (N 0)) (SKIP) (SKIP) (P [''B'', ''B1'', ''B1a'']),
Trans (J [''B'', ''5'']) (S []) (Bc True) (SKIP) (SKIP) (P [''B'', ''B2'', ''B2a''])] else 
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
schematic_goal "Root_Exec_for_times env '''' (3::int) s ?s"
  unfolding Chart_B_B1_B1a_def f_Chart_B_B1_def Chart_B_B1_def Chart_B_B2_B2b_def 
Chart_B_B2_B2a_def f_Chart_B_B2_def Chart_B_B2_def f_Chart_B_def Chart_B_def Chart_A_def 
f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end