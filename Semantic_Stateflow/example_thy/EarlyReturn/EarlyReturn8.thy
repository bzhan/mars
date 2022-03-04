theory EarlyReturn8
  imports "../../Final_ML"
begin

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (SKIP)
  (print1 ''du_A1'' )
  (print1 ''ex_A1'' )
  []
  [Trans (P [''A'', ''A1'']) (S []) (Bc True) (print1 ''a'' ) (SKIP) (J [''A'', ''34'']), Trans (P [''A'', ''A1'']) (S []) (Bc True) (print1 ''c'' ) (SKIP) (J [''A'', ''40''])]
  (No_Composition)"

definition Chart_A_A2 :: state where " Chart_A_A2 = State [''A'', ''A2'']
  (print1 ''en_A2'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. if str = ''A1'' then Chart_A_A1 else 
if str = ''A2'' then Chart_A_A2 else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (''x'' ::= N (-1)) (SKIP) (P [''A'', ''A1''])])
 (False) (f_Chart_A))"

definition Chart_B_B1 :: state where " Chart_B_B1 = State [''B'', ''B1'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'', ''B1'']) (S [''E'']) (Bc True) (SKIP) (SKIP) (P [''B'', ''B3'']), Trans (P [''B'', ''B1'']) (S []) (Bc True) (print1 ''b'' ) ((send1 ''E'' True); (print1 ''tb'' )) (P [''B'', ''B2''])]
  (No_Composition)"

definition Chart_B_B2 :: state where " Chart_B_B2 = State [''B'', ''B2'']
  (print1 ''en_B2'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart_B_B3 :: state where " Chart_B_B3 = State [''B'', ''B3'']
  (print1 ''en_B3'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_B :: string2state where 
" f_Chart_B = 
(λstr. if str = ''B1'' then Chart_B_B1 else 
if str = ''B2'' then Chart_B_B2 else 
if str = ''B3'' then Chart_B_B3 else 
No_State )"

definition Chart_B :: state where " Chart_B = State [''B'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''B'', ''B1''])])
 (False) (f_Chart_B))"

definition Chart_C_C1 :: state where " Chart_C_C1 = State [''C'', ''C1'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''C'', ''C1'']) (S []) (Bc True) (SKIP) (SKIP) (P [''C'', ''C2''])]
  (No_Composition)"

definition Chart_C_C2 :: state where " Chart_C_C2 = State [''C'', ''C2'']
  (print1 ''en_C2'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''C'', ''C2'']) (S []) (Bc True) (SKIP) (SKIP) (P [''C'', ''C3''])]
  (No_Composition)"

definition Chart_C_C3 :: state where " Chart_C_C3 = State [''C'', ''C3'']
  (print1 ''en_C3'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_C :: string2state where 
" f_Chart_C = 
(λstr. if str = ''C1'' then Chart_C_C1 else 
if str = ''C2'' then Chart_C_C2 else 
if str = ''C3'' then Chart_C_C3 else 
No_State )"

definition Chart_C :: state where " Chart_C = State [''C'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''C'', ''C1''])])
 (False) (f_Chart_C))"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''B'' then Chart_B else 
if str = ''C'' then Chart_C else 
No_State )"

definition Root :: comp where " Root = And [''A'', ''B'', ''C'']
 (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''A'', ''34''] then [Trans (J [''A'', ''34'']) (S []) ((V ''x'') [>] (N 0)) (SKIP) (SKIP) (J [''A'', ''35''])] else 
if str = [''A'', ''35''] then [Trans (J [''A'', ''35'']) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A2''])] else 
if str = [''A'', ''40''] then [Trans (J [''A'', ''40'']) (S [''E'']) (Bc True) (SKIP) (SKIP) (J [''A'', ''41''])] else 
if str = [''A'', ''41''] then [Trans (J [''A'', ''41'']) (S [''E'']) (Bc True) (SKIP) (SKIP) (P [''A'', ''A2''])] else 
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
schematic_goal "Root_Exec_for_times env '''' (2::int) s ?s"
  unfolding Chart_A_A1_def Chart_A_A2_def f_Chart_A_def Chart_A_def Chart_B_B1_def 
Chart_B_B2_def Chart_B_B3_def f_Chart_B_def Chart_B_def Chart_C_C1_def Chart_C_C2_def 
Chart_C_C3_def f_Chart_C_def Chart_C_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def 
  by stateflow_execution2

end