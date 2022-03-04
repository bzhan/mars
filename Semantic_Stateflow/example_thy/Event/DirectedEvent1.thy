theory DirectedEvent1
  imports "../../Final_ML"
begin

definition Chart_AM_A_A1 :: state where " Chart_AM_A_A1 = State [''AM'', ''A'', ''A1'']
  (print1 ''en_A1'' )
  (SKIP)
  (print1 ''ex_A1'' )
  []
  [Trans (P [''AM'', ''A'', ''A1'']) (S []) ((V ''data'') [==] (N 1)) (send2 ''E_one'' False [''AM'', ''B'']) (SKIP) (P [''AM'', ''A'', ''A2''])]
  (No_Composition)"

definition Chart_AM_A_A2 :: state where " Chart_AM_A_A2 = State [''AM'', ''A'', ''A2'']
  (print1 ''en_A2'' )
  (SKIP)
  (print1 ''ex_A2'' )
  []
  [Trans (P [''AM'', ''A'', ''A2'']) (S [''E_two'']) (Bc True) (SKIP) (SKIP) (P [''AM'', ''A'', ''A1''])]
  (No_Composition)"

definition f_Chart_AM_A :: string2state where 
" f_Chart_AM_A = 
(λstr. if str = ''A1'' then Chart_AM_A_A1 else 
if str = ''A2'' then Chart_AM_A_A2 else 
No_State )"

definition Chart_AM_A :: state where " Chart_AM_A = State [''AM'', ''A'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''AM'', ''A'', ''A1''])])
 (False) (f_Chart_AM_A))"

definition Chart_AM_B_B1 :: state where " Chart_AM_B_B1 = State [''AM'', ''B'', ''B1'']
  (print1 ''en_B1'' )
  (SKIP)
  (print1 ''ex_B1'' )
  []
  [Trans (P [''AM'', ''B'', ''B1'']) (S [''E_one'']) (Bc True) (send2 ''E_one'' False [''AM'',''C'']) (SKIP) (P [''AM'', ''B'', ''B2''])]
  (No_Composition)"

definition Chart_AM_B_B2 :: state where " Chart_AM_B_B2 = State [''AM'', ''B'', ''B2'']
  (print1 ''en_B2'' )
  (SKIP)
  (print1 ''ex_B2'' )
  []
  [Trans (P [''AM'', ''B'', ''B2'']) (S [''E_two'']) (Bc True) (send2 ''E_two'' False [''AM'', ''A'']) (SKIP) (P [''AM'', ''B'', ''B1''])]
  (No_Composition)"

definition f_Chart_AM_B :: string2state where 
" f_Chart_AM_B = 
(λstr. if str = ''B1'' then Chart_AM_B_B1 else 
if str = ''B2'' then Chart_AM_B_B2 else 
No_State )"

definition Chart_AM_B :: state where " Chart_AM_B = State [''AM'', ''B'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''AM'', ''B'', ''B1''])])
 (False) (f_Chart_AM_B))"

definition Chart_AM_C_C1 :: state where " Chart_AM_C_C1 = State [''AM'', ''C'', ''C1'']
  (print1 ''en_C1'' )
  (SKIP)
  (print1 ''ex_C1'' )
  []
  [Trans (P [''AM'', ''C'', ''C1'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (P [''AM'', ''C'', ''C2''])]
  (No_Composition)"

definition Chart_AM_C_C2 :: state where " Chart_AM_C_C2 = State [''AM'', ''C'', ''C2'']
  (print1 ''en_C2'' )
  (SKIP)
  (print1 ''ex_C2'' )
  []
  [Trans (P [''AM'', ''C'', ''C2'']) (S []) ((V ''data'') [==] (N 1)) (send2 ''E_two'' False [''AM'', ''B'']) (SKIP) (P [''AM'', ''C'', ''C1''])]
  (No_Composition)"

definition f_Chart_AM_C :: string2state where 
" f_Chart_AM_C = 
(λstr. if str = ''C1'' then Chart_AM_C_C1 else 
if str = ''C2'' then Chart_AM_C_C2 else 
No_State )"

definition Chart_AM_C :: state where " Chart_AM_C = State [''AM'', ''C'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''AM'', ''C'', ''C1''])])
 (False) (f_Chart_AM_C))"

definition f_Chart_AM :: string2state where 
" f_Chart_AM = 
(λstr. if str = ''A'' then Chart_AM_A else 
if str = ''B'' then Chart_AM_B else 
if str = ''C'' then Chart_AM_C else 
No_State )"

definition Chart_AM :: state where " Chart_AM = State [''AM'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (And [''A'', ''B'', ''C'']
 (f_Chart_AM))"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''AM'' then Chart_AM else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''data'' ::= N 1) (SKIP) (P [''AM''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. [])"

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
  unfolding Chart_AM_A_A1_def Chart_AM_A_A2_def f_Chart_AM_A_def Chart_AM_A_def Chart_AM_B_B1_def 
Chart_AM_B_B2_def f_Chart_AM_B_def Chart_AM_B_def Chart_AM_C_C1_def Chart_AM_C_C2_def 
f_Chart_AM_C_def Chart_AM_C_def f_Chart_AM_def Chart_AM_def f_Chart_def Root_def 
g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end