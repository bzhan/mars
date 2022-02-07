theory DirectedEvent6
  imports Final_ML 
begin

definition Chart1_A :: state where " Chart1_A = State [''A'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'']) (S []) ((V ''data'') [==] (N 1)) ((''data'' ::= N 2); ((print1 ''a'' ); ((send2 ''F'' False [''A''] ); (print1 ''b'' )))) (SKIP) (P [''B'']), Trans (P [''A'']) (S [''F'']) (Bc True) (print1 ''c'' ) (SKIP) (P [''C''])]
  (No_Composition)"

definition Chart1_B :: state where " Chart1_B = State [''B'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart1_C_C1 :: state where " Chart1_C_C1 = State [''C'', ''C1'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''C'', ''C1'']) (S [''F'']) (Bc True) (print1 ''d'' ) (SKIP) (P [''C'', ''C2''])]
  (No_Composition)"

definition Chart1_C_C2 :: state where " Chart1_C_C2 = State [''C'', ''C2'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart1_C :: string2state where 
" f_Chart1_C = 
(λstr. if str = ''C1'' then Chart1_C_C1 else 
if str = ''C2'' then Chart1_C_C2 else 
No_State )"

definition Chart1_C :: state where " Chart1_C = State [''C'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''C'', ''C1''])])
 (False) (f_Chart1_C))"

definition f_Chart1 :: string2state where 
" f_Chart1 = 
(λstr. if str = ''A'' then Chart1_A else 
if str = ''B'' then Chart1_B else 
if str = ''C'' then Chart1_C else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''data'' ::= N 1) (SKIP) (P [''A''])])
 (False) (f_Chart1)"

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
  unfolding Chart1_A_def Chart1_B_def Chart1_C_C1_def Chart1_C_C2_def f_Chart1_C_def 
Chart1_C_def f_Chart1_def Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end