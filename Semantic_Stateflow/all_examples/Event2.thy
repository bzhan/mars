theory Event2
  imports "../Final_ML" 
begin

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'', ''A1'']) (S [''E'']) (Bc True) (print1 ''a'' ) (SKIP) (P [''A'', ''A2''])]
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
  [Trans (P [''B'', ''B1'']) (S []) (Bc True) (print1 ''b'' ) ((send1 ''E'' True); (print1 ''tb'' )) (P [''B'', ''B2''])]
  (No_Composition)"

definition Chart_B_B2 :: state where " Chart_B_B2 = State [''B'', ''B2'']
  (print1 ''en_B2'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_B :: string2state where 
" f_Chart_B = 
(λstr. if str = ''B1'' then Chart_B_B1 else 
if str = ''B2'' then Chart_B_B2 else 
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
  [Trans (P [''C'', ''C1'']) (S [''E'']) (Bc True) (print1 ''c'' ) (SKIP) (P [''C'', ''C2''])]
  (No_Composition)"

definition Chart_C_C2 :: state where " Chart_C_C2 = State [''C'', ''C2'']
  (print1 ''en_C2'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_C :: string2state where 
" f_Chart_C = 
(λstr. if str = ''C1'' then Chart_C_C1 else 
if str = ''C2'' then Chart_C_C2 else 
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
" g = (λ str. [])"

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
schematic_goal "Root_Exec_for_times env ['''', ''''] (2::int) s
 (Status (Vals ?v1 ?v2 ?v3 ?v4 ([''b'', ''a'', ''en_A2'', ''c'', ''en_C2'', ''tb'', ''en_B2''], ?o2)) (?I))"
  unfolding Chart_A_A1_def Chart_A_A2_def f_Chart_A_def Chart_A_def Chart_B_B1_def 
Chart_B_B2_def f_Chart_B_def Chart_B_def Chart_C_C1_def Chart_C_C2_def f_Chart_C_def 
Chart_C_def f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end