theory EarlyReturn17
  imports "../Final_ML" 
begin

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (print1 ''en_A1'' )
  (SKIP)
  (print1 ''ex_A1'' )
  []
  [Trans (P [''A'', ''A1'']) (S [''E'']) ((V ''x'') [>] (N 0)) (SKIP) (SKIP) (P [''A'', ''A3'']), Trans (P [''A'', ''A1'']) (S []) ((V ''x'') [>] (N 0)) (print1 ''outA1'' ) (SKIP) (J [''A'', ''12'']), Trans (P [''A'', ''A1'']) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A2''])]
  (No_Composition)"

definition Chart_A_A4 :: state where " Chart_A_A4 = State [''A'', ''A4'']
  (print1 ''en_A4'' )
  (SKIP)
  (print1 ''ex_A4'' )
  []
  []
  (No_Composition)"

definition Chart_A_A3 :: state where " Chart_A_A3 = State [''A'', ''A3'']
  (print1 ''en_A3'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart_A_A2 :: state where " Chart_A_A2 = State [''A'', ''A2'']
  (print1 ''en_A2'' )
  (SKIP)
  (print1 ''ex_A2'' )
  []
  [Trans (P [''A'', ''A2'']) (S [''E'']) ((V ''x'') [<] (N 0)) (SKIP) (SKIP) (P [''A'', ''A3'']), Trans (P [''A'', ''A2'']) (S []) ((V ''x'') [<] (N 0)) (print1 ''outA2'' ) (SKIP) (J [''A'', ''12''])]
  (No_Composition)"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. if str = ''A1'' then Chart_A_A1 else 
if str = ''A4'' then Chart_A_A4 else 
if str = ''A3'' then Chart_A_A3 else 
if str = ''A2'' then Chart_A_A2 else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''en_A'' )
  (SKIP)
  (print1 ''ex_A'' )
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (''x'' ::= N (-1)) (SKIP) (P [''A'', ''A1''])])
 (False) (f_Chart_A))"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''A'', ''12''] then [Trans (J [''A'', ''12'']) (S []) (Bc True) ((send1 ''E'' False); (print1 ''E'' )) (SKIP) (P [''A'', ''A4''])] else 
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
schematic_goal "Root_Exec_for_times env ['''', ''''] (3::int) s
 (Status (Vals ?v1 ?v2 ?v3 ?v4 ([''en_A'', ''en_A1'', ''ex_A1'', ''en_A2'', ''outA2'', ''ex_A2'', ''en_A3''], ?o2)) (?I))"
  unfolding Chart_A_A1_def Chart_A_A4_def Chart_A_A3_def Chart_A_A2_def f_Chart_A_def 
Chart_A_def f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end