theory Messages2
  imports "../Final_ML" 
begin

definition Chart_A :: state where " Chart_A = State [''A'']
  (((((((print1 ''en_A'' );''M1'' ::= N 4);send3 ''M1'' );''M'' ::= N 3);send3 ''M'' );''M1'' ::= N 3);send3 ''M1'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'']) (M ''M'') ((V ''M'') [==] (N 3)) (SKIP) (SKIP) (P [''B''])]
  (No_Composition)"

definition Chart_B :: state where " Chart_B = State [''B'']
  ((print1 ''en_B'' );''y'' ::= N 1)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'']) (M ''M1'') ((V ''M1'') [==] (N 4)) (SKIP) (SKIP) (P [''C''])]
  (No_Composition)"

definition Chart_C :: state where " Chart_C = State [''C'']
  ((print1 ''en_C'' );''y'' ::= N 2)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''C'']) (M ''M1'') ((V ''M1'') [==] (N 3)) (SKIP) (SKIP) (P [''D''])]
  (No_Composition)"

definition Chart_D :: state where " Chart_D = State [''D'']
  (print1 ''en_D'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''B'' then Chart_B else 
if str = ''C'' then Chart_C else 
if str = ''D'' then Chart_D else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. [])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) (λx. []) ([],[]) "

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
text\<open>EXECUTION PROOF\<close>
schematic_goal "Root_Exec_for_times env ['''', ''''] (4::int) s
 (Status (Vals ?v1 ?v2 ?v3 ?v4 ([''en_A'', ''en_B'', ''en_C'', ''en_D''], ?o2)) (?I))"
  unfolding Chart_A_def Chart_B_def Chart_C_def Chart_D_def f_Chart_def Root_def 
g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end