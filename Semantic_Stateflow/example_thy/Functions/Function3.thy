theory Function3
  imports "../Final_ML" 
begin

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''en_A'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'']) (S []) (Bc True) (No_Expr ::= ''compute''<No_Expr>) (SKIP) (J [''29''])]
  (No_Composition)"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''en_B'' )
  (SKIP)
  (SKIP)
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
" g = (λ str. if str = [''29''] then [Trans (J [''29'']) (S []) (((V ''a1'') [==] (N 0)) && (((V ''a2'') [==] (N 2)) && ((V ''a3'') [==] (N 4)))) (SKIP) (SKIP) (P [''B''])] else 
[])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) (λx. []) ([],[]) "

definition I :: ctxt where 
"I str = (Info False [] [])"
definition fe::fenv where " 
fe str = (if str = ''compute'' then ((''a1'' ::= N 0); ((''a2'' ::= Plus (N 1) (N 1)); (''a3'' ::= Plus (N 2) (N 2))),
No_Expr,
No_Expr) else 
if str = ''f'' then (print1 ''test'' ,
([[V ''s'', No_Expr]]),
No_Expr) else 
(SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text\<open>EXECUTION PROOF\<close>
schematic_goal "Root_Exec_for_times env ['''', ''''] (2::int) s
 (Status (Vals ?v1 ?v2 ?v3 ?v4 ([''en_A'', ''en_B''], ?o2)) (?I))"
  unfolding Chart_A_def Chart_B_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def 
  by stateflow_execution2

end