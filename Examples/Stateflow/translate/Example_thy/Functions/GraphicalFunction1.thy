theory GraphicalFunction1
  imports Final_ML 
begin

definition Chart_A :: state where " Chart_A = State [''A'']
  ((print1 ''en_A''); ((([[V '''', No_Expr]])::= ''find''<<No_Expr>>)))
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'']) (S []) ((V '''') [==] (N 4)) (SKIP) (SKIP) (P [''B''])]
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
" g = (λ str. if str = [''2''] then [Trans (J [''2'']) (S []) (((V ''i'') [<=] (N 3)) && ((V ''a'') [<] (N 3))) (SKIP) (SKIP) (J [''5'']),
Trans (J [''2'']) (S []) ((V ''i'') [>] (N 4)) (SKIP) (SKIP) (J [''10'']),
Trans (J [''2'']) (S []) (Bc True) (''index'' ::= V ''i'') (SKIP) (J [''12''])] else 
if str = [''10''] then [Trans (J [''10'']) (S []) (Bc True) (''index'' ::= N (-1)) (SKIP) (J [''12''])] else 
if str = [''12''] then [] else 
if str = [''5''] then [Trans (J [''5'']) (S []) (Bc True) ((''i'' ::= Plus (V ''i'') (N 1)); (''a'' ::= Plus (V ''a'') (N 1))) (SKIP) (J [''6''])] else 
if str = [''6''] then [Trans (J [''6'']) (S []) (Bc True) (SKIP) (SKIP) (J [''2''])] else 
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
ge str = (if str = ''find'' then ((Trans (NONE) (S []) (Bc True) ((''i'' ::= N 1); (''a'' ::= N 0)) (SKIP) (J [''2''])),
No_Expr,
([[V ''index'', No_Expr]])) else 
((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text‹EXECUTION PROOF›
schematic_goal "Root_Exec_for_times env '''' (2::int) s ?s"
  unfolding Chart_A_def Chart_B_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def 
  by stateflow_execution2

end