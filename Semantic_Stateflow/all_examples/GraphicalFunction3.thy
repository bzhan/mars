theory GraphicalFunction3
  imports "../Final_ML" 
begin

definition Chart_B :: state where " Chart_B = State [''B'']
  ((((print1 ''en_B'' );([[V ''x'', ([[V ''y'', No_Expr]])]])::= ''square''<<([[V ''x'', ([[V ''y'', No_Expr]])]])>>);print2 (V ''x''));print2 (V ''x''))
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart_A :: state where " Chart_A = State [''A'']
  ((print1 ''en_A'' ); ((([[V '''', No_Expr]])::=''find''<<([[N 4, No_Expr]])>>)))
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'']) (S []) ((V '''') [==] (N 3)) (SKIP) (SKIP) (P [''B''])]
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''B'' then Chart_B else 
if str = ''A'' then Chart_A else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''2''] then [Trans (J [''2'']) (S []) (((V ''i'') [<=] (V ''N'')) && ((V ''a'') [<=] (N 2))) (SKIP) (SKIP) (J [''5'']),
Trans (J [''2'']) (S []) ((V ''i'') [>] (V ''N'')) (SKIP) (SKIP) (J [''10'']),
Trans (J [''2'']) (S []) (Bc True) (''index'' ::= V ''i'') (SKIP) (J [''12''])] else 
if str = [''10''] then [Trans (J [''10'']) (S []) (Bc True) (''index'' ::= N (-1)) (SKIP) (J [''12''])] else 
if str = [''12''] then [] else 
if str = [''5''] then [Trans (J [''5'']) (S []) (Bc True) ((''i'' ::= Plus (V ''i'') (N 1)); (''a'' ::= Plus (V ''a'') (N 1))) (SKIP) (J [''6''])] else 
if str = [''6''] then [Trans (J [''6'']) (S []) (Bc True) (SKIP) (SKIP) (J [''2''])] else 
if str = [''30''] then [Trans (J [''30'']) (S []) (Bc True) (''r'' ::= Multiply (V ''i1'') (V ''i1'')) (SKIP) (J [''33''])] else 
if str = [''33''] then [Trans (J [''33'']) (S []) (Bc True) (''s'' ::= Multiply (V ''j1'') (V ''j1'')) (SKIP) (J [''34''])] else 
if str = [''34''] then [] else 
[])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) (λx. []) ([],[]) "

definition I :: ctxt where 
"I str = (Info False [] [])"
definition fe::fenv where " 
fe str = (if str = ''f'' then (print1 ''test'' ,
([[V ''s'', No_Expr]]),
No_Expr) else 
(SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (if str = ''find'' then ((Trans (NONE) (S []) (Bc True) ((''i'' ::= N 1); (''a'' ::= N 1)) (SKIP) (J [''2''])),
([[V ''N'', No_Expr]]),
([[V ''index'', No_Expr]])) else 
if str = ''square'' then ((Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (J [''30''])),
([[V ''i1'', ([[V ''j1'', No_Expr]])]]),
([[V ''r'', ([[V ''s'', No_Expr]])]])) else 
((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text\<open>EXECUTION PROOF\<close>
schematic_goal "Root_Exec_for_times env ['''', ''''] (2::int) s
 (Status (Vals ?v1 ?v2 ?v3 ?v4 ([''en_A'', ''en_B''], ?o2)) (?I))"
  unfolding Chart_B_def Chart_A_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def 
  by stateflow_execution2

end