theory Junctions7
  imports "../../Final_ML"
begin

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''enA'' )
  (SKIP)
  (print1 ''exA'' )
  []
  [Trans (P [''A'']) (S []) ((V ''x'') [>] (N 2)) (SKIP) (print1 ''xge2'' ) (J [''5'']), Trans (P [''A'']) (S []) ((V ''x'') [==] (N 2)) (SKIP) (print1 ''xeq2'' ) (J [''5'']), Trans (P [''A'']) (S []) ((V ''x'') [<] (N 2)) (SKIP) (print1 ''xle2'' ) (J [''5''])]
  (No_Composition)"

definition Chart_C :: state where " Chart_C = State [''C'']
  (print1 ''enC'' )
  (SKIP)
  (print1 ''exC'' )
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''C'' then Chart_C else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) ((''x'' ::= N 1); ((''y'' ::= N 2); (''z'' ::= N 3))) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''5''] then [Trans (J [''5'']) (S []) ((V ''y'') [>] (N 2)) (SKIP) (print1 ''yge2'' ) (J [''15'']),
Trans (J [''5'']) (S []) ((V ''y'') [==] (N 2)) (SKIP) (print1 ''yeq2'' ) (J [''15'']),
Trans (J [''5'']) (S []) ((V ''y'') [<] (N 2)) (SKIP) (print1 ''yle2'' ) (J [''15''])] else 
if str = [''15''] then [Trans (J [''15'']) (S []) ((V ''z'') [>] (N 2)) (SKIP) (print1 ''zge2'' ) (P [''C'']),
Trans (J [''15'']) (S []) ((V ''z'') [==] (N 2)) (SKIP) (print1 ''zeq2'' ) (P [''C'']),
Trans (J [''15'']) (S []) ((V ''z'') [<] (N 2)) (SKIP) (print1 ''zle2'' ) (P [''C''])] else 
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
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text‹EXECUTION PROOF›
schematic_goal "Root_Exec_for_times env '''' (2::int) s ?s"
  unfolding Chart_A_def Chart_C_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def
  by stateflow_execution2

end