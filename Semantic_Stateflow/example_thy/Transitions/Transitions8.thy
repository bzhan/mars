theory Transitions8
  imports "../../Final_ML"
begin

definition Chart_S :: state where " Chart_S = State [''S'']
  (print1 ''enS'' )
  (print1 ''duS'' )
  (SKIP)
  [Trans (P [''S'']) (S []) ((V ''x'') [<] (N 3)) ((print1 ''ca1'' ); (''x'' ::= Plus (V ''x'') (N 1))) (SKIP) (P [''S'']), Trans (P [''S'']) (S []) (Bc True) ((print1 ''ca2'' ); (''x'' ::= Plus (V ''x'') (N 1))) (SKIP) (P [''S''])]
  [Trans (P [''S'']) (S []) ((V ''x'') [>=] (N 5)) (SKIP) (SKIP) (P [''T''])]
  (No_Composition)"

definition Chart_T :: state where " Chart_T = State [''T'']
  (print1 ''enT'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''S'' then Chart_S else 
if str = ''T'' then Chart_T else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''x'' ::= N 1) (SKIP) (P [''S''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. [])"

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
schematic_goal "Root_Exec_for_times env '''' (6::int) s ?s"
  unfolding Chart_S_def Chart_T_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def
  by stateflow_execution2

end