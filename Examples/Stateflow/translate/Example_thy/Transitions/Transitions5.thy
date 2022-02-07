theory Transitions5
  imports Final_ML 
begin

definition Chart_S_A :: state where " Chart_S_A = State [''S'', ''A'']
  (print1 ''enA'' )
  (SKIP)
  (print1 ''exA'' )
  []
  [Trans (P [''S'', ''A'']) (S []) (Bc True) (SKIP) (SKIP) (P [''S'', ''B''])]
  (No_Composition)"

definition Chart_S_B :: state where " Chart_S_B = State [''S'', ''B'']
  (print1 ''enB'' )
  (SKIP)
  (print1 ''exB'' )
  []
  [Trans (P [''S'', ''B'']) (S []) (Bc True) (SKIP) (SKIP) (P [''S'', ''A''])]
  (No_Composition)"

definition f_Chart_S :: string2state where 
" f_Chart_S = 
(λstr. if str = ''A'' then Chart_S_A else 
if str = ''B'' then Chart_S_B else 
No_State )"

definition Chart_S :: state where " Chart_S = State [''S'']
  (print1 ''enS'' )
  (print1 ''duS'' )
  (SKIP)
  [Trans (P [''S'']) (S []) (Bc True) (print1 ''condInner'' ) (print1 ''tranInner'' ) (P [''S''])]
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''S'', ''A''])])
 (False) (f_Chart_S))"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''S'' then Chart_S else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''S''])])
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
schematic_goal "Root_Exec_for_times env '''' (2::int) s ?s"
  unfolding Chart_S_A_def Chart_S_B_def f_Chart_S_def Chart_S_def f_Chart_def Root_def 
g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end