theory Junctions1
  imports "../../Final_ML"
begin

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''enB'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''enA'' )
  (print1 ''duA'' )
  (SKIP)
  []
  [Trans (P [''A'']) (S []) (Bc True) (SKIP) (SKIP) (J [''3''])]
  (No_Composition)"

definition Chart_C :: state where " Chart_C = State [''C'']
  (print1 ''enC'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart_E :: state where " Chart_E = State [''E'']
  (print1 ''enE'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart_D :: state where " Chart_D = State [''D'']
  (print1 ''enD'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''B'' then Chart_B else 
if str = ''A'' then Chart_A else 
if str = ''C'' then Chart_C else 
if str = ''E'' then Chart_E else 
if str = ''D'' then Chart_D else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''y'' ::= N 4) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''3''] then [Trans (J [''3'']) (S []) ((V ''y'') [>] (N 10)) (SKIP) (SKIP) (P [''B'']),
Trans (J [''3'']) (S []) ((V ''y'') [>] (N 5)) (SKIP) (SKIP) (P [''C'']),
Trans (J [''3'']) (S []) ((V ''y'') [>] (N 3)) (SKIP) (SKIP) (P [''D'']),
Trans (J [''3'']) (S []) ((V ''y'') [>=] (N 1)) (SKIP) (SKIP) (P [''E''])] else 
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
  unfolding Chart_B_def Chart_A_def Chart_C_def Chart_E_def Chart_D_def f_Chart_def 
Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end