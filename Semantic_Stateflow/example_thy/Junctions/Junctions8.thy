theory Junctions8
  imports Final_ML 
begin

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''enA'' )
  (print1 ''duA'' )
  (print1 ''exA'' )
  [Trans (P [''A'']) (S []) (Bc True) (print1 ''ca2'' ) (SKIP) (J [''A'', ''14''])]
  [Trans (P [''A'']) (S []) ((V ''x'') [>=] (N 1)) (print1 ''ca1'' ) (SKIP) (J [''5''])]
  (No_Composition)"

definition Chart_C :: state where " Chart_C = State [''C'']
  (print1 ''enC'' )
  (SKIP)
  (print1 ''exC'' )
  []
  [Trans (P [''C'']) (S []) (Bc True) (''x'' ::= N 0) (SKIP) (P [''A''])]
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''C'' then Chart_C else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (''x'' ::= N 1) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''A'', ''14''] then [Trans (J [''A'', ''14'']) (S []) (Bc True) (SKIP) (SKIP) (J [''5''])] else 
if str = [''5''] then [Trans (J [''5'']) (S []) (Bc True) (SKIP) (SKIP) (P [''C''])] else 
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
schematic_goal "Root_Exec_for_times env '''' (4::int) s ?s"
  unfolding f_Chart_A_def Chart_A_def Chart_C_def f_Chart_def Root_def g_def v_def 
I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end