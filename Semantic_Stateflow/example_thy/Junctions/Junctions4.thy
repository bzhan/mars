theory Junctions4
  imports "../../Final_ML"
begin

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (print1 ''enA1'' )
  (SKIP)
  (print1 ''exA1'' )
  []
  [Trans (P [''A'', ''A1'']) (S []) (Bc True) (print1 ''c1'' ) (print1 ''t1'' ) (J [''B'', ''13''])]
  (No_Composition)"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. if str = ''A1'' then Chart_A_A1 else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''enA'' )
  (print1 ''duA'' )
  (print1 ''exA'' )
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A1''])])
 (False) (f_Chart_A))"

definition Chart_C_C2 :: state where " Chart_C_C2 = State [''C'', ''C2'']
  (print1 ''enC2'' )
  (SKIP)
  (print1 ''exC2'' )
  []
  []
  (No_Composition)"

definition f_Chart_C :: string2state where 
" f_Chart_C = 
(λstr. if str = ''C2'' then Chart_C_C2 else 
No_State )"

definition Chart_C :: state where " Chart_C = State [''C'']
  (print1 ''enC'' )
  (SKIP)
  (print1 ''exC'' )
  []
  []
  (Or ([])
 (False) (f_Chart_C))"

definition f_Chart_B :: string2state where 
" f_Chart_B = 
(λstr. No_State )"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''enB'' )
  (SKIP)
  (print1 ''exB'' )
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''C'' then Chart_C else 
if str = ''B'' then Chart_B else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''B'', ''13''] then [Trans (J [''B'', ''13'']) (S []) (Bc True) (print1 ''c2'' ) (print1 ''t2'' ) (P [''C'', ''C2''])] else 
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
  unfolding Chart_A_A1_def f_Chart_A_def Chart_A_def Chart_C_C2_def f_Chart_C_def 
Chart_C_def f_Chart_B_def Chart_B_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def 
  by stateflow_execution2

end