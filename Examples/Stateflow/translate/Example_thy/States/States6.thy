theory States6
  imports Final_ML 
begin

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (print1 ''enA1'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart_A_A2 :: state where " Chart_A_A2 = State [''A'', ''A2'']
  (print1 ''enA2'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. if str = ''A1'' then Chart_A_A1 else 
if str = ''A2'' then Chart_A_A2 else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''enA'' )
  (SKIP)
  (SKIP)
  []
  []
  (And [''A1'', ''A2'']
 (f_Chart_A))"

definition Chart_B_B1 :: state where " Chart_B_B1 = State [''B'', ''B1'']
  (print1 ''enB1'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition Chart_B_B2 :: state where " Chart_B_B2 = State [''B'', ''B2'']
  (print1 ''enB2'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_B :: string2state where 
" f_Chart_B = 
(λstr. if str = ''B1'' then Chart_B_B1 else 
if str = ''B2'' then Chart_B_B2 else 
No_State )"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''enB'' )
  (SKIP)
  (SKIP)
  []
  []
  (And [''B1'', ''B2'']
 (f_Chart_B))"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''B'' then Chart_B else 
No_State )"

definition Root :: comp where " Root = And [''A'', ''B'']
 (f_Chart)"

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
  unfolding Chart_A_A1_def Chart_A_A2_def f_Chart_A_def Chart_A_def Chart_B_B1_def 
Chart_B_B2_def f_Chart_B_def Chart_B_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def
  by stateflow_execution2

end