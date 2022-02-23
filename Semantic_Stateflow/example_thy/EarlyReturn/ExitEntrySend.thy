theory ExitEntrySend
  imports "../../Final_ML"
begin

definition Chart_B_B1 :: state where " Chart_B_B1 = State [''B'', ''B1'']
  (print1 ''Entry B1'' )
  (print1 ''During B1'' )
  (print1 ''Exit B1'' )
  []
  []
  (No_Composition)"

definition Chart_B_B2 :: state where " Chart_B_B2 = State [''B'', ''B2'']
  (print1 ''Entry B2'' )
  (print1 ''During B2'' )
  (print1 ''Exit B2'' )
  []
  [Trans (P [''B'', ''B2'']) (S [''F'']) (Bc True) (SKIP) (print1 ''Transition Action2'' ) (P [''A''])]
  (No_Composition)"

definition f_Chart_B :: string2state where 
" f_Chart_B = 
(λstr. if str = ''B1'' then Chart_B_B1 else 
if str = ''B2'' then Chart_B_B2 else 
No_State )"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''Entry B'' ;send1 ''F'' False)
  (print1 ''During B'' )
  (print1 ''Exit B'' )
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''B'', ''B1''])])
 (False) (f_Chart_B))"

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (print1 ''Entry A1'' )
  (print1 ''During A1'' )
  (print1 ''Exit A1'' ;send1 ''F'' False)
  []
  [Trans (P [''A'', ''A1'']) (S [''E'']) (Bc True) (SKIP) (print1 ''Transition Action1'' ) (P [''B'', ''B2''])]
  (No_Composition)"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. if str = ''A1'' then Chart_A_A1 else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''Entry A'' )
  (print1 ''During A'' )
  (print1 ''Exit A'' )
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A1''])])
 (False) (f_Chart_A))"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''B'' then Chart_B else 
if str = ''A'' then Chart_A else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. [])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) ([],[]) "

definition I :: ctxt where 
"I str = (Info False [] [])"
definition fe::fenv where " 
fe str = ((SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text‹EXECUTION PROOF›
schematic_goal "Root_Exec_for_times env ''E'' (2::int) s ?s"
  unfolding Chart_B_B1_def Chart_B_B2_def f_Chart_B_def Chart_B_def Chart_A_A1_def 
f_Chart_A_def Chart_A_def f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def 
s_def
  by stateflow_execution2

end