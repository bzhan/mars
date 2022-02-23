theory TransitiontoMultipleDestinations
  imports "../../Final_ML"
begin

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''Entry B'' )
  (print1 ''During B'' )
  (print1 ''Exit B'' )
  []
  []
  (No_Composition)"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''Entry A'' )
  (print1 ''During A'' )
  (print1 ''Exit A'' )
  []
  [Trans (P [''A'']) (S []) (Bc True) (SKIP) (SKIP) (J [''3''])]
  (No_Composition)"

definition Chart_C :: state where " Chart_C = State [''C'']
  (print1 ''Entry C'' )
  (print1 ''During C'' )
  (print1 ''Exit A'' )
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''B'' then Chart_B else 
if str = ''A'' then Chart_A else 
if str = ''C'' then Chart_C else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''3''] then [Trans (J [''3'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (P [''B'']),
Trans (J [''3'']) (S [''E_two'']) (Bc True) (SKIP) (SKIP) (P [''C''])] else 
[])"

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
schematic_goal "Root_Exec_for_times env ''E_two'' (2::int) s ?s"
  unfolding Chart_B_def Chart_A_def Chart_C_def f_Chart_def Root_def g_def v_def 
I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end