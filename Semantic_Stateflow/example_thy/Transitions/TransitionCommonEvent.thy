theory TransitionCommonEvent
  imports "../Final_ML" 
begin

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''Entry A'' )
  (print1 ''During A'' )
  (print1 ''Exit A'' )
  []
  [Trans (P [''A'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (P [''B'']), Trans (P [''A'']) (S []) (Bc True) (SKIP) (SKIP) (J [''8''])]
  (No_Composition)"

definition Chart_C :: state where " Chart_C = State [''C'']
  (print1 ''Entry C'' )
  (print1 ''During C'' )
  (print1 ''Exit A'' )
  []
  []
  (No_Composition)"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''Entry B'' )
  (print1 ''During B'' )
  (print1 ''Exit B'' )
  []
  [Trans (P [''B'']) (S []) (Bc True) (SKIP) (SKIP) (J [''8''])]
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
" g = (λ str. if str = [''8''] then [Trans (J [''8'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (P [''C''])] else 
[])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) (λx. []) ([],[]) "

definition I :: ctxt where 
"I str = (Info False [] [])"
definition fe::fenv where " 
fe str = ((SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "

definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I" 
text\<open>EXECUTION PROOF\<close>
schematic_goal "Root_Exec_for_times env [''E_one'', ''E_one''] (2::int) s
 (Status (Vals ?v1 ?v2 ?v3 ?v4 ([''Entry A'', ''Exit A'', ''Entry B''], ?o2)) (?I))"
  unfolding Chart_A_def Chart_C_def Chart_B_def f_Chart_def Root_def g_def v_def 
I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end