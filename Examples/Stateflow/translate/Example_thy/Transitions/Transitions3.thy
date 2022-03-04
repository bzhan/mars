theory Transitions3
  imports Final_ML 
begin

definition Chart_A_b :: state where " Chart_A_b = State [''A'', ''b'']
  (print1 ''b'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'', ''b'']) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''c''])]
  (No_Composition)"

definition Chart_A_c_c1 :: state where " Chart_A_c_c1 = State [''A'', ''c'', ''c1'']
  (print1 ''c1'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'', ''c'', ''c1'']) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''c'', ''c2''])]
  (No_Composition)"

definition Chart_A_c_c2 :: state where " Chart_A_c_c2 = State [''A'', ''c'', ''c2'']
  (print1 ''c2'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A'', ''c'', ''c2'']) (S []) (Bc True) (SKIP) (SKIP) (P [''B''])]
  (No_Composition)"

definition f_Chart_A_c :: string2state where 
" f_Chart_A_c = 
(λstr. if str = ''c1'' then Chart_A_c_c1 else 
if str = ''c2'' then Chart_A_c_c2 else 
No_State )"

definition Chart_A_c :: state where " Chart_A_c = State [''A'', ''c'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''c'', ''c1''])])
 (True) (f_Chart_A_c))"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(λstr. if str = ''b'' then Chart_A_b else 
if str = ''c'' then Chart_A_c else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''b''])])
 (True) (f_Chart_A))"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''B'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''B'']) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])]
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''A'' then Chart_A else 
if str = ''B'' then Chart_B else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''A'', ''c'', ''26''] then [] else 
if str = [''A'', ''21''] then [] else 
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
schematic_goal "Root_Exec_for_times env '''' (6::int) s ?s"
  unfolding Chart_A_b_def Chart_A_c_c1_def Chart_A_c_c2_def f_Chart_A_c_def Chart_A_c_def 
f_Chart_A_def Chart_A_def Chart_B_def f_Chart_def Root_def g_def v_def I_def fe_def 
ge_def env_def s_def 
  by stateflow_execution2

end