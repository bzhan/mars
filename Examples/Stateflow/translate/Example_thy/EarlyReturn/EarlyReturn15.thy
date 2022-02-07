theory EarlyReturn15
  imports Final_ML 
begin

definition Chart_S_A1_A1a :: state where " Chart_S_A1_A1a = State [''S'', ''A1'', ''A1a'']
  (print1 ''enA1a'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''S'', ''A1'', ''A1a'']) (S []) (Bc True) (print1 ''ca'' ) ((send1 ''E'' True); (print1 ''ta'' )) (P [''S'', ''A1'', ''A1b''])]
  (No_Composition)"

definition Chart_S_A1_A1b :: state where " Chart_S_A1_A1b = State [''S'', ''A1'', ''A1b'']
  (print1 ''enA1b'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_S_A1 :: string2state where 
" f_Chart_S_A1 = 
(λstr. if str = ''A1a'' then Chart_S_A1_A1a else 
if str = ''A1b'' then Chart_S_A1_A1b else 
No_State )"

definition Chart_S_A1 :: state where " Chart_S_A1 = State [''S'', ''A1'']
  (print1 ''enA1'' )
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''S'', ''A1'', ''A1a''])])
 (False) (f_Chart_S_A1))"

definition Chart_S_A2 :: state where " Chart_S_A2 = State [''S'', ''A2'']
  (print1 ''enA2'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart_S :: string2state where 
" f_Chart_S = 
(λstr. if str = ''A1'' then Chart_S_A1 else 
if str = ''A2'' then Chart_S_A2 else 
No_State )"

definition Chart_S :: state where " Chart_S = State [''S'']
  (print1 ''enS'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''S'']) (S [''E'']) (Bc True) (SKIP) (SKIP) (P [''B''])]
  (And [''A1'', ''A2'']
 (f_Chart_S))"

definition Chart_B :: state where " Chart_B = State [''B'']
  (print1 ''enB'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''S'' then Chart_S else 
if str = ''B'' then Chart_B else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''S''])])
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
schematic_goal "Root_Exec_for_times env '''' (2::int) s ?s"
  unfolding Chart_S_A1_A1a_def Chart_S_A1_A1b_def f_Chart_S_A1_def Chart_S_A1_def 
Chart_S_A2_def f_Chart_S_def Chart_S_def Chart_B_def f_Chart_def Root_def g_def v_def 
I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end