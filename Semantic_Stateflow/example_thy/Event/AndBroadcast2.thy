theory AndBroadcast2
  imports "../../Final_ML"
begin

definition Chart_A_A1_A1a :: state where " Chart_A_A1_A1a = State [''A'', ''A1'', ''A1a'']
  (print1 ''Entry A1a'' )
  (print1 ''During A1a'' )
  (print1 ''Exit A1a'' )
  []
  [Trans (P [''A'', ''A1'', ''A1a'']) (S [''E_one'']) (Bc True) (SKIP) (SKIP) (P [''A'', ''A1'', ''A1b''])]
  (No_Composition)"

definition Chart_A_A1_A1b :: state where " Chart_A_A1_A1b = State [''A'', ''A1'', ''A1b'']
  (print1 ''Entry A1b'' )
  (print1 ''During A1b'' )
  (print1 ''Exit A1b'' )
  []
  []
  (No_Composition)"

definition f_Chart_A_A1 :: string2state where 
" f_Chart_A_A1 = 
(\<lambda>str. if str = ''A1a'' then Chart_A_A1_A1a else 
if str = ''A1b'' then Chart_A_A1_A1b else 
No_State )"

definition Chart_A_A1 :: state where " Chart_A_A1 = State [''A'', ''A1'']
  (print1 ''Entry A1'' )
  ((print1 ''During A1''); on2 ''E_one''::(send1 ''E_two'' False) )
  (print1 ''Exit A1'' )
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A1'', ''A1a''])])
 (False) (f_Chart_A_A1))"

definition Chart_A_A2_A2a :: state where " Chart_A_A2_A2a = State [''A'', ''A2'', ''A2a'']
  (print1 ''Entry A2a'' )
  (print1 ''During A2a'' )
  (print1 ''Exit A2a'' )
  []
  [Trans (P [''A'', ''A2'', ''A2a'']) (S [''E_two'']) (Bc True) (SKIP) (SKIP) (P [''A'', ''A2'', ''A1b''])]
  (No_Composition)"

definition Chart_A_A2_A1b :: state where " Chart_A_A2_A1b = State [''A'', ''A2'', ''A1b'']
  (print1 ''Entry A2b'' )
  (print1 ''During A2b'' )
  (print1 ''Exit A2b'' )
  []
  []
  (No_Composition)"

definition f_Chart_A_A2 :: string2state where 
" f_Chart_A_A2 = 
(\<lambda>str. if str = ''A2a'' then Chart_A_A2_A2a else 
if str = ''A1b'' then Chart_A_A2_A1b else 
No_State )"

definition Chart_A_A2 :: state where " Chart_A_A2 = State [''A'', ''A2'']
  (print1 ''Entry A2'' )
  (print1 ''During A2'' )
  (print1 ''Exit A2'' )
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A'', ''A2'', ''A2a''])])
 (False) (f_Chart_A_A2))"

definition f_Chart_A :: string2state where 
" f_Chart_A = 
(\<lambda>str. if str = ''A1'' then Chart_A_A1 else 
if str = ''A2'' then Chart_A_A2 else 
No_State )"

definition Chart_A :: state where " Chart_A = State [''A'']
  (print1 ''Entry A'' )
  (print1 ''During A'' )
  (print1 ''Exit A'' )
  []
  []
  (And [''A1'', ''A2'']
 (f_Chart_A))"

definition f_Chart :: string2state where 
" f_Chart = 
(\<lambda>str. if str = ''A'' then Chart_A else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (\<lambda> str. [])"

definition v :: vals where " v = Vals (\<lambda>str. 0) (\<lambda>p str. 0) (\<lambda>p. 0) (\<lambda>x. []) ([],[]) "

definition I :: ctxt where 
"I str = (Info False [] [])"
definition fe::fenv where " 
fe str = ((SKIP, No_Expr, No_Expr)) "

definition ge::genv where " 
ge str = (((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) "


definition env::env where "env = Env Root fe ge g" 
definition s::status where " s = Status v I"  
text\<open>EXECUTION PROOF\<close>
schematic_goal "Root_Exec_for_times env [''E_one'', ''E_one''] (2::int) s ?s"
  unfolding Chart_A_A1_A1a_def Chart_A_A1_A1b_def f_Chart_A_A1_def Chart_A_A1_def 
Chart_A_A2_A2a_def Chart_A_A2_A1b_def f_Chart_A_A2_def Chart_A_A2_def f_Chart_A_def 
Chart_A_def f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2