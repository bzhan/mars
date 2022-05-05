theory Messages8
  imports "../../Final_ML"
begin

definition MessageReceiver_A0 :: state where " MessageReceiver_A0 = State [''A0'']
  (print1 ''en_A0'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A0'']) (T1 (After (''Sec'') (N 3))) (Bc True) (SKIP) (SKIP) (P [''A1''])]
  (No_Composition)"

definition MessageReceiver_A1 :: state where " MessageReceiver_A1 = State [''A1'']
  (print1 ''en_A1'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A1'']) (M ''M'') ((V ''M'') [==] (N 2)) (SKIP) (SKIP) (P [''A2''])]
  (No_Composition)"

definition MessageReceiver_A2 :: state where " MessageReceiver_A2 = State [''A2'']
  (print1 ''en_A2'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''A2'']) (M ''M1'') ((V ''M1'') [==] (N 3)) (SKIP) (SKIP) (P [''A3''])]
  (No_Composition)"

definition MessageReceiver_A3 :: state where " MessageReceiver_A3 = State [''A3'']
  (print1 ''en_A3'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_MessageReceiver :: string2state where 
" f_MessageReceiver = 
(λstr. if str = ''A0'' then MessageReceiver_A0 else 
if str = ''A1'' then MessageReceiver_A1 else 
if str = ''A2'' then MessageReceiver_A2 else 
if str = ''A3'' then MessageReceiver_A3 else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''A0''])])
 (False) (f_MessageReceiver)"

definition g :: juncs where 
" g = (λ str. [])"

definition v :: vals where " v = Vals (λstr. 0) (λp str. 0) (λp. 0) (λx. [])([],[]) "

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
text\<open>EXECUTION PROOF\<close>
schematic_goal "Root_Exec_for_times env '''' (2::int) s ?s"
  unfolding MessageReceiver_A0_def MessageReceiver_A1_def MessageReceiver_A2_def 
MessageReceiver_A3_def f_MessageReceiver_def Root_def g_def v_def I_def fe_def ge_def 
 env_def s_def 
  by stateflow_execution2

end