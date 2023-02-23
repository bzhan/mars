theory EarlyReturn19
  imports "../Final_ML" 
begin

definition f_Chart_S :: string2state where 
" f_Chart_S = 
(λstr. No_State )"

definition Chart_S :: state where " Chart_S = State [''S'']
  (print1 ''enS'' )
  (print1 ''duS'' )
  (print1 ''exS'' )
  [Trans (P [''S'']) (S []) (Bc True) (print1 ''ca1'' ) ((send1 ''E'' True); (print1 ''ta1'' )) (J [''S'', ''15''])]
  [Trans (P [''S'']) (S [''E'']) (Bc True) (SKIP) (SKIP) (P [''T''])]
  (No_Composition)"

definition Chart_T :: state where " Chart_T = State [''T'']
  (print1 ''enT'' )
  (SKIP)
  (SKIP)
  []
  []
  (No_Composition)"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''S'' then Chart_S else 
if str = ''T'' then Chart_T else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''S''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''S'', ''15''] then [Trans (J [''S'', ''15'']) (S []) (Bc True) (print1 ''ca2'' ) (print1 ''ta2'' ) (P [''S''])] else 
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
schematic_goal "Root_Exec_for_times env ['''', ''''] (2::int) s
 (Status (Vals ?v1 ?v2 ?v3 ?v4 ([''enS'', ''duS'', ''ca1'', ''ca2'', ''exS'', ''enT''], ?o2)) (?I))"
  unfolding f_Chart_S_def Chart_S_def Chart_T_def f_Chart_def Root_def g_def v_def 
I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

end