theory LAP
  imports "../Final_ML"
begin

definition Chart_RunW_Running :: state where " Chart_RunW_Running = State [''RunW'', ''Running'']
  (SKIP)
  ((((print1 ''edu_Running'') ;''disp_cent'' ::= V ''cent'');''disp_sec'' ::= V ''sec'');''disp_min'' ::= V ''mins'')
  (SKIP)
  []
  [Trans (P [''RunW'', ''Running'']) (S [''LAP'']) (Bc True) (SKIP) (SKIP) (P [''RunW'', ''Lap'']), Trans (P [''RunW'', ''Running'']) (S [''START'']) (Bc True) (SKIP) (SKIP) (P [''StopW'', ''Reset''])]
  (No_Composition)"

definition Chart_RunW_Lap :: state where " Chart_RunW_Lap = State [''RunW'', ''Lap'']
  (print1 ''en_Lap'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''RunW'', ''Lap'']) (S [''LAP'']) (Bc True) (SKIP) (SKIP) (P [''RunW'', ''Running'']), Trans (P [''RunW'', ''Lap'']) (S [''START'']) (Bc True) (SKIP) (SKIP) (P [''StopW'', ''LapStop''])]
  (No_Composition)"

definition f_Chart_RunW :: string2state where 
" f_Chart_RunW = 
(λstr. if str = ''Running'' then Chart_RunW_Running else 
if str = ''Lap'' then Chart_RunW_Lap else 
No_State )"

definition Chart_RunW :: state where " Chart_RunW = State [''RunW'']
  (print1 ''en_RunW'' )
  (SKIP)
  (SKIP)
  [Trans (P [''RunW'']) (S [''TIC'']) (Bc True) ((print1 ''cond_TIC'' ); (''cent'' ::= Plus (V ''cent'') (N 1))) (SKIP) (J [''RunW'', ''29''])]
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''RunW'', ''Running''])])
 (False) (f_Chart_RunW))"

definition f_Chart_StopW_Reset :: string2state where 
" f_Chart_StopW_Reset = 
(λstr. No_State )"

definition Chart_StopW_Reset :: state where " Chart_StopW_Reset = State [''StopW'', ''Reset'']
  (((print1 ''en_Reset'') ;send1 ''LAP'' False);send1 ''START'' False)
  (SKIP)
  (SKIP)
  [Trans (P [''StopW'', ''Reset'']) (S [''LAP'']) (Bc True) ((''cent'' ::= N 0); ((''sec'' ::= N 0); ((''mins'' ::= N 0); ((''disp_cent'' ::= N 0); ((''disp_sec'' ::= N 0); (''disp_min'' ::= N 0)))))) (SKIP) (J [''StopW'', ''Reset'', ''16''])]
  [Trans (P [''StopW'', ''Reset'']) (S [''START'']) (Bc True) (SKIP) (SKIP) (P [''RunW'', ''Running''])]
  (No_Composition)"

definition Chart_StopW_LapStop :: state where " Chart_StopW_LapStop = State [''StopW'', ''LapStop'']
  (print1 ''en_LapStop'' )
  (SKIP)
  (SKIP)
  []
  [Trans (P [''StopW'', ''LapStop'']) (S [''LAP'']) (Bc True) (SKIP) (SKIP) (P [''StopW'', ''Reset'']), Trans (P [''StopW'', ''LapStop'']) (S [''START'']) (Bc True) (SKIP) (SKIP) (P [''RunW'', ''Lap''])]
  (No_Composition)"

definition f_Chart_StopW :: string2state where 
" f_Chart_StopW = 
(λstr. if str = ''Reset'' then Chart_StopW_Reset else 
if str = ''LapStop'' then Chart_StopW_LapStop else 
No_State )"

definition Chart_StopW :: state where " Chart_StopW = State [''StopW'']
  (print1 ''en_StopW'' )
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''StopW'', ''Reset''])])
 (False) (f_Chart_StopW))"

definition f_Chart :: string2state where 
" f_Chart = 
(λstr. if str = ''RunW'' then Chart_RunW else 
if str = ''StopW'' then Chart_StopW else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''StopW''])])
 (False) (f_Chart)"

definition g :: juncs where 
" g = (λ str. if str = [''RunW'', ''29''] then [Trans (J [''RunW'', ''29'']) (S []) ((V ''cent'') [==] (N 100)) ((''cent'' ::= N 0); (''sec'' ::= Plus (V ''sec'') (N 1))) (SKIP) (J [''RunW'', ''30'']),
Trans (J [''RunW'', ''29'']) (S []) (Bc True) (SKIP) (SKIP) (J [''RunW'', ''31''])] else 
if str = [''RunW'', ''30''] then [Trans (J [''RunW'', ''30'']) (S []) ((V ''sec'') [==] (N 60)) ((''sec'' ::= N 0); (''mins'' ::= Plus (V ''mins'') (N 1))) (SKIP) (J [''RunW'', ''31'']),
Trans (J [''RunW'', ''30'']) (S []) (Bc True) (SKIP) (SKIP) (J [''RunW'', ''31''])] else 
if str = [''RunW'', ''31''] then [] else 
if str = [''StopW'', ''Reset'', ''16''] then [] else 
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
schematic_goal "Root_Exec_for_times env ''TIC'' (11::int) s ?s"
  unfolding Chart_RunW_Running_def Chart_RunW_Lap_def f_Chart_RunW_def Chart_RunW_def 
f_Chart_StopW_Reset_def Chart_StopW_Reset_def Chart_StopW_LapStop_def f_Chart_StopW_def 
Chart_StopW_def f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  by stateflow_execution2

definition s2::status where "s2 = Status
 (Vals
   ((λstr. 0)
    (''cent'' := 0, ''sec'' := 0, ''mins'' := 0, ''disp_cent'' := 0, ''disp_sec'' := 0,
     ''disp_min'' := 0))
   ((λp str. 0)
    ([] := λstr. 0, [''StopW''] := (λstr. 0)(''LAP'' := 1, ''START'' := 1, ''tick'' := 2),
     [''StopW'', ''Reset''] := (λstr. 0)(''LAP'' := 1, ''START'' := 1, ''tick'' := 2),
     [''RunW''] := (λstr. 0)([] := 1, ''tick'' := 1),
     [''RunW'', ''Running''] := (λstr. 0)([] := 1, ''tick'' := 1)))
   ((λp. 0)
    ([] := 0, [''StopW''] := 0, [''StopW'', ''Reset''] := 0, [''RunW''] := 1,
     [''RunW'', ''Running''] := 1))
   ([''en_StopW'', ''en_Reset'', ''en_RunW'', ''edu_Running''], []))
 ((λstr. Info False [] [])
  ([''StopW'', ''Reset''] := Info False [] [], [''StopW''] := Info False [] [],
   [] := Info True ''RunW'' [], [''RunW'', ''Running''] := Info True [] [],
   [''RunW''] := Info True ''Running'' []))"

schematic_goal "Root_Exec_for_times env ''LAP'' (1::int) s2 ?s2"
  unfolding Chart_RunW_Running_def Chart_RunW_Lap_def f_Chart_RunW_def Chart_RunW_def 
f_Chart_StopW_Reset_def Chart_StopW_Reset_def Chart_StopW_LapStop_def f_Chart_StopW_def 
Chart_StopW_def f_Chart_def Root_def g_def v_def I_def fe_def ge_def env_def s2_def 
  by stateflow_execution2

end