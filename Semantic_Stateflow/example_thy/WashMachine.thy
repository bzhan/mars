theory WashMachine
  imports "../Final_ML"
begin

definition Washing_machine_OFF_Initial_State :: state where " Washing_machine_OFF_Initial_State = State [''OFF'', ''Initial_State'']
  (((''n1'' ::= N 5); ''n2'' ::= N 10); ''n3'' ::= (N 45))
  (SKIP)
  (SKIP)
  []
  [Trans (P [''OFF'', ''Initial_State'']) (S [''SWITCH'']) (Bc True) (SKIP) (SKIP) (P [''ON'', ''Add_Water''])]
  (No_Composition)"

definition Washing_machine_OFF_off :: state where " Washing_machine_OFF_off = State [''OFF'', ''off'']
  ((''time'' ::= N 0);''finish'' ::= N 0)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''OFF'', ''off'']) (S [''ON'']) (Bc True) (SKIP) (SKIP) (P [''OFF'', ''Initial_State''])]
  (No_Composition)"

definition Washing_machine_OFF_Pending_State :: state where " Washing_machine_OFF_Pending_State = State [''OFF'', ''Pending_State'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  [Trans (P [''OFF'', ''Pending_State'']) (S [''SWITCH'']) (Bc True) (SKIP) (SKIP) (P [''ON'']), Trans (P [''OFF'', ''Pending_State'']) (S [''OFF'']) (Bc True) (SKIP) (SKIP) (P [''OFF'', ''off''])]
  (No_Composition)"

definition f_Washing_machine_OFF :: string2state where 
" f_Washing_machine_OFF = 
(λstr. if str = ''Initial_State'' then Washing_machine_OFF_Initial_State else 
if str = ''off'' then Washing_machine_OFF_off else 
if str = ''Pending_State'' then Washing_machine_OFF_Pending_State else 
No_State )"

definition Washing_machine_OFF :: state where " Washing_machine_OFF = State [''OFF'']
  (SKIP)
  (SKIP)
  (SKIP)
  []
  []
  (Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''OFF'', ''off''])])
 (False) (f_Washing_machine_OFF))"

definition Washing_machine_ON_Add_Water :: state where " Washing_machine_ON_Add_Water = State [''ON'', ''Add_Water'']
  (SKIP)
  (''time'' ::= Plus (V ''time'') (N 1))
  (SKIP)
  []
  [Trans (P [''ON'', ''Add_Water'']) (S []) ((V ''time'') [>=] (V ''n1'')) (SKIP) (''time'' ::= N 0) (P [''ON'', ''Washing''])]
  (No_Composition)"

definition Washing_machine_ON_Washing :: state where " Washing_machine_ON_Washing = State [''ON'', ''Washing'']
  (SKIP)
  (''time'' ::= Plus (V ''time'') (N 1))
  (SKIP)
  []
  [Trans (P [''ON'', ''Washing'']) (S []) ((V ''time'') [>=] (V ''n2'')) (SKIP) (''time'' ::= N 0) (P [''ON'', ''Add_Water''])]
  (No_Composition)"

definition f_Washing_machine_ON :: string2state where 
" f_Washing_machine_ON = 
(λstr. if str = ''Add_Water'' then Washing_machine_ON_Add_Water else 
if str = ''Washing'' then Washing_machine_ON_Washing else 
No_State )"

definition Washing_machine_ON :: state where " Washing_machine_ON = State [''ON'']
  (SKIP)
  (on2 ''E'' :: print1 ''Washing Completed!'' )
  (SKIP)
  []
  [Trans (P [''ON'']) (S [''OFF'']) (Bc True) (SKIP) (SKIP) (P [''OFF'']), 
Trans (P [''ON'']) (S [''SWITCH'']) (Bc True) 
(''n3'' ::= Minus (V ''n3'') (TemporalCount ''Sec'')) (SKIP) (P [''OFF'', ''Pending_State'']), 
Trans (P [''ON'']) (T1 (After (''Sec'') (V ''n3''))) ((V ''finish'') [==] (N 0)) ((''finish'' ::= N 1); (send1 ''E'' False)) (SKIP) (P [''OFF''])]
  (Or ([])
 (True) (f_Washing_machine_ON))"

definition f_Washing_machine :: string2state where 
" f_Washing_machine = 
(λstr. if str = ''OFF'' then Washing_machine_OFF else 
if str = ''ON'' then Washing_machine_ON else 
No_State )"

definition Root :: comp where " Root = Or ([Trans (NONE) (S []) (Bc True) (SKIP) (SKIP) (P [''OFF''])])
 (False) (f_Washing_machine)"

definition g :: juncs where 
" g = (λ str. if str = [''ON'', ''13''] then [] else 
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
text‹EXECUTION PROOF›
schematic_goal "Root_Exec_for_times env ['''',''ON''] (2::int) s ?s"
  unfolding Washing_machine_OFF_Initial_State_def Washing_machine_OFF_off_def Washing_machine_OFF_Pending_State_def 
f_Washing_machine_OFF_def Washing_machine_OFF_def Washing_machine_ON_Add_Water_def 
Washing_machine_ON_Washing_def f_Washing_machine_ON_def Washing_machine_ON_def f_Washing_machine_def 
Root_def g_def v_def I_def fe_def ge_def env_def s_def 
  apply simp
  by stateflow_execution2

definition s2::status where "s2 = Status
 (Vals ((λstr. 0)(''time'' := 0, ''finish'' := 0, ''n1'' := 5, ''n2'' := 10, ''n3'' := 45))
   ((λp str. 0)
    ([] := λstr. 0, [''OFF''] := (λstr. 0)(''ON'' := 1, ''tick'' := 1),
     [''OFF'', ''off''] := (λstr. 0)(''ON'' := 1, ''tick'' := 1),
     [''OFF'', ''Initial_State''] := λstr. 0))
   ((λp. 0)([] := 0, [''OFF''] := 1, [''OFF'', ''off''] := 1, [''OFF'', ''Initial_State''] := 0))
   (λx. []) ([], []))
 ((λstr. Info False [] [])
  ([] := Info True ''OFF'' [], [''OFF'', ''off''] := Info False [] [],
   [''OFF'', ''Initial_State''] := Info True [] [], [''OFF''] := Info True ''Initial_State'' []))"

schematic_goal "Root_Exec_for_times env [''SWITCH''] (1::int) s2 ?s2"
  unfolding Washing_machine_OFF_Initial_State_def Washing_machine_OFF_off_def Washing_machine_OFF_Pending_State_def 
f_Washing_machine_OFF_def Washing_machine_OFF_def Washing_machine_ON_Add_Water_def 
Washing_machine_ON_Washing_def f_Washing_machine_ON_def Washing_machine_ON_def f_Washing_machine_def 
Root_def g_def v_def I_def fe_def ge_def env_def s2_def 
  apply simp
  by stateflow_execution2

definition s3::status where "s3 = Status
 (Vals ((λstr. 0)(''time'' := 0, ''finish'' := 0, ''n1'' := 5, ''n2'' := 10, ''n3'' := 45))
   ((λp str. 0)
    ([] := λstr. 0, [''OFF'', ''off''] := (λstr. 0)(''ON'' := 1, ''tick'' := 1),
     [''OFF''] := (λstr. 0)(''ON'' := 1, ''SWITCH'' := 1, ''tick'' := 2),
     [''OFF'', ''Initial_State''] := (λstr. 0)(''SWITCH'' := 1, ''tick'' := 1), [''ON''] := λstr. 0,
     [''ON'', ''Add_Water''] := λstr. 0))
   ((λp. 0)
    ([] := 0, [''OFF'', ''off''] := 1, [''OFF''] := 2, [''OFF'', ''Initial_State''] := 1,
     [''ON''] := 0, [''ON'', ''Add_Water''] := 0))
   (λx. []) ([], []))
 ((λstr. Info False [] [])
  ([''OFF'', ''off''] := Info False [] [], [''OFF'', ''Initial_State''] := Info False [] [],
   [''OFF''] := Info False [] [], [] := Info True ''ON'' [],
   [''ON'', ''Add_Water''] := Info True [] [], [''ON''] := Info True ''Add_Water'' []))"

schematic_goal "Root_Exec_for_times env '''' (15::int) s3 ?s3"
  unfolding Washing_machine_OFF_Initial_State_def Washing_machine_OFF_off_def Washing_machine_OFF_Pending_State_def 
f_Washing_machine_OFF_def Washing_machine_OFF_def Washing_machine_ON_Add_Water_def 
Washing_machine_ON_Washing_def f_Washing_machine_ON_def Washing_machine_ON_def f_Washing_machine_def 
Root_def g_def v_def I_def fe_def ge_def env_def s3_def 
  apply simp
  by stateflow_execution2

definition s4::status where "s4 = Status
 (Vals ((λstr. 0)(''finish'' := 0, ''n1'' := 5, ''n2'' := 10, ''n3'' := 45, ''time'' := 9))
   ((λp str. 0)
    ([] := λstr. 0, [''OFF'', ''off''] := (λstr. 0)(''ON'' := 1, ''tick'' := 1),
     [''OFF''] := (λstr. 0)(''ON'' := 1, ''SWITCH'' := 1, ''tick'' := 2),
     [''OFF'', ''Initial_State''] := (λstr. 0)(''SWITCH'' := 1, ''tick'' := 1),
     [''ON'', ''Add_Water''] := (λstr. 0)([] := 6, ''tick'' := 6),
     [''ON''] := (λstr. 0)([] := 15, ''tick'' := 15),
     [''ON'', ''Washing''] := (λstr. 0)([] := 9, ''tick'' := 9)))
   ((λp. 0)
    ([] := 0, [''OFF'', ''off''] := 1, [''OFF''] := 2, [''OFF'', ''Initial_State''] := 1,
     [''ON'', ''Add_Water''] := 6, [''ON''] := 15, [''ON'', ''Washing''] := 9))
   (λx. []) ([], []))
 ((λstr. Info False [] [])
  ([''OFF'', ''off''] := Info False [] [], [''OFF'', ''Initial_State''] := Info False [] [],
   [''OFF''] := Info False [] [], [] := Info True ''ON'' [],
   [''ON'', ''Add_Water''] := Info False [] [], [''ON'', ''Washing''] := Info True [] [],
   [''ON''] := Info True ''Washing'' ''Add_Water''))"

schematic_goal "Root_Exec_for_times env [''SWITCH''] (1::int) s4 ?s4"
  unfolding Washing_machine_OFF_Initial_State_def Washing_machine_OFF_off_def Washing_machine_OFF_Pending_State_def 
f_Washing_machine_OFF_def Washing_machine_OFF_def Washing_machine_ON_Add_Water_def 
Washing_machine_ON_Washing_def f_Washing_machine_ON_def Washing_machine_ON_def f_Washing_machine_def 
Root_def g_def v_def I_def fe_def ge_def env_def s4_def 
  apply simp
  by stateflow_execution2

definition s5::status where "s5 = Status
 (Vals ((λstr. 0)(''finish'' := 0, ''n1'' := 5, ''n2'' := 10, ''time'' := 9, ''n3'' := 29))
   ((λp str. 0)
    ([] := λstr. 0, [''OFF'', ''off''] := (λstr. 0)(''ON'' := 1, ''tick'' := 1),
     [''OFF'', ''Initial_State''] := (λstr. 0)(''SWITCH'' := 1, ''tick'' := 1),
     [''ON'', ''Add_Water''] := (λstr. 0)([] := 6, ''tick'' := 6),
     [''ON'', ''Washing''] := (λstr. 0)([] := 9, ''tick'' := 9),
     [''ON''] := (λstr. 0)([] := 15, ''SWITCH'' := 1, ''tick'' := 16), [''OFF''] := λstr. 0,
     [''OFF'', ''Pending_State''] := λstr. 0))
   ((λp. 0)
    ([] := 0, [''OFF'', ''off''] := 1, [''OFF'', ''Initial_State''] := 1, [''ON'', ''Add_Water''] := 6,
     [''ON'', ''Washing''] := 9, [''ON''] := 16, [''OFF''] := 0, [''OFF'', ''Pending_State''] := 0))
   (λx. []) ([], []))
 ((λstr. Info False [] [])
  ([''OFF'', ''off''] := Info False [] [], [''OFF'', ''Initial_State''] := Info False [] [],
   [''ON'', ''Add_Water''] := Info False [] [], [''ON'', ''Washing''] := Info False [] [],
   [''ON''] := Info False [] ''Washing'', [] := Info True ''OFF'' [],
   [''OFF'', ''Pending_State''] := Info True [] [], [''OFF''] := Info True ''Pending_State'' []))"

schematic_goal "Root_Exec_for_times env [''SWITCH''] (1::int) s5 ?s5"
  unfolding Washing_machine_OFF_Initial_State_def Washing_machine_OFF_off_def Washing_machine_OFF_Pending_State_def 
f_Washing_machine_OFF_def Washing_machine_OFF_def Washing_machine_ON_Add_Water_def 
Washing_machine_ON_Washing_def f_Washing_machine_ON_def Washing_machine_ON_def f_Washing_machine_def 
Root_def g_def v_def I_def fe_def ge_def env_def s5_def 
  apply simp
  by stateflow_execution2

definition s6::status where "s6 = Status
 (Vals ((λstr. 0)(''finish'' := 0, ''n1'' := 5, ''n2'' := 10, ''time'' := 9, ''n3'' := 29))
   ((λp str. 0)
    ([] := λstr. 0, [''OFF'', ''off''] := (λstr. 0)(''ON'' := 1, ''tick'' := 1),
     [''OFF'', ''Initial_State''] := (λstr. 0)(''SWITCH'' := 1, ''tick'' := 1),
     [''ON'', ''Add_Water''] := (λstr. 0)([] := 6, ''tick'' := 6),
     [''OFF''] := (λstr. 0)(''SWITCH'' := 1, ''tick'' := 1),
     [''OFF'', ''Pending_State''] := (λstr. 0)(''SWITCH'' := 1, ''tick'' := 1), [''ON''] := λstr. 0,
     [''ON'', ''Washing''] := λstr. 0))
   ((λp. 0)
    ([] := 0, [''OFF'', ''off''] := 1, [''OFF'', ''Initial_State''] := 1, [''ON'', ''Add_Water''] := 6,
     [''OFF''] := 1, [''OFF'', ''Pending_State''] := 1, [''ON''] := 0, [''ON'', ''Washing''] := 0))
   (λx. []) ([], []))
 ((λstr. Info False [] [])
  ([''OFF'', ''off''] := Info False [] [], [''OFF'', ''Initial_State''] := Info False [] [],
   [''ON'', ''Add_Water''] := Info False [] [], [''OFF'', ''Pending_State''] := Info False [] [],
   [''OFF''] := Info False [] [], [] := Info True ''ON'' [], [''ON'', ''Washing''] := Info True [] [],
   [''ON''] := Info True ''Washing'' ''Washing''))"

schematic_goal "Root_Exec_for_times env [''OFF''] (1::int) s6 ?s6"
  unfolding Washing_machine_OFF_Initial_State_def Washing_machine_OFF_off_def Washing_machine_OFF_Pending_State_def 
f_Washing_machine_OFF_def Washing_machine_OFF_def Washing_machine_ON_Add_Water_def 
Washing_machine_ON_Washing_def f_Washing_machine_ON_def Washing_machine_ON_def f_Washing_machine_def 
Root_def g_def v_def I_def fe_def ge_def env_def s6_def 
  apply simp
  by stateflow_execution2

schematic_goal "Root_Exec_for_times env '''' (30::int) s6 ?s6"
  unfolding Washing_machine_OFF_Initial_State_def Washing_machine_OFF_off_def Washing_machine_OFF_Pending_State_def 
f_Washing_machine_OFF_def Washing_machine_OFF_def Washing_machine_ON_Add_Water_def 
Washing_machine_ON_Washing_def f_Washing_machine_ON_def Washing_machine_ON_def f_Washing_machine_def 
Root_def g_def v_def I_def fe_def ge_def env_def s6_def 
  apply simp
  by stateflow_execution2

end