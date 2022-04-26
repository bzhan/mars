theory Semantics_Final
  imports Syntax_Final
begin


text \<open>Semantics for Stateflow with "send" \<close>

text \<open>source state is the source for act "send".\<close>
type_synonym source_state = path
definition h0 :: "string \<Rightarrow> int" where 
  "h0 = (\<lambda>str. 0::int)"

\<comment> \<open>redefinition hd, tl, last and butlast in string list\<close>
fun hd :: "string list \<Rightarrow> string" where
  "hd [] = []"
| "hd (x#xs) = x"
primrec (nonexhaustive) last :: "string list \<Rightarrow> string" where
"last (x # xs) = (if xs = [] then x else last xs)"
primrec butlast :: "string list \<Rightarrow> string list" where
"butlast [] = []" |
"butlast (x # xs) = (if xs = [] then [] else x # butlast xs)"
primrec tl :: "string list \<Rightarrow> string list" where
"tl [] = []" |
"tl (x # xs) = xs"

text \<open>the following functions is the same as those in "Semantics.thy"\<close>
fun inner :: "string \<Rightarrow> string list \<Rightarrow> bool" where
   "inner e [] = False"
 | "inner e (x#xs) = (if (e = x) then True else (inner e xs))"

fun update_status :: "transition \<Rightarrow> status \<Rightarrow> status" where
   Update_status1: "update_status (Trans src (S strl) c a1 a2 trg) s = s"
 | Update_status2: "update_status (Trans src (T1 temp_l) c a1 a2 trg) s = s"
 | Update_status3: "update_status (Trans src (M m) c a1 a2 trg) (Status(Vals s h1 h2 h3 (output1, output2)) I)
 = (if h3 m = [] then (Status(Vals s h1 h2 h3 (output1, output2)) I) else
Status (Vals (s(m := (List.hd (h3 m)))) h1 h2 (h3(m := (List.tl (h3 m)))) (output1, output2)) I)"

fun enable :: "transition \<Rightarrow> string \<Rightarrow> status \<Rightarrow> path \<Rightarrow> bool" where
   Enable1: "enable (Trans src (S strl) c a1 a2 trg) e s p = (((strl = []) \<or> (inner e strl)) 
           \<and> (cval c (get_vals s) p))"
 | Enable2: "enable (Trans src (T1 temp_l) c a1 a2 trg) e s p = ((tval1 temp_l (get_vals s) p) 
           \<and> (cval c (get_vals s) p))"
 | Enable3: "enable (Trans src (M m) c a1 a2 trg) e s p = ((length (get_message_queue s m) > 0)
           \<and> (cval c (get_vals (update_status (Trans src (M m) c a1 a2 trg) s)) p))"

text \<open>return the least common ancestor\<close>
fun lca :: "path \<Rightarrow> path \<Rightarrow> path" where
  "lca [] xs = []"
| "lca xs [] = []"
| "lca (a#xs) (b#ys) = (if a = b then (a#lca xs ys) else [])"

text \<open>the highest path is defined for outer transitions in state_exec,
which means the highest position of a transition\<close>
fun highest_path :: "transition \<Rightarrow> path" where
  "highest_path (Trans (P p) str c a1 a2 (P q)) = (lca p q)"
| "highest_path (Trans (P p) str c a1 a2 (J q)) = (lca p q)"
| "highest_path (Trans (J p) str c a1 a2 (P q)) = (lca p q)"
| "highest_path (Trans (J p) str c a1 a2 (J q)) = (lca p q)"
| "highest_path (Trans (J p) str c a1 a2 (HJ q)) = (lca p q)"
| "highest_path (Trans (P p) str c a1 a2 (HJ q)) = (lca p q)"
| "highest_path (Trans (HJ p) va vb vc vd ve) = []"
|  "highest_path (Trans vg va vb vc vd NONE) = []"
|  "highest_path (Trans NONE va vb vc vd ve) = []"


\<comment> \<open>FindState1 and FindState2 return the state referred to by the given path.\<close>
primrec FindState1 :: "path \<Rightarrow> comp \<Rightarrow> state" 
    and FindState2 :: "path \<Rightarrow> state \<Rightarrow> state" where
  "FindState1 p No_Composition = No_State"
| "FindState1 p (And pl f) = (if (f(hd p) = No_State) then No_State
                else (FindState2 (tl p) (f(hd p))))"
| "FindState1 p (Or TL b  f) = (if (f(hd p) = No_State) then No_State
                else (FindState2 (tl p) (f(hd p))))"
| "FindState2 p No_State  = No_State"
| "FindState2 p (State name a1 a2 a3 tl1 tl2 C) = (if (p = []) then
  (State name a1 a2 a3 tl1 tl2 C) else (FindState1 p C))"

primrec FindComposition1 :: "path \<Rightarrow> comp \<Rightarrow> comp" 
    and FindComposition2 :: "path \<Rightarrow> state \<Rightarrow> comp" where
  "FindComposition1 p No_Composition = No_Composition"
| "FindComposition1 p (And pl f) = (if (p = []) then (And pl f)
                else (FindComposition2 (tl p) (f(hd p))))"
| "FindComposition1 p (Or TL b f) = (if (p = []) then (Or TL b f)
                else (FindComposition2 (tl p) (f(hd p))))"
| "FindComposition2 p No_State  = No_Composition"
| "FindComposition2 p (State name a1 a2 a3 tl1 tl2 C) = (FindComposition1 p C)"

fun entry_path :: "path \<Rightarrow> path \<Rightarrow> path" where
  "entry_path p [] = []"
| "entry_path [] p = p"
| "entry_path (a#p1) (b#p2) = (if (a = b) then (entry_path p1 p2) else (b#p2))"

value "entry_path [''A'',''B'',''D''] [''A'', ''B'', ''C'']"
value "lca [''A'', ''B''] [''A'', ''C'']"

fun update_vals1 :: "exp \<Rightarrow> exp \<Rightarrow> vals \<Rightarrow> vals" where
  "update_vals1 a1 (V x) (Vals s1 h1 h2 h3 (output1, output2)) = 
    (Vals (s1(x := (aval a1 (Vals s1 h1 h2 h3 (output1, output2)) []))) h1 h2 h3 (output1, output2))"
| "update_vals1 a1 a2 v = v"

inductive update_vals2 :: "exp2 \<Rightarrow> exp2 \<Rightarrow> vals \<Rightarrow> vals \<Rightarrow> bool" where
  Update_NoExpr1: "update_vals2 No_Expr a2 v v"
| Update_NoExpr2: "update_vals2 a1 No_Expr v v"
| Update_exp2: "a1 = ([[a1_1, a1_2]])
  \<Longrightarrow> a2 = ([[a2_1, a2_2]])
  \<Longrightarrow> v2 = update_vals1 a1_1 a2_1 v1
  \<Longrightarrow> update_vals2 a1_2 a2_2 v2 v3
  \<Longrightarrow> update_vals2 a1 a2 v1 v3"

type_synonym con = bool (*con = true when the source is active, otherwise con = false*)
type_synonym is_send = bool (*is_send = true when the execution is in "Send"*)
type_synonym transition_status = int  (*-1,0,1*)
type_synonym path2state = "path \<Rightarrow> state"
type_synonym string2state = "string \<Rightarrow> state"
type_synonym transition_actions = "act list"
text \<open>all execution need to be written together\<close>
text \<open>each execution contains two Compositions(Chart),
the first comp is fixed by Root\<close>
inductive act_exec :: "env \<Rightarrow> act \<Rightarrow> string \<Rightarrow> source_state \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool"
\<comment> \<open>the static env; act; event;dynamic status; source state path for send; 
dynamic status after execution; early return tag\<close>
  and actlist_exec :: "env \<Rightarrow> act list \<Rightarrow> string \<Rightarrow> source_state \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool"
\<comment> \<open>the same as above\<close>
  and trans_exec :: "env \<Rightarrow> transition \<Rightarrow> string \<Rightarrow> source_state \<Rightarrow> status 
  \<Rightarrow> status \<Rightarrow> con \<Rightarrow> act \<Rightarrow> source_target \<Rightarrow> bool"
  and translist_exec :: "env \<Rightarrow> transition list \<Rightarrow> string \<Rightarrow> source_state \<Rightarrow> status
  \<Rightarrow> status \<Rightarrow> transition_status \<Rightarrow> con \<Rightarrow> transition_actions \<Rightarrow> source_target \<Rightarrow> path \<Rightarrow> bool"
\<comment> \<open>the static env; transition list; triggering string; dynamic status; source_path; 
dynamic status after execution;transition status(0,1,-1); early return tag; 
transition act(list); target; p is the highest path in transition\<close>
  and comp_exit :: "env \<Rightarrow> comp \<Rightarrow> path \<Rightarrow> string \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool" 
\<comment> \<open>the static env; comp; name for comp Info; event;dynamic status; 
dynamic status after execution; con\<close>
  and state_exit :: "env \<Rightarrow> state \<Rightarrow> string \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool"
  and pathlist_exit :: "env \<Rightarrow> string list \<Rightarrow> string \<Rightarrow> string2state \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool" 

  and comp_entry :: "env \<Rightarrow> comp \<Rightarrow> path \<Rightarrow> string \<Rightarrow> path \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool"
\<comment> \<open>the static env; comp; name for comp Info; dynamic status; 
string is the triggering event for default transition; entry path for transition target;
dynamic status after execution; con\<close>
  and state_entry :: "env \<Rightarrow> state \<Rightarrow> string \<Rightarrow> path \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool"
\<comment> \<open>path here is the entry path for transition target\<close>
  and pathlist_entry :: "env \<Rightarrow> string list \<Rightarrow> string2state \<Rightarrow> 
    string \<Rightarrow> path \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool" 
\<comment> \<open>the static env; state; triggering event; dynamic status; 
dynamic status after execution; con; is_send = True to pause the clock\<close>
  and state_exec :: "env \<Rightarrow> state \<Rightarrow> string \<Rightarrow> is_send \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool"
  and comp_exec :: "env \<Rightarrow> comp \<Rightarrow> path \<Rightarrow> string \<Rightarrow> is_send \<Rightarrow> status \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool" 
  and pathlist_exec :: "env \<Rightarrow> string list \<Rightarrow> string2state \<Rightarrow> string \<Rightarrow> is_send \<Rightarrow> status
        \<Rightarrow> status \<Rightarrow> con \<Rightarrow> bool" where
  Skip: "act_exec env SKIP e scr_p s s True"

| Assign: "v1 = (Vals h1 h2 h3 h4 (output1, output2))
  \<Longrightarrow> v2 = (Vals (h1(x := aval a v1 src_p)) h2 h3 h4 (output1, output2)) 
  \<Longrightarrow> act_exec env (x ::= a) e src_p (Status v1 I) (Status v2 I) True"

| On1: " tval1 temporal_logic (get_vals s1) src_p = True
  \<Longrightarrow> act_exec env c e src_p s1 s2 b
  \<Longrightarrow> act_exec env (on1 temporal_logic :: c) e src_p s1 s2 b"
| On2: " tval1 temporal_logic (get_vals s) src_p = False
  \<Longrightarrow> act_exec env (on1 temporal_logic :: c) e src_p s s True"

| On3: "e = event
  \<Longrightarrow> act_exec env c e src_p s1 s2 b
  \<Longrightarrow> act_exec env (on2 event :: c) e src_p s1 s2 b"
| On4: "e \<noteq> event
  \<Longrightarrow> act_exec env (on2 event :: c) e src_p s s True"

| Print1: "v1 = (Vals h1 h2 h3 h4 (output1, output2))
  \<Longrightarrow> v2 = (Vals h1 h2 h3 h4 (output1@[a], output2))
  \<Longrightarrow> act_exec env (Print1 a) e src_p (Status v1 I) (Status v2 I) True"
| Print2: "v1 = (Vals h1 h2 h3 h4 (output1, output2))
  \<Longrightarrow> v2 = (Vals h1 h2 h3 h4 (output1, output2@[aval a v1 src_p]))
  \<Longrightarrow> act_exec env (Print2 a) e src_p (Status v1 I) (Status v2 I) True"

| Send1: "comp_exec env (get_root env) [] e True (Status v1 I1) (Status v2 I2) b
  \<Longrightarrow> (I2 src_p = Info b1 str1 str2)
  \<Longrightarrow> act_exec env (send1 e False) e0 src_p (Status v1 I1) (Status v2 I2) b1"

| Send2: "comp_exec env (get_root env) [] e True (Status v1 I1) (Status v2 I2) b
  \<Longrightarrow> (I2 (butlast src_p) = Info b1 str1 str2)
  \<Longrightarrow> b3 = (b1 \<and> (str1 = []))
  \<Longrightarrow> act_exec env (send1 e True) e0 src_p (Status v1 I1) (Status v2 I2) b3"

\<comment> \<open>send e to a specific state\<close>
| Send3: "state_exec env (FindState1 p (get_root env)) e True (Status v1 I1) (Status v2 I2) b
  \<Longrightarrow> (I2 src_p = Info b1 str1 str2)
  \<Longrightarrow> act_exec env (send2 e False p) e0 src_p (Status v1 I1) (Status v2 I2) b1"
| Send4: "state_exec env (FindState1 p (get_root env)) e True (Status v1 I1) (Status v2 I2) b
  \<Longrightarrow> (I2 (butlast src_p) = Info b1 str1 str2)
  \<Longrightarrow> b3 = (b1 \<and> (str1 = []))
  \<Longrightarrow> act_exec env (send2 e True p) e0 src_p (Status v1 I1) (Status v2 I2) b3"
\<comment> \<open>send Message\<close>
| Send5: "v1 = (Vals h1 h2 h3 h4 (output1, output2))
\<Longrightarrow> act_exec env (send3 vname) e src_p (Status v1 I) 
(Status (Vals h1 h2 h3 (h4(vname := (h4 vname)@[(aval (V vname) v1 src_p)] )) (output1, output2)) I ) True"
| Seq1: "act_exec env c\<^sub>1 e src_p s1 s2 True \<Longrightarrow>
        act_exec env c\<^sub>2 e src_p s2 s3 b \<Longrightarrow>
        act_exec env (c\<^sub>1;c\<^sub>2) e src_p s1 s3 b"
| Seq2: "act_exec env c\<^sub>1 e src_p s1 s2 False \<Longrightarrow>
        act_exec env (c\<^sub>1;c\<^sub>2) e src_p s1 s2 False"

| Funapp: "fe = get_fenv env
  \<Longrightarrow> update_vals2 a2 (fst(snd(fe f))) v1 v2
  \<Longrightarrow> act_exec env (fst(fe f)) e src_p (Status v2 I1) (Status v3 I2) True
  \<Longrightarrow> update_vals2 (snd(snd(fe f))) a1 v3 v4
  \<Longrightarrow> act_exec env (a1 ::= f<a2>) e src_p (Status v1 I1) (Status v4 I2) True"

| Grafun: "ge = get_genv env
  \<Longrightarrow> update_vals2 a2 (fst(snd(ge f))) v1 v2
  \<Longrightarrow> translist_exec env [fst(ge f)] '''' src_p  (Status v2 I1)
                (Status v3 I2) (-1) True [] trg p
  \<Longrightarrow> update_vals2 (snd(snd(ge f))) a1 v3 v4
  \<Longrightarrow> act_exec env (a1 ::= f<<a2>>) e src_p (Status v1 I1) (Status v4 I2) True"
(*| Funapp: "act_exec env (fst(fe f)) v1 src_p Chart1 g v2 Chart2 True
  \<Longrightarrow> v2 = (Vals s2 h21 h22 (output1, output2)) 
  \<Longrightarrow> s3 = (s2(x := (aval (snd(fe f)) v2 src_p))) 
  \<Longrightarrow> act_exec env (x ::= f<a>) v1 src_p Chart1 g (Vals s3 h21 h22 (output1, output2)) Chart2 True"
|Grafun:  "translist_exec env [(fst(snd(ge f)))] e v1 src_p g (-1) Chart1 v2 Chart2 True [] trg p \<Longrightarrow>
          trg = (J (snd(snd(ge f)))) \<Longrightarrow>
          v2 = (Vals s2 h21 h22 o2) \<Longrightarrow>
          s3 = s2(x := aval (snd(fe f)) v2 src_p) \<Longrightarrow>
          act_exec env (x ::= f<<a>>) v1 src_p Chart1 g (Vals s3 h21 h22 o2) Chart2 True"*)
\<comment> \<open>act list for transition list\<close>

| ActionList_Execution1:"actlist_exec env [] e src_p s s True"

| ActionList_Execution2:"act_exec env a e src_p s1 s2 True
  \<Longrightarrow> actlist_exec env al e src_p s2 s3 b
  \<Longrightarrow> actlist_exec env (a#al) e src_p s1 s3 b"
| ActionList_Execution3:"act_exec env a e src_p s1 s2 False
  \<Longrightarrow> actlist_exec env (a#al) e src_p s1 s2 False"


| Trans_Execution1:"enable t e (Status v1 I1) src_p
  \<Longrightarrow> (Status v2 I2) = update_status t (Status v1 I1)
  \<Longrightarrow> act_exec env (condition_action t) e src_p (Status v2 I2) (Status v3 I3) True
  \<Longrightarrow> a = (transition_action t) 
  \<Longrightarrow> trg = (target t)
  \<Longrightarrow> trans_exec env t e src_p (Status v1 I1) (Status v3 I3) True a trg"

| Trans_Execution2:"enable t e (Status v1 I1) src_p
  \<Longrightarrow> (Status v2 I2) = update_status t (Status v1 I1)
  \<Longrightarrow> act_exec env (condition_action t) e src_p (Status v2 I2) (Status v3 I3) False
  \<Longrightarrow> trans_exec env t e src_p (Status v1 I1) (Status v3 I3) False SKIP NONE"


\<comment> \<open>If the first transition is not enabled, the rest list is executed.
   e is triggering event, s is initial valuation, g is junction function
   n1 is status indicating and n2 is send condition
   whether the transition succeeds, fails or goes to a terminal junction\<close>

| TLinduction: "\<not>(enable t e s1 src_p)
  \<Longrightarrow> s2 = update_status t s1
  \<Longrightarrow> T \<noteq> []
  \<Longrightarrow> translist_exec env T e src_p s2 s3 n b A trg p
  \<Longrightarrow> translist_exec env (t#T) e src_p s1 s3 n b A trg p"

\<comment> \<open>When the last transition fails, the transition list fails, with status 0.\<close>
| Fail: "\<not>(enable t e s1 src_p)
  \<Longrightarrow> s2 = update_status t s1
  \<Longrightarrow> translist_exec env [t] e src_p s1 s2 (0::int) True [] NONE []"
\<comment> \<open>The transition goes to a terminal junction.\<close>
| Termination: "translist_exec env [] e src_p s s (-1::int) True [] NONE []"
\<comment> \<open>The transition t reaches a state target (with status 1), and the execution completes.\<close>

| ToState: "trans_exec env t e src_p s1 s2 True a trg
  \<Longrightarrow> trg = P p1
  \<Longrightarrow> p = (highest_path t)
  \<Longrightarrow> translist_exec env (t#T) e src_p s1 s2 (1::int) True [a] trg p"
| ToHistoryJunction: "trans_exec env t e src_p (Status v1 I1) (Status v2 I2) True a trg
  \<Longrightarrow> trg = HJ p1
  \<Longrightarrow> p = (highest_path t)
  \<Longrightarrow> str1 = history_active_string p1 I2
  \<Longrightarrow> str2 = (if str1 \<noteq> [] then [str1] else []::string list)
  \<Longrightarrow> translist_exec env (t#T) e src_p (Status v1 I1) 
                (Status v2 I2) (1::int) True [a] (P (p1@str2)) p"

\<comment> \<open>the transition t lead its source inactive\<close>
| SrcInactive: "trans_exec env t e src_p s1 s2 False a trg
  \<Longrightarrow> translist_exec env (t#T) e src_p s1 s2 (1::int) False [] NONE []"
\<comment> \<open>The transition t reaches a junction first, and then goes to a target state.
    The context of the transition path is defined by p2.\<close>

| ToJunctionInduction1: "trans_exec env t e src_p s1 s2 True a (J str)
  \<Longrightarrow> g = get_juncs env
  \<Longrightarrow> translist_exec env (g(str)) e src_p s2 s3 (1::int) True A trg2 p1
  \<Longrightarrow> p2 = (lca (highest_path t) p1)
  \<Longrightarrow> translist_exec env (t#T) e src_p s1 s3 (1::int) True (a#A) trg2 p2"

\<comment> \<open>The transition t reaches a junction first, and then leads its source inactive\<close>
| ToJunctionInduction2: "trans_exec env t e src_p s1 s2 True a (J str)
  \<Longrightarrow> g = get_juncs env
  \<Longrightarrow> translist_exec env (g(str)) e src_p s2 s3 n False A trg2 p
  \<Longrightarrow> translist_exec env (t#T) e src_p s1 s3 n False [] NONE []"

\<comment> \<open>The first transition is enabled but fails due to the failing of junctions\<close>
| ToJunctionInduction3: "trans_exec env t e src_p s1 s2 True a (J str)
  \<Longrightarrow> g = get_juncs env
  \<Longrightarrow> translist_exec env (g(str)) e src_p s2 s3 (0::int) True [] NONE []
  \<Longrightarrow> T \<noteq> [] 
  \<Longrightarrow> translist_exec env T e src_p s3 s4 n1 b A trg2 p
  \<Longrightarrow> translist_exec env (t#T) e src_p s1 s4 n1 b A trg2 p"

\<comment> \<open>The last transition is enabled but fails. 
3 and 4 can't be merged because T=[] lead to n1 = -1 not 0\<close>
| ToJunctionInduction4: "trans_exec env t e src_p s1 s2 True a (J str)
  \<Longrightarrow> g = get_juncs env
  \<Longrightarrow> translist_exec env (g(str)) e src_p s2 s3 (0::int) True [] NONE []
  \<Longrightarrow> translist_exec env [t] e src_p s1 s3 (0::int) True [] NONE []"

\<comment> \<open>The transition t is enabled but reaches a terminal junction, then the
    execution terminates.\<close>
| ToJunctionInduction5: "trans_exec env t e src_p s1 s2 True a (J str)
  \<Longrightarrow> g = get_juncs env
  \<Longrightarrow> translist_exec env (g(str)) e src_p s2 s3 (-1::int) True [] NONE []
  \<Longrightarrow> translist_exec env (t#T) e src_p s1 s3 (-1::int) True [] NONE []"


\<comment> \<open>For exiting a state, the composition exits, then the state exits by executing
    the exit act.\<close>
\<comment> \<open>when execute exit actions, we can not use temporal logic because they only occur
in during actions ans transitions, but when exit a state we should set "n = 0"\<close>

| State_Exit1:"(ST = State name a1 a2 a3 tl1 tl2 C)
  \<Longrightarrow> is_active_state name I1 = True
  \<Longrightarrow> comp_exit env C name e (Status v1 I1) s2 True
  \<Longrightarrow> act_exec env a3 e name s2 (Status v3 I3) True
  \<Longrightarrow> I3 name = Info b1 str1 str2
  \<Longrightarrow> I4 = I3(name := Info False str1 str2)
  \<Longrightarrow> state_exit env ST e (Status v1 I1) (Status v3 I4) True"

|  State_Exit2:"state_exit env No_State e s s True"
| State_Exit3:"(ST = State name a1 a2 a3 tl1 tl2 C)
  \<Longrightarrow> is_active_state name I = False
  \<Longrightarrow> state_exit env ST e (Status v I) (Status v I) True"

| State_Exit4:"(ST = State name a1 a2 a3 tl1 tl2 C)
  \<Longrightarrow> is_active_state name I1 = True
  \<Longrightarrow> comp_exit env C name e (Status v1 I1) s2 False
  \<Longrightarrow> state_exit env ST e (Status v1 I1) s2 False"
| State_Exit5:"(ST = State name a1 a2 a3 tl1 tl2 C)
  \<Longrightarrow> is_active_state name I1 = True
  \<Longrightarrow> comp_exit env C name e (Status v1 I1) s2 True
  \<Longrightarrow> act_exec env a3 e name s2 s3 False
  \<Longrightarrow> state_exit env ST e (Status v1 I1) s3 False"

| No_Composition_Exit:"comp_exit env No_Composition name e s s True"

\<comment> \<open>The Or composition exits by exiting the active state.\<close>
| Or_Exit1:"C = (Or TL b f)
  \<Longrightarrow> I1 name = Info b1 str1 str2
  \<Longrightarrow> state_exit env (f(str1)) e (Status v1 I1) (Status v2 I2) True
  \<Longrightarrow> str2' = (if b then str1 else [])
  \<Longrightarrow> I3 = (I2(name := Info b1 [] str2'))
  \<Longrightarrow> comp_exit env C name e (Status v1 I1) (Status v2 I3) True"
\<comment> \<open>here the C is active, but finally whether C becomes inactive or not\<close>
| Or_Exit2:"C = (Or TL b f)
  \<Longrightarrow> I1 name = Info b1 str1 str2
  \<Longrightarrow> state_exit env (f(str1)) e (Status v1 I1) s2 False
  \<Longrightarrow> comp_exit env C name e (Status v1 I1) s2 False"

\<comment> \<open>A sequence of and states exits, by exiting them
    in reverse order.\<close>
| Empty_List_Exit: "pathlist_exit env [] e f s s True"

\<comment> \<open>list exit and state exit may lead con = False\<close>
| List_Exit1:"state_exit env (f(str)) e s1 s2 True
  \<Longrightarrow> pathlist_exit env sl e f s2 s3 b
  \<Longrightarrow> pathlist_exit env (sl@[str]) e f s1 s3 b"
| List_Exit2:"state_exit env (f(str)) e s1 s2 False
  \<Longrightarrow> pathlist_exit env (sl@[str]) e f s1 s2 False"

\<comment> \<open>An and diagram exits, by exiting all the parallel
    states in reverse order. \<close>
| And_Exit1:"C = (And sl f)
  \<Longrightarrow> pathlist_exit env sl e f s1 (Status v2 I2) True
  \<Longrightarrow> comp_exit env C name e s1 (Status v2 (I2(name := Info False [] []))) True"
| And_Exit2:"C = (And sl f)
  \<Longrightarrow> pathlist_exit env sl e f s1 s2 False
  \<Longrightarrow> comp_exit env C name e s1 s2 False"

\<comment> \<open>The state is entered by executing the entry act of the state first,
    and then entering the composition.\<close>

\<comment> \<open>when we entry a state, temporal logic cannot be used either. 
And here we set "n = 0"\<close>

| State_Entry1:"(ST = State name a1 a2 a3 tl1 tl2 C) 
  \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
  \<Longrightarrow> v2 = (Vals h1 (h2(name := (\<lambda>str. 0::int))) (h3(name := 0 )) h4 (output1, output2))
  \<Longrightarrow> I1 name = Info b1 str1 str2
  \<Longrightarrow> I1 (butlast name) = Info b1' str1' str2'
  \<Longrightarrow> I_tmp = Info True (last name) str2'
  \<Longrightarrow> I2 = I1(name := Info True str1 str2,
                      (butlast name):= I_tmp)
  \<Longrightarrow> act_exec env a1 e name (Status v2 I2) (Status v3 I3) True
  \<Longrightarrow> comp_entry env C name e (tl p) (Status v3 I3) (Status v4 I4) b
  \<Longrightarrow> state_entry env ST e p (Status v1 I1) (Status v4 I4) b"

| State_Entry2:" state_entry env No_State e p s s True"

| State_Entry3:"(ST = State name a1 a2 a3 tl1 tl2 C) 
  \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
  \<Longrightarrow> v2 = (Vals h1 (h2(name := (\<lambda>str. 0::int))) (h3(name := 0 )) h4 (output1, output2))
  \<Longrightarrow> I1 name = Info b1 str1 str2
  \<Longrightarrow> I1 (butlast name) = Info b1' str1' str2'
  \<Longrightarrow> I_tmp = Info True (last name) str2'
  \<Longrightarrow> I2 = I1(name := Info True str1 str2,
                      (butlast name):= I_tmp)
  \<Longrightarrow> act_exec env a1 e name (Status v2 I2) s3 False
  \<Longrightarrow> state_entry env ST e p (Status v1 I1) s3 False"

| No_Composition_Entry:"comp_entry env No_Composition name e p s s True"

\<comment> \<open>The Or composition is entered, by entering the state that is to be activited
, TL is the default transition list\<close>

| Or_Entry1:"C = Or TL b f
  \<Longrightarrow> p = []
  \<Longrightarrow> b = False
  \<Longrightarrow> translist_exec env TL e name s1 s2 n True A trg p1
  \<Longrightarrow> trg = P p0
  \<Longrightarrow> actlist_exec env A e name s2 s3 True
  \<Longrightarrow> state_entry env (f(hd (entry_path name p0))) e (entry_path name p0) s3 s4 b2
  \<Longrightarrow> comp_entry  env C name e p s1 s4 b2"

| Or_Entry2:"C = Or TL b f
  \<Longrightarrow> p = []
  \<Longrightarrow> b = False
  \<Longrightarrow> translist_exec env TL e name s1 s2 n False A trg p1
  \<Longrightarrow> comp_entry env C name e p s1 s2 False"

| Or_Entry3:"C = Or TL b f
  \<Longrightarrow> p = []
  \<Longrightarrow> b = False
  \<Longrightarrow> translist_exec env TL e name s1 s2 n True A trg p1
  \<Longrightarrow> trg = P p0
  \<Longrightarrow> actlist_exec env A e name s2 s3 False
  \<Longrightarrow> comp_entry env C name e p s1 s3 False"
| Or_Entry5:"C = Or TL b f
  \<Longrightarrow> p = []
  \<Longrightarrow> b = True
  \<Longrightarrow> str2 = history_active_string name I1
  \<Longrightarrow> str2 \<noteq> []
  \<Longrightarrow> state_entry env (f(str2)) e p (Status v1 I1) s2 b2
  \<Longrightarrow> comp_entry env C name e p (Status v1 I1) s2 b2"

| Or_Entry7:"C = Or TL b f
  \<Longrightarrow> p \<noteq> []
  \<Longrightarrow> state_entry env (f(hd p)) e p s1 s2 b2
  \<Longrightarrow> comp_entry env C name e p s1 s2 b2"

| Or_Entry8: "C = Or TL b f
  \<Longrightarrow> p = []
  \<Longrightarrow> b = True
  \<Longrightarrow> str2 = history_active_string name I1
  \<Longrightarrow> str2 = []
  \<Longrightarrow> translist_exec env TL e name (Status v1 I1) s2 n True A trg p1
  \<Longrightarrow> trg = P p0
  \<Longrightarrow> actlist_exec env A e name s2 s3 True
  \<Longrightarrow> state_entry env (f(hd (entry_path name p0))) e (entry_path name p0) s3 s4 b2
  \<Longrightarrow> comp_entry env C name e p (Status v1 I1) s4 b2"

| Or_Entry9: "C = Or TL b f
  \<Longrightarrow> p = []
  \<Longrightarrow> b = True
  \<Longrightarrow> str2 = history_active_string name I1
  \<Longrightarrow> str2 = []
  \<Longrightarrow> translist_exec env TL e name (Status v1 I1) s2 n False A trg p1
  \<Longrightarrow> comp_entry env C name e p (Status v1 I1) s2 False"
| Or_Entry10: "C = Or TL b f
  \<Longrightarrow> p = []
  \<Longrightarrow> b = True
  \<Longrightarrow> str2 = history_active_string name I1
  \<Longrightarrow> str2 = []
  \<Longrightarrow> translist_exec env TL e name (Status v1 I1) s2 n True A trg p1
  \<Longrightarrow> trg = P p0
  \<Longrightarrow> actlist_exec env A e name s2 s3 False
  \<Longrightarrow> comp_entry env C name e p (Status v1 I1) s3 False"

| Empty_List_Entry: "pathlist_entry env [] f e p s s True"

\<comment> \<open>A sequence of and states is entered in the sequential order.\<close>
\<comment> \<open>hd p is used to locate the target\<close>
| Path_List_Entry1:"str = (hd p)
  \<Longrightarrow> state_entry  env (f(str)) e p s1 s2 True
  \<Longrightarrow> pathlist_entry env sl f e p s2 s3 b
  \<Longrightarrow> pathlist_entry env (str#sl) f e p s1 s3 b"
| Path_List_Entry2:"str = (hd p)
  \<Longrightarrow> state_entry env (f(str)) e p s1 s2 False
  \<Longrightarrow> pathlist_entry env (str#sl) f e p s1 s2 False"

| Path_List_Entry4:"str \<noteq> (hd p)
  \<Longrightarrow> state_entry env (f(str)) e [] s1 s2 True
  \<Longrightarrow> pathlist_entry env sl f e p s2 s3 b
  \<Longrightarrow> pathlist_entry env (str#sl) f e p s1 s3 b"
| Path_List_Entry5:"str \<noteq> (hd p)
  \<Longrightarrow> state_entry env (f(str)) e [] s1 s2 False
  \<Longrightarrow> pathlist_entry env (str#sl) f e p s1 s2 False"


\<comment> \<open>An And diagram is entered by entering all the parallel states.\<close>
| And_Entry:"C = (And sl f)
  \<Longrightarrow> pathlist_entry env sl f e p s1 s2 b
  \<Longrightarrow> comp_entry env C name e p s1 s2 b"

| No_Composition_Execution:
  "comp_exec env No_Composition name e is_send s s True"
| No_State_Execution:"state_exec env No_State e is_send s s True"
| Inactive_State_Execution: "ST = (State name a1 a2 a3 tl1 tl2 C)
  \<Longrightarrow> is_active_state name I = False
  \<Longrightarrow> state_exec env ST e is_send (Status v I) (Status v I) True"

\<comment> \<open>temporal event's count++ in a state_exec,
 here we update the state in the "Chart" at the beginning. And we need 
set temporal count in every transition and during_action 
because "count" may be changed during the execution
CASE: send will increase the temporal count but remain the state "time"\<close>
| Outer_Trans_Execution1:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) (Status v3 I2) (1::int) True A trg path
   \<Longrightarrow> trg = P p
   \<Longrightarrow> ex_ST = (if name = path then (butlast name) else (lca name path))
   \<Longrightarrow> comp_exit env (FindComposition1 ex_ST (get_root env)) ex_ST e (Status v3 I2) 
                  (Status v4 I3) True
   \<Longrightarrow> actlist_exec env A e name (Status v4 I3) (Status v5 I4) True
   \<Longrightarrow> en_ST = (if name = path then (butlast p) else (lca p path))
   \<Longrightarrow> p1 = (if name = path then [last p] else (entry_path path p))
   \<Longrightarrow> comp_entry env (FindComposition1 en_ST (get_root env)) en_ST e p1 (Status v5 I4)
                  (Status v6 I5) b
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v6 I5) b"

| Outer_Trans_Termination:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) (Status v3 I2) n False A trg path
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v3 I2) False"

| Outer_Trans_Execution2:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) (Status v3 I2) (1::int) True A trg path
   \<Longrightarrow> trg = P p
   \<Longrightarrow> ex_ST = (if name = path then (butlast name) else (lca name path))
   \<Longrightarrow> comp_exit env (FindComposition1 ex_ST (get_root env)) ex_ST e (Status v3 I2) 
                  (Status v4 I3) False
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v4 I3) False"

| Outer_Trans_Execution3:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) (Status v3 I2) (1::int) True A trg path
   \<Longrightarrow> trg = P p
   \<Longrightarrow> ex_ST = (if name = path then (butlast name) else (lca name path))
   \<Longrightarrow> comp_exit env (FindComposition1 ex_ST (get_root env)) ex_ST e (Status v3 I2) 
                  (Status v4 I3) True
   \<Longrightarrow> actlist_exec env A e name (Status v4 I3) (Status v5 I4) False
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v5 I4) False"

| Inner_Trans_Execution1:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) (Status v3 I2) n True A trg1 path1
   \<Longrightarrow> n = 0 \<or> n = -1
   \<Longrightarrow> act_exec env a2 e name (Status v3 I2) (Status v4 I3) True
   \<Longrightarrow> translist_exec env tl1 e name (Status v4 I3) (Status v5 I4) (1::int) True A2 trg2 path
   \<Longrightarrow> trg2 = P p
   \<Longrightarrow> ex_ST = (lca name path)
   \<Longrightarrow> comp_exit env (FindComposition1 ex_ST (get_root env)) ex_ST e 
       (Status v5 I4) (Status v6 I5) True
   \<Longrightarrow> actlist_exec env A2 e name (Status v6 I5) (Status v7 I6) True
   \<Longrightarrow> p1 = (entry_path path p)
   \<Longrightarrow> p2 = (if (name = p) then name else (butlast p))
   \<Longrightarrow> comp_entry env (FindComposition1 p2 (get_root env)) p2 e p1 (Status v7 I6)
                   (Status v8 I7) b
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v8 I7) b"

| Inner_Trans_Execution2:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) (Status v3 I2) n True A trg1 path1
   \<Longrightarrow> n = 0 \<or> n = -1
   \<Longrightarrow> act_exec env a2 e name (Status v3 I2) (Status v4 I3) False
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v4 I3) False"
| Inner_Trans_Execution3:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) (Status v3 I2) n True A trg1 path1
   \<Longrightarrow> n = 0 \<or> n = -1
   \<Longrightarrow> act_exec env a2 e name (Status v3 I2) (Status v4 I3) True
   \<Longrightarrow> translist_exec env tl1 e name (Status v4 I3) (Status v5 I4) (1::int) True A2 trg2 path
   \<Longrightarrow> trg2 = P p
   \<Longrightarrow> ex_ST = (lca name path)
   \<Longrightarrow> comp_exit env (FindComposition1 ex_ST (get_root env)) ex_ST e 
       (Status v5 I4) (Status v6 I5) False
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v6 I5) False"
| Inner_Trans_Execution4:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) (Status v3 I2) n True A trg1 path1
   \<Longrightarrow> n = 0 \<or> n = -1
   \<Longrightarrow> act_exec env a2 e name (Status v3 I2) (Status v4 I3) True
   \<Longrightarrow> translist_exec env tl1 e name (Status v4 I3) (Status v5 I4) (1::int) True A2 trg2 path
   \<Longrightarrow> trg2 = P p
   \<Longrightarrow> ex_ST = (lca name path)
   \<Longrightarrow> comp_exit env (FindComposition1 ex_ST (get_root env)) ex_ST e 
       (Status v5 I4) (Status v6 I5) True
   \<Longrightarrow> actlist_exec env A2 e name (Status v6 I5) (Status v7 I6) False
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v7 I6) False"

| Inner_Trans_Termination:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) (Status v3 I2) n True A trg1 path1
   \<Longrightarrow> n = 0 \<or> n = -1
   \<Longrightarrow> act_exec env a2 e name (Status v3 I2) (Status v4 I3) True
   \<Longrightarrow> translist_exec env tl1 e name (Status v4 I3) (Status v5 I4) n2 False A2 trg2 path
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v5 I4) False"

| Fail_Trans_Execution:
  "ST1 = (State name a1 a2 a3 tl1 tl2 C)
   \<Longrightarrow> is_active_state name I1 = True
   \<Longrightarrow> v1 = (Vals h1 h2 h3 h4 (output1, output2))
   \<Longrightarrow> h2' = h2(name := ((h2 name)(e := (h2 name e)+1 , ''tick'' := (h2 name ''tick'')+1 )))
   \<Longrightarrow> h3' = (if (is_send = True) then h3 else h3(name := (h3 name)+1))
   \<Longrightarrow> v2 = (Vals h1 h2' h3' h4 (output1, output2))
   \<Longrightarrow> translist_exec env tl2 e name (Status v2 I1) s2 n1 True A trg1 path1
   \<Longrightarrow> n1 = 0 \<or> n1 = -1
   \<Longrightarrow> act_exec env a2 e name s2 (Status v4 I3) True
   \<Longrightarrow> translist_exec env tl1 e name (Status v4 I3) (Status v5 I4) n2 True A2 trg2 path
   \<Longrightarrow> n2 = 0 \<or> n2 = -1
   \<Longrightarrow> comp_exec env C name e is_send (Status v5 I4) (Status v6 I5) b
   \<Longrightarrow> state_exec env ST1 e is_send (Status v1 I1) (Status v6 I5) b"

| Or_Execution:"C = Or TL b f
   \<Longrightarrow> is_active_state [] I1 = True
   \<Longrightarrow> str1 = current_active_string name I1
   \<Longrightarrow> state_exec env (f(str1)) e is_send (Status v1 I1) s2 b1
   \<Longrightarrow> comp_exec env C name e is_send (Status v1 I1) s2 b1"

(*SC is the Stateflow Chart state*)
| Start_Execution:"C \<noteq> No_Composition
   \<Longrightarrow> is_active_state [] I1 = False
   \<Longrightarrow> SC = State [] SKIP SKIP SKIP [] [] C   
   \<Longrightarrow> state_entry env SC e [] (Status v1 I1) s2 b1
   \<Longrightarrow> comp_exec env C name e is_send (Status v1 I1) s2 b1"

| Empty_Pathlist_Execution:
  "pathlist_exec env [] f e is_send s s True"

| Pathlist_Execution1:"state_exec env (f(str)) e is_send s1 s2 True
   \<Longrightarrow> pathlist_exec env strl f e is_send s2 s3 b
   \<Longrightarrow> pathlist_exec env (str#strl) f e is_send s1 s3 b"
| Pathlist_Execution2:"state_exec env (f(str)) e is_send s1 s2 False
   \<Longrightarrow> pathlist_exec env (str#strl) f e is_send s1 s2 False"

| And_Execution:"C = And strl f
   \<Longrightarrow> is_active_state [] (get_ctxt s1) = True
   \<Longrightarrow> pathlist_exec env strl f e is_send s1 s2 b
   \<Longrightarrow> comp_exec env C name e is_send s1 s2 b"


inductive Root_Exec_for_times :: "env \<Rightarrow> string list \<Rightarrow> int \<Rightarrow> status \<Rightarrow> status \<Rightarrow> bool" where
Root_Exec_for_Times1: "Root_Exec_for_times env el 0 s s"
| Root_Exec_for_Times2: "n > 0
  \<Longrightarrow> comp_exec env (get_root env) [] (hd el) False s1 s2 b
  \<Longrightarrow> Root_Exec_for_times env (tl el) (n-1) s2 s3
  \<Longrightarrow> Root_Exec_for_times env el n s1 s3"


end


