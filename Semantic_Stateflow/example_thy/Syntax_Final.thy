theory Syntax_Final
  imports Complex_Main 
begin

subsection \<open>Syntax\<close>

type_synonym vname = string
type_synonym fname = string
type_synonym val = real
\<comment> \<open>get_val means variable's value\<close>
type_synonym var_val = "vname \<Rightarrow> val"
type_synonym path = "string list"
\<comment> \<open>we use h1 and h2 to deal with temporal logic,
h1 is for event, h2 is for tick count\<close>
type_synonym event_val = "path \<Rightarrow> vname \<Rightarrow> int"
type_synonym time_val = "path \<Rightarrow> real"
type_synonym message_val = "vname \<Rightarrow> real list"
datatype vals =  Vals "var_val" "event_val" "time_val" "message_val" "string list \<times> real list"


datatype exp = N real | V vname 
  | Plus exp exp   ("_[+]_"  [100,100] 48)
  | Minus exp exp  ("_[-]_"  [100,100] 48)
  | Multiply exp exp ("_[*]_"  [100,100] 47)
  | Divide exp exp   ("_[div]_"  [100,100] 46)
  | TemporalCount vname       (*only occurs in state actions*)

(*the following exp2 is for function calls*)
datatype exp2 = No_Expr
  | Concat exp exp2 ("[[_,_]]"   [100,100] 45)

fun aval :: "exp \<Rightarrow> vals \<Rightarrow> path \<Rightarrow> val" where
  "aval (N n) v p = n" |
  "aval (V x) (Vals s h1 h2 h3 (output1, output2)) p = s x" |
  "aval (a\<^sub>1 [+] a\<^sub>2) v p = aval a\<^sub>1 v p + aval a\<^sub>2 v p" |
  "aval (a\<^sub>1 [-] a\<^sub>2) v p = aval a\<^sub>1 v p - aval a\<^sub>2 v p" |
  "aval (a\<^sub>1 [*] a\<^sub>2) v p = aval a\<^sub>1 v p * aval a\<^sub>2 v p" |
  "aval (a\<^sub>1 [div] a\<^sub>2) v p = (aval a\<^sub>1 v p) div (aval a\<^sub>2 v p)" |
  "aval (TemporalCount x) (Vals s h1 h2 h3 (output1, output2)) p = (if (x = ''Sec'') then (h2 p) 
                                              else (h1 p x))" 

datatype temp_cond = Before vname exp
  | After vname exp
  | At vname exp
  | Every vname exp

datatype event = S "string list" | T1 temp_cond | M vname

datatype condition = Bc bool | Not condition 
  | And condition condition  ("_&&_")
  | Or condition condition   ("_||_")
  | Less exp exp           ("_[<]_")
  | LessEqual exp exp      ("_[<=]_")
  | Greater exp exp        ("_[>]_")
  | GreaterEqual exp exp   ("_[>=]_")
  | Equal exp exp          ("_[==]_")
  | NotEqual exp exp       ("_[!=]_")
  | T2 temp_cond

\<comment> \<open>calculate for temporal logic
notice that we only use Before and After when E = ''Sec''\<close>
fun tval1 :: "temp_cond \<Rightarrow> vals \<Rightarrow> path \<Rightarrow> bool" where
Before: "tval1 (Before E expr) (Vals s h1 h2 h3 (output1, output2)) p 
         = (if (E = ''Sec'') then ((h2 p) < (aval expr (Vals s h1 h2 h3 (output1, output2)) p)) 
         else (real_of_int(h1 p E) < (aval expr (Vals s h1 h2 h3 (output1, output2)) p)))"
| After: "tval1 (After E expr) (Vals s h1 h2 h3 (output1, output2)) p 
         = (if (E = ''Sec'') then ((h2 p) \<ge> (aval expr (Vals s h1 h2 h3 (output1, output2)) p)) 
         else (real_of_int(h1 p E) >= (aval expr (Vals s h1 h2 h3 (output1, output2)) p)))"
| At: "tval1 (At E expr) (Vals s h1 h2 h3 (output1, output2)) p
         = (real_of_int(h1 p E) = (aval expr (Vals s h1 h2 h3 (output1, output2)) p))" 
| Every: "tval1 (Every E expr) (Vals s h1 h2 h3 (output1, output2)) p 
          = (((h1 p E) > 0) \<and> ((aval expr (Vals s h1 h2 h3 (output1, output2)) p) dvd real_of_int(h1 p E)) )"


\<comment> \<open>calculate for conditions\<close>
fun cval :: "condition \<Rightarrow> vals \<Rightarrow> path \<Rightarrow> bool" where
  bval1:"cval (Bc b) v p = b" |
  "cval (Not b) v p= (\<not> cval b v p)" |
  "cval (b\<^sub>1&&b\<^sub>2) v p = (cval b\<^sub>1 v p \<and> cval b\<^sub>2 v p)" |
  "cval (b\<^sub>1||b\<^sub>2) v p = (cval b\<^sub>1 v p \<or> cval b\<^sub>2 v p)" |
  "cval (a\<^sub>1 [<] a\<^sub>2) v p = (aval a\<^sub>1 v p < aval a\<^sub>2 v p)" |
  "cval (a\<^sub>1 [<=] a\<^sub>2) v p = (aval a\<^sub>1 v p \<le> aval a\<^sub>2 v p)" |
  "cval (a\<^sub>1 [>] a\<^sub>2) v p = (aval a\<^sub>1 v p > aval a\<^sub>2 v p)" |
  "cval (a\<^sub>1 [>=] a\<^sub>2) v p = (aval a\<^sub>1 v p \<ge> aval a\<^sub>2 v p)" |
  "cval (a\<^sub>1 [==] a\<^sub>2) v p = (aval a\<^sub>1 v p = aval a\<^sub>2 v p)" |
  "cval (a\<^sub>1 [!=] a\<^sub>2) v p = (aval a\<^sub>1 v p \<noteq> aval a\<^sub>2 v p)" |
  "cval (T2 temporal_logic) v p = tval1 temporal_logic v p"


type_synonym is_in_transition_action = bool
\<comment> \<open>when act "send" occur in the position of transition act, then 
is_in_transition_action = True, 
otherwise is_in_transition_action = False\<close>
datatype act =
  SKIP    
| Assign vname exp        ("_ ::= _" [1000, 38] 37 )
| Seq    act  act    ("_; _"  [28, 32] 70)
| On1 temp_cond act    ("on1 _:: _" 62)
| On2 string act        ("on2 _:: _" 62)
| Print1 vname         ("print1 _" 63)
| Print2 exp         ("print2 _" 65)
| Send1  string is_in_transition_action   ("send1 _ _" [59] 59)
| Send2  string is_in_transition_action path  ("send2 _ _ _" 64)
(*Send1 for BoardEvent_Send, Send2 for DirectedEvent_Send*)
| Send3  vname    ("send3 _" 64) (*Message Send*)
| Funapp exp2 fname exp2 ("_ ::= _<_>" [1000, 40, 38] 37) (*function application x::=f<e>*)
| Grafun exp2 fname exp2 ("_ ::= _<<_>>" [1000, 40, 38] 37) (*graphical function application x::=f<<e>>*)

text \<open>the middle exp2 is Incoming parameters, the last exp2 is return values\<close>
type_synonym fenv = "fname \<Rightarrow> act \<times> exp2 \<times> exp2"
(*act, function args, function returns*)

text \<open>junction path include the position of the junction, and the last part of 
the path is the junction's name which is unique in a stateflow chart\<close>
datatype source_target = J "path" |P "path" | HJ "path" | NONE

text \<open>source, transition_event, condition, condition act, transition act, target\<close>
datatype transition =  Trans "source_target" "event" "condition"
                  "act" "act" "source_target"

text \<open>give a junction path, return the corresponding transition list\<close>
type_synonym juncs = "path \<Rightarrow> transition list"

text \<open>genv defines a graphical function, with a flow graph, a default transition, and a target junction.\<close>

text \<open>the middle exp2 is Incoming parameters, the last exp2 is return values\<close>
type_synonym genv = "fname \<Rightarrow> transition \<times> exp2 \<times> exp2"

\<comment> \<open>functions for transition\<close>
fun source :: "transition \<Rightarrow> source_target" where
  "source (Trans s _ c a1 a2 t) = s"
fun trans_event :: "transition \<Rightarrow> event" where
  "trans_event (Trans s e c a1 a2 t) = e"
fun trans_c :: "transition \<Rightarrow> condition" where
  "trans_c (Trans s _ c a1 a2 t) = c"
fun condition_action :: "transition \<Rightarrow> act" where
  "condition_action (Trans s _ c a1 a2 t) = a1"
fun transition_action :: "transition \<Rightarrow> act" where
  "transition_action (Trans s _ c a1 a2 t) = a2"
fun target :: "transition \<Rightarrow> source_target" where
  "target (Trans s _ c a1 a2 t) = t"



text \<open>state: name path; entry act; during act; exit act; 
inner transitions; outer transitions; comp;
Or_composition: default transition list;has history junction(bool); map string to state;
And_composition: state string list; map string to state\<close>
datatype state =  State "path" "act" "act" "act" 
"transition list" "transition list" "comp"
| No_State
and comp  = And "string list" "string \<Rightarrow> state"
| Or "transition list" "bool" "string \<Rightarrow> state"
| No_Composition

\<comment> \<open>information: the info for a path
state_is_active; compostion_active_string; 
history_active_string(= [] in the beginning)
note that And_Composition only has the first value 
because transitions cannot start or end in the children of And_State and 
history junction can only occur in a Or_State\<close>
datatype information = Info "bool" "string" "string"
definition h0 :: information where 
  "h0 = Info True [] []"

type_synonym ctxt = "path \<Rightarrow> information"

\<comment> \<open>functions for information\<close>
fun get_Info1 :: "information \<Rightarrow> bool" where
  "get_Info1 (Info b1 str1 str2) = b1"
fun is_active_state :: "path \<Rightarrow> ctxt \<Rightarrow> bool" where
  Is_Active_State:"is_active_state p f = get_Info1 (f p)"

fun get_Info2 :: "information \<Rightarrow> string" where
  "get_Info2 (Info b1 str1 str2) = str1"
fun current_active_string :: "path \<Rightarrow> ctxt \<Rightarrow> string" where
  "current_active_string p f = get_Info2 (f p)"

fun get_Info3 :: "information \<Rightarrow> string" where
  "get_Info3 (Info b1 str1 str2) = str2"
fun history_active_string :: "path \<Rightarrow> ctxt \<Rightarrow> string" where
  "history_active_string p f = get_Info3 (f p)"


\<comment> \<open>functions for state\<close>
fun get_name :: "state \<Rightarrow> path" where
  "get_name (State p _ _ _ _ _ _ ) = p"
| "get_name No_State = []"
fun entry_action :: "state \<Rightarrow> act" where
  "entry_action (State _ a1 _ _ _ _ _ ) = a1"
| "entry_action No_State = SKIP"
fun during_action :: "state \<Rightarrow> act" where
  "during_action (State _ _ a2 _ _ _ _ ) = a2"
| "during_action No_State = SKIP"
fun exit_action :: "state \<Rightarrow> act" where
  "exit_action (State _ _ _ a3 _ _ _ ) = a3"
| "exit_action No_State = SKIP"
fun transition_list_in :: "state \<Rightarrow> transition list" where
  "transition_list_in (State _ _ _ _ trl1 _ _) = trl1"
| "transition_list_in No_State = []"
fun transition_list_out :: "state \<Rightarrow> transition list" where
  "transition_list_out (State _ _ _ _ _ trl2 _) = trl2"
| "transition_list_out No_State = []"
fun state_c :: "state \<Rightarrow> comp" where
  "state_c (State _ _ _ _ _ _ C) = C"
| "state_c No_State = No_Composition"

type_synonym root = comp
datatype env = Env "root" "fenv" "genv" "juncs"

fun get_root :: "env \<Rightarrow> comp" where
  "get_root (Env C _ _ _) = C"
fun get_fenv :: "env \<Rightarrow> fenv" where
  "get_fenv (Env _ fe _ _) = fe"
fun get_genv :: "env \<Rightarrow> genv" where
  "get_genv (Env _ _ ge _) = ge"
fun get_juncs :: "env \<Rightarrow> juncs" where
  "get_juncs (Env _ _ _ g) = g"

datatype status = Status "vals" "ctxt"
fun get_vals :: "status \<Rightarrow> vals" where
  "get_vals (Status v _) = v"
fun get_ctxt :: "status \<Rightarrow> ctxt" where
  "get_ctxt (Status _ I) = I"
fun get_message_queue :: "status \<Rightarrow> message_val" where
  "get_message_queue (Status (Vals _ _ _ h3 _) _) = h3"


end


