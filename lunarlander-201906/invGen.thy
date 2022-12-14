theory invGen
	imports HHL_SL
begin

declare [[ML_print_depth = 50]]

ML {*

fun trans_real ctxt t =
  case t of
    Const (@{const_name plus}, _) $ u $ v =>
    trans_real ctxt u ^ "+" ^ trans_real ctxt v
  | Const (@{const_name minus}, _) $ u $ v =>
    trans_real ctxt u ^ "-" ^ trans_real ctxt v
  | Const (@{const_name uminus}, _) $ u =>
    "(-" ^ trans_real ctxt u ^ ")"
  | Const (@{const_name times}, _) $ u $ v =>
    "(" ^ trans_real ctxt u ^ ")*(" ^ trans_real ctxt v ^ ")"
  | Const (@{const_name divide}, _) $ u $ v =>
    "(" ^ trans_real ctxt u ^ ")/(" ^ trans_real ctxt v ^ ")"
  | Const (@{const_name power}, _) $ u $ v =>
    "(" ^ trans_real ctxt u ^ ")^(" ^ trans_real ctxt v ^ ")"
  | _ =>
    Syntax.pretty_term ctxt t
  |> Pretty.string_of
  |> YXML.parse_body
  |> XML.content_of |> space_explode " " |> split_last |> snd

fun trans_nat ctxt t = Syntax.pretty_term ctxt t
  |> Pretty.string_of
  |> YXML.parse_body |> split_last |> snd |> single
  |> XML.content_of |> space_explode " " |> split_last |> snd

fun trans_string t = HOLogic.dest_string t;

fun trans_exp ctxt t =
  let
    fun trans t =
      (case t of
        @{term "Add :: exp \<Rightarrow> exp \<Rightarrow> exp"} $ t $ u =>
          Buffer.add "(" #>
          trans t #>
          Buffer.add "+" #>
          trans u #>
          Buffer.add ")"
        | @{term "Sub :: exp \<Rightarrow> exp \<Rightarrow> exp"} $ t $ u =>
          Buffer.add "(" #>
          trans t #>
          Buffer.add "-" #>
          trans u #>
          Buffer.add ")"
        | @{term "Mul :: exp \<Rightarrow> exp \<Rightarrow> exp"} $ t $ u =>
          Buffer.add " " #>
          trans t #>
          Buffer.add "*" #>
          trans u #>
          Buffer.add " "
        | @{term "Div :: exp \<Rightarrow> exp \<Rightarrow> exp"} $ t $ u =>
          Buffer.add " " #>
          trans t #>
          Buffer.add "/" #>
          trans u #> 
          Buffer.add " "
        | @{term "Pow :: exp \<Rightarrow> nat \<Rightarrow> exp"} $ t $ u =>
          Buffer.add " " #>
          trans t #>
          Buffer.add "^" #>
          Buffer.add (trans_nat ctxt u) #> 
          Buffer.add " "

        | @{term "Syntax_SL.exp.RVar :: string \<Rightarrow> exp"} $ t =>
          Buffer.add (trans_string t)
       
        | @{term "Syntax_SL.exp.Real :: real \<Rightarrow> exp"} $ t =>
          Buffer.add "(" #>
          Buffer.add (trans_real ctxt t) #>
          Buffer.add ")"
        | _ =>
        let
          val _ = writeln "trans_exp"
          val _ = Syntax.pretty_term ctxt t |> Pretty.string_of |> writeln
        in
          error "inacceptable term: trans_exp"
        end)
    in Buffer.content (trans t Buffer.empty) 
end

fun add_quote s =
  if String.isPrefix "{" s then s else "\"" ^ s ^ "\""

fun trans_string_list t =
  "[" ^ Library.commas (map (add_quote o trans_string) (HOLogic.dest_list t)) ^ "]"

fun trans_exp_list ctxt t =
  "[" ^ Library.commas (map (add_quote o trans_exp ctxt) (HOLogic.dest_list t)) ^ "]"

fun pair_to_json (k, v) =
  "\"" ^ k ^ "\":" ^ v

fun dict_to_json lst =
  "{" ^ commas (map pair_to_json lst) ^ "}"

fun strip_fAnd t =
  case t of
    Const (@{const_name fAnd}, _) $ v $ u =>
      strip_fAnd v @ strip_fAnd u
  | _ => [t]

fun trans_fform ctxt t =
  let
    fun trans t =
      (case t of
        Const (@{const_name fTrue}, _) =>
        Buffer.add " True "
      | Const (@{const_name fFalse}, _) =>
        Buffer.add " False "
      | Const (@{const_name fEqual}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"eq\""),
          ("lhs", add_quote (trans_exp ctxt t)), ("rhs", add_quote (trans_exp ctxt u))])
      | Const (@{const_name fLess}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"lt\""),
          ("lhs", add_quote (trans_exp ctxt t)), ("rhs", add_quote (trans_exp ctxt u))])
      | Const (@{const_name fGreater}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"gt\""),
          ("lhs", add_quote (trans_exp ctxt t)), ("rhs", add_quote (trans_exp ctxt u))])
      | Const (@{const_name fLessEqual}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"le\""),
          ("lhs", add_quote (trans_exp ctxt t)), ("rhs", add_quote (trans_exp ctxt u))])
      | Const (@{const_name fGreaterEqual}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"ge\""),
          ("lhs", add_quote (trans_exp ctxt t)), ("rhs", add_quote (trans_exp ctxt u))])
      | Const (@{const_name fNot}, _) $ (Const (@{const_name fEqual}, _) $ t $ u) =>
        Buffer.add (dict_to_json [("ty", "\"neq\""),
          ("lhs", add_quote (trans_exp ctxt t)), ("rhs", add_quote (trans_exp ctxt u))])
      | Const (c, @{typ fform}) =>
        if String.isSuffix "Inv" c then
          Buffer.add "Inv"
        else
          error ("unexpected constant " ^ c ^ ": trans_fform")
      | Const (@{const_name fImp}, _) $ _ $ _ =>
        Buffer.add (trans_single_goal ctxt t)
      | Const (@{const_name fSubForm}, _) $ t $ u $ v =>
        Buffer.add "{" #>
        Buffer.add "\"ty\":" #> Buffer.add "\"subst\"" #> Buffer.add "," #>
        Buffer.add "\"var\":\"" #> Buffer.add (trans_string v) #> Buffer.add "\"," #>
        Buffer.add "\"expr\":\"" #> Buffer.add (trans_exp ctxt u) #> Buffer.add "\"," #>
        Buffer.add "\"base\":" #> Buffer.add (add_quote (trans_fform ctxt t)) #>
        Buffer.add "}"
      | @{term "Syntax_SL.close :: fform \<Rightarrow> fform"} $ t =>
        Buffer.add "close" #>
        Buffer.add "(" #>
        trans t #>
        Buffer.add ")"
      | Const (@{const_name exeFlow}, _) $ (Const (@{const_name Cont}, _) $ t $ u $ _ $ v) $ v' =>
        let
          val _ = writeln "v"
          val _ = Syntax.pretty_term ctxt v |> Pretty.string_of |> writeln
          val _ = writeln (string_of_int (length (strip_fAnd v)))
        in
        Buffer.add "{" #>
        Buffer.add "\"ty\":" #> Buffer.add "\"ode\"" #> Buffer.add "," #>
        Buffer.add "\"vars\":" #> Buffer.add (trans_string_list t) #> Buffer.add "," #>
        Buffer.add "\"diffs\":" #> Buffer.add (trans_exp_list ctxt u) #> Buffer.add "," #>
        Buffer.add "\"domain\":" #> Buffer.add (trans_fform_list ctxt (strip_fAnd v)) #> Buffer.add "," #>
        Buffer.add "\"base\":" #> Buffer.add (add_quote (trans_fform ctxt v')) #>
        Buffer.add "}"
        end
      | _ =>
        let
          val _ = writeln "trans_fform"
          val _ = Syntax.pretty_term ctxt t |> Pretty.string_of |> writeln
        in
          error "inacceptable term: trans_fform"
        end)
  in Buffer.content (trans t Buffer.empty) 
end

and trans_fform_list ctxt ts =
  "[" ^ Library.commas (map (add_quote o trans_fform ctxt) ts) ^ "]"

and trans_single_goal ctxt t =
  case t of
    Const (@{const_name fImp}, _) $ t $ u =>
      let
        val froms = strip_fAnd t
        val tos = strip_fAnd u
      in
        dict_to_json [
          ("ty", "\"implies\""),
          ("from", trans_fform_list ctxt froms),
          ("to", trans_fform_list ctxt tos)]
      end
  | _ => let val _ = writeln "trans_single_goal" in error "inacceptable term: single goal" end

fun get_rvars t =
  case t of
    Const (@{const_name RVar}, _) $ n => [trans_string n]
  | A $ B => Library.union (op =) (get_rvars A) (get_rvars B)
  | _ => []

fun trans_goal ctxt t =
  case t of
    Const (@{const_name All}, _) $ Abs (_, _, f $ Bound 0) =>
    dict_to_json [
      ("vars", "[" ^ Library.commas (map add_quote (get_rvars f)) ^ "]"),
      ("constraints", "[" ^ Library.commas (map (trans_single_goal ctxt) (strip_fAnd f)) ^ "]")
    ]
  | _ => let val _ = writeln "trans_goal" in error "inacceptable term: goal" end

fun isTrue x =
  if x = "True\n" then true
  else false

fun to_shell_format s =
  String.translate (fn s => if s = #"\"" then "\\" ^ str(s) else str(s)) s

fun decide_SOS p =
  let
    val sh = if ML_System.platform_is_windows then "inv_windows.sh" else "inv.sh"
    val out = "$MARSHOME/SOSInvGenerator/" ^ sh ^ " \"" ^ to_shell_format p ^ "\""
            |> Isabelle_System.bash_output
            |> fst
    val res_line = out |> split_lines |> map trim_line |> filter (fn t => t <> "") |> split_last |> snd
    val _ = writeln res_line
  in
    res_line <> "error"
  end
*}

text \<open>Unit tests\<close>
ML {*
val ctxt = @{context};
trans_real ctxt @{term "0.128::real"};
trans_real ctxt @{term "3::real"};
trans_string @{term "''abc''"};
trans_exp ctxt @{term "Real 3"};
trans_exp ctxt @{term "Real 3 [+] RVar ''x''"};
trans_exp_list ctxt @{term "[Real 3, RVar ''x'', Real 3 [+] RVar ''x'']"};
trans_fform ctxt @{term "fTrue"};
*}

ML {*
fun trans_inv_check ctxt t inv consts =
  (case HOLogic.dest_Trueprop t of
    Const (@{const_name All}, _) $ Abs (_, _, f $ Bound 0) =>
    let
      val goals = strip_fAnd f
    in
      (dict_to_json [
        ("vars", "[" ^ Library.commas (map add_quote (get_rvars f @ consts)) ^ "]"),
        ("inv", add_quote inv),
        ("constraints", "[" ^ Library.commas (map (trans_single_goal ctxt) (strip_fAnd f)) ^ "]")
      ], length goals)
    end
  | _ => error "inacceptable term: goal")

fun decide_check_inv p num_goal =
  let
    val sh = if ML_System.platform_is_windows then "inv_check_windows.sh" else "inv_check.sh"
    val out = "$MARSHOME/SOSInvGenerator/" ^ sh ^ " \"" ^ to_shell_format p ^ "\""
            |> Isabelle_System.bash_output
            |> fst
    val out_lines = out |> split_lines |> map trim_line |> filter (fn t => t <> "")
    val out_lines = drop (length out_lines - num_goal) out_lines
    val _ = map (fn t => writeln t) out_lines
  in
    length out_lines = num_goal andalso forall (fn t => t = "true") out_lines
  end
*}

oracle inv_oracle_SOS = {* fn ct =>
  let
    val thy = Thm.theory_of_cterm ct
    val ctxt = Proof_Context.init_global thy
    val _ = writeln (Syntax.pretty_term ctxt (Thm.term_of ct) |> Pretty.string_of)
    val goal = trans_goal ctxt (HOLogic.dest_Trueprop (Thm.term_of ct))
    val _ = writeln goal
  in
    if decide_SOS goal
    then ct
    else error "Proof failed."
  end
*}

oracle inv_check_oracle = {* fn ct =>
  let
    val thy = Thm.theory_of_cterm ct
    val ctxt = Proof_Context.init_global thy
    val cf = Thm.dest_arg1 ct
    val f = Thm.term_of cf
    val args = Thm.term_of (Thm.dest_arg ct)
    val strs = HOLogic.dest_list args
    val str_inv = HOLogic.dest_string (hd strs)
    val str_consts = map HOLogic.dest_string (tl strs)
    val (p, num_goal) = trans_inv_check ctxt f str_inv str_consts
    val _ = writeln p
  in
    if decide_check_inv p num_goal
    then cf
    else error "Proof failed."
  end
*}

ML{*
fun inv_oracle_SOS_tac ctxt =
  CSUBGOAL (fn (goal, i) =>
  (case try inv_oracle_SOS goal of
    NONE => no_tac
  | SOME th => resolve_tac ctxt [th] i))
*}

method_setup inv_oracle_SOS = {*
  Scan.succeed (fn ctxt => (SIMPLE_METHOD' (inv_oracle_SOS_tac ctxt)))
*} 

ML {*
fun inv_check_oracle_tac strs ctxt =
  CSUBGOAL (fn (goal, i) =>
  (case try inv_check_oracle (Thm.cterm_of ctxt (HOLogic.mk_prod
    (Thm.term_of goal, HOLogic.mk_list @{typ string} (map HOLogic.mk_string strs)))) of
    NONE => no_tac
  | SOME th => resolve_tac ctxt [th] i))
*}

method_setup inv_check_oracle = {*
  Scan.repeat (Scan.lift Parse.string) >> (fn strs => fn ctxt => SIMPLE_METHOD' (inv_check_oracle_tac strs ctxt))
*}
term "''abc''"
end
