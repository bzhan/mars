theory invGen
	imports HHL_SL
begin

declare [[ML_print_depth = 50]]

ML {*

fun trans_real t = Syntax.pretty_term @{context} t
  |> Pretty.string_of
  |> YXML.parse_body
  |> XML.content_of;

fun trans_nat t = Syntax.pretty_term @{context} t
  |> Pretty.string_of
  |> YXML.parse_body
  |> XML.content_of;

fun trans_string t = HOLogic.dest_string t;

fun trans_val t =
  let
    fun trans t =
      (case t of
       @{term "Syntax_SL.val.Real :: real \<Rightarrow> val"} $ t =>
          Buffer.add "(" #>
          Buffer.add (trans_real t) #>
          Buffer.add ")"
        | @{term "Syntax_SL.val.String :: string \<Rightarrow> val"} $ t =>
          Buffer.add "(" #>
          Buffer.add (trans_string t) #>
          Buffer.add ")"
        | @{term "Syntax_SL.val.Bool :: bool \<Rightarrow> val"} $ t =>
          trans t
        | Free (n, @{typ bool}) =>
          Buffer.add " " #>
          Buffer.add n #>
          Buffer.add " "
        | _ => error "inacceptable term: trans_val")
  in Buffer.content (trans t Buffer.empty) 
end


fun trans_exp t =
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
          Buffer.add (trans_nat u) #> 
          Buffer.add " "

        | @{term "Syntax_SL.exp.RVar :: string \<Rightarrow> exp"} $ t =>
          Buffer.add (trans_string t)
        | @{term "Syntax_SL.exp.SVar :: string \<Rightarrow> exp"} $ t =>
          Buffer.add (trans_string t)
        | @{term "Syntax_SL.exp.BVar :: string \<Rightarrow> exp"} $ t =>
          Buffer.add (trans_string t)

        | @{term "Syntax_SL.exp.Con :: val \<Rightarrow> exp"} $ t =>
          Buffer.add "(" #>
          Buffer.add (trans_val t) #>
          Buffer.add ")"
        | _ =>
        let
          val _ = Syntax.pretty_term @{context} t |> Pretty.string_of |> writeln
        in
          error "inacceptable term: trans_exp"
        end)
    in Buffer.content (trans t Buffer.empty) 
end

fun trans_pair t =
  let
    fun trans t =
      (case t of
        @{term "Product_Type.Pair :: string \<Rightarrow> typeid \<Rightarrow> string * typeid"} $ u $ _ =>
          Buffer.add (trans_string u)
      | _ => error "inacceptable term (trans_pair)")
  in Buffer.content (trans t Buffer.empty) 
end

fun add_quote s =
  if String.isPrefix "{" s then s else "\"" ^ s ^ "\""

fun trans_pair_list t =
  "[" ^ Library.commas (map (add_quote o trans_pair) (HOLogic.dest_list t)) ^ "]"

fun trans_exp_list t =
  "[" ^ Library.commas (map (add_quote o trans_exp) (HOLogic.dest_list t)) ^ "]"

fun pair_to_json (k, v) =
  "\"" ^ k ^ "\":" ^ v

fun dict_to_json lst =
  "{" ^ commas (map pair_to_json lst) ^ "}"

fun trans_fform t =
  let
    fun trans t =
      (case t of
        Const (@{const_name fTrue}, _) =>
        Buffer.add " True "
      | Const (@{const_name fFalse}, _) =>
        Buffer.add " False "
      | Const (@{const_name fEqual}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"eq\""),
          ("lhs", add_quote (trans_exp t)), ("rhs", add_quote (trans_exp u))])
      | Const (@{const_name fLess}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"lt\""),
          ("lhs", add_quote (trans_exp t)), ("rhs", add_quote (trans_exp u))])
      | Const (@{const_name fGreater}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"gt\""),
          ("lhs", add_quote (trans_exp t)), ("rhs", add_quote (trans_exp u))])
      | Const (@{const_name fLessEqual}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"le\""),
          ("lhs", add_quote (trans_exp t)), ("rhs", add_quote (trans_exp u))])
      | Const (@{const_name fGreaterEqual}, _) $ t $ u =>
        Buffer.add (dict_to_json [("ty", "\"ge\""),
          ("lhs", add_quote (trans_exp t)), ("rhs", add_quote (trans_exp u))])
      | Const (@{const_name fNot}, _) $ (Const (@{const_name fEqual}, _) $ t $ u) =>
        Buffer.add (dict_to_json [("ty", "\"neq\""),
          ("lhs", add_quote (trans_exp t)), ("rhs", add_quote (trans_exp u))])
      | Const (c, @{typ fform}) =>
        if String.isSuffix "Inv" c then
          Buffer.add "Inv"
        else
          error ("unexpected constant " ^ c ^ ": trans_fform")
      | Const (@{const_name fSubForm}, _) $ t $ u $ v $ _ =>
        Buffer.add "{" #>
        Buffer.add "\"ty\":" #> Buffer.add "\"subst\"" #> Buffer.add "," #>
        Buffer.add "\"var\":\"" #> Buffer.add (trans_string v) #> Buffer.add "\"," #>
        Buffer.add "\"expr\":\"" #> Buffer.add (trans_exp u) #> Buffer.add "\"," #>
        Buffer.add "\"base\":" #> Buffer.add (add_quote (trans_fform t)) #>
        Buffer.add "}"
      | @{term "Syntax_SL.close :: fform \<Rightarrow> fform"} $ t =>
        Buffer.add "close" #>
        Buffer.add "(" #>
        trans t #>
        Buffer.add ")"
      | Const (@{const_name exeFlow}, _) $ (Const (@{const_name Cont}, _) $ t $ u $ _ $ v) $ v' =>
        Buffer.add "{" #>
        Buffer.add "\"ty\":" #> Buffer.add "\"ode\"" #> Buffer.add "," #>
        Buffer.add "\"vars\":" #> Buffer.add (trans_pair_list t) #> Buffer.add "," #>
        Buffer.add "\"diffs\":" #> Buffer.add (trans_exp_list u) #> Buffer.add "," #>
        Buffer.add "\"domain\":" #> Buffer.add (add_quote (trans_fform v)) #> Buffer.add "," #>
        Buffer.add "\"base\":" #> Buffer.add (add_quote (trans_fform v')) #>
        Buffer.add "}"
      | _ =>
        let
          val _ = Syntax.pretty_term @{context} t |> Pretty.string_of |> writeln
        in
          error "inacceptable term: trans_fform"
        end)
  in Buffer.content (trans t Buffer.empty) 
end

fun strip_fAnd t =
  case t of
    Const (@{const_name fAnd}, _) $ v $ u =>
      v :: strip_fAnd u
  | _ => [t]

fun trans_fform_list ts =
  "[" ^ Library.commas (map (add_quote o trans_fform) ts) ^ "]"

fun trans_single_goal t =
  case t of
    Const (@{const_name fImp}, _) $ t $ u =>
      let
        val froms = strip_fAnd t
        val tos = strip_fAnd u
      in
        dict_to_json [
          ("ty", "\"implies\""),
          ("from", trans_fform_list froms),
          ("to", trans_fform_list tos)]
      end
  | _ => error "inacceptable term: single goal"

fun get_rvars t =
  case t of
    Const (@{const_name RVar}, _) $ n => [trans_string n]
  | A $ B => Library.union (op =) (get_rvars A) (get_rvars B)
  | _ => []

fun trans_goal t =
  case t of
    Const (@{const_name All}, _) $ Abs (_, _, f $ Bound 0) =>
    dict_to_json [
      ("vars", "[" ^ Library.commas (map add_quote (get_rvars f)) ^ "]"),
      ("constraints", "[" ^ Library.commas (map trans_single_goal (strip_fAnd f)) ^ "]")
    ]
  | _ => error "inacceptable term: goal"

fun isTrue x =
  if x = "True\n" then true
  else false

fun decide_SOS p = "~/SOS/inv.sh "^"\""^p^"\""
  |> Isabelle_System.bash_output
  |> fst
  |> isTrue;
*}

text \<open>Unit tests\<close>
ML {*
trans_real @{term "0.128::real"};
trans_real @{term "3::real"};
trans_string @{term "''abc''"};
trans_val @{term "Real 0.123"};
trans_val @{term "String ''abc''"};
trans_val @{term "Bool (n::bool)"};
trans_exp @{term "Con Real 3"};
trans_exp @{term "Con Real 3 [+] RVar ''x''"};
trans_pair @{term "(''u'', R)"};
trans_pair_list @{term "[(''u'', R), (''v'', S)]"};
trans_exp_list @{term "[Con Real 3, RVar ''x'', Con Real 3 [+] RVar ''x'']"};
trans_fform @{term "fTrue"};
*}

ML {*
fun trans_inv_check t inv =
  (case HOLogic.dest_Trueprop t of
    Const (@{const_name All}, _) $ Abs (_, _, f $ Bound 0) =>
    let
      val goals = strip_fAnd f
    in
      (dict_to_json [
        ("vars", "[" ^ Library.commas (map add_quote (get_rvars f)) ^ "]"),
        ("inv", add_quote inv),
        ("constraints", "[" ^ Library.commas (map trans_single_goal (strip_fAnd f)) ^ "]")
      ], length goals)
    end
  | _ => error "inacceptable term: goal")

fun to_shell_format s =
  String.translate (fn s => if s = #"\"" then "\\" ^ str(s) else str(s)) s

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
    forall (fn t => t = "true") out_lines
  end
*}

oracle inv_oracle_SOS = {* fn ct =>
  if decide_SOS (trans_goal (Thm.term_of ct))
  then ct
  else error "Proof failed." *}

oracle inv_check_oracle = {* fn ct =>
  let
    val cf = Thm.dest_arg1 ct
    val f = Thm.term_of cf
    val inv = Thm.term_of (Thm.dest_arg ct)
    val str_inv = HOLogic.dest_string inv
    val (p, num_goal) = trans_inv_check f str_inv
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
fun inv_check_oracle_tac str ctxt =
  CSUBGOAL (fn (goal, i) =>
  (case try inv_check_oracle (Thm.cterm_of ctxt (HOLogic.mk_prod (Thm.term_of goal, HOLogic.mk_string str))) of
    NONE => no_tac
  | SOME th => resolve_tac ctxt [th] i))
*}

method_setup inv_check_oracle = {*
  Scan.lift Parse.string >> (fn str => fn ctxt => SIMPLE_METHOD' (inv_check_oracle_tac str ctxt))
*}

end
