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

fun trans_goal t =
  case t of
    @{term "HOL.All :: fform \<Rightarrow> bool"} $ Abs (_, _, f $ Bound 0) =>
    "[" ^ Library.commas (map trans_single_goal (strip_fAnd f)) ^ "]"
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

oracle inv_oracle_SOS = {* fn ct =>
  if decide_SOS (trans_goal (Thm.term_of ct))
  then ct
  else error "Proof failed."*}

ML{*
fun inv_oracle_SOS_tac ctxt =
  CSUBGOAL (fn (goal, i) =>
  (case try inv_oracle_SOS goal of
    NONE => no_tac
  | SOME th => resolve_tac ctxt [th] i))
*}

method_setup inv_oracle_SOS = {*
  Scan.succeed (fn ctxt => (Method.SIMPLE_METHOD' (inv_oracle_SOS_tac ctxt)))
*} 

end
