theory invGen
	imports processDef
begin

ML{*
fun trans_string t =
  let
    fun trans t =
      (case t of
       Free (n, @{typ string}) =>
        Buffer.add " " #>
        Buffer.add n #>
        Buffer.add " "
      | _ => error "inacceptable term: trans_string")
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_real t =
  let
    fun trans t =
      (case t of
       Free (n, @{typ real}) =>
        Buffer.add " " #>
        Buffer.add n #>
        Buffer.add " "
      | _ => error "inacceptable term: trans_real")
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_bool t =
  let
    fun trans t =
      (case t of
       Free (n, @{typ bool}) =>
        Buffer.add " " #>
        Buffer.add n #>
        Buffer.add " "
      | _ => error "inacceptable term: trans_bool")
  in Buffer.content (trans t Buffer.empty) 
end

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
          Buffer.add "(" #>
          Buffer.add (trans_bool t) #>
          Buffer.add ")"
        | _ => error "inacceptable term: trans_val")
  in Buffer.content (trans t Buffer.empty) 
end


fun trans_exp t =
  let
    fun trans t =
      (case t of
        @{term " Add :: exp \<Rightarrow> exp \<Rightarrow> exp"} $ t $ u =>
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

        | @{term "Syntax_SL.exp.RVar :: string \<Rightarrow> exp"} $ t =>
          Buffer.add "RVar" #>
          Buffer.add (trans_string t)
        | @{term "Syntax_SL.exp.SVar :: string \<Rightarrow> exp"} $ t =>
          Buffer.add "SVar" #>
          Buffer.add (trans_string t)
        | @{term "Syntax_SL.exp.BVar :: string \<Rightarrow> exp"} $ t =>
           Buffer.add "BVar" #>
           Buffer.add (trans_string t)

        | @{term "Syntax_SL.exp.Con :: val \<Rightarrow> exp"} $ t =>
          Buffer.add "(" #>
          Buffer.add (trans_val t) #>
          Buffer.add ")"
        | _ => error "inacceptable term: trans_exp")
    in Buffer.content (trans t Buffer.empty) 
end

fun trans_fform t =
  let
    fun trans t =
      (case t of
        @{term "Syntax_SL.fTrue"}  =>
        Buffer.add " True "
      | @{term "Syntax_SL.fFalse"}  =>
        Buffer.add " False "
      | @{term "Syntax_SL.fEqual :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add "==" #>
        Buffer.add (trans_exp u) #>
        Buffer.add ")"
      | @{term "Syntax_SL.fLess :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add "<" #>
        Buffer.add (trans_exp u) #>
        Buffer.add ")"
      | @{term "Syntax_SL.fLessEqual :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add "\<le>" #>
        Buffer.add (trans_exp u) #>
        Buffer.add ")"
      | @{term "Syntax_SL.fGreaterEqual :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add "\<ge>" #>
        Buffer.add (trans_exp u) #>
        Buffer.add ")"
      | @{term "Syntax_SL.fNot :: fform \<Rightarrow> fform"} $ t  =>
        Buffer.add "!(" #>
        trans t #>
        Buffer.add ")"
      | @{term "Syntax_SL.fAnd :: fform \<Rightarrow> fform \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        trans t #>
        Buffer.add "&&" #>
        trans u #>
        Buffer.add ")"
      | @{term "Syntax_SL.fOr :: fform \<Rightarrow> fform \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        trans t #>
        Buffer.add "||" #>
        trans u #>
        Buffer.add ")"
      | @{term "Syntax_SL.fImp :: fform \<Rightarrow> fform \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "{" #>
        trans t #>
        Buffer.add  " ," #>
        trans u #>
        Buffer.add "}"
      | @{term "Syntax_SL.fSubForm :: fform \<Rightarrow> exp \<Rightarrow> string \<Rightarrow> typeid \<Rightarrow> fform"} $ t $ u $ v $ w =>
        Buffer.add "(" #>
        trans t #>
        Buffer.add "[" #>
        Buffer.add (trans_exp u) #>
        Buffer.add "," #>
        Buffer.add (trans_string v) #>
        Buffer.add " " #>
        Buffer.add ("w") #>
        Buffer.add "]" #>
        Buffer.add ")"
      | @{term "Syntax_SL.close :: fform \<Rightarrow> fform"} $ t  =>
        Buffer.add "close" #>
        Buffer.add "(" #>
        trans t #>
        Buffer.add ")"     
           | _ => error "inacceptable term: trans_fform")
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_allCons t = 
  let
    fun trans t =
      (case t of
        @{term "forall :: fform \<Rightarrow> bool"} $ u =>
        Buffer.add " " #>
        Buffer.add (trans_fform u) #>
        Buffer.add " "
      | _ => error "inacceptable term")
  in Buffer.content (trans t Buffer.empty)
end

fun isTrue x =
  if x = "True\n" then true
  else false

fun decide_SOS p = "~/SOS/inv.sh "^"\""^p^"\""
  |> Isabelle_System.bash_output
  |> fst
  |> isTrue;
*}

oracle inv_oracle_SOS = {* fn ct =>
  if decide_SOS (trans_allCons (Thm.term_of ct))
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
