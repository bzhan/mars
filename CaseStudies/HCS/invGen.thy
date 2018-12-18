theory invGen
	imports "processDef"
begin


declare [[ML_print_depth = 50]]
ML{*

fun transReal t = Syntax.pretty_term @{context} t
  |> Pretty.string_of
  |> YXML.parse_body
  |> XML.content_of;
fun transString t = HOLogic.dest_string t;

fun transVar t =
  let
    fun trans t =
      (case t of
       Free (n, @{typ string}) =>
        Buffer.add " " #>
        Buffer.add n #>
        Buffer.add " "
      | _ => error "inacceptable term: transVar")
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
          Buffer.add "" #>
          trans t #>
          Buffer.add "*" #>
          trans u #>
          Buffer.add ""
        | @{term "Div :: exp \<Rightarrow> exp \<Rightarrow> exp"} $ t $ u =>
          Buffer.add "" #>
          trans t #>
          Buffer.add "/" #>
          trans u #>
          Buffer.add ""

        | @{term "LSyntax.exp.RVar :: string \<Rightarrow> exp"} $ t =>
          Buffer.add (transString t)
        | @{term "LSyntax.exp.SVar :: string \<Rightarrow> exp"} $ t =>
          Buffer.add (transString t)
        | @{term "LSyntax.exp.BVar :: string \<Rightarrow> exp"} $ t =>
          Buffer.add (transString t)

        | @{term "LSyntax.exp.Real :: real \<Rightarrow> exp"} $ t =>
          Buffer.add "(" #>
          Buffer.add (transReal t) #>
          Buffer.add ")"
        | @{term "LSyntax.exp.String :: char list \<Rightarrow> exp"} $ t =>
          Buffer.add "(" #>
          Buffer.add (transString t) #>
          Buffer.add ")"
        | @{term "LSyntax.exp.Bool :: bool \<Rightarrow> exp"} $ t =>
          trans t
        | Free (n, @{typ string}) =>
          Buffer.add " " #>
          Buffer.add n #>
          Buffer.add " "
        | Free (n, @{typ exp}) =>
          Buffer.add " " #>
          Buffer.add n #>
          Buffer.add " "
        | Free (n, @{typ bool}) =>
          Buffer.add " " #>
          Buffer.add n #>
          Buffer.add " "
        | Free (n, @{typ 'a}) =>
          Buffer.add " " #>
          Buffer.add n #>
          Buffer.add " "
        | _ => error "inacceptable term: trans_exp")
    in Buffer.content (trans t Buffer.empty) 
end

fun trans_substf_pair t =
  let
    fun trans t =
      (case t of
        @{term "Product_Type.Pair :: exp \<Rightarrow> exp  \<Rightarrow> exp*exp"} $ u $ v   =>
          Buffer.add "{" #>
          Buffer.add (trans_exp u) #>
          Buffer.add "," #>
          Buffer.add (trans_exp v) #>
          Buffer.add "}"

      | _ => error "inacceptable term (trans_substf_pair)")
  in Buffer.content (trans t Buffer.empty) 
end


fun trans_substF_args t =
  let
    fun trans t =
      (case t of
        @{term "List.list.Cons :: exp \<times> exp \<Rightarrow> (exp \<times> exp) list \<Rightarrow> (exp \<times> exp) list"} $ u $ v   =>
          Buffer.add "{" #>
          Buffer.add (trans_substf_pair u) #>
          Buffer.add "," #>
          Buffer.add (trans_substF_args v) #>
          Buffer.add "}"

      | @{term "List.list.Nil :: (exp \<times> exp) list"}   =>
          Buffer.add "Null"

      | _ => error "inacceptable term (trans_substF_args)")
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_flow t =
  let
    fun trans t =
      (case t of
        @{term "LSyntax.flow.Flow :: string \<Rightarrow> string  => flow"} $ t $ u   =>        
        Buffer.add "{{" #>        
        Buffer.add (transString t) #>
        Buffer.add "}" #>
        Buffer.add "," #> 
        Buffer.add "{" #>
        Buffer.add (transString u) #>
        Buffer.add "}}"
      | Free (n, @{typ bool}) =>
        Buffer.add " " #>
        Buffer.add n #>
        Buffer.add " "
      | _ => error "inacceptable term")
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_fform t =
  let
    fun trans t =
      (case t of
        @{term "LSyntax.fform.WFalse"}  =>
        Buffer.add " False "
      | @{term "LSyntax.fform.WTrue"}  =>
        Buffer.add " True "
      | @{term "LSyntax.fform.WEq :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add "==" #>
        Buffer.add (trans_exp u) #>
        Buffer.add ")"
      | @{term "LSyntax.fform.Less :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add "<" #>
        Buffer.add (trans_exp u) #>
        Buffer.add ")"
      | @{term "LSyntax.fform.Great :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add ">" #>
        Buffer.add (trans_exp u) #>
        Buffer.add ")"
      | @{term "LSyntax.equal_less :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add "<=" #>
        Buffer.add (trans_exp u) #>
        Buffer.add ")"
      | @{term "LSyntax.equal_greater :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add ">=" #>
        Buffer.add (trans_exp u) #>
        Buffer.add ")"
      | @{term "LSyntax.fform.WNot :: fform \<Rightarrow> fform"} $ t  =>
        Buffer.add "!(" #>
        trans t #>
        Buffer.add ")"
      | @{term "LSyntax.fform.WConj :: fform \<Rightarrow> fform \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        trans t #>
        Buffer.add "&&" #>
        trans u #>
        Buffer.add ")"
      | @{term "LSyntax.fform.WDisj :: fform \<Rightarrow> fform \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        trans t #>
        Buffer.add "||" #>
        trans u #>
        Buffer.add ")"
      | @{term "LSyntax.fform.WImp :: fform \<Rightarrow> fform \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "{" #>
        trans t #>
        Buffer.add  " ," #>
        trans u #>
        Buffer.add "}"
      | @{term "LSyntax.fform.WIff :: fform \<Rightarrow> fform \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        trans t #>
        Buffer.add "==" #>
        trans u #>
        Buffer.add ")"
      | @{term "LSyntax.fform.WAll :: string \<Rightarrow> fform \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "ForAll" #>
        Buffer.add "[" #>
        trans t #>
        Buffer.add "," #>
        trans u #>
        Buffer.add "]"     
      | @{term "LSyntax.fform.WEx :: string \<Rightarrow> fform \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "Exists" #>
        Buffer.add "[" #>
        trans t #>
        Buffer.add "," #>
        trans u #>
        Buffer.add "]" 
      | Free (n, @{typ string}) =>
        Buffer.add " " #>
        Buffer.add n #>
        Buffer.add " "
      | Free (n, @{typ 'a}) =>
        Buffer.add " " #>
        Buffer.add n #>
        Buffer.add " "
      | Free (n, @{typ fform}) =>
        Buffer.add " " #>
        Buffer.add n #>
        Buffer.add " "
      | @{term "Inv :: fform"} =>
        Buffer.add "Inv" 

      | @{term "HCSP_Com.substF::  (exp \<times> exp) list \<Rightarrow> fform \<Rightarrow> fform"} $ u $ v =>
        Buffer.add "{" #>
        Buffer.add (trans_substF_args u) #>
        Buffer.add "," #>
        Buffer.add (trans_fform v) #>
        Buffer.add "}"

      | @{term "LSyntax.exeFlow:: flow \<Rightarrow> fform \<Rightarrow> fform \<Rightarrow> fform"} $ u $ v $ _ =>
        Buffer.add "{" #>
        Buffer.add (trans_flow u) #>
        Buffer.add "," #>
        Buffer.add (trans_fform v) #>
        Buffer.add "}"
      | _ => error "inacceptable term: trans_fform")
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_each_goal t =
  let
    fun trans t =
      (case t of
       _ => 
        Buffer.add (trans_fform t)) #>
        Buffer.add ","  
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_Cons_fform t =
  let
    fun trans t =
      (case t of
        @{term "LSyntax.fform.WConj ::  fform \<Rightarrow> fform \<Rightarrow> fform"} $ v $ u  =>
        Buffer.add (trans_Cons_fform v) #>
        Buffer.add (trans_Cons_fform u)
      | _ => Buffer.add (trans_each_goal t) )
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_seq0 t =
  let
    fun trans t =
      (case t of
        @{term "DSequents.SeqO' :: fform \<Rightarrow> seq' \<Rightarrow> seq'"} $ v $ _  =>
        Buffer.add "{" #>
        Buffer.add (trans_Cons_fform v) #>
        Buffer.add "Null}"
      | _ => error "inacceptable term :trans_seq0")
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_allCons t = 
  let
    fun trans t =
      (case t of
        @{term "DLK0.Trueprop :: (seq' \<Rightarrow> seq') \<Rightarrow> (seq' \<Rightarrow> seq') \<Rightarrow> prop"} $ _ $ Abs (_,_,u)  =>
        Buffer.add (trans_seq0 u)
      | _ => error "inacceptable term")
  in Buffer.content (trans t Buffer.empty) 
end

fun isTrue x = 
      if x="True\n" then true
      else false   

fun decide_SOS p = "bash $MARSHOME/SOSInvGenerator/inv.sh "^"\""^p^"\""
  |> Isabelle_System.bash_output
  |> fst
  |> isTrue;

fun decide_QE p = "bash $MARSHOME/QEInvGenerator/qe.sh "^"\""^p^"\""
  |> Isabelle_System.bash_output
  |> fst
  |> isTrue;
*}

oracle inv_oracle_SOS = {* fn ct =>
  if decide_SOS (trans_allCons  (Thm.term_of ct))
  then ct
  else error "Proof failed."*}

oracle inv_oracle_QE = {* fn ct =>
  if decide_QE (trans_allCons  (Thm.term_of ct))
  then ct
  else error "Proof failed."*}

ML{*

fun inv_oracle_SOS_tac ctxt =
  CSUBGOAL (fn (goal, i) =>
  (case try inv_oracle_SOS goal of
    NONE => no_tac
  | SOME th => resolve_tac ctxt [th] i))
fun inv_oracle_QE_tac ctxt =
  CSUBGOAL (fn (goal, i) =>
  (case try inv_oracle_QE goal of
    NONE => no_tac
  | SOME th => resolve_tac ctxt [th] i))
*}

method_setup inv_oracle_SOS = {*
  Scan.succeed (Method.SIMPLE_METHOD' o inv_oracle_SOS_tac)
*} 

method_setup inv_oracle_QE = {*
  Scan.succeed (Method.SIMPLE_METHOD' o inv_oracle_QE_tac)
*} 

end
