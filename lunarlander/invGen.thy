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
        @{term "Product_Type.Pair :: string \<Rightarrow> typeid  \<Rightarrow> string * typeid"} $ u $ v   =>
         (* Buffer.add "{" #>*)
          Buffer.add (trans_string u) 
          (*#>Buffer.add "}"*)

      | _ => error "inacceptable term (trans_pair)")
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_pair_list t =
  let
    fun trans t =
      (case t of
        @{term "List.list.Cons :: (string * typeid) \<Rightarrow> (string * typeid) list \<Rightarrow> (string * typeid) list"} $ u $ v   =>
          (*Buffer.add "{" #>*)
          Buffer.add (trans_pair u) #>
          Buffer.add "," #>
          Buffer.add (trans_pair_list v) 
          (*Buffer.add "}"*)

      | @{term "List.list.Nil :: (string * typeid) list"}   =>
          Buffer.add "Null"

      | _ => error "inacceptable term (trans_pair_list)")
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_exp_list t =
  let
    fun trans t =
      (case t of
        @{term "List.list.Cons :: exp \<Rightarrow> exp list \<Rightarrow> exp list"} $ u $ v   =>
          (*Buffer.add "{" #>*)
          Buffer.add (trans_exp u) #>
          Buffer.add "," #>
          Buffer.add (trans_exp_list v)
          (* #>Buffer.add "}"*)

      | @{term "List.list.Nil :: exp list"}   =>
          Buffer.add "Null"

      | _ => error "inacceptable term (trans_exp_list)")
  in Buffer.content (trans t Buffer.empty) 
end

(*Note: the domain of the continuous evolution is not included here. *)
fun trans_proc t =
  let
    fun trans t =
      (case t of
        @{term "Syntax_SL.proc.Cont ::(string * typeid) list \<Rightarrow> exp list  => fform \<Rightarrow> fform \<Rightarrow> proc"} $ t $ u $ _ $ v =>
        Buffer.add "{{" #>
        Buffer.add (trans_pair_list t) #>
        Buffer.add "}" #>
        Buffer.add "," #>
        Buffer.add "{" #>
        Buffer.add (trans_exp_list u) #>
        Buffer.add "}" #>
        Buffer.add "," #>
        Buffer.add "{" #>
        Buffer.add (trans_fform v) #>
        Buffer.add "}}"
      | _ => error "inacceptable proc")
  in Buffer.content (trans t Buffer.empty)
end

and trans_fform t =
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
      | @{term "Syntax_SL.fGreater :: exp \<Rightarrow> exp \<Rightarrow> fform"} $ t $ u =>
        Buffer.add "(" #>
        Buffer.add (trans_exp t) #>
        Buffer.add ">" #>
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


      | Const (c, @{typ fform}) =>
        if String.isSuffix "Inv" c then
          Buffer.add "Inv"
        else
          error ("unexpected constant " ^ c ^ ": trans_fform")
      | @{term "Syntax_SL.fSubForm :: fform \<Rightarrow> exp \<Rightarrow> string \<Rightarrow> typeid \<Rightarrow> fform"} $ t $ u $ v $ _ =>
        Buffer.add "{" #>
        Buffer.add "{" #>
        Buffer.add (trans_string v) #>
        Buffer.add "," #>
        Buffer.add (trans_exp u) #>
        Buffer.add "}" #>
        Buffer.add "," #>
        trans t #>
        Buffer.add "}"
      | @{term "Syntax_SL.close :: fform \<Rightarrow> fform"} $ t  =>
        Buffer.add "close" #>
        Buffer.add "(" #>
        trans t #>
        Buffer.add ")"
      | @{term "Op_SL.exeFlow:: proc \<Rightarrow> fform \<Rightarrow> fform"} $ u $ v =>
        Buffer.add "{" #>
        Buffer.add (trans_proc u) #>
        Buffer.add "," #>
        Buffer.add (trans_fform v) #>
        Buffer.add "}"     
      | _ =>
        let
          val _ = Syntax.pretty_term @{context} t |> Pretty.string_of |> writeln
        in
          error "inacceptable term: trans_fform"
        end)
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
        @{term "Syntax_SL.fAnd ::  fform \<Rightarrow> fform \<Rightarrow> fform"} $ v $ u  =>
        Buffer.add (trans_Cons_fform v) #>
        Buffer.add (trans_Cons_fform u)
      | _ => Buffer.add (trans_each_goal t) )
  in Buffer.content (trans t Buffer.empty) 
end

fun trans_goal t = 
  let
    fun trans t =
      (case t of
        @{term "HOL.All :: fform \<Rightarrow> bool"} $ Abs (_, _, f $ Bound 0) =>
          Buffer.add "{" #>
          Buffer.add (trans_Cons_fform f) #>
          Buffer.add "Null}"
      | _ => error "inacceptable term: goal")
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

text \<open>Test functions for goal.thy constraints\<close>

ML {*
val res = trans_proc @{term "
  <[(''plant_v1_1'', R), (''plant_m1_1'', R), (''plant_r1_1'', R), (''plant_t'', R)] :
   [(RVar ''control_1'') [div] (RVar ''plant_m1_1'') [-] (Con Real (811 / 500)),
    (Con Real 0) [-] (RVar ''control_1'') [div] (Con Real 2548),
    (RVar ''plant_v1_1''),
    (Con Real 1)] && Inv1 & (RVar ''plant_t'') [<] (Con Real (16 / 125))>
"};
*}
(*
ML{*

val t1 = @{term " (((RVar ''plant_t'') [\<ge>] (Con Real 0)) [&] (RVar ''plant_t'' [\<le>] Con Real (16 / 125)) [&] Inv [\<longrightarrow>]
         ((RVar ''plant_v1_1'') [+] (Con Real 2) [<] (Con Real (1 / 20)) [&] ((RVar ''plant_v1_1'') [+] (Con Real 2) [>] (Con Real (- (1 / 20))))))"}
val t2 = @{term "  ((((RVar ''plant_v1_1'') [=] (Con Real (- 2))) [&] ((RVar ''plant_m1_1'') [=] (Con Real 1250)) [&] ((RVar ''control_1'') [=] (Con Real (4055 / 2))) [&]
           ((RVar ''plant_t'') [=] (Con Real 0))) [\<longrightarrow>] Inv)"}
val t3 = @{term " (((RVar ''plant_t'') [=] (Con Real (16 / 125))) [&] Inv) [\<longrightarrow>] (Inv\<lbrakk>(Con Real 0),''plant_t'',R\<rbrakk>)"}
val t4 = @{term "(Inv [\<longrightarrow>]
          (Inv\<lbrakk>(RVar ''plant_m1_1'') [*]
              ((Con (Real (811 / 500))) [-] (Con Real (1 / 100)) [*] ((RVar ''control_1'') [**] (RVar ''plant_m1_1'') [-] (Con Real (811 / 500))) [-]
               (Con Real (3 / 5)) [*] ((RVar ''plant_v1_1'') [+] (Con Real 2))),''control_1'',R\<rbrakk>) )"}

val t5 = @{term "(exeFlow
           (<[(''plant_v1_1'', R), (''plant_m1_1'', R), (''plant_r1_1'', R),
              (''plant_t'',
               R)]:[(RVar ''control_1'') [**] (RVar ''plant_m1_1'') [-] (Con Real (811 / 500)), (Con Real 0) [-] (RVar ''control_1'') [**] (Con Real 2548),
                    (RVar ''plant_v1_1''), (Con Real 1)]&&Inv1&(RVar ''plant_t'') [<] (Con Real 16 / 125)>)
           Inv [\<longrightarrow>]
          Inv)"}

val t6 = @{term "(exeFlow
           (<[(''plant_v1_1'', R), (''plant_m1_1'', R), (''plant_r1_1'', R),
              (''plant_t'',
               R)]:[(RVar ''control_1'') [**] (RVar ''plant_m1_1'') [-] (Con Real 811 / 500), (Con Real 0) [-] (RVar ''control_1'') [**] (Con Real 2842),
                    (RVar ''plant_v1_1''), (Con Real 1)]&&Inv2&(RVar ''plant_t'') [<] (Con Real 16 / 125)>)
           Inv [\<longrightarrow>]
          Inv)"}

val tt = @{term "t1 [&] t2 [&] t3 [&] t4 [&] t5 [&] t6"}

val t = @{term "\<forall> s.  ((((RVar ''plant_t'') [\<ge>] (Con Real 0)) [&] (RVar ''plant_t'' [\<le>] Con Real (16 / 125)) [&] Inv [\<longrightarrow>]
         ((RVar ''plant_v1_1'') [+] (Con Real 2) [<] (Con Real (1 / 20)) [&] ((RVar ''plant_v1_1'') [+] (Con Real 2) [>] (Con Real (- (1 / 20))))) )
[&]
          ((((RVar ''plant_v1_1'') [=] (Con Real (- 2))) [&] ((RVar ''plant_m1_1'') [=] (Con Real 1250)) [&] ((RVar ''control_1'') [=] (Con Real (4055 / 2))) [&]
           ((RVar ''plant_t'') [=] (Con Real 0))) [\<longrightarrow>] Inv)

[&]
         ((((RVar ''plant_t'') [=] (Con Real (16 / 125))) [&] Inv) [\<longrightarrow>] (Inv\<lbrakk>(Con Real 0),''plant_t'',R\<rbrakk>))

[&]
         ((Inv [\<longrightarrow>]
          (Inv\<lbrakk>(RVar ''plant_m1_1'') [*]
              ((Con (Real (811 / 500))) [-] (Con Real (1 / 100)) [*] ((RVar ''control_1'') [**] (RVar ''plant_m1_1'') [-] (Con Real (811 / 500))) [-]
               (Con Real (3 / 5)) [*] ((RVar ''plant_v1_1'') [+] (Con Real 2))),''control_1'',R\<rbrakk>) ))
 [&]
         (exeFlow
           (<[(''plant_v1_1'', R), (''plant_m1_1'', R), (''plant_r1_1'', R),
              (''plant_t'',
               R)]:[(RVar ''control_1'') [**] (RVar ''plant_m1_1'') [-] (Con Real (811 / 500)), (Con Real 0) [-] (RVar ''control_1'') [**] (Con Real 2548),
                    (RVar ''plant_v1_1''), (Con Real 1)]&&Inv1&(RVar ''plant_t'') [<] (Con Real 16 / 125)>)
           Inv [\<longrightarrow>]
          Inv)

 [&]
         (exeFlow
           (<[(''plant_v1_1'', R), (''plant_m1_1'', R), (''plant_r1_1'', R),
              (''plant_t'',
               R)]:[(RVar ''control_1'') [**] (RVar ''plant_m1_1'') [-] (Con Real 811 / 500), (Con Real 0) [-] (RVar ''control_1'') [**] (Con Real 2842),
                    (RVar ''plant_v1_1''), (Con Real 1)]&&Inv2&(RVar ''plant_t'') [<] (Con Real 16 / 125)>)
           Inv [\<longrightarrow>]
          Inv) 

 ) s "} 

val res = trans_goal t

*}
*)

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
