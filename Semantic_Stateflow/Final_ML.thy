theory Final_ML
  imports Semantics_Final
begin

ML \<open>
val pwriteln = Pretty.writeln
val pretty_term = Syntax.pretty_term
\<close>
\<comment> \<open>temporal logic expression\<close>
ML \<open>
fun tempval ctxt temp v p = 
  let val fun_h1 = nth (v |> Thm.term_of |> Term.strip_comb |> snd) 1
      val fun_h2 = nth (v |> Thm.term_of |> Term.strip_comb |> snd) 2
      val ch1 = Thm.cterm_of ctxt fun_h1
      val ch2 = Thm.cterm_of ctxt fun_h2
  in
    case temp of
      Const (@{const_name "Before"}, _) $ event $ n =>
      let
        val cevent = Thm.cterm_of @{context} event
        val cn = Thm.cterm_of @{context} n
        val before_th = @{thm Before};
        val args = before_th |> Thm.concl_of |> 
            Term.dest_comb |> snd |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd
        val idp = nth args 2 |> Term.dest_Var
        val idE = hd args |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idn = hd args |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val idh1 = nth (tl args |> hd |> Term.strip_comb |> snd) 1 |> Term.dest_Var
        val idh2 = nth (tl args |> hd |> Term.strip_comb |> snd) 2 |> Term.dest_Var
        val th1 = before_th |> Drule.instantiate_normalize ([], [(idE, cevent), (idp, p), 
            (idn, cn), (idh1, ch1), (idh2, ch2)])
        val th1' = th1 RS @{thm eq_reflection}
        val rhs = th1' |> Thm.rhs_of
        val th2 = Simplifier.asm_full_rewrite ctxt rhs;
        val rhs2 = th2 |> Thm.rhs_of
        val b1 = (Thm.term_of rhs2 aconv @{term True})
        val b2 = (Thm.term_of rhs2 aconv @{term False})
      in
        (if b1 then true else (if b2 then false 
        else (raise TERM ("Expression can't be simplified!", []))))
        (*Thm.term_of rhs2 aconv @{term True}*)
      end
   |  Const (@{const_name "After"}, _) $ event $ n =>
      let
        val cevent = Thm.cterm_of @{context} event
        val cn = Thm.cterm_of @{context} n
        val after_th = @{thm After};
        val args = after_th |> Thm.concl_of |> 
            Term.dest_comb |> snd |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd
        val idp = nth args 2 |> Term.dest_Var
        val idE = hd args |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idn = hd args |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val idh1 = nth (tl args |> hd |> Term.strip_comb |> snd) 1 |> Term.dest_Var
        val idh2 = nth (tl args |> hd |> Term.strip_comb |> snd) 2 |> Term.dest_Var
        val th1 = after_th |> Drule.instantiate_normalize ([], [(idE, cevent), (idp, p), 
            (idn, cn), (idh1, ch1), (idh2, ch2)])
        val th1' = th1 RS @{thm eq_reflection}
        val rhs = th1' |> Thm.rhs_of
        val th2 = Simplifier.asm_full_rewrite ctxt rhs;
        val rhs2 = th2 |> Thm.rhs_of
        val b1 = (Thm.term_of rhs2 aconv @{term True})
        val b2 = (Thm.term_of rhs2 aconv @{term False})
      in
        (if b1 then true else (if b2 then false 
        else (raise TERM ("Expression can't be simplified!", []))))
        (*Thm.term_of rhs2 aconv @{term True}*)
      end
   |  Const (@{const_name "At"}, _) $ event $ n =>
      let
        val cevent = Thm.cterm_of @{context} event
        val cn = Thm.cterm_of @{context} n
        val at_th = @{thm At};
        val args = at_th |> Thm.concl_of |> 
            Term.dest_comb |> snd |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd
        val idp = nth args 2 |> Term.dest_Var
        val idE = hd args |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idn = hd args |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val idh1 = nth (tl args |> hd |> Term.strip_comb |> snd) 1 |> Term.dest_Var
        val idh2 = nth (tl args |> hd |> Term.strip_comb |> snd) 2 |> Term.dest_Var
        val th1 = at_th |> Drule.instantiate_normalize ([], [(idE, cevent), (idp, p), 
            (idn, cn), (idh1, ch1), (idh2, ch2)])
        val th1' = th1 RS @{thm eq_reflection}
        val rhs = th1' |> Thm.rhs_of
        val th2 = Simplifier.asm_full_rewrite ctxt rhs;
        val rhs2 = th2 |> Thm.rhs_of
        val b1 = (Thm.term_of rhs2 aconv @{term True})
        val b2 = (Thm.term_of rhs2 aconv @{term False})
      in
        (if b1 then true else (if b2 then false 
        else (raise TERM ("Expression can't be simplified!", []))))
        (*Thm.term_of rhs2 aconv @{term True}*)
      end
   |  Const (@{const_name "Every"}, _) $ event $ n =>
      let
        val cevent = Thm.cterm_of @{context} event
        val cn = Thm.cterm_of @{context} n
        val every_th = @{thm Every};
        val args = every_th |> Thm.concl_of |> 
            Term.dest_comb |> snd |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd
        val idp = nth args 2 |> Term.dest_Var
        val idE = hd args |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idn = hd args |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val idh1 = nth (tl args |> hd |> Term.strip_comb |> snd) 1 |> Term.dest_Var
        val idh2 = nth (tl args |> hd |> Term.strip_comb |> snd) 2 |> Term.dest_Var
        val th1 = every_th |> Drule.instantiate_normalize ([], [(idE, cevent), (idp, p), 
            (idn, cn), (idh1, ch1), (idh2, ch2)])
        val th1' = th1 RS @{thm eq_reflection}
        val rhs = th1' |> Thm.rhs_of
        val th2 = Simplifier.asm_full_rewrite ctxt rhs;
        val rhs2 = th2 |> Thm.rhs_of
        val b1 = (Thm.term_of rhs2 aconv @{term True})
        val b2 = (Thm.term_of rhs2 aconv @{term False})
      in
        (if b1 then true else (if b2 then false 
        else (raise TERM ("Expression can't be simplified!", []))))
        (*Thm.term_of rhs2 aconv @{term True}*)
      end
   |  _ => raise TERM ("Not supported", [temp])
  end
\<close>

\<comment> \<open>evaluation for update_vals2\<close>
ML \<open>
fun evaluate_update_vals ctxt a1 a2 v = 
  if a1 aconvc @{cterm "No_Expr"} then
    let
      val Update_NoExpr_th1 = @{thm Update_NoExpr1}
      val args = Update_NoExpr_th1 |> Thm.concl_of 
                   |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val ida2 = nth args 1 |> Term.dest_Var
      val idv = nth args 2 |> Term.dest_Var
    in
      Update_NoExpr_th1  |> Drule.instantiate_normalize ([], [(ida2, a2), (idv, v)])
    end
  else if a2 aconvc @{cterm "No_Expr"} then
    let
      val Update_NoExpr_th2 = @{thm Update_NoExpr2}
      val args = Update_NoExpr_th2 |> Thm.concl_of 
                   |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val ida1 = nth args 0|> Term.dest_Var
      val idv = nth args 2 |> Term.dest_Var
    in
      Update_NoExpr_th2  |> Drule.instantiate_normalize ([], [(ida1, a1), (idv, v)])
    end
  else
    let
      val Update_aexp2_th = @{thm Update_exp2}
      val args = Update_aexp2_th |> Thm.concl_of 
                   |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val ida1 = nth args 0 |> Term.dest_Var
      val ida2 = nth args 1 |> Term.dest_Var
      val idv = nth args 2 |> Term.dest_Var
      val th1 = Update_aexp2_th  |> Drule.instantiate_normalize ([], [(ida1, a1), 
              (ida2, a2), (idv, v)])
      val th2 = asm_full_simplify ctxt th1
      val a1_1 = th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                  |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd |> hd |>
                  Thm.cterm_of ctxt
      val ida1_1 = th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                  |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd |> tl |> hd |>
                  Term.dest_Var
      val a2_1 = th2 |> Thm.prems_of |> tl |> hd |> Term.dest_comb |> snd 
                  |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd |> hd |>
                  Thm.cterm_of ctxt
      val ida2_1 = th2 |> Thm.prems_of |> tl |> hd |> Term.dest_comb |> snd 
                  |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd |> tl |> hd |>
                  Term.dest_Var
      val a1_2 = th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                  |> Term.strip_comb |> snd |> tl |> hd 
                  |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val ida1_2 = th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                  |> Term.strip_comb |> snd |> tl |> hd 
                  |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
      val a2_2 = th2 |> Thm.prems_of |> tl |> hd |> Term.dest_comb |> snd 
                  |> Term.strip_comb |> snd |> tl |> hd 
                  |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val ida2_2 = th2 |> Thm.prems_of |> tl |> hd |> Term.dest_comb |> snd 
                  |> Term.strip_comb |> snd |> tl |> hd 
                  |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
      val th3 = th2 |> Drule.instantiate_normalize ([], [(ida1_1, a1_1), (ida1_2, a1_2),
                  (ida2_1, a2_1), (ida2_2, a2_2)])
      val th4 = asm_full_simplify ctxt th3
      val th5 = @{thm refl} RS th4
      val v2 = th5 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
            |> Term.strip_comb |> snd |> tl |> tl |> hd |> Thm.cterm_of ctxt
      val th_update = evaluate_update_vals ctxt a1_2 a2_2 v2
    in
      th_update RS th5
    end
\<close>


\<comment> \<open>evaluation for some simple actions\<close>
ML \<open>
fun evaluate_skip env e p s = 
  let
    val skip_th = @{thm Skip}
    val args = skip_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val ids = nth args 4 |> Term.dest_Var
  in
    skip_th |> Drule.instantiate_normalize ([], [(idenv, env), (ide, e),
        (idp, p), (ids, s)])
  end
\<close>

ML \<open>
val ctxt = @{context}
fun evaluate_assign ctxt env x a e p s = 
  let
    val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
    val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    val assign_th = @{thm Assign}
    val args = assign_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idx = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val ida = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val th1 = assign_th |> Drule.instantiate_normalize ([], [(idenv, env),(idv, v), (idp, p), 
        (ide, e), (idI, I), (idx, x), (ida, a)])
    val th2 = [@{thm refl}, @{thm refl}] MRS th1
  in
    asm_full_simplify ctxt th2
  end
\<close>

ML \<open>
fun evaluate_On1 ctxt env temp as1 e p s = 
  let
    val ON1_th = @{thm On1}
    val args = ON1_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idas = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val ids = nth args 4 |> Term.dest_Var
    val x = as1 |> Thm.dest_arg1
    val a = as1 |> Thm.dest_arg
    val th_assign = evaluate_assign ctxt env x a e p s
    val th1 = ON1_th |> Drule.instantiate_normalize ([], [(idenv, env), (idt, temp), 
      (idas, as1), (ide, e), (idp, p), (ids, s)]);
    val th2 = asm_full_simplify ctxt th1
  in
    [th_assign] MRS th2
  end;

fun evaluate_On2 ctxt env temp as1 e p s = 
  let
    val ON2_th = @{thm On2}
    val args = ON2_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idas = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val ids = nth args 4 |> Term.dest_Var
    val th1 = ON2_th |> Drule.instantiate_normalize ([], [(idenv, env),(idt, temp), (idas, as1), 
         (ide, e), (idp, p),(ids, s)])
  in
    asm_full_simplify ctxt th1
  end

fun evaluate_On3 ctxt env event as1 e p s = 
  let
    val ON3_th = @{thm On3}
    val args = ON3_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idas = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val ids = nth args 4 |> Term.dest_Var
    val x = as1 |> Thm.dest_arg1
    val a = as1 |> Thm.dest_arg
    val _ = pwriteln (pretty_term ctxt (Thm.term_of as1))
    val th_assign = evaluate_assign ctxt env x a e p s
    val th1 = ON3_th |> Drule.instantiate_normalize ([], [(idenv, env),(idt, event), (idas, as1), 
         (ide, e), (idp, p),(ids, s)])
    val th2 = asm_full_simplify ctxt th1
  in
    th_assign RS th2
  end

fun evaluate_On4 ctxt env event as1 e p s = 
  let
    val ON4_th = @{thm On4}
    val args = ON4_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idas = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val ids = nth args 4 |> Term.dest_Var
    val th1 = ON4_th |> Drule.instantiate_normalize ([], [(idenv, env),(idt, event), (idas, as1), 
         (ide, e), (idp, p),(ids, s)])
  in
    asm_full_simplify ctxt th1
  end
\<close>


ML \<open>
fun evaluate_Print1 ctxt env message e p s = 
  let
    val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
    val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    val print1_th = @{thm Print1}
    val args = print1_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idmessage = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val th1 = print1_th |> Drule.instantiate_normalize ([], [(idenv, env),(idv, v), (idp, p), 
     (idmessage, message), (idI, I), (ide, e)])
    val th2 = [@{thm refl},@{thm refl}] MRS th1
  in
    asm_full_simplify ctxt th2
  end;

fun evaluate_Print2 ctxt env message e p s = 
  let
    val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
    val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    val print2_th = @{thm Print2}
    val args = print2_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idmessage = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val th1 = print2_th |> Drule.instantiate_normalize ([], [(idenv, env),(idv, v), (idp, p), 
     (idmessage, message), (idI, I), (ide, e)])
    val th2 = [@{thm refl}, @{thm refl}] MRS th1
  in
    asm_full_simplify ctxt th2
  end
\<close>

ML \<open>
fun evaluate_al1 env e p s = 
  let
    val al1_th = @{thm ActionList_Execution1}
    val args = al1_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    (*val ida = args |> hd |> Term.strip_comb |> snd |> hd |> Term.dest_Var*)
    val idenv = nth args 0 |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val ids = nth args 4|> Term.dest_Var
  in
    al1_th |> Drule.instantiate_normalize ([], [(idenv, env), (ide, e), 
    (idp, p), (ids, s)])
  end
\<close>

\<comment> \<open>Enable\<close>
ML \<open>
fun enable_ML ctxt t e v p = 
  let
    val condition = nth (t |> Thm.term_of |> Term.strip_comb |> snd) 1 
    val c = nth (t |> Thm.term_of |> Term.strip_comb |> snd) 2 |> (Thm.cterm_of ctxt)
  in
    case condition of
      Const (@{const_name "S"}, _) $_ =>
      let
        val enable1_th = @{thm Enable1}
        val str = nth (t |> Thm.term_of |> Term.strip_comb |> snd) 1 |> Term.dest_comb
                  |> snd |> (Thm.cterm_of ctxt)
        val args = enable1_th |> Thm.concl_of |> Term.dest_comb 
                  |> snd |> Term.strip_comb |> snd |> tl |> hd |> Term.strip_comb |> snd;
        val ide = nth args 0 |> Term.strip_comb |> snd |> tl 
                    |> hd |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idstr = nth args 0 |> Term.strip_comb |> snd |> tl 
                  |> hd |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val idc = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idv = nth (nth args 1 |> Term.strip_comb |> snd) 1 |> Term.dest_Var
        val idp = nth (nth args 1 |> Term.strip_comb |> snd) 2 |> Term.dest_Var;
        val th1 = enable1_th |> Drule.instantiate_normalize ([], [(idstr,str),(idv, v), (idp, p), 
                 (ide,e),(idc, c)])
        val th1' = th1 RS @{thm eq_reflection}
        val rhs = th1' |> Thm.rhs_of
        val th2 = Simplifier.asm_full_rewrite ctxt rhs;
        val rhs2 = th2 |> Thm.rhs_of
      in
        Thm.term_of rhs2 aconv @{term True}
      end
    | Const (@{const_name "T1"}, _) $temp' =>
      let
        val enable2_th = @{thm Enable2}
        val temp = Thm.cterm_of ctxt temp'
        val args = enable2_th |> Thm.concl_of |> Term.dest_comb 
                  |> snd |> Term.strip_comb |> snd |> tl |> hd |> Term.strip_comb |> snd;
        val idtemp = nth args 0 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idc = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idv = nth (nth args 1 |> Term.strip_comb |> snd) 1 |> Term.dest_Var
        val idp = nth (nth args 1 |> Term.strip_comb |> snd) 2 |> Term.dest_Var;
        val th1 = enable2_th |> Drule.instantiate_normalize ([], [(idtemp,temp),(idv, v), (idp, p), 
                 (idc, c)])
        val th1' = th1 RS @{thm eq_reflection}
        val rhs = th1' |> Thm.rhs_of
        val th2 = Simplifier.asm_full_rewrite ctxt rhs
        val rhs2 = th2 |> Thm.rhs_of
      in
        Thm.term_of rhs2 aconv @{term True}
      end
  | _ => raise TERM ("Not supported", [condition])
  end
\<close>



ML \<open>
fun evaluate_Fail ctxt env t e p s = 
  let
    val Fail_th  = @{thm Fail}
    val args = Fail_th |> Thm.concl_of  |> Term.strip_comb |> snd |> hd 
                   |> Term.strip_comb |> snd 
    val idenv = nth args 0 |> Term.dest_Var
    val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val ids = nth args 4 |> Term.dest_Var
    val th1 = Fail_th |> Drule.instantiate_normalize ([], [(idt,t), (idp, p), 
             (idenv, env), (ids, s), (ide, e)])
  in
    asm_full_simplify ctxt th1
  end
\<close>

ML \<open>
fun evaluate_Termination env e p s = 
  let
    val Term_th = @{thm Termination}
    val args = Term_th |> Thm.concl_of  |> Term.strip_comb |> snd |> hd 
                   |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val ids = nth args 4 |> Term.dest_Var
  in
    Term_th |> Drule.instantiate_normalize ([], [(idp, p), 
             (idenv, env), (ids, s), (ide, e)])
  end
\<close>



ML \<open>
fun evaluate_No_Composition_Exit env name e s = 
  let
    val No_Composition_Exit_th = @{thm No_Composition_Exit}
    val args = No_Composition_Exit_th |> Thm.concl_of |> Term.dest_comb 
               |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idname = nth args 2 |> Term.dest_Var
    val ide = nth args 3 |> Term.dest_Var
    val ids = nth args 4 |> Term.dest_Var
  in
     No_Composition_Exit_th |> Drule.instantiate_normalize ([], [(idenv, env), (idname, name),
        (ide, e), (ids, s)])
  end
\<close>

ML \<open>
fun evaluate_No_State_Exit ctxt env e s = 
  let
    val No_State_Exit_th = @{thm State_Exit2}
    val args = No_State_Exit_th |> Thm.concl_of |> Term.dest_comb 
               |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val ids = nth args 3 |> Term.dest_Var
    val th1 = No_State_Exit_th |> Drule.instantiate_normalize ([], [(idenv, env),(ide, e), 
               (ids, s)])
  in
    asm_full_simplify ctxt th1
  end
\<close>

ML \<open>
fun evaluate_State_Exit3 ctxt env ST e s = 
  let
    val State_Exit3_th = @{thm State_Exit3}
    val args = State_Exit3_th |> Thm.concl_of |> Term.dest_comb 
               |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idST = nth args 1 |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val ids = nth args 3 |> Term.dest_Var
    val th1 = State_Exit3_th |> Drule.instantiate_normalize ([], [(idST,ST),(idenv, env), 
               (ide, e), (ids, s)])
    val th2 = @{thm refl} RS th1
  in
    asm_full_simplify ctxt th2
  end
\<close>

ML \<open>
fun evaluate_No_State_Entry env e p s = 
let
  val No_State_Entry_th = @{thm State_Entry2}
  val args = No_State_Entry_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb
                   |> snd
  val idenv = nth args 0 |> Term.dest_Var
  val ide = nth args 2 |> Term.dest_Var
  val idp = nth args 3 |> Term.dest_Var
  val ids = nth args 4 |> Term.dest_Var
in
  No_State_Entry_th |> Drule.instantiate_normalize ([], [(idenv, env), (ide, e),
               (ids, s),(idp, p)])
end
\<close>

ML \<open>
fun evaluate_No_Composition_Entry env name e p s = 
let
  val No_Composition_Entry_th = @{thm No_Composition_Entry}
  val args = No_Composition_Entry_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb
               |> snd
  val idenv = nth args 0 |> Term.dest_Var
  val idname = nth args 2 |> Term.dest_Var
  val ide = nth args 3 |> Term.dest_Var
  val idp = nth args 4 |> Term.dest_Var
  val ids = nth args 5 |> Term.dest_Var
in
  No_Composition_Entry_th |> Drule.instantiate_normalize ([], [(idname,name),(ide,e)
            ,(idenv, env),(idp,p),(ids, s)])
end
\<close>


ML \<open>
fun evaluate_No_State_Execution env e is_send s = 
  let
    val No_State_Execution_th = @{thm No_State_Execution}
    val args = No_State_Execution_th |> Thm.concl_of |> Term.dest_comb |> snd 
                |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idis_send = nth args 3 |> Term.dest_Var
    val ids = nth args 4 |> Term.dest_Var
  in
    No_State_Execution_th |> Drule.instantiate_normalize ([], [(idenv, env), (ide, e),
         (ids, s),(idis_send, is_send)])
  end
\<close>

ML \<open>
fun evaluate_No_Composition_Execution env name e is_send s = 
  let
    val No_Composition_Execution_th = @{thm No_Composition_Execution}
    val args = No_Composition_Execution_th |> Thm.concl_of |> Term.dest_comb |> snd 
                |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idname = nth args 2 |> Term.dest_Var
    val ide = nth args 3 |> Term.dest_Var
    val idis_send = nth args 4 |> Term.dest_Var
    val ids = nth args 5 |> Term.dest_Var
  in
    No_Composition_Execution_th |> Drule.instantiate_normalize ([], [(idenv, env), (ide, e),
      (ids, s),(idname, name),(idis_send, is_send)])
  end
\<close>

ML \<open>
fun evaluate_Empty_Pathlist_Execution env f e is_send s = 
  let
    val Empty_Pathlist_Execution_th = @{thm Empty_Pathlist_Execution}
    val args = Empty_Pathlist_Execution_th |> Thm.concl_of |> Term.dest_comb |> snd 
                    |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idf = nth args 2 |> Term.dest_Var
    val ide = nth args 3 |> Term.dest_Var
    val idis_send = nth args 4 |> Term.dest_Var
    val ids = nth args 5 |> Term.dest_Var
  in
    Empty_Pathlist_Execution_th |> Drule.instantiate_normalize ([], [(idenv, env), (ide, e),
      (ids, s),(idf, f),(idis_send, is_send)])
  end
\<close>

ML \<open>
val ctxt = @{context}
fun evaluate_Inactive_State_Execution ctxt env ST e is_send s = 
  let
    val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
    val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    val Inactive_State_Execution_th = @{thm Inactive_State_Execution}
    val args = Inactive_State_Execution_th |> Thm.concl_of |> Term.dest_comb |> snd 
                    |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idST = nth args 1 |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idis_send = nth args 3 |> Term.dest_Var
    val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val th1 = Inactive_State_Execution_th |> Drule.instantiate_normalize ([], [(idenv, env), 
        (ide, e),(idST,ST),(idv, v),(idI, I),(idis_send, is_send)])
    val args2 = th1 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                    |> Term.strip_comb |> snd |> tl |> hd
                    |> Term.strip_comb |> snd
    val idname = nth args2 0 |> Term.dest_Var
    val iden_act = nth args2 1 |> Term.dest_Var
    val iddu_act = nth args2 2 |> Term.dest_Var
    val idex_act = nth args2 3 |> Term.dest_Var
    val idtrans_out = nth args2 4 |> Term.dest_Var
    val idtrans_in = nth args2 5 |> Term.dest_Var
    val idC = nth args2 6 |> Term.dest_Var
    val state = th1 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                    |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd
    val name = nth state 0 |> Thm.cterm_of ctxt
    val en_act = nth state 1 |> Thm.cterm_of ctxt
    val du_act = nth state 2 |> Thm.cterm_of ctxt
    val ex_act = nth state 3 |> Thm.cterm_of ctxt
    val trans_out = nth state 4 |> Thm.cterm_of ctxt
    val trans_in = nth state 5 |> Thm.cterm_of ctxt
    val C = nth state 6 |> Thm.cterm_of ctxt
    val th2 = th1 |> Drule.instantiate_normalize ([], [(idname, name), (iden_act, en_act),
                   (iddu_act,du_act),(idex_act, ex_act),(idtrans_out, trans_out),
                   (idtrans_in, trans_in), (idC, C)])
  in
    asm_full_simplify ctxt th2
  end
\<close>

\<comment> \<open>all execution need to be written together because the action 
"Send" need call the Root Execution\<close>

ML \<open>
fun evaluate_action ctxt env cmd e p s =
  case cmd of
    Const (@{const_name "SKIP"}, _) =>
      evaluate_skip env e p s
  | Const (@{const_name "Assign"}, _) $ x $ a =>
    let
      val cx = Thm.cterm_of ctxt x
      val ca = Thm.cterm_of ctxt a
    in
      evaluate_assign ctxt env cx ca e p s |> asm_full_simplify ctxt
    end
  | Const (@{const_name "Seq"}, _) $ cmd1 $ cmd2 =>
    let
      val th1 = evaluate_action ctxt env cmd1 e p s
      val args = th1 |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val b = nth args 6 |> Thm.cterm_of ctxt
      val s2 = nth args 5 |> Thm.cterm_of ctxt
    in
      if b aconvc @{cterm "True"} then
        let
          val th2 = evaluate_action ctxt env cmd2 e p s2
        in
          [th1, th2] MRS @{thm Seq1}
        end
      else
        th1 RS @{thm Seq2}
    end
  | Const (@{const_name "On1"}, _) $ temp $ as1 =>
    let
      val ctemp = Thm.cterm_of ctxt temp
      val cas1 = Thm.cterm_of ctxt as1
      val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
    in
      (if (tempval ctxt temp v p = true) then 
        let
          val ON1_th = @{thm On1}
          val args = ON1_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
          val idenv = nth args 0 |> Term.dest_Var
          val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val idas = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
          val ide = nth args 2 |> Term.dest_Var
          val idp = nth args 3 |> Term.dest_Var
          val ids = nth args 4 |> Term.dest_Var
          val th_assign = evaluate_action ctxt env as1 e p s
          val th1 = ON1_th |> Drule.instantiate_normalize ([], [(idenv, env), (idt, ctemp), 
            (idas, cas1), (ide, e), (idp, p), (ids, s)]);
          val th2 = asm_full_simplify ctxt th1
        in
          [th_assign] MRS th2
        end
       else (evaluate_On2 ctxt env ctemp cas1 e p s))
    end
  | Const (@{const_name "On2"}, _) $ event' $ as1' =>
    let
      val event = Thm.cterm_of ctxt event'
      val as1 = Thm.cterm_of ctxt as1'
    in
      if event aconvc e then
        let
          val ON3_th = @{thm On3}
          val args = ON3_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
          val idenv = nth args 0 |> Term.dest_Var
          val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val idas = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
          val ide = nth args 2 |> Term.dest_Var
          val idp = nth args 3 |> Term.dest_Var
          val ids = nth args 4 |> Term.dest_Var
          val th_assign = evaluate_action ctxt env as1' e p s
          val th1 = ON3_th |> Drule.instantiate_normalize ([], [(idenv, env),(idt, event), (idas, as1), 
               (ide, e), (idp, p),(ids, s)])
          val th2 = asm_full_simplify ctxt th1
        in
          th_assign RS th2
        end
      else
        evaluate_On4 ctxt env event as1 e p s
    end
  | Const (@{const_name "Print1"}, _) $ message =>
    let
      val cmessage = Thm.cterm_of ctxt message
    in
      evaluate_Print1 ctxt env cmessage e p s
    end
  | Const (@{const_name "Print2"}, _) $ message =>
    let
      val cmessage = Thm.cterm_of ctxt message
    in
      evaluate_Print2 ctxt env cmessage e p s
    end

\<comment> \<open>here b0 is a boolean value to tell whether this send action is in transition actions\<close>
  | Const (@{const_name "Send1"}, _) $ e' $ b0' =>
    let
      val e1 = Thm.cterm_of ctxt e'
      val empty_p = @{cterm "[]::string list"}
      val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    in
      if b0' aconv @{term "False"} then
        let
          val Send1_th = @{thm Send1}
          val args = Send1_th |> Thm.concl_of |> Term.dest_comb |> snd
                                 |> Term.strip_comb |> snd
          val idenv = nth args 0 |> Term.dest_Var
          val ide1 = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val ide = nth args 2 |> Term.dest_Var
          val idp = nth args 3 |> Term.dest_Var
          val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
          val th1 = Send1_th |> Drule.instantiate_normalize ([], [(idenv, env),(ide, e),
                  (ide1, e1), (idp, p), (idv, v), (idI, I)])
          val th2 = asm_full_simplify ctxt th1
          val root = env |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
          val comp_th = evaluate_Composition_Execution ctxt env root empty_p e1 @{cterm "True"} s
          val th3 = comp_th RS th2
          val I1 = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                       |> Term.strip_comb |> snd) 0 |> Term.dest_comb |> fst |> Thm.cterm_of ctxt
          val src_p = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                       |> Term.strip_comb |> snd) 0 |> Term.dest_comb |> snd |> Thm.cterm_of ctxt
          val info_th = Thm.apply I1 src_p 
                                |> Simplifier.rewrite ctxt
          val info_eq = info_th RS @{thm meta_eq_to_obj_eq}
          val th4 = info_eq RS th3
        in
          asm_full_simplify ctxt th4
        end
      else
        let
          val Send2_th = @{thm Send2}
          val args = Send2_th |> Thm.concl_of |> Term.dest_comb |> snd
                                 |> Term.strip_comb |> snd
          val idenv = nth args 0 |> Term.dest_Var
          val ide1 = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val ide = nth args 2 |> Term.dest_Var
          val idp = nth args 3 |> Term.dest_Var
          val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
          val th1 = Send2_th |> Drule.instantiate_normalize ([], [(idenv, env),(ide, e),
                  (ide1, e1), (idp, p), (idv, v), (idI, I)])
          val th2 = asm_full_simplify ctxt th1
          val root = env |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
          val comp_th = evaluate_Composition_Execution ctxt env root empty_p e1 @{cterm "True"} s
          val th3 = comp_th RS th2
          val I1 = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                       |> Term.strip_comb |> snd) 0 |> Term.dest_comb |> fst |> Thm.cterm_of ctxt
          val src_p = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                       |> Term.strip_comb |> snd) 0 |> Term.dest_comb |> snd |> Thm.cterm_of ctxt
          val info_th = Thm.apply I1 src_p 
                                |> Simplifier.rewrite ctxt
          val info_eq = info_th RS @{thm meta_eq_to_obj_eq}
          val th4 = info_eq RS th3
          val th5 = @{thm refl} RS th4
        in
          asm_full_simplify ctxt th5
        end
    end
  | Const (@{const_name "Send2"}, _) $ e' $ b0' $ p1' =>    (*directed send to p1*)
    let
      val e1 = Thm.cterm_of ctxt e'
      val p1 = Thm.cterm_of ctxt p1'
      val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    in
      if b0' aconv @{term "False"} then
        let
          val Send3_th = @{thm Send3}
          val args = Send3_th |> Thm.concl_of |> Term.dest_comb |> snd
                                 |> Term.strip_comb |> snd
          val idenv = nth args 0 |> Term.dest_Var
          val ide1 = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val idp1 = nth (nth args 1 |> Term.strip_comb |> snd) 2 |> Term.dest_Var
          val ide = nth args 2 |> Term.dest_Var
          val idp = nth args 3 |> Term.dest_Var
          val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
          val th1 = Send3_th |> Drule.instantiate_normalize ([], [(idenv, env),(ide, e),
                  (ide1, e1), (idp1, p1), (idp, p), (idv, v), (idI, I)])
          val th2 = asm_full_simplify ctxt th1
          val ST = nth (th2 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
          val state_th = evaluate_State_Execution ctxt env ST e1 @{cterm "True"} s
          val th3 = state_th RS th2
          val I1 = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                       |> Term.strip_comb |> snd) 0 |> Term.dest_comb |> fst |> Thm.cterm_of ctxt
          val src_p = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                       |> Term.strip_comb |> snd) 0 |> Term.dest_comb |> snd |> Thm.cterm_of ctxt
          val info_th = Thm.apply I1 src_p 
                                |> Simplifier.rewrite ctxt
          val info_eq = info_th RS @{thm meta_eq_to_obj_eq}
          val th4 = info_eq RS th3
        in
          asm_full_simplify ctxt th4
        end
      else
        let
          val Send4_th = @{thm Send4}
          val args = Send4_th |> Thm.concl_of |> Term.dest_comb |> snd
                                 |> Term.strip_comb |> snd
          val idenv = nth args 0 |> Term.dest_Var
          val ide1 = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val idp1 = nth (nth args 1 |> Term.strip_comb |> snd) 2 |> Term.dest_Var
          val ide = nth args 2 |> Term.dest_Var
          val idp = nth args 3 |> Term.dest_Var
          val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
          val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
          val th1 = Send4_th |> Drule.instantiate_normalize ([], [(idenv, env),(ide, e),
                  (ide1, e1), (idp1, p1), (idp, p), (idv, v), (idI, I)])
          val th2 = asm_full_simplify ctxt th1
          val ST = nth (th2 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
          val state_th = evaluate_State_Execution ctxt env ST e1 @{cterm "True"} s
          val th3 = state_th RS th2
          val I1 = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                       |> Term.strip_comb |> snd) 0 |> Term.dest_comb |> fst |> Thm.cterm_of ctxt
          val src_p = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                       |> Term.strip_comb |> snd) 0 |> Term.dest_comb |> snd |> Thm.cterm_of ctxt
          val info_th = Thm.apply I1 src_p 
                                |> Simplifier.rewrite ctxt
          val info_eq = info_th RS @{thm meta_eq_to_obj_eq}
          val th4 = info_eq RS th3
          val th5 = @{thm refl} RS th4
        in
          asm_full_simplify ctxt th5
        end
    end
  | Const (@{const_name "Funapp"}, _) $ a1' $ f' $ a2' => 
    let
      val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
      val a1 = Thm.cterm_of ctxt a1'
      val f = Thm.cterm_of ctxt f'
      val a2 = Thm.cterm_of ctxt a2'
      val funapp_th = @{thm Funapp}
      val args = funapp_th |> Thm.concl_of |> 
                   Term.dest_comb |> snd |> Term.strip_comb |> snd
      val idenv = nth args 0 |> Term.dest_Var
      val ida1 = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
      val idf = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
      val ida2 = nth args 1 |> Term.strip_comb |> snd |> tl |> tl |> hd |> Term.dest_Var
      val ide = nth args 2 |> Term.dest_Var
      val idp = nth args 3 |> Term.dest_Var
      val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
      val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
      val th1 = funapp_th |> Drule.instantiate_normalize ([], [(idenv, env),
                (ide,e),(ida1,a1),(idf,f),(ida2,a2),
                (idv,v),(idp, p),(idI, I)])
      val th1_2 = asm_full_simplify ctxt th1
      val th1_3 = @{thm refl} RS th1_2
      val th1' = asm_full_simplify ctxt th1_3
      val args2 = th1' |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                  |> Term.strip_comb |> snd
      val tmp_a = nth args2 1 |> Thm.cterm_of ctxt
      val update_th1 = evaluate_update_vals ctxt a2 tmp_a v
      val th2 = update_th1 RS th1'
      val cmd = nth (th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 1 
      val s1 = nth (th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
      val act_th = evaluate_action ctxt env cmd e p s1
      val th3 = act_th RS th2
      val tmp_a = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 0 |> Thm.cterm_of ctxt
      val v2 = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 2 |> Thm.cterm_of ctxt
      val update_th2 = evaluate_update_vals ctxt tmp_a a1 v2
    in
      update_th2 RS th3
    end
  | Const (@{const_name "Grafun"}, _) $ a1' $ f' $ a2' => 
    let
      val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
      val a1 = Thm.cterm_of ctxt a1'
      val f = Thm.cterm_of ctxt f'
      val a2 = Thm.cterm_of ctxt a2'
      val grafun_th = @{thm Grafun}
      val args = grafun_th |> Thm.concl_of |> 
                   Term.dest_comb |> snd |> Term.strip_comb |> snd
      val idenv = nth args 0 |> Term.dest_Var
      val ida1 = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
      val idf = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
      val ida2 = nth args 1 |> Term.strip_comb |> snd |> tl |> tl |> hd |> Term.dest_Var
      val ide = nth args 2 |> Term.dest_Var
      val idp = nth args 3 |> Term.dest_Var
      val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
      val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
      val th1 = grafun_th |> Drule.instantiate_normalize ([], [(idenv, env),
                (ide,e),(ida1,a1),(idf,f),(ida2,a2),
                (idv,v),(idp, p),(idI, I)])
      val th1_2 = asm_full_simplify ctxt th1
      val th1_3 = @{thm refl} RS th1_2
      val th1' = asm_full_simplify ctxt th1_3
      val args2 = th1' |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                  |> Term.strip_comb |> snd
      val tmp_a = nth args2 1 |> Thm.cterm_of ctxt
      val update_th1 = evaluate_update_vals ctxt a2 tmp_a v
      val th2 = update_th1 RS th1'
      val TL = nth (th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
      val s1 = nth (th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
      val trans_th = evaluate_transition_list ctxt env TL @{cterm "''''::string"} p s1
      val th3 = trans_th RS th2
      val tmp_a = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 0 |> Thm.cterm_of ctxt
      val v2 = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                   |> Term.strip_comb |> snd) 2 |> Thm.cterm_of ctxt
      val update_th2 = evaluate_update_vals ctxt tmp_a a1 v2
    in
      update_th2 RS th3
    end
  | _ => raise TERM ("Not supported", [cmd])
and evaluate_actionlist ctxt env al e p s = 
  if ((Thm.term_of al) aconv @{term "[]::act list"})
  then evaluate_al1 env e p s
  else
    let 
      val cmd = al |> Thm.term_of |> Term.strip_comb |> snd |> hd
      val rest_al =  hd (map (Thm.cterm_of ctxt) 
                    (al |> Thm.term_of |> Term.strip_comb |> snd |> tl))
      val th1 = evaluate_action ctxt env cmd e p s
      val args = th1 |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val b = nth args 6 |> Thm.cterm_of ctxt
      val s2 = nth args 5 |> Thm.cterm_of ctxt
    in
      if b aconvc @{cterm "True"} then
        let
          val th2 = evaluate_actionlist ctxt env rest_al e p s2
        in
          [th1, th2] MRS @{thm ActionList_Execution2}
        end
      else
        th1 RS @{thm ActionList_Execution3}
    end

and evaluate_transition ctxt env t e p s = 
  let
    val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
    val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    val Trans_th = @{thm Trans_Execution1}
    val args = Trans_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idt = nth args 1 |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idp = nth args 3 |> Term.dest_Var
    val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val th1 = Trans_th |> Drule.instantiate_normalize ([], [(idt,t),(idv, v), (idp, p), 
             (ide, e), (idenv, env), (idI, I)])
    val th2 = asm_full_simplify ctxt th1
    val condition_action = nth (t |> Thm.term_of |> Term.strip_comb |> snd) 3
    val th3 = evaluate_action ctxt env condition_action e p s
    val args = th3 |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
    val b = nth args 6 |> Thm.cterm_of ctxt
  in
    if b aconvc @{cterm "True"} then
      [th3,@{thm refl},@{thm refl}] MRS th2
    else
      let
        val Trans2_th = @{thm Trans_Execution2}
        val args = Trans2_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
        val idenv = nth args 0 |> Term.dest_Var
        val idt = nth args 1 |> Term.dest_Var
        val ide = nth args 2 |> Term.dest_Var
        val idp = nth args 3 |> Term.dest_Var
        val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val th1 = Trans2_th |> Drule.instantiate_normalize ([], [(idt,t),(idv, v), (idp, p), 
             (ide, e), (idenv, env), (idI, I)])
        val th2 = asm_full_simplify ctxt th1
      in
        th3 RS th2
      end
  end

and evaluate_transition_list ctxt env TL e p s = 
  if (Thm.term_of TL) aconv @{term "[]::transition list"} then   (*Termination*)
    evaluate_Termination env e p s
  else
    let 
      val t = TL |> Thm.term_of |>  Term.strip_comb |> snd |> hd |> (Thm.cterm_of ctxt)
      val T = TL |> Thm.term_of |>  Term.strip_comb |> snd |> tl |> hd   (*t#T*)
      val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    in
      if enable_ML ctxt t e v p = false then
        if T aconv @{term "[]::transition list"} then     (*Fail*)
          evaluate_Fail ctxt env t e p s
        else  (*TLInduction*)
          let
            val C_T = Thm.cterm_of ctxt T
            val th_Induction = evaluate_transition_list ctxt env C_T e p s
            val TLInduction_th = @{thm TLinduction}
            val args = TLInduction_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd
            val idenv = nth args 0 |> Term.dest_Var
            val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
            val idT = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
            val ide = nth args 2 |> Term.dest_Var
            val idp = nth args 3 |> Term.dest_Var
            val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
            val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
            val th1 = TLInduction_th |> Drule.instantiate_normalize ([], [(idt,t)
                ,(idT, C_T),(idv, v), (idp, p), (idenv, env), (idI, I), (ide, e)])
            val th2 = asm_full_simplify ctxt th1
          in
            th_Induction RS th2
          end
      else
        let
          val th_trans = evaluate_transition ctxt env t e p s
          val args1 = th_trans |> Thm.concl_of |> Term.dest_comb 
                    |> snd |> Term.strip_comb |> snd
          val b = nth args1 6 |> Thm.cterm_of ctxt
          val trg = nth args1 8
        in
          if b aconvc @{cterm "False"} then
            let
              val C_T = Thm.cterm_of ctxt T
              val inactive_th = @{thm SrcInactive}
              val args = inactive_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd
              val idT = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
              val th1 = inactive_th |> Drule.instantiate_normalize ([], [(idT, C_T)])
            in
              th_trans RS th1
            end
          else
            case trg of
              Const (@{const_name "P"}, _) $ _ =>    (*ToState*)
                let
                  val ToState_th = @{thm ToState}
                  val args = ToState_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
                  val idenv = nth args 0 |> Term.dest_Var
                  val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
                  val idT = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
                  val ide = nth args 2 |> Term.dest_Var
                  val idp = nth args 3 |> Term.dest_Var
                  val ids = nth args 4 |> Term.dest_Var
                  val th1 = ToState_th |> Drule.instantiate_normalize ([], [(idt,t),(idenv,env),
                          (idT,(Thm.cterm_of ctxt T)),(ids, s),(idp, p),(ide, e)])
                  val th2 = [th_trans, @{thm refl}] MRS th1
                  val th3 = asm_full_simplify ctxt th2
                in
                  @{thm refl} RS th3
                end 
            | Const (@{const_name "HJ"}, _) $ _ =>    (*ToHistoryJucntion*)
                let
                  val ToHJ_th = @{thm ToHistoryJunction}
                  val args = ToHJ_th |> Thm.concl_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
                  val idenv = nth args 0 |> Term.dest_Var
                  val idt = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
                  val idT = nth args 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
                  val ide = nth args 2 |> Term.dest_Var
                  val idp = nth args 3 |> Term.dest_Var
                  val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
                  val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
                  val th1 = ToHJ_th |> Drule.instantiate_normalize ([], [(idt,t)
                ,(idT, (Thm.cterm_of ctxt T)),(idv, v), (idp, p), (idenv, env), (idI, I), (ide, e)])
                  val th2 = [th_trans, @{thm refl}] MRS th1
                  val th3 = asm_full_simplify ctxt th2
                  val th4 = [@{thm refl}] MRS th3
                  val th5 = asm_full_simplify ctxt th4
                  val th6 = @{thm refl} RS th5
                  val th7 = asm_full_simplify ctxt th6
                  val th8 = @{thm refl} RS th7
                in
                  asm_full_simplify ctxt th8
                end
            | Const (@{const_name "J"}, _) $ str =>
                let
                  val s2 = nth args1 5 |> Thm.cterm_of ctxt
                  val g = nth (env |> Thm.term_of |> Term.strip_comb |> snd) 3 |> Thm.cterm_of ctxt
                  val TL2 = (Thm.term_of g) $ str |> Thm.cterm_of ctxt 
                      |> Simplifier.rewrite ctxt |> Thm.rhs_of (*TL2 = g(str)*)
                  val th_trans2 = evaluate_transition_list ctxt env TL2 e p s2
                  val b2 = nth (th_trans2 |> Thm.concl_of |> Term.dest_comb 
                    |> snd |> Term.strip_comb |> snd) 7 |> Thm.cterm_of ctxt
                in
                  if b2 aconvc @{cterm "False"} then
                    let
                      val C_T = Thm.cterm_of ctxt T
                      val ToJunc2_th = @{thm ToJunctionInduction2}
                      val args2 = ToJunc2_th |> Thm.concl_of |> Term.dest_comb 
                              |> snd |> Term.strip_comb |> snd
                      val idT = nth args2 1 |> Term.strip_comb |> snd 
                                |> tl |> hd |> Term.dest_Var
                      val th1 = ToJunc2_th |> Drule.instantiate_normalize ([], [(idT, C_T)])
                      val th2 = th_trans RS th1
                      val th2' = @{thm refl} RS th2
                      val th3 = asm_full_simplify ctxt th2'
                    in
                      th_trans2 RS th3
                    end
                  else
                    let 
                      val n = nth (th_trans2 |> Thm.concl_of |> Term.dest_comb 
                            |> snd |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
                      val s3 = nth (th_trans2 |> Thm.concl_of |> Term.dest_comb 
                            |> snd |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
                    in
                      if n aconvc @{cterm "-1::int"} then
                        let
                          val ToJunc5_th = @{thm ToJunctionInduction5}
                          val args2 = ToJunc5_th |> Thm.concl_of |> Term.dest_comb 
                                      |> snd |> Term.strip_comb |> snd
                          val idT = nth args2 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
                          val C_T = T |> Thm.cterm_of ctxt    (*cterm of T*)
                          val th1 = ToJunc5_th |> Drule.instantiate_normalize ([], [(idT,C_T)])
                          val th2 = th_trans RS th1
                          val th2' = @{thm refl} RS th2
                          val th3 = asm_full_simplify ctxt th2'
                        in
                          th_trans2 RS th3
                        end
                      else if n aconvc @{cterm "0::int"} then
                        if T aconv @{term "[]::transition list"} then   (*ToJunctionInduction3*)
                          let 
                            val ToJunc4_th = @{thm ToJunctionInduction4}
                            val th1 = th_trans RS ToJunc4_th
                            val th2 = @{thm refl} RS th1
                            val th3 = asm_full_simplify ctxt th2
                          in
                            th_trans2 RS th3
                          end
                        else    (*ToJunctionInduction3*)
                          let 
                            val C_T = T |> Thm.cterm_of ctxt    (*cterm of T*)
                            val th_trans3 = evaluate_transition_list ctxt env C_T e p s3
                            val ToJunc3_th = @{thm ToJunctionInduction3}
                            val args2 = ToJunc3_th |> Thm.concl_of |> Term.dest_comb 
                                        |> snd |> Term.strip_comb |> snd
                            val idT = nth args2 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
                            val th1 = ToJunc3_th |> Drule.instantiate_normalize ([], [(idT,C_T)])
                            val th2 = th_trans RS th1
                            val th2' = @{thm refl} RS th2
                            val th3 = asm_full_simplify ctxt th2'
                          in
                            [th_trans2, th_trans3] MRS th3
                          end
                      else if n aconvc @{cterm "1::int"} then    (*ToJunctionInduction1*)
                        let
                          val C_T = T |> Thm.cterm_of ctxt    (*cterm of T*)
                          val ToJunc1_th = @{thm ToJunctionInduction1}
                          val args2 = ToJunc1_th |> Thm.concl_of |> Term.dest_comb 
                                    |> snd |> Term.strip_comb |> snd
                          val idT = nth args2 1 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
                          val th1 = ToJunc1_th |> Drule.instantiate_normalize ([], [(idT,C_T)])
                          val th2 = th_trans RS th1
                          val th2' = @{thm refl} RS th2
                          val th3 = asm_full_simplify ctxt th2'
                          val th4 = th_trans2 RS th3
                          val th5 = asm_full_simplify ctxt th4
                        in
                          @{thm refl} RS th5
                        end
                      else
                        raise CTERM ("n can't be this value!", [n]) 
                    end
                end
            | _ => raise TERM ("Transition Target Type Error", [trg])
        end
    end

and evaluate_exit_state ctxt env ST e s = 
  if (Thm.term_of ST) aconv @{term "No_State"} then    (*State_Exit2*)
    evaluate_No_State_Exit ctxt env e s
  else
    let
      val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
      val name = nth (ST |> Thm.term_of |> Term.strip_comb |> snd) 0 |> Thm.cterm_of ctxt
      val b1 = @{term "is_active_state"} $ (Thm.term_of name) $ (Thm.term_of I)
              |> Thm.cterm_of ctxt |> Simplifier.rewrite ctxt |> Thm.rhs_of
      val C = nth (ST |> Thm.term_of |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
      val exit_action = nth (ST |> Thm.term_of |> Term.strip_comb |> snd) 3
    in
      if (Thm.term_of b1) aconv @{term "False"} then    (*State_Exit3*)
        evaluate_State_Exit3 ctxt env ST e s
      else
        let
          val comp_th = evaluate_exit_composition ctxt env C name e s
          val b2 = nth (comp_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
        in
          if b2 aconvc @{cterm "False"} then
            let
              val State_Exit4_th = @{thm State_Exit4}
              val args = State_Exit4_th |> Thm.concl_of |> Term.dest_comb 
                         |> snd |> Term.strip_comb |> snd
              val idenv = nth args 0 |> Term.dest_Var
              val idST = nth args 1 |> Term.dest_Var
              val ide = nth args 2 |> Term.dest_Var
              val idv = nth args 3 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
              val idI = nth args 3 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
              val th1 = State_Exit4_th |> Drule.instantiate_normalize ([], [(idST,ST),(ide, e), 
                         (idenv, env), (idv, v), (idI, I)])
              val th2 = @{thm refl} RS th1
              val th3 = asm_full_simplify ctxt th2
            in
              comp_th RS th3
            end
          else
            let
              val State_Exit1_th = @{thm State_Exit1}
              val args = State_Exit1_th |> Thm.concl_of |> Term.dest_comb 
                         |> snd |> Term.strip_comb |> snd
              val idenv = nth args 0 |> Term.dest_Var
              val idST = nth args 1 |> Term.dest_Var
              val ide = nth args 2 |> Term.dest_Var
              val idv = nth args 3 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
              val idI = nth args 3 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
              val th1 = State_Exit1_th |> Drule.instantiate_normalize ([], [(idST,ST),(ide, e), 
                     (idenv, env), (idv, v), (idI, I)])
              val th2 = @{thm refl} RS th1
              val th3 = asm_full_simplify ctxt th2
              val th3' = comp_th RS th3
              val th3'' = asm_full_simplify ctxt th3'
              val s2 = nth (th3'' |> Thm.prems_of |> hd |> Term.strip_comb |> snd |> hd
                      |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
              val action_th = evaluate_action ctxt env exit_action e name s2
              val b3 = nth (action_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
            in
              if b3 aconvc @{cterm "False"} then
                let
                  val State_Exit5_th = @{thm State_Exit5}
                  val args = State_Exit5_th |> Thm.concl_of |> Term.dest_comb 
                             |> snd |> Term.strip_comb |> snd
                  val idenv = nth args 0 |> Term.dest_Var
                  val idST = nth args 1 |> Term.dest_Var
                  val ide = nth args 2 |> Term.dest_Var
                  val idv = nth args 3 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
                  val idI = nth args 3 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
                  val th1 = State_Exit5_th |> Drule.instantiate_normalize ([], [(idST,ST),(ide, e), 
                         (idenv, env), (idv, v), (idI, I)])
                  val th2 = @{thm refl} RS th1
                  val th3 = asm_full_simplify ctxt th2
                  val th4 = comp_th RS th3
                in
                  action_th RS th4
                end
              else
                let
                  val th4 = action_th RS th3''
                  val I3 = nth (action_th |> Thm.concl_of |> Term.dest_comb 
                    |> snd |> Term.strip_comb |> snd) 5 
                    |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
                  val tmp = Thm.apply I3 name |> Simplifier.rewrite ctxt
                  val Chart_th = tmp RS @{thm meta_eq_to_obj_eq}
                in
                  [Chart_th, @{thm refl}] MRS th4
                end
            end
        end
    end
and evaluate_exit_composition ctxt env C name e s = 
  case (Thm.term_of C) of
    Const (@{const_name "No_Composition"}, _) =>     (*No_Composition_Exit*)
      evaluate_No_Composition_Exit env name e s
  | Const (@{const_name "Or"}, _) $ _ $ _ $ _ =>     (*Or_Exit*)
      let
        val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
        val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
        val Or_Exit1_th = @{thm Or_Exit1}
        val args = Or_Exit1_th |> Thm.concl_of |> Term.dest_comb |> 
                            snd |> Term.strip_comb |> snd
        val idenv = nth args 0 |> Term.dest_Var
        val idC = nth args 1 |> Term.dest_Var
        val idname = nth args 2 |> Term.dest_Var
        val ide = nth args 3 |> Term.dest_Var
        val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val th1 = Or_Exit1_th |> Drule.instantiate_normalize ([], [(idenv, env), (idC, C),
          (idv, v),(idname,name), (idI, I), (ide, e)])
        val tmp = Thm.apply I name |> Simplifier.rewrite ctxt
        val Chart_th = tmp RS @{thm meta_eq_to_obj_eq}
        val th2 = [@{thm refl}, Chart_th] MRS th1
        val th3 = asm_full_simplify ctxt th2
        val ST = nth (th3 |> Thm.prems_of |> hd |> Term.strip_comb |> snd |> hd
                |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
        val state_th = evaluate_exit_state ctxt env ST e s
        val b = nth (state_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
      in
        if b aconvc @{cterm "False"} then
        let
          val Or_Exit2_th = @{thm Or_Exit2}
          val th1 = Or_Exit2_th |> Drule.instantiate_normalize ([], [(idenv, env), (idC, C),
          (idv, v),(idname,name), (idI, I), (ide, e)])
          val tmp = Thm.apply I name |> Simplifier.rewrite ctxt
          val Chart_th = tmp RS @{thm meta_eq_to_obj_eq}
          val th2 = [@{thm refl}, Chart_th] MRS th1
          val th3 = asm_full_simplify ctxt th2
        in
          state_th RS th3
        end
        else
          let
            val th4 = state_th RS th3
            val th5 = asm_full_simplify ctxt th4
          in
            [@{thm refl}, @{thm refl}] MRS th5
          end
      end
  | Const (@{const_name "And"}, _) $ sl' $ f' =>     (*And_Exit*)
    let
      val sl = Thm.cterm_of ctxt sl'
      val f = Thm.cterm_of ctxt f'
      val And_Exit1_th = @{thm And_Exit1}
      val args = And_Exit1_th |> Thm.concl_of |> Term.dest_comb |> 
                            snd |> Term.strip_comb |> snd
      val idenv = nth args 0 |> Term.dest_Var
      val idC = nth args 1 |> Term.dest_Var
      val idname = nth args 2 |> Term.dest_Var
      val ide = nth args 3 |> Term.dest_Var
      val ids = nth args 4 |> Term.dest_Var
      val th1 = And_Exit1_th |> Drule.instantiate_normalize ([], [(idC, C),
          (idenv, env), (ids, s), (idname,name), (ide, e)])
      val th2 = @{thm refl} RS th1
      val pathlist_th = path_lsit_exit_execution ctxt env sl e f s
      val b = nth (pathlist_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
    in
      if b aconvc @{cterm "False"} then
      let
        val And_Exit2_th = @{thm And_Exit2}
        val th1 = And_Exit2_th |> Drule.instantiate_normalize ([], [(idC, C),
          (idenv, env), (ids, s), (idname,name), (ide, e)])
        val th2 = @{thm refl} RS th1
        val th3 = asm_full_simplify ctxt th2
      in
        pathlist_th RS th3
      end
      else
        let
          val th3 = asm_full_simplify ctxt th2
        in
          pathlist_th RS th3
        end
    end
  |_ => raise CTERM ("Not supported", [C])
and path_lsit_exit_execution ctxt env sl e f s = 
    if (Thm.term_of sl) aconv @{term "[]::string list"} then
      let
        val empty_list_exit_th = @{thm Empty_List_Exit}
        val args = empty_list_exit_th |> Thm.concl_of |> Term.dest_comb |> snd
                   |> Term.strip_comb |> snd
        val idenv = nth args 0 |> Term.dest_Var
        val ide = nth args 2 |> Term.dest_Var
        val idf = nth args 3 |> Term.dest_Var
        val ids = nth args 4 |> Term.dest_Var
      in
        empty_list_exit_th |> Drule.instantiate_normalize ([], [(idenv, env), (ide,e), 
                    (idf,f), (ids, s)])
      end
    else
      let
        val Term_butlast = @{term butlast}
        val Term_last = @{term last}
        val sl1 = Term_butlast $ (Thm.term_of sl) |> Thm.cterm_of ctxt |> Simplifier.rewrite ctxt |> Thm.rhs_of
        val str = Term_last $ (Thm.term_of sl) |> Thm.cterm_of ctxt |> Simplifier.rewrite ctxt |> Thm.rhs_of
        val path_list_exit1_th = @{thm List_Exit1}
        val args = path_list_exit1_th |> Thm.concl_of |> Term.dest_comb |> snd
                   |> Term.strip_comb |> snd
        val idenv = nth args 0 |> Term.dest_Var
        val idsl1 = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idstr = nth args 1 |> Term.dest_comb |> snd |> Term.strip_comb 
                    |> snd |> hd |> Term.dest_Var
        val ide = nth args 2 |> Term.dest_Var
        val idf = nth args 3 |> Term.dest_Var
        val ids = nth args 4 |> Term.dest_Var
        val th1 = path_list_exit1_th |> Drule.instantiate_normalize ([], [(idsl1,sl1),
                  (idenv, env), (idstr,str),(ide,e),(idf,f),(ids, s)])
        val th2 = asm_full_simplify ctxt th1
        \<comment> \<open>This is a trick that we can't use f(str) to construct the state\<close>
        (*val state = (Thm.term_of f) $ (Thm.term_of str) |> 
                    Term.dest_comb |> fst;*)
        val state = th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                   |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
        val state_th = evaluate_exit_state ctxt env state e s
        val b = nth (state_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
      in
        if b aconvc @{cterm "False"} then
        let
          val path_list_exit2_th = @{thm List_Exit2}
          val th1 = path_list_exit2_th |> Drule.instantiate_normalize ([], [(idsl1,sl1),
                  (idenv, env), (idstr,str),(ide,e),(idf,f),(ids, s)])
          val th2 = asm_full_simplify ctxt th1
        in
          state_th RS th2
        end
        else
          let
            val th3 = state_th RS th2
            val th4 = asm_full_simplify ctxt th3
            val args2 = th4 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                   |> Term.strip_comb |> snd
            val s2 = nth args2 4 |> Thm.cterm_of ctxt
            val sl1_exit_th = path_lsit_exit_execution ctxt env sl1 e f s2
          in
            sl1_exit_th RS th4
          end
      end

and evaluate_entry_state ctxt env ST e p s = 
  if (Thm.term_of ST) aconv @{term "No_State"} then    (*No_State_Entry*)
    evaluate_No_State_Entry env e p s
  else
    let
      val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
      val name = nth (ST |> Thm.term_of |> Term.strip_comb |> snd) 0 |> (Thm.cterm_of ctxt)
      val C = nth (ST |> Thm.term_of |> Term.strip_comb |> snd) 6 |> (Thm.cterm_of ctxt)
      val State_Entry1_th = @{thm State_Entry1}
      val args = State_Entry1_th |> Thm.concl_of |> Term.dest_comb |> snd
                  |> Term.strip_comb |> snd
      val idenv = nth args 0 |> Term.dest_Var
      val idST = nth args 1 |> Term.dest_Var
      val ide = nth args 2 |> Term.dest_Var
      val idp = nth args 3 |> Term.dest_Var
      val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
      val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
      val th1 = State_Entry1_th |> Drule.instantiate_normalize ([], [(idST,ST),(idv, v), 
                 (idenv, env), (ide, e), (idI, I), (idp, p)])
      val th2 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th1
      val tmp = Thm.apply I name |> Simplifier.rewrite ctxt
      val Chart_th = tmp RS @{thm meta_eq_to_obj_eq}
      val th3 = Chart_th RS th2
      val cterm_butlast = @{cterm butlast}
      val tmp2 = Thm.apply I (Thm.apply cterm_butlast name) |> Simplifier.rewrite ctxt
      val Chart_th2 = tmp2 RS @{thm meta_eq_to_obj_eq}
      val th4 = [Chart_th2, @{thm refl}, @{thm refl}] MRS th3
      val th4' = asm_full_simplify ctxt th4
      val entry_action = nth (ST |> Thm.term_of |> Term.strip_comb |> snd) 1
      val s2 = nth (th4' |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                  |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
      val action_th = evaluate_action ctxt env entry_action e name s2
      val b1 = nth (action_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
    in
      if b1 aconvc @{cterm "False"} then
      let
        val State_Entry3_th = @{thm State_Entry3}
        val th1 = State_Entry3_th |> Drule.instantiate_normalize ([], [(idST,ST),(idv, v), 
                 (idenv, env), (ide, e), (idI, I), (idp, p)])
        val th2 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th1
        val tmp = Thm.apply I name |> Simplifier.rewrite ctxt
        val Chart_th = tmp RS @{thm meta_eq_to_obj_eq}
        val th3 = Chart_th RS th2
        val cterm_butlast = @{cterm butlast}
        val tmp2 = Thm.apply I (Thm.apply cterm_butlast name) |> Simplifier.rewrite ctxt
        val Chart_th2 = tmp2 RS @{thm meta_eq_to_obj_eq}
        val th4 = [Chart_th2, @{thm refl}, @{thm refl}] MRS th3
        val th4' = asm_full_simplify ctxt th4
      in
        action_th RS th4'
      end
      else
        let
          val th6 = action_th RS th4'
          val s3 = nth (th6 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                  |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
          val new_p = nth (th6 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                  |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
          val Comp_th = evaluate_entry_composition ctxt env C name e new_p s3
        in
          Comp_th RS th6
        end
    end
and evaluate_entry_composition ctxt env C name e p s = 
case (Thm.term_of C) of
  Const (@{const_name "No_Composition"}, _) =>     (*No_Composition_Entry*)
    evaluate_No_Composition_Entry env name e p s
| Const (@{const_name "Or"}, _) $ TL' $ b' $ _ =>     (*Or_Entry*)
    let
      val TL = Thm.cterm_of ctxt TL'
    in
      if (Thm.term_of p) aconv @{term "[]::string list"} then
        if b' aconv @{term "False"} then
          let
            val Or_Entry1_th = @{thm Or_Entry1}      (*Or_Entry1*)
            val args = Or_Entry1_th |> Thm.concl_of |> Term.dest_comb |> snd
                        |> Term.strip_comb |> snd
            val idenv = nth args 0 |> Term.dest_Var
            val idC = nth args 1 |> Term.dest_Var
            val idname = nth args 2 |> Term.dest_Var
            val ide = nth args 3 |> Term.dest_Var
            val idp = nth args 4 |> Term.dest_Var
            val ids = nth args 5 |> Term.dest_Var
            val th1 = Or_Entry1_th |> Drule.instantiate_normalize ([], [(idC,C),(idname,name), 
                       (idenv, env), (ide, e), (idp, p), (ids, s)])
            val th2 = @{thm refl} RS th1
            val th3 = asm_full_simplify ctxt th2
            val name = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                            |> Term.strip_comb |> snd) 3 |> Thm.cterm_of ctxt
            val trans_th = evaluate_transition_list ctxt env TL e name s
            val b1 = nth (trans_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd) 7 |> Thm.cterm_of ctxt
          in
            if b1 aconvc @{cterm "False"} then
            let
              val Or_Entry2_th = @{thm Or_Entry2}      (*Or_Entry2*)
              val th1 = Or_Entry2_th |> Drule.instantiate_normalize ([], [(idC,C),(idname,name), 
                       (idenv, env), (ide, e), (idp, p), (ids, s)])
              val th2 = @{thm refl} RS th1
              val th3 = asm_full_simplify ctxt th2
            in
              trans_th RS th3
            end
            else
            let
              val th4 = trans_th RS th3
              val th5 = asm_full_simplify ctxt th4
              val th6 = @{thm refl} RS th5
              val action_list = nth (th6 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                          |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
              val s2 = nth (th6 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                          |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
              val actionlist_th = evaluate_actionlist ctxt env action_list e name s2
              val b2 = nth (actionlist_th |> Thm.concl_of |> Term.dest_comb 
                     |> snd |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
            in
              if b2 aconvc @{cterm "False"} then
              let
                val Or_Entry3_th = @{thm Or_Entry3}      (*Or_Entry3*)
                val th1 = Or_Entry3_th |> Drule.instantiate_normalize ([], [(idC,C),(idname,name), 
                       (idenv, env), (ide, e), (idp, p), (ids, s)])
                val th2 = @{thm refl} RS th1
                val th3 = asm_full_simplify ctxt th2
                val th4 = trans_th RS th3
                val th5 = asm_full_simplify ctxt th4
                val th6 = @{thm refl} RS th5
              in
                actionlist_th RS th6
              end
              else
                let
                  val th7 = actionlist_th RS th6
                  val th8 = asm_full_simplify ctxt th7
                  val ST = nth (th8 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                          |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
                  val s3 = nth (th8 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                          |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
                  val new_p = nth (th8 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                          |> Term.strip_comb |> snd) 3 |> Thm.cterm_of ctxt
                  val state_th = evaluate_entry_state ctxt env ST e new_p s3
                in
                  state_th RS th8
                end
              end
          end
        else
          let
            val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
            val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
            val Or_Entry5_th = @{thm Or_Entry5}      (*Or_Entry5*)
            val args = Or_Entry5_th |> Thm.concl_of |> Term.dest_comb |> snd
                        |> Term.strip_comb |> snd
            val idenv = nth args 0 |> Term.dest_Var
            val idC = nth args 1 |> Term.dest_Var
            val idname = nth args 2 |> Term.dest_Var
            val ide = nth args 3 |> Term.dest_Var
            val idp = nth args 4 |> Term.dest_Var
            val idv = nth args 5 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
            val idI = nth args 5 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
            val th1 = Or_Entry5_th |> Drule.instantiate_normalize ([], [(idC,C),(idname,name)
                      ,(idv, v), (idenv, env), (ide, e), (idI, I), (idp, p)])
            val th2 = @{thm refl} RS th1
            val th3 = asm_full_simplify ctxt th2
            val th4 = @{thm refl} RS th3
            val str2 = nth (th4 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                            |> Term.strip_comb |> snd |> hd |> Term.strip_comb 
                            |> snd) 0|> Thm.cterm_of ctxt
          in
            if str2 aconvc @{cterm "[]::string"} then    
              let
                val Or_Entry9_th = @{thm Or_Entry9}      (*Or_Entry9*)
                val th1 = Or_Entry9_th |> Drule.instantiate_normalize ([], [(idC,C),(idname,name)
                      ,(idv, v), (idenv, env), (ide, e), (idI, I), (idp, p)])
                val th2 = @{thm refl} RS th1
                val th3 = asm_full_simplify ctxt th2
                val th3' = @{thm refl} RS th3
                val th3'' = asm_full_simplify ctxt th3'
                val trans_th = evaluate_transition_list ctxt env TL e name s
                val b1 = nth (trans_th |> Thm.concl_of |> Term.dest_comb 
                           |> snd |> Term.strip_comb |> snd) 7 |> Thm.cterm_of ctxt
              in
                if b1 aconvc @{cterm "False"} then
                  trans_th RS th3''
                else
                  let
                    val Or_Entry10_th = @{thm Or_Entry10}      (*Or_Entry10*)
                    val th1 = Or_Entry10_th |> Drule.instantiate_normalize ([], [(idC,C),(idname,name)
                      ,(idv, v), (idenv, env), (ide, e), (idI, I), (idp, p)])
                    val th2 = @{thm refl} RS th1
                    val th3 = asm_full_simplify ctxt th2
                    val th3' = @{thm refl} RS th3
                    val th3'' = asm_full_simplify ctxt th3'
                    val th4 = trans_th RS th3''
                    val th5 = asm_full_simplify ctxt th4
                    val th6 = @{thm refl} RS th5
                    val action_list = nth (th6 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                                |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
                    val s2 = nth (th6 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                                |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
                    val actionlist_th = evaluate_actionlist ctxt env action_list e name s2
                    val b2 = nth (actionlist_th |> Thm.concl_of |> Term.dest_comb 
                           |> snd |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
                  in
                    if b2 aconvc @{cterm "False"} then
                      actionlist_th RS th6
                    else
                      let
                        val Or_Entry8_th = @{thm Or_Entry8}      (*Or_Entry8*)
                        val th1 = Or_Entry8_th |> Drule.instantiate_normalize ([], [(idC,C),(idname,name)
                                ,(idv, v), (idenv, env), (ide, e), (idI, I), (idp, p)])
                        val th2 = @{thm refl} RS th1
                        val th3 = asm_full_simplify ctxt th2
                        val th3' = @{thm refl} RS th3
                        val th3'' = asm_full_simplify ctxt th3'
                        val th4 = trans_th RS th3''
                        val th5 = asm_full_simplify ctxt th4
                        val th6 = @{thm refl} RS th5
                        val th8 = actionlist_th RS th6
                        val th9 = asm_full_simplify ctxt th8
                        val ST = nth (th9 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                                |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
                        val s3 = nth (th9 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                                |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
                        val new_p = nth (th9 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                                |> Term.strip_comb |> snd) 3 |> Thm.cterm_of ctxt
                        val state_th = evaluate_entry_state ctxt env ST e new_p s3
                      in
                        state_th RS th9
                      end
                  end
              end
            else
              let
                val th5 = asm_full_simplify ctxt th4
                val ST = nth (th5 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                                    |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
                val state_th = evaluate_entry_state ctxt env ST e p s
              in
                state_th RS th5
              end
          end
      else
        let
          val Or_Entry7_th = @{thm Or_Entry7}      (*Or_Entry7*)
          val args = Or_Entry7_th |> Thm.concl_of |> Term.dest_comb |> snd
                        |> Term.strip_comb |> snd
          val idenv = nth args 0 |> Term.dest_Var
          val idC = nth args 1 |> Term.dest_Var
          val idname = nth args 2 |> Term.dest_Var
          val ide = nth args 3 |> Term.dest_Var
          val idp = nth args 4 |> Term.dest_Var
          val ids = nth args 5 |> Term.dest_Var
          val th1 = Or_Entry7_th |> Drule.instantiate_normalize ([], [(idC,C),(idname,name), 
                       (idenv, env), (ide, e), (idp, p), (ids, s)])
          val th2 = @{thm refl} RS th1
          val th3 = asm_full_simplify ctxt th2
          val ST = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                                |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
          val state_th = evaluate_entry_state ctxt env ST e p s
        in
          state_th RS th3
        end
    end
| Const (@{const_name "And"}, _) $ sl' $ f' =>     (*And_Entry*)
    let
      val sl = Thm.cterm_of ctxt sl'
      val f = Thm.cterm_of ctxt f'
      val And_Entry_th = @{thm And_Entry}
      val args = And_Entry_th |> Thm.concl_of |> Term.dest_comb |> 
                            snd |> Term.strip_comb |> snd
      val idenv = nth args 0 |> Term.dest_Var
      val idC = nth args 1 |> Term.dest_Var
      val idname = nth args 2 |> Term.dest_Var
      val ide = nth args 3 |> Term.dest_Var
      val idp = nth args 4 |> Term.dest_Var
      val ids = nth args 5 |> Term.dest_Var
      val th1 = And_Entry_th |> Drule.instantiate_normalize ([], [(idC, C), (idenv, env),
          (idname,name), (ide, e), (idp, p), (ids, s)])
      val th2 = @{thm refl} RS th1
      val th3 = asm_full_simplify ctxt th2
      val pathlist_th = path_list_entry_execution ctxt env sl f e p s
    in
      pathlist_th RS th3
    end
|_ => raise CTERM ("Not supported", [C])
and path_list_entry_execution ctxt env sl f e p s = 
    if (Thm.term_of sl) aconv @{term "[]::string list"} then
      let
        val empty_list_entry_th = @{thm Empty_List_Entry}
        val args = empty_list_entry_th |> Thm.concl_of |> Term.dest_comb |> snd
                   |> Term.strip_comb |> snd
        val idenv = nth args 0 |> Term.dest_Var
        val idf = nth args 2 |> Term.dest_Var
        val ide = nth args 3 |> Term.dest_Var
        val idp = nth args 4 |> Term.dest_Var
        val ids = nth args 5 |> Term.dest_Var
      in
        empty_list_entry_th |> Drule.instantiate_normalize ([], [(ids,s), (ide, e),
        (idenv, env), (idp, p), (idf,f)])
      end
    else
      let
        val sl1 = @{term tl} $ (Thm.term_of sl) |> Thm.cterm_of ctxt 
                  |> Simplifier.rewrite ctxt |> Thm.rhs_of
        val str = @{term hd} $ (Thm.term_of sl) |> Thm.cterm_of ctxt 
                  |> Simplifier.rewrite ctxt |> Thm.rhs_of
        val hd_p = Thm.apply @{cterm hd} p |> Simplifier.rewrite ctxt |> Thm.rhs_of
      in
        if str aconvc hd_p then
          let
            val path_list_entry_th2 = @{thm Path_List_Entry2}
            val args = path_list_entry_th2 |> Thm.concl_of |> Term.dest_comb |> snd
                   |> Term.strip_comb |> snd
            val idenv = nth args 0 |> Term.dest_Var
            val idstr = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
            val idsl1 = nth args 1 |> Term.dest_comb |> snd |> Term.dest_Var
            val idf = nth args 2 |> Term.dest_Var
            val ide = nth args 3 |> Term.dest_Var
            val idp = nth args 4 |> Term.dest_Var
            val ids = nth args 5 |> Term.dest_Var
            val th1 = path_list_entry_th2 |> Drule.instantiate_normalize ([], [(idsl1,sl1),
                      (idenv, env),(idstr,str),(ids,s),(idf,f),(ide,e),(idp,p)])
            val th2 = asm_full_simplify ctxt th1
            val ST = nth (th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                              |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
            val state_th = evaluate_entry_state ctxt env ST e p s
            val b = nth (state_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
          in
            if b aconvc @{cterm "False"} then
              state_th RS th2
            else
              let
                val path_list_entry_th1 = @{thm Path_List_Entry1}
                val th1 = path_list_entry_th1 |> Drule.instantiate_normalize ([], [(idsl1,sl1),
                      (idenv, env),(idstr,str),(ids,s),(idf,f),(ide,e),(idp,p)])
                val th2 = asm_full_simplify ctxt th1
                val th3 = state_th RS th2
                val th4 = asm_full_simplify ctxt th3
                val s2 = nth (state_th |> Thm.concl_of |> Term.dest_comb |> snd
                              |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
                val path_list_th = path_list_entry_execution ctxt env sl1 f e p s2
              in
                path_list_th RS th4
              end
          end
        else
          let
            val empty_p = @{cterm "[]::string list"}
            val path_list_entry_th5 = @{thm Path_List_Entry5}
            val args = path_list_entry_th5 |> Thm.concl_of |> Term.dest_comb |> snd
                   |> Term.strip_comb |> snd
            val idenv = nth args 0 |> Term.dest_Var
            val idstr = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
            val idsl1 = nth args 1 |> Term.dest_comb |> snd |> Term.dest_Var
            val idf = nth args 2 |> Term.dest_Var
            val ide = nth args 3 |> Term.dest_Var
            val idp = nth args 4 |> Term.dest_Var
            val ids = nth args 5 |> Term.dest_Var
            val th1 = path_list_entry_th5 |> Drule.instantiate_normalize ([], [(idsl1,sl1),
                      (idenv, env),(idstr,str),(ids,s),(idf,f),(ide,e),(idp,p)])
            val th2 = asm_full_simplify ctxt th1
            val ST = nth (th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                              |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
            val state_th = evaluate_entry_state ctxt env ST e empty_p s
            val b = nth (state_th |> Thm.concl_of |> Term.dest_comb 
                       |> snd |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
          in
            if b aconvc @{cterm "False"} then
              state_th RS th2
            else
              let
                val path_list_entry_th4 = @{thm Path_List_Entry4}
                val th1 = path_list_entry_th4 |> Drule.instantiate_normalize ([], [(idsl1,sl1),
                      (idenv, env),(idstr,str),(ids,s),(idf,f),(ide,e),(idp,p)])
                val th2 = asm_full_simplify ctxt th1
                val th3 = state_th RS th2
                val th4 = asm_full_simplify ctxt th3
                val s2 = nth (state_th |> Thm.concl_of |> Term.dest_comb |> snd
                              |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
                val path_list_th = path_list_entry_execution ctxt env sl1 f e p s2
              in
                path_list_th RS th4
              end
          end    
      end

and evaluate_State_Execution ctxt env ST e is_send s = 
if ST aconvc @{cterm "No_State"} then
  evaluate_No_State_Execution env e is_send s
else
  let
    val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
    val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    val Outer_Trans_Execution1_th = @{thm Outer_Trans_Execution1}
    val args = Outer_Trans_Execution1_th |> Thm.concl_of |> Term.dest_comb |> snd 
                    |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idST = nth args 1 |> Term.dest_Var
    val ide = nth args 2 |> Term.dest_Var
    val idis_send = nth args 3 |> Term.dest_Var
    val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val th1 = Outer_Trans_Execution1_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
    val args3 = nth (th1 |> Thm.prems_of) 2 |> Term.dest_comb |> snd 
                    |> Term.strip_comb |> snd |> tl |> hd
                    |> Term.strip_comb |> snd
    val ids = nth args3 0 |> Term.dest_Var
    val idh1 = nth args3 1 |> Term.dest_Var
    val idh2 = nth args3 2 |> Term.dest_Var
    val ido1 = nth args3 3 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val ido2 =  nth args3 3 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
    val V = nth (th1 |> Thm.prems_of) 2 |> Term.dest_comb |> snd 
                    |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd
    val s = nth V 0 |> Thm.cterm_of ctxt
    val h1 = nth V 1 |> Thm.cterm_of ctxt
    val h2 = nth V 2 |> Thm.cterm_of ctxt
    val o1 = nth V 3 |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
    val o2 = nth V 3 |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
    val th2 = @{thm refl} RS th1
    val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                    (idh2,h2),(ido1, o1),(ido2, o2)])
    val th3 = asm_full_simplify ctxt th2'
    val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
    val trans_out = nth (th4 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                        |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
    val s2 = nth (th4 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                        |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
    val name = nth (th4 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                        |> Term.strip_comb |> snd) 3 |> Thm.cterm_of ctxt
    val outer_trans_th = evaluate_transition_list ctxt env trans_out e name s2
    val n1 = nth (outer_trans_th |> Thm.concl_of |> Term.dest_comb |> snd 
                        |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
    val b1 = nth (outer_trans_th |> Thm.concl_of |> Term.dest_comb |> snd 
                        |> Term.strip_comb |> snd) 7 |> Thm.cterm_of ctxt
  in
    if b1 aconvc @{cterm "False"} then
    let
      val Outer_Trans_Termination_th = @{thm Outer_Trans_Termination}     (*Outer Transition Termination*)
      val th1 = Outer_Trans_Termination_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
      val th2 = @{thm refl} RS th1
      val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                      (idh2,h2),(ido1, o1),(ido2, o2)])
      val th3 = asm_full_simplify ctxt th2'
      val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
    in
      outer_trans_th RS th4
    end
    else if n1 aconvc @{cterm "1::int"} then
    let
      val th5 = outer_trans_th RS th4
      val idp0 = th5 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                           |> Term.strip_comb |> snd |> tl |> hd
                           |> Term.strip_comb |> snd |> hd |> Term.dest_Var
      val p0 = th5 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                           |> Term.strip_comb |> snd |> hd
                           |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val th6 = th5 |> Drule.instantiate_normalize ([], [(idp0,p0)])
      val ctrm = th6 |>Thm.prems_of |> hd |> Term.dest_comb |> snd
            |> Term.strip_comb |> snd  |> hd |> Thm.cterm_of ctxt
      val th_tmp = (Thm.beta_conversion true ctrm) RS @{thm meta_eq_to_obj_eq}
      val th7 = th_tmp RS th6
      val th8 = @{thm refl} RS th7
      val th9 = asm_full_simplify ctxt th8
      val C_out = nth (th9 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
      val name2 = nth (th9 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 2 |> Thm.cterm_of ctxt
      val s3 = nth (th9 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
      val comp_exit_th = evaluate_exit_composition ctxt env C_out name2 e s3
      val b6 = nth (comp_exit_th |> Thm.concl_of |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
    in
      if b6 aconvc @{cterm "False"} then
      let
        val Outer_Trans_Execution2_th = @{thm Outer_Trans_Execution2}    
        (* Outer_Trans Terminate in Exit "Send" *)
        val th1 = Outer_Trans_Execution2_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
        val th2 = @{thm refl} RS th1
        val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                        (idh2,h2),(ido1, o1),(ido2, o2)])
        val th3 = asm_full_simplify ctxt th2'
        val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
        val th5 = outer_trans_th RS th4
        val th6 = th5 |> Drule.instantiate_normalize ([], [(idp0,p0)])
        val ctrm = th6 |>Thm.prems_of |> hd |> Term.dest_comb |> snd
            |> Term.strip_comb |> snd  |> hd |> Thm.cterm_of ctxt
        val th_tmp = (Thm.beta_conversion true ctrm) RS @{thm meta_eq_to_obj_eq}
        val th7 = th_tmp RS th6
        val th8 = @{thm refl} RS th7
        val th9 = asm_full_simplify ctxt th8
      in
        comp_exit_th RS th9
      end
      else
      let
        val th10 = comp_exit_th RS th9
        val action_list = nth (th10 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                 |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
        val name = nth (th10 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                 |> Term.strip_comb |> snd) 3 |> Thm.cterm_of ctxt
        val s4 = nth (th10 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                 |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
        val actionlist_th = evaluate_actionlist ctxt env action_list e name s4
        val b7 = nth (actionlist_th |> Thm.concl_of |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
      in
        if b7 aconvc @{cterm "False"} then
        let
           val Outer_Trans_Execution3_th = @{thm Outer_Trans_Execution3}
            (* Outer_Trans Terminate in Transition action "Send" *)
           val th1 = Outer_Trans_Execution3_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
           val th2 = @{thm refl} RS th1
           val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                           (idh2,h2),(ido1, o1),(ido2, o2)])
           val th3 = asm_full_simplify ctxt th2'
           val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
           val th5 = outer_trans_th RS th4
           val th6 = th5 |> Drule.instantiate_normalize ([], [(idp0,p0)])
           val ctrm = th6 |>Thm.prems_of |> hd |> Term.dest_comb |> snd
                   |> Term.strip_comb |> snd  |> hd |> Thm.cterm_of ctxt
           val th_tmp = (Thm.beta_conversion true ctrm) RS @{thm meta_eq_to_obj_eq}
           val th7 = th_tmp RS th6
           val th8 = @{thm refl} RS th7
           val th9 = asm_full_simplify ctxt th8
           val th10 = comp_exit_th RS th9
        in
          actionlist_th RS th10
        end
        else
        let
          val th11 = actionlist_th RS th10
          val th13 = [@{thm refl}, @{thm refl}] MRS th11
          val th14 = asm_full_simplify ctxt th13
          val C_in = nth (th14 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                              |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
          val name3 = nth (th14 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                              |> Term.strip_comb |> snd) 2 |> Thm.cterm_of ctxt
          val s5 = nth (th14 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                              |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
          val p_in = nth (th14 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                              |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
          val comp_entry_th = evaluate_entry_composition ctxt env C_in name3 e p_in s5
        in
          comp_entry_th RS th14
        end
      end
    end
    else
      let
        val Fail_Trans_Execution_th = @{thm Fail_Trans_Execution}
        val args = Fail_Trans_Execution_th |> Thm.concl_of |> Term.dest_comb |> snd 
                        |> Term.strip_comb |> snd
        val idenv = nth args 0 |> Term.dest_Var
        val idST = nth args 1 |> Term.dest_Var
        val ide = nth args 2 |> Term.dest_Var
        val idis_send = nth args 3 |> Term.dest_Var
        val idv = nth args 4 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idI = nth args 4 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val th1 = Fail_Trans_Execution_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
        val args3 = nth (th1 |> Thm.prems_of) 2 |> Term.dest_comb |> snd 
                    |> Term.strip_comb |> snd |> tl |> hd
                    |> Term.strip_comb |> snd
        val ids = nth args3 0 |> Term.dest_Var
        val idh1 = nth args3 1 |> Term.dest_Var
        val idh2 = nth args3 2 |> Term.dest_Var
        val ido1 = nth args3 3 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val ido2 =  nth args3 3 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val V = nth (th1 |> Thm.prems_of) 2 |> Term.dest_comb |> snd 
                        |> Term.strip_comb |> snd |> hd |> Term.strip_comb |> snd
        val s = nth V 0 |> Thm.cterm_of ctxt
        val h1 = nth V 1 |> Thm.cterm_of ctxt
        val h2 = nth V 2 |> Thm.cterm_of ctxt
        val o1 = nth V 3 |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
        val o2 = nth V 3 |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
        val th2 = @{thm refl} RS th1
        val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                        (idh2,h2),(ido1, o1),(ido2, o2)])
        val th3 = asm_full_simplify ctxt th2'
        val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
        val th5 = outer_trans_th RS th4
        val th6 = asm_full_simplify ctxt th5
        val du_act = nth (th6 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
        val s3 = nth (th6 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
        val during_action_th = evaluate_action ctxt env (Thm.term_of du_act) e name s3
        val b2 = nth (during_action_th |> Thm.concl_of |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
      in
        if b2 aconvc @{cterm "False"} then
        let
          val Inner_Trans_Execution2_th = @{thm Inner_Trans_Execution2}
          (* Inner_Trans Terminate in During "Send" *)
          val th1 = Inner_Trans_Execution2_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
          val th2 = @{thm refl} RS th1
          val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                          (idh2,h2),(ido1, o1),(ido2, o2)])
          val th3 = asm_full_simplify ctxt th2'
          val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
          val th5 = outer_trans_th RS th4
          val th6 = asm_full_simplify ctxt th5
        in
          during_action_th RS th6
        end
        else
          let
            val th8 = during_action_th RS th6
            val trans_in = nth (th8 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
            val s4 = nth (th8 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
            val inner_trans_th = evaluate_transition_list ctxt env trans_in e name s4
            val n2 = nth (inner_trans_th |> Thm.concl_of |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
            val b3 = nth (inner_trans_th |> Thm.concl_of |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 7 |> Thm.cterm_of ctxt
          in
            if b3 aconvc @{cterm "False"} then
            let
              val Inner_Trans_Termination_th = @{thm Inner_Trans_Termination}
              (* Inner_Trans Terminate in Inner Transition *)
              val th1 = Inner_Trans_Termination_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
              val th2 = @{thm refl} RS th1
              val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                              (idh2,h2),(ido1, o1),(ido2, o2)])
              val th3 = asm_full_simplify ctxt th2'
              val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
              val th5 = outer_trans_th RS th4
              val th6 = asm_full_simplify ctxt th5
              val th8 = during_action_th RS th6
            in
              inner_trans_th RS th8
            end
            else if n2 aconvc @{cterm "1::int"} then
              let
                val Inner_Trans_Execution1_th = @{thm Inner_Trans_Execution1}
                        (* Inner_Trans Terminate Succeed *)
                val th1 = Inner_Trans_Execution1_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
                val th2 = @{thm refl} RS th1
                val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                                (idh2,h2),(ido1, o1),(ido2, o2)])
                val th3 = asm_full_simplify ctxt th2'
                val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
                val th5 = outer_trans_th RS th4
                val th6 = asm_full_simplify ctxt th5
                val th8 = during_action_th RS th6
                val th9 = inner_trans_th RS th8
                val th10 = asm_full_simplify ctxt th9
                val idp0 = th10 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                           |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
                val p0 = th10 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                           |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
                val th11 = th10 |> Drule.instantiate_normalize ([], [(idp0,p0)])
                val ctrm = th11 |>Thm.prems_of |> hd |> Term.dest_comb |> snd
                    |> Term.strip_comb |> snd  |> hd |> Thm.cterm_of ctxt
                val th_tmp = (Thm.beta_conversion true ctrm) RS @{thm meta_eq_to_obj_eq}
                val th12 = th_tmp RS th11
                val th12' = @{thm refl} RS th12
                val th12'' = asm_full_simplify ctxt th12'
                val C = nth (th12'' |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                 |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
                val ex_ST = nth (th12'' |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                 |> Term.strip_comb |> snd) 2 |> Thm.cterm_of ctxt
                val s5 = nth (th12'' |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                 |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
                val comp_exit_th = evaluate_exit_composition ctxt env C ex_ST e s5
                val b4 = nth (comp_exit_th |> Thm.concl_of |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
              in
                if b4 aconvc @{cterm "False"} then
                let
                  val Inner_Trans_Execution3_th = @{thm Inner_Trans_Execution3}
                  (* Inner_Trans Terminate in Exit "Send" *)
                  val th1 = Inner_Trans_Execution3_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
                  val th2 = @{thm refl} RS th1
                  val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                                  (idh2,h2),(ido1, o1),(ido2, o2)])
                  val th3 = asm_full_simplify ctxt th2'
                  val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
                  val th5 = outer_trans_th RS th4
                  val th6 = asm_full_simplify ctxt th5
                  val th8 = during_action_th RS th6
                  val th9 = inner_trans_th RS th8
                  val th10 = asm_full_simplify ctxt th9
                  val th11 = th10 |> Drule.instantiate_normalize ([], [(idp0,p0)])
                  val ctrm = th11 |>Thm.prems_of |> hd |> Term.dest_comb |> snd
                      |> Term.strip_comb |> snd  |> hd |> Thm.cterm_of ctxt
                  val th_tmp = (Thm.beta_conversion true ctrm) RS @{thm meta_eq_to_obj_eq}
                  val th12 = th_tmp RS th11
                  val th12' = @{thm refl} RS th12
                  val th12'' = asm_full_simplify ctxt th12'
                in
                  comp_exit_th RS th12''
                end
                else
                let
                  val th13 = comp_exit_th RS th12''
                  val action_list = nth (th13 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                   |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
                  val s6 = nth (th13 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                   |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
                  val actionlist_th = evaluate_actionlist ctxt env action_list e name s6
                  val b5 = nth (actionlist_th |> Thm.concl_of |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
                in
                  if b5 aconvc @{cterm "False"} then
                  let
                    val Inner_Trans_Execution4_th = @{thm Inner_Trans_Execution4}
                    (* Inner_Trans Terminate in Transition Action "Send" *)
                    val th1 = Inner_Trans_Execution4_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
                   (idST,ST),(idenv, env),(idI, I),(idis_send, is_send)])
                    val th2 = @{thm refl} RS th1
                    val th2' = th2 |> Drule.instantiate_normalize ([], [(ids, s), (idh1, h1),
                                    (idh2,h2),(ido1, o1),(ido2, o2)])
                    val th3 = asm_full_simplify ctxt th2'
                    val th4 = [@{thm refl}, @{thm refl}, @{thm refl}] MRS th3
                    val th5 = outer_trans_th RS th4
                    val th6 = asm_full_simplify ctxt th5
                    val th8 = during_action_th RS th6
                    val th9 = inner_trans_th RS th8
                    val th10 = asm_full_simplify ctxt th9
                    val th11 = th10 |> Drule.instantiate_normalize ([], [(idp0,p0)])
                    val ctrm = th11 |>Thm.prems_of |> hd |> Term.dest_comb |> snd
                        |> Term.strip_comb |> snd  |> hd |> Thm.cterm_of ctxt
                    val th_tmp = (Thm.beta_conversion true ctrm) RS @{thm meta_eq_to_obj_eq}
                    val th12 = th_tmp RS th11
                    val th12' = @{thm refl} RS th12
                    val th12'' = asm_full_simplify ctxt th12'
                    val th13 = comp_exit_th RS th12''
                  in
                    actionlist_th RS th13
                  end
                  else
                  let
                    val th15 = actionlist_th RS th13
                    val th16 = [@{thm refl}, @{thm refl}] MRS th15
                    val th17 = asm_full_simplify ctxt th16
                    val C_in = nth (th17 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                               |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
                    val name2 = nth (th17 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                               |> Term.strip_comb |> snd) 2 |> Thm.cterm_of ctxt
                    val s7 = nth (th17 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                               |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
                    val p_in = nth (th17 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                               |> Term.strip_comb |> snd) 4 |> Thm.cterm_of ctxt
                    val comp_entry_th = evaluate_entry_composition ctxt env C_in name2 e p_in s7
                  in
                    comp_entry_th RS th17
                  end 
                end
              end
            else
              let
                val th9 = inner_trans_th RS th8
                val th10 = asm_full_simplify ctxt th9
                val C = nth (th10 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                 |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
                val s5 = nth (th10 |>Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                    |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
                val comp_exec_th = 
              evaluate_Composition_Execution ctxt env C name e is_send s5
              in
                comp_exec_th RS th10
              end
          end
      end
  end
and evaluate_Composition_Execution ctxt env C name e is_send s = 
let
  val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
  val I = s |> Thm.term_of |> Term.strip_comb |> snd |> tl |> hd |> Thm.cterm_of ctxt
  val empty_p = @{cterm "[]::string list"}
  val info = Simplifier.rewrite ctxt (Thm.apply I empty_p) |> Thm.rhs_of
  val b0 = info |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
in
  if (b0 aconvc @{cterm "False"}) then
    let
      val Start_Execution_th = @{thm Start_Execution}
      val args = Start_Execution_th |> Thm.concl_of |> Term.dest_comb |> snd 
                      |> Term.strip_comb |> snd
      val idenv = nth args 0 |> Term.dest_Var
      val idC = nth args 1 |> Term.dest_Var
      val idname = nth args 2 |> Term.dest_Var
      val ide = nth args 3 |> Term.dest_Var
      val idis_send = nth args 4 |> Term.dest_Var
      val idv = nth args 5 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
      val idI = nth args 5 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
      val th1 = Start_Execution_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
               (idC,C), (idname, name),(idI, I),(idenv, env),(idis_send, is_send)])
      val th3 = asm_full_simplify ctxt th1
      val th5 = @{thm refl} RS th3
      val ST = nth (th5 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                              |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
      val empty_p = @{cterm "[]::string list"}
      val state_entry_th = evaluate_entry_state ctxt env ST e empty_p s
      
    in
      state_entry_th RS th5
    end
  else
    case (Thm.term_of C) of
      Const (@{const_name "No_Composition"}, _) =>     (*No_Composition_Execution*)
        evaluate_No_Composition_Execution env name e is_send s
    | Const (@{const_name "Or"}, _) $ TL' $ b' $ f' =>     (*Or_Execution*)
      let
        val TL = Thm.cterm_of ctxt TL'
        val b = Thm.cterm_of ctxt b'
        val f = Thm.cterm_of ctxt f'
        val Or_Execution_th = @{thm Or_Execution}
        val args = Or_Execution_th |> Thm.concl_of |> Term.dest_comb |> snd 
                        |> Term.strip_comb |> snd
        val idenv = nth args 0 |> Term.dest_Var
        val idC = nth args 1 |> Term.dest_Var
        val idname = nth args 2 |> Term.dest_Var
        val ide = nth args 3 |> Term.dest_Var
        val idis_send = nth args 4 |> Term.dest_Var
        val idv = nth args 5 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
        val idI = nth args 5 |> Term.strip_comb |> snd |> tl |> hd |> Term.dest_Var
        val th1 = Or_Execution_th |> Drule.instantiate_normalize ([], [(idv, v), (ide, e),
               (idC,C), (idname, name),(idI, I),(idenv, env),(idis_send, is_send)])
        val idTL = nth (th1 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                              |> Term.strip_comb |> snd |> tl |> hd |> Term.strip_comb 
                              |> snd) 0 |> Term.dest_Var
        val idb = nth (th1 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                              |> Term.strip_comb |> snd |> tl |> hd |> Term.strip_comb 
                              |> snd) 1 |> Term.dest_Var
        val idf = nth (th1 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                              |> Term.strip_comb |> snd |> tl |> hd |> Term.strip_comb 
                              |> snd) 2 |> Term.dest_Var
        val th2 = th1 |> Drule.instantiate_normalize ([], [(idTL,TL),(idb, b), 
                           (idf, f)])
        val th3 = asm_full_simplify ctxt th2
        val th4 = @{thm refl} RS th3
        val th5 = asm_full_simplify ctxt th4
        val ST = nth (th5 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
        val state_execution_th = 
        evaluate_State_Execution ctxt env ST e is_send s
      in
        state_execution_th RS th5
      end
    | Const (@{const_name "And"}, _) $ sl' $ f' =>     (*And_Execution*)
      let
        val sl = Thm.cterm_of ctxt sl'
        val f = Thm.cterm_of ctxt f'
        val And_Execution_th = @{thm And_Execution}
        val args = And_Execution_th |> Thm.concl_of |> Term.dest_comb |> snd 
                        |> Term.strip_comb |> snd
        val idenv = nth args 0 |> Term.dest_Var
        val idC = nth args 1 |> Term.dest_Var
        val idname = nth args 2 |> Term.dest_Var
        val ide = nth args 3 |> Term.dest_Var
        val idis_send = nth args 4 |> Term.dest_Var
        val ids = nth args 5 |> Term.dest_Var
        val th1 = And_Execution_th |> Drule.instantiate_normalize ([], [(ids, s), (ide, e),
                  (idC,C), (idname, name),(idenv, env),(idis_send, is_send)])
        val idsl = nth (th1 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                              |> Term.strip_comb |> snd |> tl |> hd |> Term.strip_comb 
                              |> snd) 0 |> Term.dest_Var
        val idf = nth (th1 |> Thm.prems_of |> hd |> Term.dest_comb |> snd
                              |> Term.strip_comb |> snd |> tl |> hd |> Term.strip_comb 
                              |> snd) 1 |> Term.dest_Var
        val th2 = th1 |> Drule.instantiate_normalize ([], [(idsl,sl),(idf, f)])
        val th3 = asm_full_simplify ctxt th2
        val path_list_execution_th = 
            evaluate_path_list_execution ctxt env sl f e is_send s
      in
        path_list_execution_th RS th3
      end
    |_ => raise CTERM ("Not supported", [C])
end
and evaluate_path_list_execution ctxt env sl f e is_send s = 
if sl aconvc @{cterm "[]::string list"} then
  evaluate_Empty_Pathlist_Execution env f e is_send s
else
  let
    val sl1 = @{term tl} $ (Thm.term_of sl) |> Thm.cterm_of ctxt 
                  |> Simplifier.rewrite ctxt |> Thm.rhs_of
    val str = @{term hd} $ (Thm.term_of sl) |> Thm.cterm_of ctxt 
                  |> Simplifier.rewrite ctxt |> Thm.rhs_of
    val pathlist_execution_th2 = @{thm Pathlist_Execution2}
    val args = pathlist_execution_th2 |> Thm.concl_of |> Term.dest_comb |> snd
                   |> Term.strip_comb |> snd
    val idenv = nth args 0 |> Term.dest_Var
    val idstr = nth args 1 |> Term.strip_comb |> snd |> hd |> Term.dest_Var
    val idsl1 = nth args 1 |> Term.dest_comb |> snd |> Term.dest_Var
    val idf = nth args 2 |> Term.dest_Var
    val ide = nth args 3 |> Term.dest_Var
    val idis_send = nth args 4 |> Term.dest_Var
    val ids = nth args 5 |> Term.dest_Var
    val th1 = pathlist_execution_th2 |> Drule.instantiate_normalize ([], [(idsl1,sl1),
              (idstr,str),(ids,s),(idf,f),(ide,e),(idenv,env),(idis_send, is_send)])
    val th2 = asm_full_simplify ctxt th1
    val ST = nth (th2 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
    val state_th = evaluate_State_Execution ctxt env ST e is_send s
    val b = nth (state_th |> Thm.concl_of |> Term.dest_comb |> snd 
                 |> Term.strip_comb |> snd) 6 |> Thm.cterm_of ctxt
  in
    if b aconvc @{cterm "False"} then
      state_th RS th2
    else
      let
        val pathlist_execution_th1 = @{thm Pathlist_Execution1}
        val th1 = pathlist_execution_th1 |> Drule.instantiate_normalize ([], [(idsl1,sl1),
              (idstr,str),(ids,s),(idf,f),(ide,e),(idenv,env),(idis_send, is_send)])
        val th2 = asm_full_simplify ctxt th1
        val th3 = state_th RS th2
        val s2 = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                                |> Term.strip_comb |> snd) 5 |> Thm.cterm_of ctxt
        val path_list_execution_th = 
            evaluate_path_list_execution ctxt env sl1 f e is_send s2
      in
        path_list_execution_th RS th3
      end
  end
\<close>

ML \<open>
fun evaluate_root_exec_for_times ctxt env e n s = 
  if n aconvc @{cterm "0::int"} then
    let
      val root_exec_for_times_th1 = @{thm Root_Exec_for_Times1}
      val args = root_exec_for_times_th1 |> Thm.concl_of 
                  |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val idenv = nth args 0 |> Term.dest_Var
      val ide = nth args 1 |> Term.dest_Var
      val ids = nth args 3 |> Term.dest_Var
    in
      root_exec_for_times_th1 |> Drule.instantiate_normalize ([], [(idenv, env),
              (ide, e), (ids, s)])
    end
  else
    let
      val root_exec_for_times_th2 = @{thm Root_Exec_for_Times2}
      val args = root_exec_for_times_th2 |> Thm.concl_of 
                  |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val idenv = nth args 0 |> Term.dest_Var
      val ide = nth args 1 |> Term.dest_Var
      val ids = nth args 3 |> Term.dest_Var
      val idn = nth args 2 |> Term.dest_Var
      val th1 = root_exec_for_times_th2 |> Drule.instantiate_normalize ([], [(idenv, env),
              (ide, e), (ids, s), (idn, n)])
      val th2 = asm_full_simplify ctxt th1
      val empty_name = @{cterm "[]::string list"}
      val is_send = @{cterm "False"}
      val root = env |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
      val t_start = Timing.start ()
      val comp_th = evaluate_Composition_Execution ctxt env root empty_name e is_send s
      val th3 = comp_th RS th2
      val t_end = Timing.result t_start
      val _ = writeln ("Test" ^ (Timing.message t_end))
      val s2 = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 3 |> Thm.cterm_of ctxt
      val n2 = nth (th3 |> Thm.prems_of |> hd |> Term.dest_comb |> snd 
                            |> Term.strip_comb |> snd) 2 |> Thm.cterm_of ctxt
      val root_exec_th = evaluate_root_exec_for_times ctxt env e n2 s2
    in
      root_exec_th RS th3
    end

\<close>

schematic_goal myconj:"?x = ?x \<and> ?y = ?y"
  by auto
\<comment> \<open>some tests in ML level\<close>
ML \<open>
val ctxt = @{context}
val A = @{cterm "State [''A''] SKIP SKIP SKIP [] [Trans (P [''A'']) (T1 (Before ''E_one'' (N 2))) 
((V ''x'') [>] (V ''y'')) SKIP SKIP (P [''B''])] No_Composition"}
val B = @{cterm "State [''B''] SKIP SKIP SKIP [] [] No_Composition"}
val Root = @{cterm "Or [Trans NONE (S '''') (Bc True) SKIP SKIP (P [''A''])] False
(\<lambda>x. (if x = ''A'' then (State [''A''] SKIP SKIP SKIP [] [Trans (P [''A'']) (T1 (Before ''E_one'' (N 2))) 
((V ''x'') [>] (V ''y'')) SKIP SKIP (P [''B''])] No_Composition) else
(if x = ''B'' then (State [''B''] SKIP SKIP SKIP [] [] No_Composition) else No_State)))"}
val env = @{cterm "Env (Or [Trans NONE (S '''') (Bc True) SKIP SKIP (P [''A''])] False
(\<lambda>x. (if x = ''A'' then (State [''A''] SKIP SKIP SKIP [] [Trans (P [''A'']) (T1 (Before ''E_one'' (N 2))) 
((V ''x'') [>] (V ''y'')) (''x'' ::= (N 2)) SKIP (P [''B''])] No_Composition) else
(if x = ''B'' then (State [''B''] SKIP SKIP SKIP [] [] No_Composition) else No_State))))
(\<lambda>name. (SKIP, No_Expr, No_Expr))
(\<lambda>name. ((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr))
(\<lambda>x.[]::transition list)"}
val root = env |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
val fe = nth (env |> Thm.term_of |> Term.strip_comb |> snd) 1 |> Thm.cterm_of ctxt
val ge = nth (env |> Thm.term_of |> Term.strip_comb |> snd) 2 |> Thm.cterm_of ctxt
val g = nth (env |> Thm.term_of |> Term.strip_comb |> snd) 3 |> Thm.cterm_of ctxt
val p = @{cterm "[''A'']"}
val e = @{cterm "''E_one''::string"}
val t = @{cterm "Trans (P [''A'']) (T1 (Before ''E_one'' (N 2))) 
((V ''x'') [>] (V ''y'')) (print1 ''cond_act'') SKIP (P [''B''])"}
val T = @{cterm "[Trans (P [''A'']) (T1 (After ''E_one'' (N 2))) 
((V ''x'') [>] (V ''y'')) (print1 ''cond_act'') SKIP (P [''B''])]"}
val Chart = @{cterm "\<lambda>x. (if x = [''A''] then (Info True [] []) else
if x = ([]::string list) then (Info True  ''A'' []) else
(Info False [] []))"}
val s = @{cterm "Status (Vals (\<lambda>x. (if x = ''x'' then (1::int) else (0::int)))
 (\<lambda>p str. 0) (\<lambda>x. 0) ([], [])) (\<lambda>x. (if x = [''A''] then (Info True [] []) else
if x = ([]::string list) then (Info True  ''A'' []) else
(Info False [] [])))"}
val v = s |> Thm.term_of |> Term.strip_comb |> snd |> hd |> Thm.cterm_of ctxt
val th = evaluate_exit_state ctxt env A e s
\<close>
definition fe::fenv where "
  fe name = (SKIP, No_Expr, No_Expr)"


ML \<open>
signature STATEFLOW_EXECUTION1 = 
sig
  val stateflow_execution1_tac: Proof.context -> tactic
end

structure Stateflow_Execution1 : STATEFLOW_EXECUTION1 = 
struct

fun stateflow_execution1_tac ctxt state = 
  let
    val subgoals = state |> Thm.cprop_of |> Drule.strip_imp_prems
    (*val _ = pwriteln (pretty_term ctxt (Thm.term_of (hd subgoals)))*)
  in
    if null subgoals then Seq.empty else
    let
      val c_subgoal = hd subgoals
      val subgoal = Thm.term_of c_subgoal
      val args = subgoal |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val env = nth args 0 |> Thm.cterm_of ctxt
      val C = nth args 1 |> Thm.cterm_of ctxt
      val name = nth args 2 |> Thm.cterm_of ctxt
      val e = nth args 3 |> Thm.cterm_of ctxt
      val s1 = nth args 5 |> Thm.cterm_of ctxt
      val th = evaluate_Composition_Execution ctxt env C name e @{cterm "False"} s1
      val args_res = th |> Thm.prop_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val _ = pwriteln (pretty_term ctxt (nth args_res 6))
(*      val _ = pwriteln (pretty_term ctxt (Thm.prop_of th)) *)
    in
      Seq.single (th RS state)
    end
  end
end

\<close>

lemma "V ''x'' = V ''x''"
  by auto
schematic_goal test:"?x = ?x \<and> ?y = ?y"
  by auto

method_setup stateflow_execution1 
= \<open>Scan.succeed (SIMPLE_METHOD o Stateflow_Execution1.stateflow_execution1_tac)\<close> 
"Stateflow_Execution1 prover"


ML \<open>
signature STATEFLOW_EXECUTION2 = 
sig
  val stateflow_execution2_tac: Proof.context -> tactic
end

structure Stateflow_Execution2 : STATEFLOW_EXECUTION2 = 
struct

fun stateflow_execution2_tac ctxt state = 
  let
    val subgoals = state |> Thm.cprop_of |> Drule.strip_imp_prems
    (*val _ = pwriteln (pretty_term ctxt (Thm.term_of (hd subgoals)))*)
  in
    if null subgoals then Seq.empty else
    let
      val c_subgoal = hd subgoals
      val subgoal = Thm.term_of c_subgoal
      val args = subgoal |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val env = nth args 0 |> Thm.cterm_of ctxt
      val e = nth args 1 |> Thm.cterm_of ctxt
      val n = nth args 2 |> Thm.cterm_of ctxt
      val s1 = nth args 3 |> Thm.cterm_of ctxt
      val th = evaluate_root_exec_for_times ctxt env e n s1
      val args_res = th |> Thm.prop_of |> Term.dest_comb |> snd |> Term.strip_comb |> snd
      val _ = pwriteln (pretty_term ctxt (nth args_res 4))
(*      val _ = pwriteln (pretty_term ctxt (Thm.prop_of th)) *)
    in
      Seq.single (th RS state)
    end
  end
end

\<close>

method_setup stateflow_execution2 
= \<open>Scan.succeed (SIMPLE_METHOD o Stateflow_Execution2.stateflow_execution2_tac)\<close> 
"Stateflow_Execution2 prover"


end 