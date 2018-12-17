theory Sound 
imports op HHL
begin 

no_notation FForm ("F _")
no_notation EExp ("E _")

(*The definition for the soundness of sequtial process*)
definition Valid :: "fform => proc => fform => fform => bool" ("Valid _ _ _ _")
where "Valid p Q q H = 
         (ALL f d f' d'. (evalP (Q, f, d) = (Skip, f', d')) --> evalF (last(f(d)), p)
           --> (evalF (last(f'(d')), q) & ievalF (f', H, d, d')))"

(*The definition for the soundness of parallel process*)
definition ValidP :: "fform => fform => proc => proc => fform => fform => fform => fform => bool" 
("ValidP _ _ _ _ _ _ _ _")
where "ValidP p1 p2 P Q q1 q2 H1 H2 =
         (ALL f g f' g' d d1 d2. (evalPP (P||Q,f,g,d) = (Skip,f',g',d1,d2)) 
            --> evalF (last(f(d)), p1) --> evalF (last(g(d)), p2) 
              --> (evalF (last(f'(d1)), q1) & evalF (last(g'(d2)), q2) & 
                     ievalF (f', H1, d, d1)& ievalF (g', H2, d, d2)))"

(*soundness for consequence rule of sequtial*)
lemma ConsequenceS_sound: "Valid px P qx Hx
        --> (ALL f1 d1. evalF (last(f1(d1)),(p [-->] px)))
        --> (ALL f1 d1. evalF (last(f1(d1)),(qx [-->] q)))
        --> (ALL f1 d1 d2. ievalF (f1,(Hx [-->] H),d1,d2))
        --> Valid p P q H"
apply (simp add: Imply_eval)
apply (unfold Valid_def,auto)
apply (subgoal_tac "evalF(last(f'(d')), qx)",auto)
apply (subgoal_tac "evalF(last(f(d)), px)",auto)
apply (subgoal_tac "ievalF(f', Hx, d, d')",auto)
apply (subgoal_tac "evalF(last(f(d)), px)",auto)
done

(*soundness for consequence rule of parallel*)
lemma ConsequenceP_sound: "ValidP px py Px Py qx qy Hx Hy
        --> (ALL f1 d1. evalF (last(f1(d1)),(p [-->] px)))
        --> (ALL f1 d1. evalF (last(f1(d1)),(r [-->] py)))
        --> (ALL f1 d1. evalF (last(f1(d1)),(qx [-->] q)))
        --> (ALL f1 d1. evalF (last(f1(d1)),(qy [-->] s)))
        --> (ALL f1 d1 d2. ievalF (f1,(Hx [-->] H),d1,d2))
        --> (ALL f1 d1 d2. ievalF (f1,(Hy [-->] G),d1,d2))
        --> ValidP p r Px Py q s H G"
apply (simp add: Imply_eval)
apply (unfold ValidP_def,auto)
apply blast
apply (subgoal_tac "evalF(last(g'(d2)), qy)",auto)
apply (subgoal_tac "evalF(last(f(d)), px)",auto)
apply (subgoal_tac "evalF(last(g(d)), py)",auto)
apply (subgoal_tac "ievalF(f', Hx, d, d1)",auto)
apply (subgoal_tac "evalF(last(f(d)), px)",auto)
apply (subgoal_tac "evalF(last(g(d)), py)",auto)
apply (subgoal_tac "ievalF(g', Hy, d, d2)",auto)
apply (subgoal_tac "evalF(last(f(d)), px)",auto)
apply (subgoal_tac "evalF(last(g(d)), py)",auto)
done

(*The following rules from substR_fact1 to substR are for syntatical substitution,
  and are used for proving soundness of assignment rule and communiction rule.*)
lemma substR_fact1 : " ALL f. evalE(f, substE([(RVar x, e)], v))
        = evalE(%y i. if y = x & i = R then evalE(f, e) else f(y, i), v)"
apply (induct v, auto)
apply (case_tac "evalE(%y i. if y = x & i = R then evalE(f, e) else f(y, i), v1)", auto)+
  done
  sorry

lemma substR_fact2: "substE([], e) = e"
apply (induct "e", auto)
done

lemma substR_fact3: "substF([], q) = q"
apply (induct "q", auto)
apply (simp add:substR_fact2)+
done

lemma substR_fact4: " ~ inPairForm([(RVar x, e)], WALL list q)
        ==> ((substF([(RVar x, e)], WALL list q)) = (WALL list (substF ([(RVar x, e)], q))))"
apply (simp add:inPairForm_def)
done

lemma substR_fact5 : "~inExp(list, e)
        ==> ALL f v. evalE(f, e) = evalE(%a i. if a = list then RR(v) else f(a, i), e)"
apply (induct e, auto)
apply (case_tac "evalE(f, e1)", auto)+
  done
  sorry

lemma substR_ALL : " [| ~ inPairForm([(RVar x, e)], q)
        ==> ALL f. evalF(f, substF([(RVar x, e)], q))
                 = evalF(%y i. if y = x & i = R then evalE(f, e) else f(y, i), q);
        ~ inPairForm([(RVar x, e)], WALL list q ) |]
        ==> ALL f. evalF(f, substF([(RVar x, e)], WALL list q ))
                 = evalF(%y i. if y = x & i = R then evalE(f, e) else f(y, i), WALL list q )"
apply (rule allI)
apply (cut_tac x = x and e = e and q = q and list = "list" in substR_fact4, simp)
apply (subgoal_tac "evalF(f, substF([(RVar x, e)], WALL list q ))
         = evalF (f, (WALL list substF([(RVar x, e)], q)))")
defer apply simp
apply (subgoal_tac "evalF(f, substF([(RVar x, e)], WALL list q ))
         = (ALL (v::real). (evalF((%a. %i. (if (a=list) then (RR (v)) else (f(a, i))))
              , substF([(RVar x, e)], q))))")
defer apply simp
apply (subgoal_tac "evalF(%y i. if y = x & i = R  then evalE(f, e) else f(y, i), WALL list q) =
         (let f1 = (%y i. if y = x & i = R  then evalE(f, e) else f(y, i)) in 
         (ALL (v::real). (evalF((%a. %i. (if (a=list) then (RR (v)) else (f1(a, i)))), q))))")
defer apply simp
apply (subgoal_tac "~ inPairForm([(RVar x, e)], q)")
defer apply simp
apply (subgoal_tac "ALL v. let f2 = %a i. if a = list then RR(v) else f(a, i) in
         (evalF(f2, substF([(RVar x, e)], q)) 
         = evalF(%y i. if y = x & i = R  then evalE(f2, e) else f2(y, i), q))")
defer apply simp
apply (subgoal_tac "(let f1 = %y i. if y = x & i = R  then evalE(f, e) else f(y, i) in
         ALL v. evalF(%a i. if a = list then RR(v) else f1(a, i), q)) = 
         (ALL v. let f2 = %a i. if a = list then RR(v) else f(a, i) in
           evalF(%y i. if y = x & i = R  then evalE(f2, e) else f2(y, i), q))", simp)
apply (subgoal_tac "~x=list")
apply (simp add:Let_def)
apply (subgoal_tac "ALL v t. evalE(f, e) = evalE(%a i. if a = list then RR(v) else f(a, i), e)")
apply (subgoal_tac "ALL v. (%a i. if a = list then RR(v) else if a = x & i = R then evalE(f, e) else f(a, i))
         = (%y i. if y = x & i = R  then evalE(%a i. if a = list then RR(v) else f(a, i), e) 
         else if y = list then RR(v) else f(y, i))", simp)
apply (simp add:fun_eq_iff)
apply (cut_tac list = "list" and e =  e in substR_fact5, auto)
done

lemma substR_fact6: " ~ inPairForm([(RVar x, e)], WEX list q) ==>
        ((substF([(RVar x, e)], WEX list q)) = (WEX list (substF ([(RVar x, e)], q))))"
apply (simp add:inPairForm_def)
done

lemma substR_EX : "[| ~ inPairForm([(RVar x, e)], q)
        ==> ALL f. evalF(f, substF([(RVar x, e)], q))
                 = evalF(%y i. if y = x & i = R then evalE(f, e) else f(y, i), q);
        ~ inPairForm([(RVar x, e)], WEX list q) |]
        ==> ALL f. evalF(f, substF([(RVar x, e)], WEX list q))
                 = evalF(%y i. if y = x & i = R then evalE(f, e) else f(y, i), WEX list q)"
apply (rule allI)
apply (cut_tac x = x and e = e and q = q and list = "list" in substR_fact6, simp)
apply (subgoal_tac "evalF(f, substF([(RVar x, e)], WEX list q ))
                  = evalF ( f, (WEX list substF([(RVar x, e)], q)))")
defer apply simp
apply (subgoal_tac "evalF(f, substF([(RVar x, e)], WEX list q ))
         = (EX (v::real). (evalF((%a. %i. (if (a=list) then (RR (v)) else (f(a, i))))
              , substF([(RVar x, e)], q))))")
defer apply simp
apply (subgoal_tac "evalF(%y i. if y = x & i = R  then evalE(f, e) else f(y, i), WEX list q) 
         = (let f1 = (%y i. if y = x & i = R  then evalE(f, e) else f(y, i)) in 
             (EX (v::real) .  (evalF((%a. %i. (if (a=list) then (RR (v)) else (f1(a, i)))), q))))")
defer apply simp
apply (subgoal_tac "~ inPairForm([(RVar x, e)], q)")
defer apply simp
apply (subgoal_tac "EX v. let f2 = %a i. if a = list then RR(v) else f(a, i) in
         (evalF(f2, substF([(RVar x, e)], q)) 
         = evalF(%y i. if y = x & i = R  then evalE(f2, e) else f2(y, i), q))")
defer apply simp
apply (subgoal_tac "(let f1 = %y i. if y = x & i = R  then evalE(f, e) else f(y, i)
         in EX v. evalF(%a i. if a = list then RR(v) else f1(a, i), q)) = 
         (EX v. let f2 = %a i. if a = list then RR(v) else f(a, i)
         in  evalF(%y i. if y = x & i = R  then evalE(f2, e) else f2(y, i), q))", simp)
apply (subgoal_tac "~x=list")
apply (simp add:Let_def)
apply (subgoal_tac "ALL v. evalE(f, e) = evalE(%a i. if a = list then RR(v) else f(a, i), e)")
apply (subgoal_tac "ALL v. (%a i. if a = list then RR(v) else if a = x & i = R   then evalE(f, e) else f(a, i))
         = (%y i. if y = x & i = R then evalE(%a i. if a = list then RR(v) else f(a, i), e) 
           else if y = list then RR(v) else f(y, i))", auto)
apply (simp add:fun_eq_iff)
apply (cut_tac list = "list" and e =  e in substR_fact5, auto)
done

(*lemma used for proving the soundness of assignment rule and communication rule.
  This lemma means that the substitution for a variable is equivlant to change the state.*)
lemma substR: "~inPairForm ([(RVar x, e)], q) ==> ALL f. evalF(f, substF([(RVar x, e)], q)) =
              evalF(%y i. if y = x & i = R then evalE(f, e) else f(y, i), q)"
apply (induct q)
apply simp
apply simp
defer defer defer
apply simp
apply simp
apply simp
apply simp
apply simp
defer defer
apply (simp add:substF_def)
apply (cut_tac x = x and e=e and v = "exp1" in substR_fact1)
apply (cut_tac x = x and e=e and v = "exp2" in substR_fact1)
apply (rule allI)
apply (case_tac "evalE(%y i. if y = x & i = R then evalE(f, e) else f(y, i), exp1)")
apply simp
apply simp
apply simp
apply simp
apply (simp add:substF_def)
apply (cut_tac  x = x and e=e and v = "exp1" in substR_fact1)
apply (cut_tac  x = x and e=e and v = "exp2" in substR_fact1)
apply (rule allI)
apply (case_tac "evalE(%y i. if y = x & i = R then evalE(f, e) else f(y, i), exp1)")
apply simp
apply simp
apply simp
apply simp
apply (simp add:substF_def)
apply (cut_tac  x = x and e=e and v = "exp1" in substR_fact1)
apply (cut_tac  x = x and e=e and v = "exp2" in substR_fact1)
apply (rule allI)
apply (case_tac "evalE(%y i. if y = x & i = R then evalE(f, e) else f(y, i), exp1)")
apply simp
apply simp
apply simp
apply simp
apply (cut_tac x =  x and e = e and q = q and list = "list" in substR_ALL, simp)
apply simp
apply simp
apply (cut_tac x =  x and e = e and q = q and list = "list" in substR_EX, auto)
  done
  sorry

(*soundness for assign rule of real variable, others are in the end of this file*)
lemma AssignR_sound: "~inPairForm ([(RVar x, e)], q) & 
        (ALL f. evalF (f, p [-->] (substF ([((RVar (x)), e)]) (q))))
        &   (ALL f d1 d2. ievalF (f, (l [=] (Real 0)) [-->] G, d1, d2)) --> Valid p (RVar (x)):=e q G"
apply (simp add:Imply_eval)
apply (unfold Valid_def, auto)
(*1st*)
apply (cut_tac x = "x" and e = "e" and f = "f" and d = "d" in assignR,auto)
apply (cut_tac x = x and e = e and q = q  in substR,auto)
(*2nd*)
apply (cut_tac x = "x" and e = "e" and f = "f" and d = "d" in assignR,simp)
apply (subgoal_tac "ievalF(f', l [=] Real 0, d', d')",auto)
apply (cut_tac L=0 in L_eval,auto)
done

(*soundness for continue rule*)
lemma continue_sound: "(ALL f1 d1 d2. evalF (last(f1(d1)),Init [-->] F)) 
        & (ALL f1 d1 d2. evalF (last(f1(d1)),((p [&] close(F) [&] close([~]b)) [-->] q)))
        & (ALL f1 d1 d2. ievalF (f1,((((l [=] Real 0) [|] (high (close(F) [&] p [&] close(b)))) [&] Rg) [-->] G),d1,d2))
        & (disj (p, F))
        --> Valid (Init [&] p) (<F&&b> : Rg) q G"
apply (unfold Valid_def, auto)
(*1st*)
apply (cut_tac F = F and b = b and  Rg = "Rg" and f = f and d = d and f' = "f'" and d' = "d'" in continue, auto)
apply (subgoal_tac "evalF(last(f'(d')), p) & evalF(last(f'(d')), close(F)) & evalF(last(f'(d')), NotForm(b))",auto)
apply (cut_tac f = "last(f'(d'))" and b = d and c = "d'" and p = F in close_fact1, auto)
apply (cut_tac f = "last(f'(d'))" and b = d and c = "d'" and p = b in close_fact2, auto)
(*2nd*)
apply (simp add:Imply_eval And_eval Or_eval)
apply (cut_tac F = F and b = b and  Rg = "Rg" and f = f and d = d and f' = "f'" and d' = "d'" in continue, auto)
apply (subgoal_tac "( ((ievalF(f', (l [=] Real 0), d, d')) | (ievalF(f', (high (close(F) [&] p [&] close(b))), d, d')) ) &
             (ievalF(f', Rg, d, d')) ) --> (ievalF(f',G,d,d'))")
prefer 2 
apply simp
apply (subgoal_tac "( ((ievalF(f', (l [=] Real 0), d, d')) | (ievalF(f', (high (close(F) [&] p [&] close(b))), d, d')) ) &
             (ievalF(f', Rg, d, d')) )",simp)
apply auto
apply (case_tac "d=d'",auto)
apply (cut_tac L=0 in L_eval,auto)
apply (subgoal_tac "ievalF(f', high (close(F) [&] p [&] close(b)), d, d')",simp)
apply (simp add: high_eval And_eval,auto)
apply (subgoal_tac "evalFP(f', F [&] b, ka)",auto)
apply (simp add: evalFP_def And_eval)
apply (rule allI)
apply (subgoal_tac "inList(s, f'(ka)) --> evalF(s, F) & evalF(s, b)")
defer
apply blast
apply (rule impI)
apply (subgoal_tac "evalF(s, F) & evalF(s, b)")
defer
apply blast
apply (rule conjI)
apply (cut_tac s=s and p=F in close_fact3,simp)
apply assumption
apply (rule conjI)
defer
apply (cut_tac s=s and p=b in close_fact3,simp)
apply assumption
apply blast
done

(*soundness for sequence rule*)
lemma Sequence_sound: "(Valid p P m H
        & Valid m Q q G)
        --> Valid p (P;(m,H);Q) q H[^]G"
apply (simp add:Valid_def, auto)
apply (cut_tac P = P and mid = "(m, H)" and Q = Q and f = f and 
               d = d and F = "f'" and D = "d'" in sequence, auto)
apply blast
apply (cut_tac P = P and mid = "(m, H)" and Q = Q and f = f and 
               d = d and F = "f'" and D = "d'" in sequence, auto)
apply (cut_tac f = "f'" and P = H and Q = G and c = d and d = "d'" in chop_eval1, auto)
apply blast
done

(*soundness for condition rule in case b is false, 
  later it is used to prove the soundness of condition rule*)
lemma ConditionF_sound: "(ALL f1 d1 d2. evalF (last(f1(d1)),(p [-->] [~] b)) 
        & evalF (last(f1(d1)),(p [-->] q))
        & ievalF (f1,((l [=] Real 0) [-->] G),d1,d2))
        --> Valid p (IF b P) q G"
apply (simp add:Imply_eval)
apply (simp add:Valid_def, auto)
apply (simp add:conditionF)+
apply (subgoal_tac " ievalF(f', l[=]Real 0, d', d')",auto)
apply (simp add:L_eval)
done

(*soundness for condition rule in case b is true, 
  later it is used to prove the soundness of condition rule*)
lemma ConditionT_sound: "(ALL f1 d1 d2. evalF (last(f1(d1)),(p [-->] b)) 
        & Valid p P q G)
        --> Valid p (IF b P) q G"
apply (simp add:Imply_eval)
apply (simp add:Valid_def, auto)
apply (cut_tac f = f and be = b and d = d and P = P and f' = "f'" and d' = "d'" in conditionT, auto)
apply (blast)
apply (cut_tac f = f and be = b and d = d and P = P and f' = "f'" and d' = "d'" in conditionT, auto)
apply blast
done

(*soundness for condition rule*)
lemma Condition_sound: "(Valid (p [&] b) (IF b P) q G
        & Valid (p [&] ([~]b)) (IF b P) q G)
        --> Valid p (IF b P) q G"
apply (simp add:Valid_def, auto)
apply blast+
done

(*soundness for nondeterministic rule of real variable*)
lemma NondeterministicR_sound: "Valid (p [&] b) P q G
        --> Valid p (NON R x : b P) q G"
apply (simp add:Valid_def,auto)
apply (cut_tac f = f and d = d and b = b and x = x and P = P and f' = "f'" and d' = "d'" in nondeterR, auto)+
done

(*soundness for nondeterministic rule of string variable*)
lemma NondeterministicS_sound: "Valid (p [&] b) P q G
        --> Valid p (NON S x : b P) q G"
apply (simp add:Valid_def,auto)
apply (cut_tac f = f and d = d and b = b and x = x and P = P and f' = "f'" and d' = "d'" in nondeterS, auto)+
done

(*soundness for nondeterministic rule of bool variable*)
lemma NondeterministicB_sound: "Valid (p [&] b) P q G
        --> Valid p (NON B x : b P) q G"
apply (simp add:Valid_def,auto)
apply (cut_tac f = f and d = d and b = b and x = x and P = P and f' = "f'" and d' = "d'" in nondeterB, auto)+
done

(*soundness for communication rule of real variable, others are in the end of this file.*)
lemma CommR_sound: "(ValidP px py Px Py qx qy Hx Hy)
        --> ~inPairForm([(RVar x, e)], ry)
        --> (ALL f g d. EX F G Da Db. evalPP(Px||Py,f,g,d) = (Skip,F,G,Da,Db))
        --> (ALL f1 d1. evalF (last(f1(d1)),(qx [-->] rx) [&] (qy [-->] (substF ([(RVar(x), e)]) (ry)))))
        --> (ALL f1 d1 d2. ievalF (f1,((Hx [^] (high (qx))) [-->] Gx) [&] ((Hy [^] (high(qy))) [-->] Gy),d1,d2))
        --> (ALL f1 f2 d1 d2. (ievalF(f1,(Hx[^](high (qx))),d1,d2) & ievalF(f2,Hy[^](l[=]Real 0),d1,d2)) |
                (ievalF(f2,(Hy[^](high (qy))),d1,d2) & ievalF(f1,Hx,d1,d2)) -->
                (ievalF(f1,H,d1,d2) & ievalF(f2,H,d1,d2)))
        --> ValidP px py (Px;m;ch!!e) (Py;M;ch??(RVar(x))) rx ry (Gx[&]H) (Gy[&]H)"
apply (simp add:Imply_eval And_eval)
apply (unfold ValidP_def,auto)
(*Proving for the 1st postcondition*)
apply (subgoal_tac "EX F G Da Db. evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db)")
prefer 2
apply simp
apply (erule exE)+
apply (subgoal_tac "evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)")
prefer 2
apply simp
apply (cut_tac Px=Px and Py=Py and f=f and g=g and d=d and ch=ch and e=e and x=x and
               F=F and G=G and Da=Da and Db=Db and m=m and M=M in communicationR,auto)
(*Proving for the 2nd postcondition*)
apply (subgoal_tac "EX F G Da Db. evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db)")
prefer 2
apply simp
apply (erule exE)+
apply (subgoal_tac "evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)")
prefer 2
apply simp
apply (cut_tac Px=Px and Py=Py and f=f and g=g and d=d and ch=ch and e=e and x=x and
               F=F and G=G and Da=Da and Db=Db and m=m and M=M in communicationR,auto)
apply (case_tac "Db < Da",auto)
apply (cut_tac x = x and e = e and q = ry in substR,auto)
apply (subgoal_tac "evalF(last(G(Db)), substF([(RVar x, e)], ry))")
prefer 2
apply (subgoal_tac "evalF(last(G(Db)), qy) --> evalF(last(G(Db)), substF([(RVar x, e)], ry))",simp)
apply blast
apply (cut_tac x=x and e=e and q=ry in substR,auto)
(*Proving for the 1st history, it is a conjunction of two formulae Gx and H*)
(*Start to prove Gx*)
apply (subgoal_tac "EX F G Da Db. evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db)")
prefer 2
apply simp
apply (erule exE)+
apply (simp add:And_eval Imply_eval)
apply (subgoal_tac "ievalF(f', Hx [^] high qx, d, d1)")
apply simp
prefer 2
apply (cut_tac Px=Px and Py=Py and f=f and g=g and d=d and ch=ch and e=e and x=x and
               F=F and G=G and Da=Da and Db=Db and m=m and M=M in communicationR,auto)
(*start for the 1st case "Da < Db"*)
apply (cut_tac f = "%t. if Da < t & t <= Db then [last(F(Da))] else F(t)" and 
               P = Hx and Q = "high qx" and c = d and d = Db in chop_eval1, auto)
apply (cut_tac x=Da in exI,auto)
apply (subgoal_tac "ievalF(%t. if Da < t & t <= Db then [last(F(Da))] else F(t), Hx, d, Da)
             = ievalF(F,Hx,d,Da)",simp)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
apply (cut_tac c=d and d=Da and f="%t. if Da < t & t <= Db then [last(F(Da))] else F(t)" and
               g=F and P=Hx in chop_interval,auto)
apply (cut_tac f="%t. if Da < t & t <= Db then [last(F(Da))] else F(t)" and P=qx and c=Da and d=Db in high_eval,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
prefer 2
apply blast
apply (simp add: evalFP_def)
(*start for the 2nd case "Db < Da"*)
apply (cut_tac f = F and P = Hx and Q = "high qx" and c = d and d = Da in chop_eval1, auto)
apply (cut_tac x=Da in exI,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
apply (simp add: high_eval,auto)
(*start for the 2nd case "Db = Da"*)
apply (cut_tac f = F and P = Hx and Q = "high qx" and c = d and d = Da in chop_eval1, auto)
apply (cut_tac x=Da in exI,auto)
apply blast
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
prefer 2
apply blast
apply (cut_tac f=F and P=qx and c=Da and d=Da in high_eval,auto) (*end for Gx*)
(*For proving H, we first prove "(Hy[^] high (qy))"*)
apply (subgoal_tac "ievalF(g', (Hy [^] high(qy)), d, d1)")
prefer 2
apply (cut_tac Px=Px and Py=Py and f=f and g=g and d=d and ch=ch and e=e and x=x and
               F=F and G=G and Da=Da and Db=Db and m=m and M=M in communicationR,auto) (*1*)
(*start for the 1st case "Db < Da"*)
apply (cut_tac f = "%t. if t = Da
                      then [last(G(Db)),
                            %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t < Da & Db < t then [last(G(Db))] else G(t)" and P = Hy and Q = "high qy" and 
               c = d and d = Da in chop_eval1, auto)
apply (cut_tac x=Db in exI,auto) (*1a*)
apply (subgoal_tac "ievalF(%t. if t = Da
                      then [last(G(Db)),
                            %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t < Da & Db < t then [last(G(Db))] else G(t),Hy, d, Db)
             = ievalF(G,Hy,d,Db)",simp)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
apply (cut_tac c=d and d=Db and f="%t. if t = Da
                      then [last(G(Db)),
                            %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t < Da & Db < t then [last(G(Db))] else G(t)" and
               g=G and P=Hy in chop_interval,simp)
apply (cut_tac f = "%t. if t = Db then []
                      else if t = Da
                           then [last(G(Db)),
                                 %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else if t < Da & Db < t then [last(G(Db))] else G(t)" and P = "high qy" and 
               Q = "l [=] Real 0" and c = Db and d = Da in chop_eval,simp)
apply (cut_tac f="%t. if t = Da
                      then [last(G(Db)),
                            %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t < Da & Db < t then [last(G(Db))] else G(t)" and
               P=qy and c=Db and d=Da in high_eval,auto)
apply (simp add: evalFP_def)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
(*start for the 2nd case "Db >= Da"*)
apply (simp add: chop_eval)
apply (cut_tac x=Db in exI,auto)
apply (cut_tac x="G(Db)" in exI,auto)
apply (cut_tac c=d and d=Db and f="%t. if t = Db then G(Db)
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and
               g=G and P=Hy in chop_interval,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
apply (cut_tac f="%t. if t = Db
                      then [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and P=qy and c=Db and d=Db in high_eval,auto)
(*start for H*)
apply (subgoal_tac "ievalF(g', Hy[^](l[=]Real 0), d, d1) | ievalF(f', Hx, d, d1)",auto)
apply (cut_tac Px=Px and Py=Py and f=f and g=g and d=d and ch=ch and e=e and x=x and
               F=F and G=G and Da=Da and Db=Db and m=m and M=M in communicationR,auto)
(*start for the 1st case Db < Da*)
apply (subgoal_tac "ievalF(F, Hx, d, Da)")
apply blast
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
(*start for the 2nd case Db >= Da*)
apply (case_tac "d=Db",auto) (*2a*)
apply (simp add: chop_eval)
apply (cut_tac x=Db in exI,auto)
apply (cut_tac x="G(Db)" in exI,auto)
apply (cut_tac c=Db and d=Db and f="%t. if t = Db then G(Db)
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and
               g=G and P=Hy in chop_interval,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, Db) = (Skip, F, G, Da, Db) -->
             evalF(last(f(Db)), px) --> evalF(last(g(Db)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, Db, Da) & ievalF(G, Hy, Db, Db)",simp)
apply blast
apply (cut_tac L=0 in L_eval,auto) (*2b*)
apply (cut_tac f = "%t. if t = Db
                      then G(Db) @
                           [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else G(t)" and P = Hy and Q = "l [=] Real 0" and c = d and d = Db in chop_eval, auto)
apply (cut_tac x=Db in exI,auto)
apply (cut_tac x="G(Db)" in exI,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
prefer 2
apply blast
apply (cut_tac c=d and d=Db and f="%t. if t = Db then G(Db)
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and
               g=G and P=Hy in chop_interval,auto)
apply (cut_tac L=0 in L_eval,auto)
apply (cut_tac x=Db in exI,auto)
apply (cut_tac x="G(Db)" in exI,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
prefer 2
apply blast
apply (cut_tac c=d and d=Db and f="%t. if t = Db then G(Db)
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and
               g=G and P=Hy in chop_interval,auto)
apply (cut_tac L=0 in L_eval,auto)
(*Proving for the 1st history, it is a conjunction of two formulae Gx and H*)
(*Start to prove Gx*)
apply (subgoal_tac "EX F G Da Db. evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db)")
prefer 2
apply simp
apply (erule exE)+
apply (simp add:And_eval Imply_eval)
apply (subgoal_tac "ievalF(g', (Hy [^] high(qy)), d, d2)")
prefer 2
apply (cut_tac Px=Px and Py=Py and f=f and g=g and d=d and ch=ch and e=e and x=x and
               F=F and G=G and Da=Da and Db=Db and m=m and M=M in communicationR,auto) (*1*)
(*start for the 1st case "Db < Da"*)
apply (cut_tac f = "%t. if t = Da
                      then [last(G(Db)),
                            %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t < Da & Db < t then [last(G(Db))] else G(t)" and P = Hy and Q = "high qy" and 
               c = d and d = Da in chop_eval1, auto)
apply (cut_tac x=Db in exI,auto) (*1a*)
apply (subgoal_tac "ievalF(%t. if t = Da
                      then [last(G(Db)),
                            %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t < Da & Db < t then [last(G(Db))] else G(t),Hy, d, Db)
             = ievalF(G,Hy,d,Db)",simp)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
apply (cut_tac c=d and d=Db and f="%t. if t = Da
                      then [last(G(Db)),
                            %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t < Da & Db < t then [last(G(Db))] else G(t)" and
               g=G and P=Hy in chop_interval,simp)
apply (cut_tac f = "%t. if t = Db then []
                      else if t = Da
                           then [last(G(Db)),
                                 %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else if t < Da & Db < t then [last(G(Db))] else G(t)" and P = "high qy" and 
               Q = "l [=] Real 0" and c = Db and d = Da in chop_eval,simp)
apply (cut_tac f="%t. if t = Da
                      then [last(G(Db)),
                            %y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t < Da & Db < t then [last(G(Db))] else G(t)" and
               P=qy and c=Db and d=Da in high_eval,auto)
apply (simp add: evalFP_def)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
(*start for the 2nd case "Db >= Da"*)
apply (simp add: chop_eval)
apply (cut_tac x=Db in exI,auto)
apply (cut_tac x="G(Db)" in exI,auto)
apply (cut_tac c=d and d=Db and f="%t. if t = Db then G(Db)
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and
               g=G and P=Hy in chop_interval,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
apply (cut_tac f="%t. if t = Db
                      then [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and P=qy and c=Db and d=Db in high_eval,auto)
(*For proving H, we first prove "(Hx[^] high (qx))"*)
apply (subgoal_tac "ievalF(f', Hx [^] high qx, d, d2)")
prefer 2
apply (cut_tac Px=Px and Py=Py and f=f and g=g and d=d and ch=ch and e=e and x=x and
               F=F and G=G and Da=Da and Db=Db and m=m and M=M in communicationR,auto)
(*start for the 1st case "Da < Db"*)
apply (cut_tac f = "%t. if Da < t & t <= Db then [last(F(Da))] else F(t)" and 
               P = Hx and Q = "high qx" and c = d and d = Db in chop_eval1, auto)
apply (cut_tac x=Da in exI,auto)
apply (subgoal_tac "ievalF(%t. if Da < t & t <= Db then [last(F(Da))] else F(t), Hx, d, Da)
             = ievalF(F,Hx,d,Da)",simp)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
apply (cut_tac c=d and d=Da and f="%t. if Da < t & t <= Db then [last(F(Da))] else F(t)" and
               g=F and P=Hx in chop_interval,auto)
apply (cut_tac f="%t. if Da < t & t <= Db then [last(F(Da))] else F(t)" and P=qx and c=Da and d=Db in high_eval,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
prefer 2
apply blast
apply (simp add: evalFP_def)
(*start for the 2nd case "Db < Da"*)
apply (cut_tac f = F and P = Hx and Q = "high qx" and c = d and d = Da in chop_eval1, auto)
apply (cut_tac x=Da in exI,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
apply (simp add: high_eval,auto)
(*start for the 2nd case "Db = Da"*)
apply (cut_tac f = F and P = Hx and Q = "high qx" and c = d and d = Da in chop_eval1, auto)
apply (cut_tac x=Da in exI,auto)
apply blast
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
prefer 2
apply blast
apply (cut_tac f=F and P=qx and c=Da and d=Da in high_eval,auto) (*end for Gx*)
(*start for H*)
apply (subgoal_tac "ievalF(g', Hy[^](l[=]Real 0), d, d2) | ievalF(f', Hx, d, d2)",auto)
apply (cut_tac Px=Px and Py=Py and f=f and g=g and d=d and ch=ch and e=e and x=x and
               F=F and G=G and Da=Da and Db=Db and m=m and M=M in communicationR,auto)
(*start for the 1st case Db < Da*)
apply (subgoal_tac "ievalF(F, Hx, d, Da)")
apply blast
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
apply blast
(*start for the 2nd case Db >= Da*)
apply (case_tac "d=Db",auto) (*2a*)
apply (simp add: chop_eval)
apply (cut_tac x=Db in exI,auto)
apply (cut_tac x="G(Db)" in exI,auto)
apply (cut_tac c=Db and d=Db and f="%t. if t = Db then G(Db)
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and
               g=G and P=Hy in chop_interval,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, Db) = (Skip, F, G, Da, Db) -->
             evalF(last(f(Db)), px) --> evalF(last(g(Db)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, Db, Da) & ievalF(G, Hy, Db, Db)",simp)
apply blast
apply (cut_tac L=0 in L_eval,auto) (*2b*)
apply (cut_tac f = "%t. if t = Db
                      then G(Db) @
                           [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                      else G(t)" and P = Hy and Q = "l [=] Real 0" and c = d and d = Db in chop_eval, auto)
apply (cut_tac x=Db in exI,auto)
apply (cut_tac x="G(Db)" in exI,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
prefer 2
apply blast
apply (cut_tac c=d and d=Db and f="%t. if t = Db then G(Db)
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and
               g=G and P=Hy in chop_interval,auto)
apply (cut_tac L=0 in L_eval,auto)
apply (cut_tac x=Db in exI,auto)
apply (cut_tac x="G(Db)" in exI,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, F, G, Da, Db) -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) -->
             evalF(last(F(Da)), qx) & evalF(last(G(Db)), qy) & ievalF(F, Hx, d, Da) & ievalF(G, Hy, d, Db)",simp)
prefer 2
apply blast
apply (cut_tac c=d and d=Db and f="%t. if t = Db then G(Db)
                      else if t = Db
                           then G(Db) @
                                [%y i. if y = x & i = R then evalE(last(G(Db)), e) else last(G(Db), y, i)]
                           else G(t)" and
               g=G and P=Hy in chop_interval,auto)
apply (cut_tac L=0 in L_eval,auto)
done

(*soundness for 1st paralle rule*)
lemma Parallel1_sound: "ValidP px py Px Py qx qy Hx Hy
        --> Valid qx Qx rx Gx
        --> Valid qy Qy ry Gy
        --> ValidP px py (Px; m; Qx) (Py; M; Qy) rx ry (Hx [^] Gx) (Hy [^] Gy)"
apply (simp add: ValidP_def Valid_def)
apply auto
(*1st*)
apply (cut_tac Px=Px and Py=Py and Qx=Qx and Qy=Qy and f=f and g=g and d=d and f'=f' and
               g'=g' and d'=d1 and D'=d2 and f''=f'' and g''=g'' and d''=d'' and D''=D'' and
               m=m and M=M in parallelN2,auto)
apply (subgoal_tac "evalP(Qx, f'', d'') = (Skip, f', d1) --> evalF(last(f''(d'')), qx) --> evalF(last(f'(d1)), rx)")
apply blast
apply auto
(*2nd*)
apply (cut_tac Px=Px and Py=Py and Qx=Qx and Qy=Qy and f=f and g=g and d=d and f'=f' and
               g'=g' and d'=d1 and D'=d2 and f''=f'' and g''=g'' and d''=d'' and D''=D'' and
               m=m and M=M in parallelN2,auto)
apply (subgoal_tac "evalP(Qy, f'', d'') = (Skip, g', d2) --> evalF(last(f''(d'')), qy) --> evalF(last(g'(d2)), ry)")
apply blast
apply auto
(*3rd*)
apply (cut_tac Px=Px and Py=Py and Qx=Qx and Qy=Qy and f=f and g=g and d=d and f'=f' and
               g'=g' and d'=d1 and D'=d2 and f''=f'' and g''=g'' and d''=d'' and D''=D'' and
               m=m and M=M in parallelN2,auto)
apply (subgoal_tac "ievalF(f', Hx, d, d'') & ievalF(f', Gx, d'', d1)",auto)
apply (cut_tac f=f' and P=Hx and Q=Gx and c=d and d=d1 in chop_eval1,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, f'', g'', d'', D'') -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) --> ievalF(f'', Hx, d, d'')")
apply blast
apply auto
apply (subgoal_tac "evalP(Qx, f'', d'') = (Skip, f', d1) -->
             evalF(last(f''(d'')), qx) --> evalF(last(f'(d1)), rx) & ievalF(f', Gx, d'', d1)")
apply blast
apply auto
(*4th*)
apply (cut_tac Px=Px and Py=Py and Qx=Qx and Qy=Qy and f=f and g=g and d=d and f'=f' and
               g'=g' and d'=d1 and D'=d2 and f''=f'' and g''=g'' and d''=d'' and D''=D'' and
               m=m and M=M and H=Hx and G=Hy in parallelN2,auto)
apply (subgoal_tac "ievalF(g', Hy, d, D'') & ievalF(g', Gy, D'', d2)",auto)
apply (cut_tac f=g' and P=Hy and Q=Gy and c=d and d=d2 in chop_eval1,auto)
apply (subgoal_tac "evalPP(Px||Py, f, g, d) = (Skip, f'', g'', d'', D'') -->
             evalF(last(f(d)), px) --> evalF(last(g(d)), py) --> ievalF(g'', Hy, d, D'')")
apply blast
apply auto
apply (subgoal_tac "evalP(Qy, g'', D'') = (Skip, g', d2) -->
             evalF(last(g''(D'')), qy) --> evalF(last(g'(d2)), ry) & ievalF(g', Gy, D'', d2)")
apply blast
apply auto
done

(*soundness for 2nd paralle rule*)
lemma Parallel2_sound: "Valid px Px qx Hx
        --> Valid py Py qy Hy
        --> ValidP px py Px Py qx qy Hx Hy"
apply (simp add: ValidP_def Valid_def)
apply auto
apply (cut_tac P=Px and Q=Py and d'="d1" and d''=d2 in parallelN1,auto)
apply (cut_tac P=Px and Q=Py and f=f and g=g and d=d and f'="f'" and g'=g' 
           and d'="d1" and d''=d2 in parallelN1,auto)
apply (subgoal_tac "evalP(Py, g, d) = (Skip, g', d2) --> evalF(last(g(d)), py) --> evalF(last(g'(d2)), qy) & ievalF(g', Hy, d, d2)")
apply blast
apply auto
apply (cut_tac P=Px and Q=Py and d'="d1" and d''=d2 in parallelN1,auto)
apply (cut_tac P=Px and Q=Py and f=f and g=g and d=d and f'="f'" and g'=g' 
           and d'="d1" and d''=d2 in parallelN1,auto)
apply (subgoal_tac "evalP(Py, g, d) = (Skip, g', d2) --> evalF(last(g(d)), py) --> evalF(last(g'(d2)), qy) & ievalF(g', Hy, d, d2)")
apply blast
apply auto
done

(*assists for proving the soundness of repetition rule*)
lemma Repetition_assist1: "[| ALL f1 d1 d2. ievalF(f1, Hx [^] Hx, d1, d2) --> ievalF(f1, Hx, d1, d2);
          ievalF(F(Suc(na)), l [=] Real 0 [|] Hx, D(0), D(na)) &
          ievalF(F(Suc(na)), l [=] Real 0 [|] Hx, D(na), D(Suc(na))) |]
            ==> ievalF(F(Suc(na)), l [=] Real 0 [|] Hx, D(0), D(Suc(na)))"
apply (simp add: Or_eval L_eval,auto)
apply (subgoal_tac "ievalF(F(Suc(na)), Hx [^] Hx, D(0), D(Suc(na))) --> ievalF(F(Suc(na)), Hx, D(0), D(Suc(na)))",auto)
apply (subgoal_tac "ievalF(F(Suc(na)), Hx [^] Hx, D(0), D(Suc(na)))",simp)
apply (rule chop_eval1,auto)
done

(*soundness for repetition rule*)
lemma Repetition_sound: "Valid px Px px Hx
        --> (ALL f1 d1 d2. ievalF (f1,(Hx [^] Hx [-->] Hx),d1,d2))
        --> Valid px (Px*) px ((l [=] Real 0) [|] Hx)" 
apply (simp add: Imply_eval)
apply (unfold Valid_def,auto)
(*1st*)
apply (cut_tac P = Px and f = f and d = d and f' = "f'" and d' = "d'" and F=F and D=D and
               H = "l [=] Real 0 [|] Hx" in repetition,auto)
apply (subgoal_tac "(ALL k<n. evalP(Px, F(k), D(k)) = (Skip, F(Suc(k)), D(Suc(k)))) --> evalF(last(F(n)(D(n))), px)")
apply blast
apply (induct_tac n,auto)
(*2nd*) 
apply (cut_tac P = Px and f = f and d = d and f' = "f'" and d' = "d'" and F=F and D=D and 
               H = "l [=] Real 0 [|] Hx" in repetition,auto)
apply (subgoal_tac "(ALL k<n. evalP(Px, F(k), D(k)) = (Skip, F(Suc(k)), D(Suc(k))) &
                    (ievalF(F(k), l [=] Real 0 [|] Hx, D(0), D(k)) --> 
                    ievalF(F(Suc(k)), l [=] Real 0 [|] Hx, D(0), D(k))))
                      --> evalF(last(F(n)(D(n))), px) & ievalF(F(n), l [=] Real 0 [|] Hx, D(0), D(n))")
apply blast
apply (induct_tac n,auto)
apply (simp add: Or_eval,auto)
apply (cut_tac f="F(0)" and L=0 and c="D(0)" and d="D(0)" in L_eval,auto)
apply (subgoal_tac "ievalF(F(Suc(na)), l [=] Real 0 [|] Hx, D(0), D(na)) &
               ievalF(F(Suc(na)), l [=] Real 0 [|] Hx, D(na), D(Suc(na)))")
apply (rule Repetition_assist1,auto)
apply (subgoal_tac "ievalF(F(Suc(na)), Hx, D(na), D(Suc(na)))")
apply (cut_tac f="F(Suc(na))" and F="l [=] Real 0" and G="Hx" and c="D(na)" and d="D(Suc(na))" in Or_eval,auto)
  done
  sorry

end
