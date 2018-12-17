theory State
imports Main
       "DCSequents/LSyntax"
   "HCSP_Com" 
(*This file defines states for HCSP programs, also regardes as interpretations for Duration Calculus.*)

begin

(*datatype interval = CC real real | CO real real | OO real real | OC real real*)

(*definition "CC l u == {l .. u}"*)

type_synonym now = real
type_synonym state = "string => typeid => val"
type_synonym cstate = "now => (state list)"

primrec evalE :: "state => exp => val" where
"evalE (f, RVar (x)) = f (x, R)" |
"evalE (f, SVar (x)) = f (x, S)" |
"evalE (f, BVar (x)) = f (x, B)" |
"evalE (f, Real (x)) = RR (x)" |
"evalE (f, String (x)) = SS (x)" |
"evalE (f, Bool (x)) = BB (x)" |
"evalE (f, e1 [+] e2) = (case (evalE (f, e1)) of RR (x) =>
                                         (case (evalE (f, e2)) of RR (y) => RR (x + y) |
                                                                          _    => Err)|
                                                              _ => Err)" |
"evalE (f, e1 [-] e2) = (case (evalE (f, e1)) of RR (x) =>
                                         (case (evalE (f, e2)) of RR (y) => RR (x - y) |
                                                                          _    => Err)|
                                                              _ => Err)" |
"evalE (f, e1 [*] e2) = (case (evalE (f, e1)) of RR (x) =>
                                         (case (evalE (f, e2)) of RR (y) => RR (x * y) |
                                                                          _    => Err)|
                                                              _ => Err)"



(*The function varE may return a list which may has repetitions of variables. However, it does not matter, because it still can judge if one variable is in the expression.*)
primrec varE :: "exp => ((typeid*string) list)" where
"varE (RVar (x)) = [(R,x)]" |
"varE (SVar (x)) = [(S,x)]" |
"varE (BVar (x)) = [(B,x)]" |
"varE (Real (x)) = []" |
"varE (String (x)) = []" |
"varE (Bool (x)) = []" |
"varE (e1 [+] e2) =  (varE(e1))@(varE(e2))" |
"varE (e1 [-] e2) = (varE(e1))@(varE(e2))" |
"varE (e1 [*] e2) = (varE(e1))@(varE(e2))"

(*The function varF may return a list which may has repetitions of variables. However, it does not matter, because it still can judge if one variable is in the form.*)
primrec varF :: "fform => ((typeid*string) list)" where
"varF (WTrue) = ([])" |
"varF (WFalse) = ([])" |
"varF (e1 [=] e2) = (varE(e1)@varE(e2))" |
"varF (e1 [<] e2) = (varE(e1)@varE(e2))" |
"varF (e1 [>] e2) = (varE(e1)@varE(e2))" |
"varF ([~] form1) = (varF(form1))" |
"varF (form1 [&] form2) = (varF(form1)@varF(form2))" |
"varF (form1 [|] form2) = (varF(form1)@varF(form2))" |
"varF (form1 [-->] form2) = (varF(form1)@varF(form2))" |
"varF (form1 [<->] form2) = (varF(form1)@varF(form2))" |
"varF (WALL x form1)= removeAll((R,x),varF(form1))" |
"varF (WEX x form1)= removeAll((R,x),varF(form1))"

primrec varP :: "proc => ((typeid*string) list)" where
"varP (Skip) = []" |
"varP (Stop) = []" |
"varP (exp1 := exp2) = varE(exp1)@varE(exp2)" |
"varP (cname !! exp) = varE(exp)" |  
"varP (cname ?? exp) = varE(exp)" |
"varP (proc1; mid; proc2) = varP(proc1)@varP(proc2)" |
"varP (IF form proc) = varF(form)@varP(proc)" |
"varP (NON type x : form proc) = removeAll((type,x),varP(proc))" |
"varP (proc1 \<rightarrow> proc2) = varP(proc1)@varP(proc2)" |
"varP (proc1 [[ proc2) = varP(proc1)@varP(proc2)" |
"varP (proc1 << proc2) = varP(proc1)@varP(proc2)" |
"varP (proc1 || proc2) = varP(proc1)@varP(proc2)" |
"varP (proc *) = varP(proc)" |
"varP (<Inv && bexp> : Rg) = varF(Inv)" |
"varP (proc1 |> time proc2) = varP(proc1)@varP(proc2)" |
"varP (proc1 [[> proc2) = varP(proc1)@varP(proc2)"

primrec inList :: "'a => 'a list => bool" where
"inList(a,[]) = False " |
"inList(a,x#xs) = (if (a=x) then True else inList(a,xs))"

definition inE :: "exp => typeid => string => bool" where
"inE == %e. %t. %s. inList((t,s),varE(e))"

definition inF :: "fform => typeid => string => bool" where
"inF == %f. %t. %s. inList((t,s),varF(f))"

definition inP :: "proc => typeid => string => bool" where
"inP == %p. %t. %s. inList((t,s),varP(p))"

end