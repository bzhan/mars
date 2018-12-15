theory op
imports Assertion
(*This file defines the operation semantics of HCSP.*)

begin

consts evalP :: "proc => cstate => now => proc * cstate * now"
consts evalPP :: "proc => cstate => cstate => now => proc * cstate * cstate * now * now"

(*We use `skip' to denote empty statement, so the opration semantics for skip is not nessary.*)

(*operation semantics for stop*)
axiomatization where
 stop :  "!!d'. evalP (Stop, f, d) = (Stop, f, d+d')"

(*operation semantics for *)
axiomatization where
 assignR :  "evalP (((RVar (x)) := e),f,d) =
   (Skip, (%t. if t = d then f(t)@[%y i. if y=x & i=R then evalE(last(f(t)),e) else last(f(t))(y,i)] else f(t)), d)" and
 assignS :  "evalP (((SVar (x)) := e),f,d) =
   (Skip, (%t. if t = d then f(t)@[%y i. if y=x & i=S then evalE(last(f(t)),e) else last(f(t))(y,i)] else f(t)), d)" and
 assignB :  "evalP (((BVar (x)) := e),f,d) =
   (Skip, (%t. if t = d then f(t)@[%y i. if y=x & i=B then evalE(last(f(t)),e) else last(f(t))(y,i)] else f(t)), d)"

(*disj p F represents that p does not contain variable of F.*)
consts disj :: "fform => fform => bool"

(*Zouliang: revise the first rule continueY same as continue.*)
(*operation semantics for continue*)
axiomatization where
 continue : "(ievalF(f',high(F[&]b),d,d')
            & ievalF(f', Rg, d, d')
            & evalF(last(f'(d')), ([~]b))
            & (ALL p. disj(p,F) --> ievalF(f',high p,d,d') & evalF(last(f'(d')),p)) )
            == evalP ((<F&&b> : Rg), f, d) = (Skip, f', d')"

(*operation semantics for sequential*)
axiomatization where
 sequence :  "(evalP (P, f, d) = (Skip, f', d') & evalP (Q, f', d') = (Skip, F, D))
                == (evalP ((P;mid;Q),f,d) = (Skip,F,D))"

(*operation semantics for condition*)
axiomatization where
 conditionT :  "evalF(last(f(d)), be)
                   ==> (evalP(P, f, d) = (Skip,f',d') == evalP ((IF be P), f, d) = (Skip,f',d'))" and
 conditionF :  "(~ evalF(last(f(d)), be))
                   ==> (evalP ((IF be P), f, d) = (Skip,f,d))"

(*operation semantics for nondeterminitic*)
axiomatization where
 nondeterR :  "(ALL v. evalF(last(f(d)), ((%x. b)(v))) & 
                 (evalP (P, f, d) = (Skip, f', d')))
                  == evalP ((NON R x : b P),f,d) = (Skip,f',d')" and
 nondeterS :  "(ALL v. evalF(last(f(d)), ((%x. b)(v))) &
                 (evalP (P, f, d) = (Skip, f', d')))
                  == evalP ((NON S x : b P),f,d) = (Skip,f',d')" and
 nondeterB :  "(ALL v. evalF(last(f(d)), ((%x. b)(v))) &
                 (evalP (P, f, d) = (Skip, f', d')))
                  == evalP ((NON B x : b P),f,d) = (Skip,f',d')"

(*operation semantics for communication*)
(*It is valid only when there are no communications occurring in P and Q.*)
axiomatization where
 communicationR :  "evalPP(Px||Py,f,g,d) = (Skip,F,G,Da,Db)
                == evalPP(((Px;m;ch!!e) || (Py;M;ch??(RVar(x)))),f,g,d) = (Skip,
                    (if Da<Db then (%t. if t>Da & t<=Db then [last(F(Da))] else F(t)) else F),
                    (if Da>Db then
                      (%t. if t=Da then last(G(Db))#[%y i. if y=x & i=R then evalE(last(G(Db)),e) 
                                                     else last(G(Db))(y,i)]
                           else (if t<Da & t>Db then [last(G(Db))] else G(t)))
                    else
                      (%t. if t=Db then G(Db)@[%y i. if y=x & i=R then evalE(last(G(Db)),e) 
                                                     else last(G(Db))(y,i)] 
                           else G(t)))
                    ,if Da>Db then Da else Db,if Da>Db then Da else Db)" and
 communicationS :  "evalPP(Px||Py,f,g,d) = (Skip,F,G,Da,Db)
                == evalPP(((Px;m;ch!!e) || (Py;M;ch??(SVar(x)))),f,g,d) = (Skip,
                    (if Da<Db then (%t. if t>Da & t<=Db then [last(F(Da))] else F(t)) else F),
                    (if Da>Db then
                      (%t. if t=Da then last(G(Db))#[%y i. if y=x & i=S then evalE(last(G(Db)),e) 
                                                     else last(G(Db))(y,i)]
                           else (if t<Da & t>Db then [last(G(Db))] else G(t)))
                    else
                      (%t. if t=Db then G(Db)@[%y i. if y=x & i=S then evalE(last(G(Db)),e) 
                                                     else last(G(Db))(y,i)] 
                           else G(t)))
                    ,if Da>Db then Da else Db,if Da>Db then Da else Db)" and
 communicationB :  "evalPP(Px||Py,f,g,d) = (Skip,F,G,Da,Db)
                == evalPP(((Px;m;ch!!e) || (Py;M;ch??(BVar(x)))),f,g,d) = (Skip,
                    (if Da<Db then (%t. if t>Da & t<=Db then [last(F(Da))] else F(t)) else F),
                    (if Da>Db then
                      (%t. if t=Da then last(G(Db))#[%y i. if y=x & i=B then evalE(last(G(Db)),e) 
                                                     else last(G(Db))(y,i)]
                           else (if t<Da & t>Db then [last(G(Db))] else G(t)))
                    else
                      (%t. if t=Db then G(Db)@[%y i. if y=x & i=B then evalE(last(G(Db)),e) 
                                                     else last(G(Db))(y,i)] 
                           else G(t)))
                    ,if Da>Db then Da else Db,if Da>Db then Da else Db)"

(*operation semantics for parallel*)
(*It is valid only when there are no communications occurring in P2 and Q2.*)
axiomatization where
parallelN1 : "evalP (P,f,d) = (Skip,f',d') & evalP (Q,g,d) = (Skip,g',d'')
                == evalPP((P||Q),f,g,d) = (Skip,f',g',d',d'')" and
parallelN2 : "evalPP ((Px||Py),f,g,d) = (Skip,f'',g'',d'',D'') & evalP(Qx,f'',d'') = (Skip,f',d') &
                evalP (Qy,g'',D'') = (Skip,g',D') & 
               (ievalF(f'',H,d,d'') --> ievalF(f',H,d,d'')) &
               (ievalF(g'',G,d,D'') --> ievalF(g',G,d,D''))
                == evalPP(((Px;m;Qx)||(Py;M;Qy)),f,g,d) = 
                      (Skip,f',g',d',D')"

(*operation semantics for repetition*)
axiomatization where
 repetition : "(evalP(P*, f, d) = (Skip, f', d'))
                 == EX n::nat. ALL k::nat. (f=F(0) & d=D(0) & f'=F(n) & d'=D(n) &
                    (k<n --> evalP(P,F(k),D(k)) = (Skip, F(k+1), D(k+1)) &
                             (ievalF(F(k),H,D(0),D(k)) --> ievalF(F(k+1),H,D(0),D(k)))))"

end