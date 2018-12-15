theory Assertion imports
"State"

begin

(*evalF defines the semantics of assertions written in first-order logic*)
primrec evalF :: "state => fform => bool" where
"evalF (f,WTrue) = (True)" |
"evalF (f,WFalse) = (False)" |
"evalF (f,e1 [=] e2) = (case (evalE (f,e1), evalE (f,e2)) of
                            (RR (r1),RR (r2)) => ((r1::real) = r2) |
                            (SS (r1),SS (r2)) => ((r1::string) = r2) | 
                            (BB (r1),BB (r2)) => ((r1::bool) = r2) | 
                            (_,_) => False)" |
"evalF (f,e1 [<] e2) = (case (evalE (f,e1), evalE (f,e2)) of
                            (RR (r1),RR (r2)) => ((r1::real) < r2) | 
                            (_,_) => False)" |
"evalF (f,e1 [>] e2) = (case (evalE (f,e1), evalE (f,e2)) of
                            (RR (r1),RR (r2)) => (r1::real) > r2 | 
                            (_,_) => False)" |
"evalF (f,[~] form1) = (~ (evalF (f,form1)))" |
"evalF (f,form1 [&] form2) = ((evalF (f,form1)) & (evalF (f,form2)))" |
"evalF (f,form1 [|] form2) = ((evalF (f,form1)) | (evalF (f,form2)))" |
"evalF (f,form1 [-->] form2) = ((evalF (f,form1)) --> (evalF (f,form2)))" |
"evalF (f,form1 [<->] form2) = ((evalF (f,form1)) \<longleftrightarrow> (evalF (f,form2)))" |
"evalF (f,WALL x form1)= (ALL (v::real). (evalF((%a. %i. (if (a=x) then (RR (v)) else (f(a, i)))), form1)))" |
"evalF (f,WEX x form1)= (EX (v::real). evalF((%a. %i. (if (a=x) then (RR (v)) else f(a, i))), form1))"


definition evalFP :: "cstate => fform => now => bool" where
"evalFP(f,P,c) == ALL s. inList(s,f(c)) --> evalF(s,P)"

(*ievalF defines the semantics of assertions written in interval logic and duration calculus*)
consts ievalF :: "cstate => fform => now => now => bool"
axiomatization where
chop_eval: "ievalF (f, P[^]Q, c, d) =  (EX k s1 s2. s1@s2=f(k) & ievalF (%t. if t=k then s1 else f(t), P, c, k)
                                                  & ievalF (%t. if t=k then s2 else f(t), Q, k, d))" and
chop_sep: "ievalF (f, P, c, d) = (ALL k s1 s2. s1@s2=f(k) --> ievalF (%t. if t=k then s1 else f(t), P, c, k)
                                                  & ievalF (%t. if t=k then s2 else f(t), P, k, d))" and
pf_eval: "ievalF (f, pf (P), c, d) = (c=d & (EX s. inList(s, f(c))) & evalF (s, P))" and
high_eval: "ievalF (f, high P, c, d) = ((ALL (k::real). (c<k & k<d) --> evalFP (f, P, k)))" and
chop_interval: "(ALL t. (c=d --> f(c)=g(c)) & (c<=t & t<=d --> f(t)=g(t))) ==> ievalF(f,P,c,d)=ievalF(g,P,c,d)"

lemma chop_eval1: "(EX k. ievalF (f, P, c, k) & ievalF (f, Q, k, d)) ==> ievalF (f, P[^]Q, c, d)"
apply (simp add: chop_eval,auto)
apply (cut_tac x=k in exI,auto)
apply (cut_tac x="f(k)" in exI,auto)
apply (subgoal_tac "f = (%t. if t = k then f(k) else f(t))",auto)
apply (subgoal_tac "(ALL ka s1 s2. s1@s2=f(ka) --> ievalF (%t. if t=ka then s1 else f(t), Q, k, ka)
                                                  & ievalF (%t. if t=ka then s2 else f(t), Q, ka, d))")
apply (subgoal_tac "ievalF(%t. if t = k then f(k) else f(t), Q, k, k) &
               ievalF(%t. if t = k then [] else f(t), Q, k, d)")
apply blast
apply (erule allE)+
apply blast
apply (cut_tac f=f and P=Q and c=k and d=d in chop_sep,auto)
done

(*The following axioms define the evaluation of formulas of part of first-order interval logic.*)
axiomatization where
True_eval : "ievalF (f,WTrue, c, d) = (True)"  and
False_eval : "ievalF (f,WFalse,c,d) = (False)" and
L_eval : "ievalF (f, (l [=] Real L), c, d) = (d-c = L)" and 
(*Equal_eval : "ievalF (f,e1 [=] e2,c,d) = evalFP(f,e1 [=] e2,c)" and
Less_eval : "ievalF (f,e1 [<] e2,c,d) = evalFP(f,e1 [<] e2,c)" and
Great_eval: "ievalF (f,e1 [>] e2,c,d) = evalFP(f,e1 [>] e2,c)" and*)
Not_eval: "ievalF (f,[~] form1,c,d) = (~ (ievalF (f,form1,c,d)))" and
And_eval: "ievalF (f,form1 [&] form2,c,d) = ((ievalF (f,form1,c,d)) & (ievalF (f,form2,c,d)))" and
Or_eval: "ievalF (f,F [|] G,c,d) = ((ievalF (f,F,c,d)) | (ievalF (f,G,c,d)))" and
Imply_eval: "ievalF (f,form1 [-->] form2,c,d) = ((ievalF (f,form1,c,d)) --> (ievalF (f,form2,c,d)))" and
Equiv_eval: "ievalF (f,form1 [<->] form2,c,d) = ((ievalF (f,form1,c,d)) <-> (ievalF (f,form2,c,d)))" and
ALL_eval: "ievalF (f,WALL x form1,c,d)= (ALL (v::real). ievalF((%t. List.map(%s. %y i. if y=x & i=R then RR(v) else s(y,i),f(t))), form1, c, d))" and
EX_eval: "ievalF (f,WEX x form1,c,d)= (EX (v::real). ievalF((%t. List.map(%s. %y i. if y=x & i=R then RR(v) else s(y,i),f(t))), form1, c, d))"

(*The following axioms define the semantic meanings of closure of formulas.*)
axiomatization where
close_fact1: "ALL t. (t>=b & t<c --> evalF (f, p)) --> (evalF (f, close(p)))" and
close_fact2: "ALL t. (t>=b & t<c --> evalF (f, p)) --> (evalF (f, close([~]p)))" and
close_fact3: "evalF (s,p) ==> evalF (s,close(p))"

end
