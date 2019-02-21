section {* Abstract syntax for Logic. *}

theory LSyntax 
  imports  Main HOL.Real
begin

(*Expressions of HCSP language.*)
datatype exp = RVar string   ("RVar _" 75 )
             | SVar string   ("SVar _" 75)
             | BVar string   ("BVar _" 75)
             | List "exp list"   ("List _" 75)
             | Real real     ("Real _" 75)
             | String string ("String _" 75)
             | Bool bool     ("Bool _" 75)
             | Add exp exp   (infixr "[+]" 70)
             | Sub exp exp   (infixl  "[-]" 70)
             | Mul exp exp   (infixr "[*]" 71)
             | Div exp exp   (infixr "[**]" 71)

(*Logic formulas.*)
datatype fform = WTrue | WFalse 
               | WEq exp exp        (infixl "[=]" 50)
               | Less exp exp       (infixl "[<]" 50)
               | Great exp exp      (infixl "[>]" 50)
               | WNot fform          ("[~] _" [40] 40)
               | WConj fform fform    (infixr "[&]" 35)
               | WDisj fform fform     (infixr "[|]" 30)
               | WImp fform fform      (infixr "[-->]" 30)
               | WIff fform fform      (infixr "[<->]" 25)
               | WAll string fform      ("WALL _ _ " 10)
               | WEx  string fform      ("WEX _ _" 10) 

datatype flow = Flow string string ("(%_,_%)" 100)
consts exeFlow :: "flow \<Rightarrow>fform \<Rightarrow> fform \<Rightarrow> fform"

definition
equal_less  (infixl "[<=]" 50) where
"x [<=] y == (x [<] y) [|] (x [=] y)"
definition
equal_greater  (infixl "[>=]" 50) where
"x [>=] y == (x [>] y) [|] (x [=] y)"

(*Define the closure of a formula*)
fun NotForm :: "fform => fform"
    and close :: "fform => fform" where
"NotForm (WTrue) = (WFalse)" |
"NotForm (WFalse) = (WTrue)" |
"NotForm (WEq e1 e2) = (WTrue)" |
"NotForm (Less e1 e2) = ((Great e1 e2) [|] (WEq e1 e2))" |
"NotForm (Great e1 e2) = ((Less e1 e2) [|] (WEq e1 e2))" |
"NotForm (WNot f1) = close(f1)" |
"NotForm (WConj f1 f2) = (NotForm(f1) [|] NotForm(f2))" |
"NotForm (WDisj f1 f2) = (NotForm(f1) [&] NotForm(f2))" |
"NotForm (WImp f1 f2) = ((close(f1)) [&] NotForm(f2))" |
"NotForm (WIff f1 f2) = (((close(f1)) [&] NotForm(f2)) [|] (close( f2) [&] NotForm(f1)))" |
"NotForm (WAll x f1) = (WEx x (NotForm(f1)))" |
"NotForm (WEx x f1) = (WAll x (NotForm(f1)))" |
"close (WTrue) = (WTrue)" |
"close (WFalse) = (WFalse)" |
"close (WEq e1 e2) = (WEq e1 e2)" |
"close (Less e1 e2) = ((Less e1 e2) [|] (WEq e1 e2))" |
"close (Great e1 e2) = ((Great e1 e2) [|] (WEq e1 e2))" |
"close (WNot f1) = NotForm(f1)" |
"close (WConj f1 f2) = (close(f1) [&] close(f2))" |
"close (WDisj f1 f2) = (close(f1) [|] close(f2))" |
"close (WImp f1 f2) = ((NotForm(f1)) [|] close(f2))" |
"close (WIff f1 f2) = (((NotForm(f1)) [|] close(f2)) [&] (close(f2) [|] close(f1)))" |
"close (WAll x f1) = (WAll x (close(f1)))" |
"close (WEx x f1) = (WEx x (close(f1)))"

(* Transfform our formulea to the formulea in isabelle for proving arith props*)
consts rvar :: "string => real"
consts svar :: "string => string"
consts bvar :: "string => bool"

datatype val = RR real | SS string  | LL "exp list" | BB bool | Err

(*Transformation of expressions*)
primrec expTrans :: "exp => val" where
"expTrans (RVar s) = RR (rvar s)" |
"expTrans (SVar s) = SS (svar s)" |
"expTrans (BVar s) = BB (bvar s)" |
"expTrans (List ls) = LL ls" |
"expTrans (Real r) = RR r" |
"expTrans (String s) = SS s" |
"expTrans (Bool b) = BB b" |
"expTrans (Add e1 e2) = (case (expTrans e1, expTrans e2) of
                            (RR r1,RR r2) => RR (r1+r2) | 
                            (_,_) => Err)" |
"expTrans (Sub e1 e2) = (case (expTrans e1, expTrans e2) of
                            (RR r1,RR r2) => RR (r1-r2) | 
                            (_,_) => Err)" |
"expTrans (Mul e1 e2) = (case (expTrans e1, expTrans e2) of
                            (RR r1,RR r2) => RR (r1*r2) | 
                            (_,_) => Err)" |
"expTrans (Div e1 e2) = (case (expTrans e1, expTrans e2) of
                            (RR r1,RR r2) => RR (r1/r2) | 
                            (_,_) => Err)"

(*Transformation of formulas*)
primrec formT :: "fform => bool" where
"formT (WTrue) = True" |
"formT (WFalse) = False" |
"formT (e1 [=] e2) = (case (expTrans e1, expTrans e2) of
                            (RR r1,RR r2) => ((r1::real) = r2) |
                            (SS r1,SS r2) => ((r1::string) = r2) | 
                            (BB r1,BB r2) => ((r1::bool) = r2) | 
                            (_,_) => False)" |
"formT (e1 [<] e2) = (case (expTrans e1, expTrans e2) of
                            (RR r1,RR r2) => ((r1::real) < r2) | 
                            (_,_) => False)" |
"formT (e1 [>] e2) = (case (expTrans e1, expTrans e2) of
                            (RR r1,RR r2) => (r1::real) > r2 | 
                            (_,_) => False)" |
"formT ([~] fform1) = (~ (formT fform1))" |
"formT (fform1 [&] fform2) = ((formT fform1) & (formT fform2))" |
"formT (fform1 [|] fform2) = ((formT fform1) | (formT fform2))" |
"formT (fform1 [-->] fform2) = ((formT fform1) --> (formT fform2))" |
"formT (fform1 [<->] fform2) = ((formT fform1) \<longleftrightarrow> (formT fform2))" |
"formT (WALL x fform1)= (let (r::real) = rvar(x) in (ALL r::real. (formT fform1)))" |
"formT (WEX x fform1)= (let (r::real) = rvar(x) in (EX r::real. (formT fform1)))"

end

