
section {* Abstract syntax for Hybrid CSP. *}

theory HCSP_Com 
  imports  Main
"DCSequents/DCSequent"
begin



type_synonym cname = string
type_synonym time = real
type_synonym bexp = fform
type_synonym Inv = fform
type_synonym Rg = fform
type_synonym mid = "fform * fform"

datatype typeid = R | S | B

datatype proc
= "Skip"
| "Stop"
| Ass "exp" "exp"          ("_ := _" [99, 95] 94)   
| Send "cname" "exp"         ("_!!_" [110,108] 100)      
| Receive "cname" "exp"    ("_??_" [110,108] 100) 
| Seq "proc" "mid" " proc"                   ("_; _ ; _"        [91,91,90 ] 90)
| Cond "bexp" "proc"                 ("IF _ _"   [95,94]93)
| Nondeter "typeid" "string" "bexp" "proc"                 ("NON _ _ : _ _"   [95,94]93)
| Pref   "proc" "proc"                  ("_\<rightarrow>_"   [95,94]93)           
| join "proc" "proc"                   (infixr "[[" 90)
| meet "proc" "proc"                  ("_<<_" [90,90] 90)
| Par    "proc" "proc"                  (infixr "||" 89)
| Rep    "proc"                               ("_*"[91] 90)
| RepA    "proc"                              ("_***"[91] 90)
| RepN    "proc" "nat"                               ("_**_"[91,92] 90)
| Cont  "Inv" "bexp" "Rg"                ("<_&&_> : _" [95,96]94)
| Cont2  "flow" "Inv" "bexp" "Rg"                ("<_&&_&&_> : _" [95,95,96]94)
| TimeOut "proc" "time" "proc"    ("_|>_ _" [95,96,94]94)
| Interp   "proc" "proc" ("_[[>_"[95,94]94)
| empty "exp" ("empty _" [94] 94)
| addL "exp" "exp" ("addL _ _" [94,94] 94)
| delL "exp" ("delL _" [94] 94)

definition isEmpty :: "exp => fform" where
"isEmpty(e1) == (case e1 of
        (List ls) => (case ls of [] => WTrue | _ => WFalse) |
        _ => WFalse)"

definition readL :: "exp => exp" where
"readL(e1) == (case e1 of
      (List ls) => hd(ls) |
      _ => (Real 0))"


type_synonym pair = "exp * exp"


primrec map :: "pair list => exp => exp" where
"map ([]) (a) = a" |
"map (x#xs) (a) = (if (fst (x) = a) then (snd (x)) else (map (xs) (a)))"


lemma "map ([(RVar ''x'', Real 2), (RVar ''y'', RVar z)],  RVar ''x'') = (Real 2)"
apply (induct, auto)
done

lemma fact1 : "map ([(RVar ''x'', Real 2), (RVar ''y'', RVar z)]) (RVar ''z'') = RVar ''z''"
apply (induct, auto)
done

(*Expression substitution: "map" records the substitution mapping.*)
primrec substE :: "pair list => exp => exp" where
"substE (mp, (RVar x)) = map (mp, (RVar x))"  |
"substE (mp, (SVar x)) = map (mp, (SVar x))"  |
"substE (mp, (BVar x)) = map (mp, (BVar x))"  |
"substE (mp, (List x)) = List x"  |
"substE (mp, (Real m)) = map (mp, (Real m))"  |
"substE (mp, (Bool b)) = map (mp, (Bool b))"  |
"substE (mp, (String s)) = map (mp, (String s))"  |
"substE (mp, (e1 [+] e2)) = substE (mp, e1) [+] substE (mp, e2)"  |
"substE (mp, (e1 [-] e2)) = substE (mp, e1) [-] substE (mp, e2)"|
"substE (mp, (e1 [*] e2)) = substE (mp, e1) [*] substE (mp, e2)"|
"substE (mp, (e1 [**] e2)) = substE (mp, e1) [**] substE (mp, e2)"

lemma "(% x. x [+] x = RVar ''z'' [+] RVar ''z'') (RVar ''z'')"
apply auto
done

lemma "substE ([(RVar ''x'', Real 1), (RVar ''y'', RVar ''z'')], (RVar ''y'' [+] RVar ''z'')) 
        = RVar ''z'' [+] RVar ''z''"
apply (induct, auto)
done 


(*Tip: for theory built on Pure, application is written by f(x) rather than f x as usual. *)

primrec lVarE :: "pair list => string => pair list" where
"lVarE ([],s) = []" |
"lVarE (x#xs,s) = (if (fst (x) = (RVar s)) then xs else x#lVarE(xs, s))"

primrec inExp :: "string => exp => bool" where
"inExp (s, (RVar x)) = (s=x)"  |
"inExp (s, (SVar x)) = (s=x)"  |
"inExp (s, (BVar x)) = (s=x)"  |
(*"inExp (s, (List x)) = (s=x)"  |*)
"inExp (s, (Real m)) = (False)"  |
"inExp (s, (Bool b)) = (False)"  |
"inExp (s, (String r)) = (False)"  |
"inExp (s, (e1 [+] e2)) = (inExp (s, e1) | inExp (s, e2))"  |
"inExp (s, (e1 [-] e2)) = (inExp (s, e1) | inExp (s, e2))"|
"inExp (s, (e1 [*] e2)) = (inExp (s, e1) | inExp (s, e2))"

primrec inPairL :: "pair list => string => bool" where
"inPairL ([],s) = False" |
"inPairL (x#xs,s) = (if (inExp (s, fst (x))) then True else inPairL(xs, s))"

primrec inPairR :: "pair list => string => bool" where
"inPairR ([],s) = False" |
"inPairR (x#xs,s) = (if (inExp (s, snd (x))) then True else inPairR(xs, s))"

(*Check if the quantifiers of a formula occur in mp*)
primrec inPairForm :: "pair list => fform => bool" where
 "inPairForm (mp) (WTrue) = False" |
 "inPairForm (mp) (WFalse) = False" |
 "inPairForm (mp) (e1 [=] e2) =False" |
 "inPairForm (mp) (e1 [<] e2) = False" |
 "inPairForm (mp) (e1 [>] e2) =False" |
 "inPairForm (mp) ([~]p) = (inPairForm (mp) (p))" |
 "inPairForm (mp) (p [&] q) = ((inPairForm (mp) (p)) | (inPairForm (mp) (q)))" |
 "inPairForm (mp) (p [|] q) = ((inPairForm (mp) (p)) | (inPairForm (mp) (q)))" |
 "inPairForm (mp) (p [-->] q) = ((inPairForm (mp) (p)) | (inPairForm (mp) (q)))" |
 "inPairForm (mp) (p [<->] q) = ((inPairForm (mp) (p)) | (inPairForm (mp) (q)))" |
 "inPairForm (mp) (WALL i p) = (inPairL (mp, i) | inPairR (mp, i) | inPairForm (mp)(p))" |
 "inPairForm (mp) (WEX i p) = (inPairL (mp, i) | inPairR (mp, i) | inPairForm (mp)(p))"

(*Formula sustitution.*)
primrec substF :: "pair list => fform => fform" where
 "substF (mp) (WTrue) = WTrue" |
 "substF (mp) (WFalse) = WFalse" |
 "substF (mp) (e1 [=] e2) = ((substE (mp, e1)) [=] (substE (mp, e2)))" |
 "substF (mp) (e1 [<] e2) = ((substE (mp, e1)) [<] (substE (mp, e2)))" |
 "substF (mp) (e1 [>] e2) = (substE (mp, e1) [>] substE (mp, e2))" |
 "substF (mp) ([~]p) = ([~](substF (mp) (p)))" |
 "substF (mp) (p [&] q) = ((substF (mp) (p)) [&] (substF (mp) (q)))" |
 "substF (mp) (p [|] q) = ((substF (mp) (p)) [|] (substF (mp) (q)))" |
 "substF (mp) (p [-->] q) = ((substF (mp) (p)) [-->] (substF (mp) (q)))" |
 "substF (mp) (p [<->] q) = ((substF (mp) (p)) [<->] (substF (mp) (q)))" |
 "substF (mp) (WALL i p) = (if ((~inPairL (mp, i)) & (~inPairR (mp, i))) then (WALL i (substF (mp)(p))) 
                           else WFalse)" |
 "substF (mp) (WEX i p) = (if ((~inPairL (mp, i)) & (~inPairR (mp, i))) then (WEX i (substF (mp)(p))) 
                           else WFalse)"

lemma allEX : "substF([(RVar ''x'', RVar ''m''), (RVar ''y'', RVar ''z'')], 
                 ((RVar ''x'')[=]Real 2) [&] (WALL ''w'' ((RVar ''w'') [>] (RVar ''z''))))
             = (((RVar ''m'')[=]Real 2) [&] (WALL ''w'' ((RVar ''w'') [>] (RVar ''z''))))"
apply auto
done


lemma fact : "substF ([(RVar ''x'', Real 2), (RVar ''y'', RVar ''z'')]) (RVar ''x'' [>] Real 1) = (Real 2 [>] Real 1)"
apply (induct, auto)
done


end




