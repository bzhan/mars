section {*The sequent calculus for interval logic*}

theory ILSequent
imports DLK0
begin


consts
(*Chop modality and interval variable *)
  chop            :: "[fform, fform] => fform"              (infixr "[^]" 38)
  l               :: exp

(*the special variable l is real*)
axiomatization where
ltrans : "l = RVar (''l'')" and
l_pos : "|- l[>=]Real 0"

datatype non = FForm  fform  ("F _")
              |EExp  exp    ("E _")


section {*Definitions and rules for rigid and chop-free.*}
consts
  RI            :: "non  => prop"     ("(RI _)")
  CF           :: "fform => prop"     ("(CF _)")

(* Rules for RI and CF , the rules for all constructs are given, not just finalconsts.*)
axiomatization where
(* Rigid RI *)
RIfalse:           "RI F (WFalse::fform)" and
RIchopI:         "[| RI F (P::fform); RI F (Q::fform) |]  ==> RI F (P[^]Q)" and
RIchopE1:     "RI F (P[^]Q)  ==> RI F (P::fform)" and
RIchopE2:     "RI F (P[^]Q)  ==> RI F (Q::fform)" and
RIconjI:          "[| RI F (P); RI F (Q) |] ==> RI F (P [&] Q)" and
RIconjE1:      "RI F (P [&] Q)  ==> RI F (P)" and
RIconjE2:      "RI F (P [&] Q)  ==> RI F (Q)" and
RIdisjI:          "[| RI F (P); RI F (Q) |] ==> RI F (P [|] Q)" and
RIdisjE1:      "RI F (P [|] Q) ==> RI F (P)" and
RIdisjE2:      "RI F (P [|] Q) ==> RI F (Q)" and
RIimpI:         "[| RI F (P::fform); RI F (Q::fform) |]  ==> RI F (P [-->] Q::fform)" and
RIimpE1:      "RI F (P[-->]Q)  ==> RI F (P)" and
RIimpE2:      "RI F (P[-->]Q)  ==> RI F (Q)" and
RInotI:         "RI F (P) ==>  RI F ([~]P)" and
RInotE:        "RI F ([~]P)  ==>  RI F (P)" 

axiomatization where
(* Quantifiers *)
RIallI:            "[| RI F (P) |] ==> RI F (WALL x P)" and
RIallE:           "[| RI F (P) |] ==> RI F (WEX x P)" and
RIequI:          "[| RI E s; RI E t |] ==> RI F (s [=] t)" and
RIadd:            "[|RI E s; RI E t|] ==> RI E (s[+]t)" and
RImult:            "[|RI E s; RI E t|] ==> RI E (s[*]t)" and
RIdev:            "[|RI E s; RI E t|] ==> RI E (s[**]t)" and
Rl : "RI E l \<Longrightarrow> False"

axiomatization where
(* Chop free CF *)
CFfalse:         "CF WFalse" and
CFimpI:         "[| CF P; CF Q |] ==> (CF P [-->] Q)"   and
CFimpE1:      "CF (P [-->] Q) ==> CF P" and
CFimpE2:      "CF (P [-->] Q) ==> CF Q" and
CFequ:           "CF (s [=] t)" and
CFconjI:        "[| CF P; CF Q |] ==> CF P[&]Q" and
CFconjE1:     "CF P[&]Q ==> CF P" and
CFconjE2:     "CF P[&]Q ==> CF Q" and
CFdisjI:        "[| CF P; CF Q |] ==> CF P[|]Q" and
CFdisjE1:     "CF P[|]Q ==> CF P" and
CFdisjE2:     "CF P[|]Q ==> CF Q" and
CFnotI:         "CF P ==> CF ([~]P)" and
CFnotE:        "CF ([~]P) ==> CF P" and
CFchop: "CF P [^] Q \<Longrightarrow> False"

axiomatization where
(* Quantifiers *)
CFexI:            "CF P(s) ==> CF (WEX x P(x))" and
CFexE:           "CF (WEX x P(x)) ==> CF P(s)" and
CFallI:            "CF P(s) ==> CF (WALL x P(x))" and
CFallE:           "CF (WALL x P(x))  ==> CF P(s)" 

section {*Sequent rules for chop modality [Zhou and Hansen modified].*}
axiomatization where
LL2:                "[| RI E s; RI E t; $H, l [=] s [+] t |- $E1 |] ==> $H, (l [=] s) [^] (l [=] t) |- $E1" and
RL2:                "[| RI E s; RI E t; $H |- l [=] s [+] t, $E1 |] ==> $H |- (l [=] s) [^] (l [=] t), $E1" and

LL3:                " $H |- P, $E1 ==> $H  |- P [^] (l [=] (Real 0)), $E1" and
RL3:                " $H, P [^] (l [=] Real 0) |- $E1 ==> $H, P |- $E1" and
LL4:                " $H, P |- $E1 ==> $H, P [^] (l [=] Real 0) |- $E1" and
RL4:                " $H |- P, $E1 ==> $H  |- P [^] (l [=] (Real 0)), $E1" and
LL3a:                " $H, P |- $E1 ==> $H, (l [=] (Real 0)) [^] P |- $E1" and
RL3a:                " $H |- P, $E1 ==> $H  |- (l [=] (Real 0)) [^] P, $E1" and
LL1:                  "[| RI E s; $H |- (l [=] s) [^] P, $E1 |] ==> $H, (l [=] s) [^] ([~]P) |- $E1" and
RL1:                  "[| RI E s; $H , (l [=] s) [^] P |- $E1 |] ==> $H |- (l [=] s) [^] ([~]P), $E1" and
LL1a:                "[| RI E s; $H |- P [^] (l [=] s) , $E1 |] ==> $H, ([~]P) [^] (l [=] s) |- $E1" and
RL1a:                "[| RI E s; $H , P [^] (l [=] s)  |- $E1 |] ==> $H |- ([~]P) [^] (l [=] s), $E1" and 

LT1:                  "[| $H, P [^] Q |- $E1;  $H, R [^] Q |- $E1|] ==> $H, (P [|] R) [^] Q |- $E1" and
RT1:                  "$H |- P [^] Q, R [^] Q, $E1 ==> $H |- (P [|] R) [^] Q, $E1" and
LT1a:                "[| $H, P [^] Q |- $E1;  $H, P [^] R |- $E1|] ==> $H, P [^] (Q [|] R) |- $E1" and
RT1a:                "$H |- P [^] Q, P [^] R, $E1 ==> $H |- P [^] (Q [|] R), $E1" and

LA2:                 "$H, P [^] (Q [^] R) |- $E1 ==> $H, (P [^] Q) [^] R |- $E1" and
RA2:                 "$H |- P [^] (Q [^] R), $E1 ==> $H |- (P [^] Q) [^] R, $E1" 

axiomatization where
LB1:                  "(!!x. $H, (P(x) [^] Q) |- $E1) ==> $H, ((WEX x P(x)) [^] Q) |- $E1" and
RB1:                 "[|RI s; CF P(x); $H |- P(x) [^] Q, $E1|] ==> $H |- (WEX x P(x)) [^] Q, $E1" 

axiomatization where
LBr:                  "(!!x. $H, (P [^] Q(x)) |- $E1) ==> $H, (P [^] (WEX x Q(x))) |- $E1" and
RBr:                 "[|RI s; CF Q(x); $H |- P [^] Q(x), $E1|] ==> $H |- P [^] (WEX x Q(x)), $E1" 

(*Zouliang: add for conjunction*)
axiomatization where
LC1:                  "$H, P [^] Q, $E1 |- $F1 ==> $H, (P [&] R) [^] Q, $E1 |- $F1" and
LC2:                  "$H, R [^] Q, $E1 |- $F1 ==> $H, (P [&] R) [^] Q, $E1 |- $F1" and
LC3:                  "$H, Q [^] P, $E1 |- $F1 ==> $H, Q [^] (P [&] R), $E1 |- $F1" and
LC4:                  "$H, Q [^] R, $E1 |- $F1 ==> $H, Q [^] (P [&] R), $E1 |- $F1" and

TT:                    "WTrue [^] WTrue == WTrue" and
LT:                    "l[<](Real m) [^] WTrue == WTrue" and
LTa:                    "l[=](Real m) [^] WTrue == WTrue" and
CML:                   "[|$H, R [^] Q, $E1 |- $F1; P|-R|] ==> $H, P [^] Q, $E1 |- $F1" and
CMR:                   "[|$H, P [^] R, $E1 |- $F1; Q|-R|] ==> $H, P [^] Q, $E1 |- $F1"
end
