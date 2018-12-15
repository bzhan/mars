theory DCSequent
imports ILSequent
begin


type_synonym s = fform

(*State durations*)
consts
dur          :: "s => exp"

(*Point formula: s holds in the considered point interval. *)
consts
pf              ::  "s => fform"    
consts
(* Everywhere: s holds everywhere in the considered interval of positive range. *)
high            ::  "s => fform"              ("high _")
(*Almost everywhere: s holds almost everywhere in the considered positive interval.*)
almost          ::  "s=>fform"                ("almost _")

axiomatization where
high_def    : " high S == ((dur (S) [=] l) [&] [~](l [=] Real 0) [&] [~] ((l[>]Real 0) [^] pf([~]S) [^] (l[>]Real 0)))" and
almost_def    : "almost S == ((dur (S) [=] l) [&] [~](l [=] Real 0))"

(* Axioms for DC for reasoning about state durations.*)
axiomatization where
DA1              : "|-dur (WFalse) [=] Real 0" and
DA2              : "|- dur (WTrue) [=] l" and
DA3a             : " (l [<=] Real 0) |- (dur (S) [<=] Real 0)" and
DA3b             : " (Real 0 [<=]  l) |- (Real 0 [<=] dur (S)) " and
DA4              : " |- dur (S1) [+] dur (S2) [=] dur (S1 [|] S2) [+] dur (S1 [&] S2)"  and
DA5              : " [|RI E s; RI E t|] ==> |- (dur (S) [=] s [^]  dur (S) [=] t) [<->] dur (S) [=] s [+] t" and
DA6              : "|- s1 [<->] s2 ==> |- dur (s1) [=] dur (s2)"

(*Part of theorems given in [Zhou&Hansen03] for DC.*)
axiomatization where
DC11     : "$H, (high WFalse) |- $H, WFalse" and
DC12    : "$H |- $E1, (high ([~]s)) ==> $H |- $E1, (dur (s) [=] (Real 0))" and
DC18     : "$H, s |- t ==> $H, (high s) |- (high t)" and
DCR3    : "$H |- (high S) [^] (high S),$E1 ==> $H |- (high S), $E1" and
DCL3    : "$H, (high S)|-$E1 ==> $H,(high S)[^](high S) |- $E1" and
DCR4    : "$H |- (high S),$E1 ==> $H |- (high S)[^] (high S),$E1" and
DCL4    : "$H, (high S)[^](high S) |-$E1 ==> $H,(high S) |- $E1" and

DCM     : "[|$H,(high Q),$F1 |- $E1; $H,P,$F1 |- Q|] ==> $H,(high P),$F1 |- $E1"
end
