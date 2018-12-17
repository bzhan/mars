section {* Abstract syntax for Hybrid CSP. *}

theory HHL
  imports  HCSP_Com
begin

consts 
spec :: "fform => proc => fform => fform => prop"   ("{_}_{_;_}" 80)
specP2 :: "fform => fform => proc => fform => fform => fform  => fform => prop"   ("{_, _}_{_, _ ; _, _}" 80)
specP3 :: "fform => fform => fform => proc => fform => fform => fform => fform => fform => fform => prop"("{_,_,_}_{_,_,_; _,_,_}" 80)
specP4 :: "fform => fform => fform => fform => proc => fform => fform => fform => fform => fform  => fform => fform  => fform => prop"   ("{_,_,_,_}_{_,_,_,_ ; _,_,_,_}" 80)
specP5 :: "fform => fform => fform => fform => fform => proc => fform => fform => fform => fform => fform => fform  => fform => fform  => fform => fform  => prop"   ("{_,_,_,_,_}_{_,_,_,_,_ ; _,_,_,_,_}" 80)
specP6 :: "fform => fform => fform => fform => fform => fform => proc => fform => fform => fform => fform => fform => fform => fform  => fform => fform => fform => fform => fform  => prop"   ("{_,_,_,_,_,_}_{_,_,_,_,_,_ ; _,_,_,_,_,_}" 80)


(*Skip rule*)
axiomatization where
Skip : "|- ((l [=] (Real 0)) [-->] G) ==> {p} Skip {p; G}" 


(*Assignment rule*)
axiomatization where
Assign  :" [| ~inPairForm ([(e, f)], q); |-(p [-->] (substF ([(e, f)]) (q)))
        [&]   ((l [=] (Real 0)) [-->] G)|] ==>
       {p} (e := f) {q; G}"


(*Example*)
lemma "{WTrue} (RVar ''x'') := (Real 2) {((RVar ''x'') [=] (Real 2)); (l [=] (Real 0))}"
apply (cut_tac p = "WTrue" and e = "(RVar ''x'')" and f = "(Real 2)" and 
                q = "((RVar ''x'') [=] (Real 2))" and G = "(l [=] (Real 0))" in Assign, auto)
apply (rule Trans,auto)
done


(*Continuous rule*)
axiomatization where
Continue : "|- (Init [-->] FF)
           [&] ((p [&] close(FF) [&] close([~]b)) [-->] q)
           [&] ((((l [=] Real 0) [|] (high (close(FF) [&] p [&] close(b)))) [&] Rg) [-->] G)
           ==> {Init [&] p} <FF&&b> : Rg {q; G}" and
ContinueT : "|- (Init[&]p [-->]FF[&]b)
           [&] ((p [&] close(FF) [&] close(b) [&] close([~]b)) [-->] q)
           [&] ((((l [=] Real 0) [|] (high (close(FF) [&] p [&] close(b)))) [&] Rg) [-->] G)
           ==> {Init [&] p} <FF&&(b)> : Rg {q; G}" and
ContinueF : "|- (p[-->][~]b) [&] (p[-->]q) [&] ((l[=](Real 0))[-->]G)
           ==> {p} <FF&&b> : Rg {q; G}"

(*Continuous rule 2*)
(*The pb in the domain refers to the discrete variables.*)
axiomatization where
Continue2 : "|- (Init [-->] FF)
           [&] ((p [&] pb [&] close(FF) [&] close([~]b)) [-->] q)
           [&] ((((l [=] Real 0) [|] (high (close(FF) [&] p [&] pb [&] close(b)))) [&] Rg) [-->] G)
[&] (exeFlow (D,b,F1) [-->]FF)
           ==> {Init [&] p} <D&&FF&&(pb[&]b)> : Rg {q; G}"  and
Continue2T : "|- (Init[&]p [-->] FF[&]b)
           [&] ((p [&] pb [&] close(FF) [&] close(b) [&] close([~]b)) [-->] q)
           [&] ((((l [=] Real 0) [|] (high (close(FF) [&] p [&] pb [&] close(b)))) [&] Rg) [-->] G)
[&](exeFlow (D,b,FF) [-->]FF)
           ==> {Init [&] p} <D&&FF&&(pb[&]b)> : Rg {q; G}" and
Continue2F : "|- (p[&] pb[-->][~]b) [&] (p[&] pb[-->]q) [&] ((l[=](Real 0))[-->]G)
           ==> {p} <D&&FF&&(pb[&]b)> : Rg {q; G}"

(*Sequential rule*)
axiomatization where
Sequence : "[| {p} P {m; H}; {m} Q {q; G} |] ==>
             {p} P; (m, H); Q {q; H [^] G}" 
(*The following rule for the case that the annotation M is discarded in the proof.*)
axiomatization where
Sequence1 : "[| {p} P {m; H}; {m} Q {q; G} |] ==>
             {p} P; M; Q {q; H [^] G}" 

(*Case rule*)
axiomatization where
Case : "[| {p [&] b} P {q; G}; {p [&] ([~]b)} P {q; G}|] 
             ==> {p} P {q; G}"
         

(*Conditional rule*)
axiomatization where
ConditionF : " [| |-(p [-->] [~] b); |- (p [-->] q); |- ((l [=] Real 0) [-->] G) |]
             ==> {p} IF b P {q; G}"
and
ConditionT :  "[| |-(p [-->] b); {p} P {q; G} |]
             ==> {p} IF b P {q; G}"
and
Condition : "[| {p [&] b} IF b P {q; G}; {p [&] ([~]b)} IF b P {q; G}|] 
             ==> {p} IF b P {q; G}"



(*Nondeterministic rule*)
axiomatization where
Nondeterministic :
"{p [&] b} P {q;G}
  ==> {p} NON i x : b P {q; G}"

(*Communication rule*)
(*H in the rule denotes the common interval range.*)
axiomatization where
Communication : "[| ~inPairForm ([(x, e)], ry);
                    {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                    |- (qx [-->] rx) [&] (qy [-->] (substF ([(x, e)]) (ry)));
                    |- ((Hx [^] (high (qx))) [-->] Gx) [&] ((Hy [^] (high (qy))) [-->] Gy);
                    |- ((((Hx [^] (high (qx))) [&] Hy) [|]((Hy [^] (high (qy))) [&] Hx)) [-->] H)
                 |]
              ==>   {px, py} ((Px; (qx, Hx); ch !! e) || (Py; (qy, Hy); ch ?? x)) {rx, ry; 
                    Gx [&] H, Gy [&] H}"


(*Communication interrupt rule*)
primrec contain :: "proc => proc => bool" where
"contain (Skip,p) = False" |
"contain (Stop,p) = False" |
"contain (x:=e,p) = False" |
"contain ((Ch!!e),p) = ((Ch!!e)=p)" |
"contain ((Ch??x),p) = ((Ch??x)=p)" |
"contain ((q;m;r),p) = False" |
"contain ((IF b q),p) = False" |
"contain ((NON i x : b q),p) = False" |
"contain ((q [[ r),p) = (if contain(q,p) then True else contain(r,p))" |
"contain ((q << r),p) = False" |
"contain ((q || r),p) = False" |
"contain ((q*),p) = False" |
"contain ((q**n),p) = False" |
"contain ((<F1 && b> : g),p) = False" |
"contain ((<D &&F1 && b> : g),p) = False" |
"contain ((q |> b r),p) = False" |
"contain ((q [[> r),p) = False"

(**)
axiomatization where
CommunicationI1 : "[| ~inPairForm ([(x, e)], ry);
                    |- Hy [-->] H;
                    |- rg [-->] H[^]WTrue;
                    {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                    |- Init [&] pre [<->] qx;
                    |- pre [&] Init [&] b [-->] F1;
                    |- (pre [&] close(F1) [&] close(b)) [-->] rx;
                    |- (qy [&] pre [&] close(F1) [&] close(b)) [-->] (substF ([(x, e)]) (ry));
                    |- (Hx [^] ((((l [=] Real 0) [|] (high (close(F1) [&] pre [&] close(b)))) [&] H)) [-->] Gx);
                    |- Hy [-->] Gy;
                    |- Hx [-->] Hxm;
                    |- Hy [-->] Hym;
                    contain(P,(ch !! e))
                 |]
              ==>   {px, py} (( Px; (qx, Hxm); (<F1 && b> :rg) [[> P) || (Py; (qy, Hym); ch ?? x))
                    {rx, ry; Gx, Gy}"
axiomatization where
CommunicationI2 : "[| ~inPairForm ([(x, e)], ry);
                    |- Hy [-->] H;
                    |- rg [-->] H[^]WTrue;
                    {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                    |- Init [&] pre [<->] qx;
                    |- pre [&] Init [&] b [-->] F1;
                    |- (qy [&] pre [&] close(F1) [&] close(b)) [-->] (substF ([(x, e)]) (rx));
                    |- qy [-->] ry;
                    |- Hx [^] ((((l [=] Real 0) [|] (high (close(F1) [&] pre [&] close(b)))) [&] H)) [-->] Gx;
                    |- Hy [-->] Gy;
                    |- Hx [-->] Hxm;
                    |- Hy [-->] Hym;
                    contain(P,(ch ?? x))
                 |]
              ==>   {px, py} (( Px; (qx, Hxm); (<F1 && b> :rg) [[> P) || (Py; (qy, Hym); ch !! e))
                    {rx, ry; Gx, Gy}"

(*Parallel rule*)
(*It is valid only when there are not communications occurring in P3 and P4.*)
axiomatization where
Parallel1: "[| {px, py} (Px || Py) {qx, qy; Hx, Hy}; {qx} Qx {rx; Gx}; {qy} Qy {ry; Gy} |]
           ==>  {px, py} ((Px; (qx, Hx); Qx) || (Py; (qy, Hy); Qy)) {rx, ry; Hx [^] Gx, Hy [^] Gy}"

(*It is valid only when there are no communications occurring in P1 and P2.*)
axiomatization where
Parallel2: "[| {px} Px {qx; Hx}; {py} Py {qy; Hy}|]
           ==> {px, py} (Px || Py) {qx, qy; Hx, Hy}"
(*It is valid in any case*)
axiomatization where
Parallel3: "[| {px, py} (Px || Py) {qx, qy; Hx[&](l[=](Real m)), Hy[&](l[=](Real m))};
               {qx, qy} (Qx || Qy) {rx, ry; Mx, My};
               |- (Hx[&](l[=](Real m))) [-->] HL;
               |- (Hy[&](l[=](Real m))) [-->] HR;
               |- ((Hx[&](l[=](Real m))) [^] Mx) [-->] Gx;
               |- ((Hy[&](l[=](Real m))) [^] My) [-->] Gy
            |]
           ==> {px, py} (Px;(qx,HL);Qx) || (Py;(qy,HR);Qy) {rx, ry; Gx, Gy}"

(*Repetition rule*)
axiomatization where
Rep : "[| {px} (Px) {px; Hx}; |- Hx [^] Hx [-->] Hx|]
           ==>  {px} (Px*) {px; Hx} "
axiomatization where
Repetition : "[| {px, py} (Px || Py) {px, py; Hx, Hy};
                 |- Hx [^] Hx [-->] Hx; |- Hy [^] Hy [-->] Hy|]
           ==>  {px, py} ((Px*) || (Py*)) {px, py; Hx, Hy} "

(*Consequence rule*)
axiomatization where
ConsequenceS : "[| {px} P {qx; Hx}; |- ((p [-->] px) [&] (qx [-->] q) [&] (Hx [-->] H))|]
            ==> {p} P {q; H}"
and
ConsequenceP : "[| {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                   |- ((p [-->] px) [&] (r [-->] py) [&] (qx [-->] q) [&] (qy [-->] s) 
                       [&] (Hx [-->] H) [&] (Hy [-->] G))|]
            ==> {p, r} (Px || Py) {q, s; H, G}"


end
