section {* Abstract syntax for Hybrid CSP. *}

theory HHL1
  imports  HCSP_Com
begin

consts 
spec :: "fform => proc => fform => fform => prop"   ("{_}_{_;_}" 80)
specP2 :: "fform => fform => proc => fform => fform => fform  => fform => prop"   ("{_, _}_{_, _ ; _, _}" 80)
specP3 :: "fform => fform => fform => proc => fform => fform => fform => fform => fform => fform => prop"("{_,_,_}_{_,_,_; _,_,_}" 80)
specP4 :: "fform => fform => fform => fform => proc => fform => fform => fform => fform => fform  => fform => fform  => fform => prop"   ("{_,_,_,_}_{_,_,_,_ ; _,_,_,_}" 80)
specP5 :: "fform => fform => fform => fform => fform => proc => fform => fform => fform => fform => fform => fform  => fform => fform  => fform => fform  => prop"   ("{_,_,_,_,_}_{_,_,_,_,_ ; _,_,_,_,_}" 80)
specP6 :: "fform => fform => fform => fform => fform => fform => proc => fform => fform => fform => fform => fform => fform => fform  => fform => fform => fform => fform => fform  => prop"   ("{_,_,_,_,_,_}_{_,_,_,_,_,_ ; _,_,_,_,_,_}" 80)

(*List rules, p do not have exp1. If p have exp1, it must be eliminated by consequence rule firstly.*)
axiomatization where
ListEmpty : "{p} empty(exp1) {exp1[=](List [])[&]p; (l [=] (Real 0))}" and
ListAdd : "{exp1[=](List ls)[&]p} (addL exp1 exp2) {(exp1[=](List (exp2#ls)))[&]p; (l [=] (Real 0))}" and
ListDel : "|- exp1[=](List (tl(ls)))[&]p [-->] post
  ==> {exp1[=](List ls)[&]p} (delL(exp1)) {post; (l [=] (Real 0))}" and
ListEmptya : "{p} empty(exp1) {p; (l [=] (Real 0))}" and
ListAdda : "{p} (addL exp1 exp2) {p; (l [=] (Real 0))}" and
ListDela : "{p} (delL(exp1)) {p; (l [=] (Real 0))}"
axiomatization where
Empty: "EL [=] List [] |- isEmpty(EL)"

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
axiomatization where
Continue2 : "|- (Init [-->] FF)
           [&] ((p [&] close(FF) [&] close([~]b)) [-->] q)
           [&] ((((l [=] Real 0) [|] (high (close(FF) [&] p [&] close(b)))) [&] Rg) [-->] G)
[&] (exeFlow (D,b,F1) [-->]FF)
           ==> {Init [&] p} <D&&FF&&b> : Rg {q; G}"  and
Continue2T : "|- (Init[&]p [-->] FF[&]b)
           [&] ((p [&] close(FF) [&] close(b) [&] close([~]b)) [-->] q)
           [&] ((((l [=] Real 0) [|] (high (close(FF) [&] p [&] close(b)))) [&] Rg) [-->] G)
[&](exeFlow (D,b,FF) [-->]FF)
           ==> {Init [&] p} <D&&FF&&(b)> : Rg {q; G}" and
Continue2F : "|- (p[-->][~]b) [&] (p[-->]q) [&] ((l[=](Real 0))[-->]G)
           ==> {p} <D&&FF&&b> : Rg {q; G}"

(*Sequential rule*)
axiomatization where
Sequence : "[| {p} P {m; H}; {m} Q {q; G} |] ==>
             {p} P; (m, H); Q {q; H [^] G}" 
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
axiomatization where
ConditionT2 :  "[| |-(pn [-->] b); {pm,pn} (Pm||Pn) {qm,qn; Gm,Gn} |]
  ==> {pm,pn} (Pm||(IF b Pn)) {qm,qn; Gm,Gn}" and
ConditionT2a :  "[| |-(pm [-->] b); {pm,pn} (Pm||Pn) {qm,qn; Gm,Gn} |]
  ==> {pm,pn} ((IF b Pm)||Pn) {qm,qn; Gm,Gn}"


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
axiomatization where
Communication1 : "[| ~inPairForm ([(x, e)], ry);
                    {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                    |- (qx [-->] rx) [&] (qx[&]qy [-->] (substF ([(x, e)]) (ry)));
                    |- ((Hx [^] (high (qx))) [-->] Gx) [&] ((Hy [^] (high (qy))) [-->] Gy);
                    |- ((((Hx [^] (high (qx))) [&] Hy) [|]((Hy [^] (high (qy))) [&] Hx)) [-->] H)
                 |]
              ==>   {px, py} ((Px; (qx, Hx); ch !! e) || (Py; (qy, Hy); ch ?? x)) {rx, ry; 
                    Gx [&] H, Gy [&] H}"
axiomatization where
CommunicationSim : "[| ~inPairForm ([(x, e)], ry);
  |- (px [-->] rx) [&] (px[&]py [-->] (substF ([(x, e)]) (ry))) |]
  ==>  {px, py} ((ch !! e) || (ch ?? x)) {rx, ry;(l[=](Real 0)), (l[=](Real 0))}"
axiomatization where
CommunicationC : "[| ~inPairForm ([(x, e)], ry);
                    {qx} (Px) {rx; (l[=](Real 0))}; 
                    |- (px [&] py) [-->] (substF ([(x, e)]) (qx));
                    |- py [-->] ry;
                    |- (l[=](Real 0)) [-->] Hx;
                    |- (l[=](Real 0)) [-->] My;
                    |- (l[=](Real 0)) [-->] My;
                   contain(Pm,(ch ?? x))|]
              ==>   {px, py} (( Pm; (qx, Hx); Px) || (ch !! e))
                    {rx, ry; Mx, My}"

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
"contain ((<FF && b> : g),p) = False" |
"contain ((q |> b r),p) = False" |
"contain ((q [[> r),p) = False"

(**)
axiomatization where
CommunicationI1 : "[| ~inPairForm ([(x, e)], ry);
                    |- Hy [-->] H;
                    |- rg [-->] H[^]WTrue;
                    {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                    |- Init [&] pre [<->] qx;
                    |- pre [&] Init [&] b [-->] FF;
                    |- (pre [&] close(FF) [&] close(b)) [-->] rx;
                    |- (qy [&] pre [&] close(FF) [&] close(b)) [-->] (substF ([(x, e)]) (ry));
                    |- (Hx [^] ((((l [=] Real 0) [|] (high (close(FF) [&] pre [&] close(b)))) [&] H)) [-->] Gx);
                    |- Hy [-->] Gy;
                    |- Hx [-->] Hxm;
                    |- Hy [-->] Hym;
                    contain(P,(ch !! e))
                 |]
              ==>   {px, py} (( Px; (qx, Hxm); (<FF && b> :rg) [[> P) || (Py; (qy, Hym); ch ?? x))
                    {rx, ry; Gx, Gy}"
axiomatization where
CommunicationI2 : "[| ~inPairForm ([(x, e)], ry);
                    |- Hy [-->] H;
                    |- rg [-->] H[^]WTrue;
                    {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                    |- Init [&] pre [<->] qx;
                    |- pre [&] Init [&] b [-->] FF;
                    |- (qy [&] pre [&] close(FF) [&] close(b)) [-->] (substF ([(x, e)]) (rx));
                    |- qy [-->] ry;
                    |- Hx [^] ((((l [=] Real 0) [|] (high (close(FF) [&] pre [&] close(b)))) [&] H)) [-->] Gx;
                    |- Hy [-->] Gy;
                    |- Hx [-->] Hxm;
                    |- Hy [-->] Hym;
                    contain(P,(ch ?? x))
                 |]
              ==>   {px, py} (( Px; (qx, Hxm); (<FF && b> :rg) [[> P) || (Py; (qy, Hym); ch !! e))
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

axiomatization where
Repetition0 : "(Pm**(0)) == Skip" and
Repetition1 : "(Pm**(Suc(0))) == Pm" and
RepetitionN : "(Pm**(am+1)) == (Pm; M; Pm**am)"

axiomatization where
RepetitionA2 : "{p1,p2} ((Pm**(am+1))||(Pn**(an+1))) {p1,p2; Ha,Hb}
==> {p1,p2} ((Pm***)||(Pn***)) {p1,p2; Ha,Hb}"

axiomatization where
RepetitionG2 : "[| {p1,p2} ((Pm***)||(Pn***)) {p1,p2; Ha,Hb}; |- Ha [^] Ha [-->] Ha; |- Hb [^] Hb [-->] Hb|]
==> {p1,p2} (Pm*||Pn*) {p1,p2; Ha,Hb}"

axiomatization where
RepetitionA6 : "{p1,p2,p3,p4,p5,p6} ((Pm**(am+1))||(Pn**(an+1))||(Po**(ao+1))||(Pp**(ap+1))||(Pq**(aq+1))||(Pr**(ar+1))) {p1,p2,p3,p4,p5,p6; Ha,Hb,Hc,Hd,He,Hf}
==> {p1,p2,p3,p4,p5,p6} ((Pm***)||(Pn***)||(Po***)||(Pp***)||(Pq***)||(Pr***)) {p1,p2,p3,p4,p5,p6; Ha,Hb,Hc,Hd,He,Hf}"

axiomatization where
RepetitionG6 : "[| {p1,p2,p3,p4,p5,p6} ((Pm***)||(Pn***)||(Po***)||(Pp***)||(Pq***)||(Pr***)) {p1,p2,p3,p4,p5,p6; Ha,Hb,Hc,Hd,He,Hf}; |- Ha [^] Ha [-->] Ha; |- Hb [^] Hb [-->] Hb; |- Hc [^] Hc [-->] Hc; |- Hd [^] Hd [-->] Hd; |- He [^] He [-->] He; |- Hf [^] Hf [-->] Hf|]
==> {p1,p2,p3,p4,p5,p6} (Pm*||Pn*||Po*||Pp*||Pq*||Pr*) {p1,p2,p3,p4,p5,p6; Ha,Hb,Hc,Hd,He,Hf}"

(*N times repetition request post and history holds for any middle state to ensure RepetitionG holds.*)
axiomatization where
RepetitionT1a : "{px, py} ((Px;M;Pz) || Py) {qx, qy; Hx, Hy}
           ==>  {px, py} (((Px**1);M;Pz) || Py) {qx, qy; Hx, Hy}" and
RepetitionTna : "[| {px, py} (((Px**m);(qx,H);Px;M;P) || Py) {qx, qy; Hx, Hy};
                 |- Hx [^] Hx [-->] Hx;
                 |- H [-->] Hx|]
           ==>  {px, py} (((Px**(m+1));M;P) || Py) {qx, qy; Hx, Hy}" and
RepetitionG : "[| {px, py} (Px**(m+1) || Py**(n+1)) {px, py; Hx, Hy};
                 |- Hx [^] Hx [-->] Hx; |- Hy [^] Hy [-->] Hy|]
           ==>  {px, py} ((Px* ) || (Py* )) {px, py; Hx, Hy} " and
RepetitionE : "[| {px, py} (((P;M;(Px**(n+1)));(qx,Hx);(Px* )) || Py) {qx, qy; Hx, Hy}|]
           ==>  {px, py} ((P;M;(Px* )) || Py) {qx, qy; Hx, Hy} "

(*Structure rule*)
axiomatization where
Structure : "{px, py} (Px || Py) {qx, qy; Hx, Hy}
           ==> {py, px} (Py || Px) {qy, qx; Hy, Hx}" and
structR : "{px, py} Q||((Px;Mx;Py);My;Pz) {qx, qy; Hx, Hy}
           ==> {px, py} Q||(Px;Mx;Py;My;Pz){qx, qy; Hx, Hy}" and
structL : "{px, py} ((Px;Mx;Py);My;Pz)||Q {qx, qy; Hx, Hy}
           ==> {px, py} (Px;Mx;Py;My;Pz)||Q{qx, qy; Hx, Hy}" and
structSkipL : "{px, py} (Skip;(px,l[=](Real 0));P)||Q {qx, qy; Hx, Hy}
           == {px, py} P||Q{qx, qy; Hx, Hy}" and
structSkipR : "{px, py} (P;(qx,Hx);Skip)||Q {qx, qy; Hx, Hy}
           == {px, py} P||Q{qx, qy; Hx, Hy}" and
Equality2: "[| Pm==Qm; Pn==Qn; {p1,p2} (Qm||Qn) {p1,p2; Ha,Hb}|]
==> {p1,p2} (Pm||Pn) {p1,p2; Ha,Hb}" and
Equality6: "[| Pm==Qm; Pn==Qn; Po==Qo; Pp==Qp; Pq==Qq; Pr==Qr; {p1,p2,p3,p4,p5,p6} (Qm||Qn||Qo||Qp||Qq||Qr) {p1,p2,p3,p4,p5,p6; Ha,Hb,Hc,Hd,He,Hf}|]
==> {p1,p2,p3,p4,p5,p6} (Pm||Pn||Po||Pp||Pq||Pr) {p1,p2,p3,p4,p5,p6; Ha,Hb,Hc,Hd,He,Hf}"


(*Consequence rule*)
axiomatization where
ConsequenceS : "[| {px} P {qx; Hx}; |- ((p [-->] px) [&] (qx [-->] q) [&] (Hx [-->] H))|]
            ==> {p} P {q; H}"
and
ConsequenceP : "[| {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                   |- ((p [-->] px) [&] (r [-->] py) [&] (qx [-->] q) [&] (qy [-->] s) 
                       [&] (Hx [-->] H) [&] (Hy [-->] G))|]
            ==> {p, r} (Px || Py) {q, s; H, G}"
and
Consequence6 : "[|{qa,qb,qc,qd,qe,qf} (Pm||Pn||Po||Pp||Pq||Pr) {ra,rb,rc,rd,re,rf; Ha,Hb,Hc,Hd,He,Hf}; |- (q1[-->]qa) [&] (q2[-->]qb) [&] (q3[-->]qc) [&] (q4[-->]qd)  [&] (q5[-->]qe) [&] (q6[-->]qf); |- (ra[-->]r1) [&] (rb[-->]r2) [&] (rc[-->]r3) [&] (rd[-->]r4)  [&] (re[-->]r5) [&] (rf[-->]r6); |- (Ha[-->]H1) [&] (Hb[-->]H2) [&] (Hc[-->]H3) [&] (Hd[-->]H4) [&] (He[-->]H5) [&] (Hf[-->]H6)|]
==> {q1,q2,q3,q4,q5,q6} (Pm||Pn||Po||Pp||Pq||Pr) {r1,r2,r3,r4,r5,r6; H1,H2,H3,H4,H5,H6}"

(*added rules for parallel with more entities*)
axiomatization where
Parallel23: "[| {p1,p2} (Pm||Pn) {q1,q2; H1,H2};
                {p3} Po {q3; H3}|]
       ==> {p1,p2,p3} (Pm||Pn||Po) {q1,q2,q3; H1,H2,H3}" and
Parallel24: "[| {p1,p2,p3} (Pm||Pn||Po) {q1,q2,q3; H1,H2,H3};
                {p4} Pp {q4; H4}|]
       ==> {p1,p2,p3,p4} (Pm||Pn||Po||Pp) {q1,q2,q3,q4; H1,H2,H3,H4}" and
Parallel25: "[| {p1,p2,p3,p4} (Pm||Pn||Po||Pp) {q1,q2,q3,q4; H1,H2,H3,H4};
                {p5} Pq {q5; H5}|]
       ==> {p1,p2,p3,p4,p5} (Pm||Pn||Po||Pp||Pq) {q1,q2,q3,q4,q5; H1,H2,H3,H4,H5}" and
Parallel26: "[| {p1,p2,p3,p4,p5} (Pm||Pn||Po||Pp||Pq) {q1,q2,q3,q4,q5; H1,H2,H3,H4,H5};
                {p6} Pr {q6; H6}|]
       ==> {p1,p2,p3,p4,p5,p6} (Pm||Pn||Po||Pp||Pq||Pr) {q1,q2,q3,q4,q5,q6; H1,H2,H3,H4,H5,H6}"
axiomatization where
ParallelSeq6: "[| {p1,p2,p3,p4,p5,p6} (Pm||Pn||Po||Pp||Pq||Pr) {q1,q2,q3,q4,q5,q6; Ha,Hb,Hc,Hd,He,Hf}; {r1,r2,r3,r4,r5,r6} (Qm||Qn||Qo||Qp||Qq||Qr) {p1,p2,p3,p4,p5,p6; G1,G2,G3,G4,G5,G6}; |- (G1[^]Ha) [-->] M1; |- (G2[^]Hb) [-->] M2; |- (G3[^]Hc) [-->] M3; |- (G4[^]Hd) [-->] M4; |- (G5[^]He) [-->] M5; |- (G6[^]Hf) [-->] M6|]
           ==> {r1,r2,r3,r4,r5,r6} ((Qm;(p1,G1);Pm)||(Qn;(p2,G2);Pn)||(Qo;(p3,G3);Po)||(Qp;(p4,G4);Pp)||(Qq;(p5,G5);Pq)||(Qr;(p6,G6);Pr)) {q1,q2,q3,q4,q5,q6; M1,M2,M3,M4,M5,M6}"

axiomatization where
ParallelSeq6a: "[|{p1}Pm{q1; Ha}; {p2}Pn{q2; Hb}; {p3}Po{q3; Hc}; {p4}Pp{q4; Hd}; {p5}Pq{q5; He}; {p6}Pr{q6; Hf}|]
==>  {p1,p2,p3,p4,p5,p6} (Pm||Pn||Po||Pp||Pq||Pr) {q1,q2,q3,q4,q5,q6; Ha,Hb,Hc,Hd,He,Hf}"

axiomatization where
ParallelSeq12a: "[| {p1,p2,p3,p4,p5,p6} (Pm||Pn||Po||Pp||Pq||Pr) {q1,q2,q3,q4,q5,q6; Ha,Hb,Hc,Hd,He,Hf}; {r1,r2} (Qm||Qn) {p1,p2; G1,G2}; |- (G1[^]Ha) [-->] M1; |- (G2[^]Hb) [-->] M2|]
           ==> {r1,r2,p3,p4,p5,p6} ((Qm;(p1,G1);Pm)||(Qn;(p2,G2);Pn)||(Po)||(Pp)||(Pq)||(Pr)) {q1,q2,q3,q4,q5,q6; M1,M2,Hc,Hd,He,Hf}" and
ParallelSeq25a: "[| {p1,p2,p3,p4,p6} (Pm||Pn||Po||Pp||Pr) {q1,q2,q3,q4,q6; Ha,Hb,Hc,Hd,Hf}; {r2,r5} (Qn||Qq) {p2,p5; G2,G5}; |- (G2[^]Hb) [-->] M2|]
           ==> {p1,r2,p3,p4,r5,p6} ((Pm)||(Qn;(p2,G2);Pn)||(Po)||(Pp)||(Qq)||(Pr)) {q1,q2,q3,q4,p5,q6; Ha,M2,Hc,Hd,G5,Hf}" and
ParallelSeq23a: "[| {p1,p2,p4,p6} (Pm||Pn||Pp||Pr) {q1,q2,q4,q6; Ha,Hb,Hd,Hf}; {r2,r3} (Qn||Qo) {p2,p3; G2,G3}; |- (G2[^]Hb) [-->] M2|]
           ==> {p1,r2,r3,p4,p6} ((Pm)||(Qn;(p2,G2);Pn)||(Qo)||(Pp)||(Pr)) {q1,q2,p3,q4,q6; Ha,M2,G3,Hd,Hf}" and
ParallelSeq23b: "[| {p1,p2,p6} (Pm||Pn||Pr) {q1,q2,q6; Ha,Hb,Hf}; {r2,r4} (Qn||Qp) {p2,p4; G2,G4}; |- (G2[^]Hb) [-->] M2|]
           ==> {p1,r2,r4,p6} ((Pm)||(Qn;(p2,G2);Pn)||(Qp)||(Pr)) {q1,q2,p4,q6; Ha,M2,G4,Hf}" and
ParallelSeq23c: "[| {p1,p2} (Pm||Pn) {q1,q2; Ha,Hb}; {r2,r6} (Qn||Qr) {p2,p6; G2,G6}; |- (G2[^]Hb) [-->] M2|]
           ==> {p1,r2,r6} ((Pm)||(Qn;(p2,G2);Pn)||(Qr)) {q1,q2,p6; Ha,M2,G6}"

axiomatization where
ParallelSeq6b: "[| {p1,p2,p3,p4,p5,p6} (Pm||Pn||Po||Pp||Pq||Pr) {q1,q2,q3,q4,q5,q6; Ha,Hb,Hc,Hd,He,Hf}; {q1,q2}Qn||Rn{r1,r2; Ga,Gb}; |- Ha[^]Ga [-->]Ma; |- Hb[^]Gb [-->]Mb|]
           ==>  {p1,p2,p3,p4,p5,p6} ((Pm;(q1,Ha);Qn)||(Pn;(q2,Hb);Rn)||Po||Pp||Pq||Pr) {r1,r2,q3,q4,q5,q6; Ma,Mb,Hc,Hd,He,Hf}"
axiomatization where
ConsequenceP5 : "[| {pa,pb,pc,pd,pe} P {qa,qb,qc,qd,qe; Ha,Hb,Hc,Hd,He}; 
                   |- (p1 [-->] pa) [&] (p2 [-->] pb) [&] (p3 [-->] pc) [&] (p4 [-->] pd) [&] (p5 [-->] pe);
                   |- (qa [-->] q1) [&] (qb [-->] q2) [&] (qc [-->] q3) [&] (qd [-->] q4) [&] (qe [-->] q5);
                   |- (Ha [-->] H1) [&] (Hb [-->] H2) [&] (Hc [-->] H3) [&] 
                      (Hd [-->] H4) [&] (He [-->] H5) |]
            ==> {p1,p2,p3,p4,p5} P {q1,q2,q3,q4,q5; H1,H2,H3,H4,H5}"
axiomatization where
Repetition5 : "[| {p1,p2,p3,p4,p5} (((Pm||Pn)||Po)||Pp)||Pq {q1,q2,q3,q4,q5; H1,H2,H3,H4,H5};
                  |- H1 [^] H1 [-->] H1; |- H2 [^] H2 [-->] H2; |- H3 [^] H3 [-->] H3;
                  |- H4 [^] H4 [-->] H4; |- H5 [^] H5 [-->] H5|]
           ==> {p1,p2,p3,p4,p5} (((Pm*||Pn*)||Po*)||Pp*)||Pq* {q1,q2,q3,q4,q5; H1,H2,H3,H4,H5}"
axiomatization where
Parallel113: "[| {p1,p2,p3} ((Pm||Pn)||Po) {q,q2,q3; H,H2,H3};
                  {q} Q {qx; Hx}; |- (H[^]Hx) [-->] Hy|]
           ==> {p1,p2,p3} (((Pm;(q,H);Q)||Pn)||Po) {qx,q2,q3; Hy,H2,H3}"
axiomatization where
Parallel115: "[| {p1,p2,p3,p4,p5} (((Pm||Pn)||Po)||Pp)||Pq {q,q2,q3,q4,q5; H,H2,H3,H4,H5};
                  {q} Q {qx; Hx}; |- (H[^]Hx) [-->] Hy|]
           ==> {p1,p2,p3,p4,p5} ((((Pm;(q,H);Q)||Pn)||Po)||Pp)||Pq {qx,q2,q3,q4,q5; Hy,H2,H3,H4,H5}"
axiomatization where
Parallel13: "[| {p1,p2,p3} (Pm||Pn)||Po {q1,q2,q3; H1,H2,H3};
                  {q3} Q {qx; Hx}; |- (H3[^]Hx) [-->] Hy|]
           ==> {p1,p2,p3} (Pm||Pn)||(Po;(q3,H3);Q) {q1,q2,qx; H1,H2,Hy}"
axiomatization where
Parallel14: "[| {p1,p2,p3,p4} ((Pm||Pn)||Po)||Pp {q1,q2,q3,q4; H1,H2,H3,H4};
                  {q4} Q {qx; Hx}; |- (H4[^]Hx) [-->] Hy|]
           ==> {p1,p2,p3,p4} ((Pm||Pn)||Po)||(Pp;(q4,H4);Q) {q1,q2,q3,qx; H1,H2,H3,Hy}"
axiomatization where
Parallel15: "[| {p1,p2,p3,p4,p5} (((Pm||Pn)||Po)||Pp)||Pq {q1,q2,q3,q4,q5; H1,H2,H3,H4,H5};
                  {q5} Q {qx; Hx}; |- (H5[^]Hx) [-->] Hy|]
           ==> {p1,p2,p3,p4,p5} (((Pm||Pn)||Po)||Pp)||(Pq;(q5,H5);Q) {q1,q2,q3,q4,qx; H1,H2,H3,H4,Hy}"
axiomatization where
Communication3 : "[| ~inPairForm ([(x, e)], qy);
                    {p1,p2,p3} (Pm||Pn)||Po {q1,q2,q3; H1,H2,H3};
                    |- (q1 [-->] qx) [&] (q3 [-->] (substF ([(x, e)]) (qy)));
                    |- ((H1 [^] (high (q1))) [-->] Hx) [&] ((H3 [^] (high (q3))) [-->] Hy);
                    |- ((((H1 [^] (high (q1))) [&] H3) [|]((H3 [^] (high (q3))) [&] H1)) [-->] H);
                    |- Hx [&] H [-->] Ha;
                    |- Hy [&] H [-->] Hb
                  |]
               ==>  {p1,p2,p3} ((Pm;(q1, H1);ch!!e)||Pn)||(Po;(q3, H3);ch??x) 
                    {qx,q2,qy; Ha,H2,Hb}"
axiomatization where
Communication4 : "[| ~inPairForm ([(x, e)], qy);
                    {p1,p2,p3,p4} ((Pm||Pn)||Po)||Pp {q1,q2,q3,q4; H1,H2,H3,H4};
                    |- (q1 [-->] qx) [&] (q4 [-->] (substF ([(x, e)]) (qy)));
                    |- ((H1 [^] (high (q1))) [-->] Hx) [&] ((H4 [^] (high (q4))) [-->] Hy);
                    |- ((((H1 [^] (high (q1))) [&] H4) [|]((H4 [^] (high (q4))) [&] H1)) [-->] H);
                    |- Hx [&] H [-->] Ha;
                    |- Hy [&] H [-->] Hb
                  |]
               ==>  {p1,p2,p3,p4} (((Pm;(q1, H1);ch!!e)||Pn)||Po)||(Pp;(q4, H4);ch??x) 
                    {qx,q2,q3,qy; Ha,H2,H3,Hb}"
axiomatization where
Communication5 : "[| ~inPairForm ([(x, e)], qy);
                    {p1,p2,p3,p4,p5} (((Pm||Pn)||Po)||Pp)||Pq {q1,q2,q3,q4,q5; H1,H2,H3,H4,H5};
                    |- (q1 [-->] qx) [&] (q5 [-->] (substF ([(x, e)]) (qy)));
                    |- ((H1 [^] (high (q1))) [-->] Hx) [&] ((H5 [^] (high (q5))) [-->] Hy);
                    |- ((((H1 [^] (high (q1))) [&] H5) [|]((H5 [^] (high (q5))) [&] H1)) [-->] H);
                    |- Hx [&] H [-->] Ha;
                    |- Hy [&] H [-->] Hb
                  |]
               ==>  {p1,p2,p3,p4,p5} ((((Pm;(q1, H1);ch!!e)||Pn)||Po)||Pp)||(Pq;(q5, H5);ch??x) 
                    {qx,q2,q3,q4,qy; Ha,H2,H3,H4,Hb}"

(*important derived rules*)
lemma structSkipEL : "{px, py} (Skip;(px,l[=](Real 0));P)||Q {qx, qy; Hx, Hy}
           ==> {px, py} P||Q{qx, qy; Hx, Hy}"
apply (cut_tac px=px and py=py and P=P and Q=Q and qx=qx and qy=qy and Hx=Hx and Hy=Hy in structSkipL,auto)
done

lemma structSkipIL : "{px, py} P||Q{qx, qy; Hx, Hy}
           ==> {px, py} (Skip;(px,l[=](Real 0));P)||Q {qx, qy; Hx, Hy}"
apply (cut_tac px=px and py=py and P=P and Q=Q and qx=qx and qy=qy and Hx=Hx and Hy=Hy in structSkipL,auto)
done

lemma structSkipER : "{px, py} (P;(qx,Hx);Skip)||Q {qx, qy; Hx, Hy}
           ==> {px, py} P||Q{qx, qy; Hx, Hy}"
apply (cut_tac px=px and py=py and P=P and Q=Q and qx=qx and qy=qy and Hx=Hx and Hy=Hy in structSkipR,auto)
done

lemma structSkipIR : "{px, py} P||Q{qx, qy; Hx, Hy}
           ==> {px, py} (P;(qx,Hx);Skip)||Q {qx, qy; Hx, Hy}"
apply (cut_tac px=px and py=py and P=P and Q=Q and qx=qx and qy=qy and Hx=Hx and Hy=Hy in structSkipR,auto)
done

lemma RepetitionT1 : "{px, py} (Px || Py) {qx, qy; Hx, Hy}
           ==>  {px, py} (Px**1 || Py) {qx, qy; Hx, Hy}"
apply (rule structSkipER)
apply (rule RepetitionT1a)
apply (rule structSkipIR,auto)
done

lemma RepetitionTn : "[| {px, py} (((Px**m);(qx,H);Px) || Py) {qx, qy; Hx, Hy};
                 |- Hx [^] Hx [-->] Hx;
                 |- H [-->] Hx|]
           ==>  {px, py} (Px**(m+1) || Py) {qx, qy; Hx, Hy}"
apply (rule structSkipER)
apply (cut_tac H="H" in RepetitionTna,auto)
apply (rule structL)
apply (rule structSkipIR,auto)
done

lemma Parallel4: "[| {py} Py {qy; Hy[&](l[=](Real 0))};
               {qx, qy} (Qx || Qy) {rx, ry; Mx, My};
               |- (Hy[&](l[=](Real 0))) [-->] HR;
               |- ((Hy[&](l[=](Real 0))) [^] My) [-->] Gy
            |]
           ==> {qx, py} (Qx) || (Py;(qy,HR);Qy) {rx, ry; Mx, Gy}"
apply (rule structSkipEL)
apply (cut_tac m=0 and Hx="l [=] Real 0" in Parallel3,auto)
apply (rule Parallel2,auto)
apply (rule Skip)
(*1*)
apply (rule impR)
apply (rule conjR)
apply (rule basic)+
apply (rule impR)
apply (rule conjL)
apply (rule basic)
apply (rule impR)
apply (rule LC1)
apply (rule LL3a)
apply (rule basic)
done

lemma Parallel1a: "[| {px, py} (Px || Py) {qx, qy; Hx, Hy}; {qy} Qy {ry; Gy}; |- Hy [^] Gy [-->] G |]
           ==>  {px, py} ((Px) || (Py; (qy, Hy); Qy)) {qx, ry; Hx, G}"
apply (rule structSkipER)
apply (subgoal_tac "{px, py}(Px;(qx, Hx);Skip)||(Py;(qy, Hy);Qy){qx,ry; (Hx [^] l [=] Real 0), Hy [^] Gy}")
apply (cut_tac px=px and py=py and qx=qx and qy=ry and Hx="Hx [^] l [=] Real 0" and Hy="Hy [^] Gy" in ConsequenceP,auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule LL4)
apply (rule basic)
apply assumption
(*start*)
apply (cut_tac px=px and py=py and Px=Px and qx=qx and Hx="Hx" and Qx=Skip and Py=Py and qy=qy and Hy=Hy and Qy=Qy and rx=qx and ry=ry and Gx="(l [=] Real 0)" and Gy=Gy in Parallel1,auto)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
done

lemma CommunicationI1b : "[| ~inPairForm ([(x, e)], ry);
                    |- Hy [-->] H;
                    |- rg [-->] H[^]WTrue;
                    {py} ( Py) {qy; Hy}; 
                    |- Init [&] pre [<->] qx;
                    |- pre [&] Init [&] b [-->] FF;
                    |- (pre [&] close(FF) [&] close(b)) [-->] rx;
                    |- (qy [&] pre [&] close(FF) [&] close(b) [-->] (substF ([(x, e)]) (ry)));
                    |- ((((l [=] Real 0) [|] (high (close(FF) [&] pre [&] close(b)))) [&] H) [-->] Gx);
                    |- Hy [-->] Gy;
                    |- Hy [-->] Hym;
                    contain(P,(ch !! e))
                 |]
              ==>   {qx, py} (((<FF && b> :rg) [[> P) || (Py; (qy, Hym); ch ?? x))
                    {rx, ry; Gx, Gy}"
apply (rule structSkipEL)
apply (cut_tac Hx="l [=] Real 0" and Init=Init in CommunicationI1,auto)
apply (rule Parallel2,auto)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (cut_tac P="((l [=] Real 0 [|] high (close(FF) [&] pre [&] close(b))) [&] H) [-->] Gx" in cut,auto)
apply (rule thinR,auto)
apply (rule impR)
apply (rule LL3a)
apply (rule impL)
apply (rule basic)+
apply (rule impR)
apply (rule basic)
done

lemma structSkipELR : "{px, py} Q||(Skip;(py,l[=](Real 0));P) {qx, qy; Hx, Hy}
           ==> {px, py} Q||P{qx, qy; Hx, Hy}"
apply (rule Structure)
apply (rule structSkipEL)
apply (rule Structure)
apply assumption
done

lemma CommunicationI1a : "[| ~inPairForm ([(x, e)], ry);
                       |- Init [&] pre [<->] px;
                       |- pre [&] Init [&] b [-->] FF;
                       |- (pre [&] close(FF) [&] close(b)) [-->] rx;
                       (*|- px [-->] rx;*)
                       |- py [&] pre [&] close(FF) [&] close(b) [-->] (substF ([(x, e)]) (ry));
                       |- (l[=]Real 0) [-->] Gx;
                       |- (l[=]Real 0) [-->] Gy;
                       contain(Px,(ch !! e))|]
              ==>   {px, py} (((<FF && b> :rg) [[> Px) || (ch ?? x)) {rx, ry; Gx, Gy}"
apply (rule structSkipEL)
apply (rule structSkipELR)
apply (cut_tac H="l [=] Real 0" and Hx="l [=] Real 0" in CommunicationI1,auto)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule RL3a)
apply (simp add: True_def)
apply (rule impR)
apply (rule basic)
apply (rule Parallel2)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule LL3a)
apply (rule conjL)
apply (rule thinL)
apply (cut_tac P="l [=] Real 0 [-->] Gx" in cut,auto)
apply (rule thinL)
apply (rule thinR,auto)
apply (rule impL)
apply (rule basic)+
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule basic)
done

lemma CommunicationI2a : "[| ~inPairForm ([(x, e)], ry);
                       |- Init [&] pre [<->] px;
                       |- pre [&] Init [&] b [-->] FF;
                       |- py [&] pre [&] close(FF) [&] close(b) [-->] (substF ([(x, e)]) (rx));
                       |- py [-->] ry;
                       |- (l[=]Real 0) [-->] Gx;
                       |- (l[=]Real 0) [-->] Gy;
                       contain(Px,(ch ?? x))|]
              ==>   {px, py} (( (<FF && b> :rg) [[> Px) || (ch !! e)) {rx, ry; Gx, Gy}"
apply (rule structSkipEL)
apply (rule structSkipELR)
apply (cut_tac H="l [=] Real 0" and Hx="l [=] Real 0" in CommunicationI2,auto)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule RL3a)
apply (simp add: True_def)
apply (rule impR)
apply (rule basic)
apply (rule Parallel2)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule LL3a)
apply (rule conjL)
apply (rule thinL)
apply (cut_tac P="l [=] Real 0 [-->] Gx" in cut,auto)
apply (rule thinL)
apply (rule thinR,auto)
apply (rule impL)
apply (rule basic)+
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule basic)
done

end
