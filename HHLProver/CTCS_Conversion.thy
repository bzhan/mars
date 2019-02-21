section {*An example on CTCS mode and level conversions.*}

theory CTCS_Conversion
  imports HHL
begin

(*First define the whole process, which is composed of a set of sub-processes.*)

type_synonym  segT = "exp * exp * exp * exp" (*Each segment contains v1, v2, s, and mode.*)
type_synonym  MAT = "segT list"

consts
chw :: "cname" (*Channel CH_win*)
chd :: "cname" (*Channel CH_DC*)
bw  :: "string"   (*Variable b_win*)
MA_n :: "MAT"
t_delay :: real
minA :: real (*Min acceleration, CONSTANT*)
maxA :: real (*Max acc, CONSTANT*)

axiomatization where 
assumpMinA: "minA > 0" and
assumpMaxA: "maxA > 0"

(****************)
(* The variables*)
(****************)
(*Variable level*)
definition level :: "exp" where
"level == RVar ''le''"
 (*Displacement, variable s, the position of the train*)
definition sf :: "exp" where
"sf == RVar ''s''"
(*Variable x2*)
definition x2 :: "exp" where
"x2 == RVar ''x2''"
(*MA*)
definition seg1 :: "segT" where
"seg1 == (RVar ''v11'', RVar ''v12'', RVar ''x2'', String ''FS'')"
definition seg2 :: "segT" where
"seg2 == (RVar ''v21'', RVar ''v22'', RVar ''e2'', String ''CO'')"
definition MA :: "MAT" where
"MA == seg1#seg2#MA_n"
(*Temp_t0*)
definition Temp_t0 :: "exp" where
"Temp_t0 == RVar ''t0''" 
(*Temp_t1*)
definition Temp_t1 :: "exp" where
"Temp_t1 == RVar ''t1''" 
(*Temp_t2*)
definition Temp_t2 :: "exp" where
"Temp_t2 == RVar ''t2''" 
(*clock time*)
definition ct :: "exp" where
"ct == RVar ''ct''" 
 (*Velocity of the Train*)
definition vel :: "exp"
where "vel == RVar ''v''" 
 (*Acceleation of the Train*)
definition acc :: "exp" where
"acc == RVar ''a''"
(*Mode of train*)
definition md :: "exp" where
"md == SVar ''md''"
(*Variable b_rConf*)
definition br :: "exp" where
"br == BVar ''br''"


(****************)
(* The driver process*)
(****************)
definition P :: "proc" where
"P ==  (IF ((BVar bw) [=] (Bool True)) 
      ((chd !! (Bool True)) [[ (chd !! (Bool False))))"

definition Driver :: "proc" where
"Driver ==  (Skip; (WTrue, l [=] Real 0); chw ?? (BVar bw)); 
     (((BVar bw) [=] (Bool False)), (l [=] Real 0) [|] (high (WTrue))); P"



(****************)
(* The train process*)
(****************)

(*checkV1, checkV2: check the given speed is less than all v1 and v2 of MAT.*)
primrec checkV1 :: "MAT => exp => fform" where
"checkV1 ([], v) = WTrue" |
"checkV1 ((a # ma), v) = ((v [<] (fst (a))) [&] (checkV1 (ma, v)))"
primrec checkV2 :: "MAT => exp => fform" where
"checkV2 ([], v) = WTrue" |
"checkV2 ((a # ma), v) = ((v [<] (fst (snd (a)))) [&] (checkV2 (ma, v)))"

(*checkS: checks the given speed is less than all the dynamic curves of MAT.*)
primrec checkS :: "MAT => exp => exp => fform" where
"checkS ([], v, s) = WTrue" |
"checkS (a#ma, v, s) = ((((v[*]v)[+](((Real 2)[*](Real minA))[*]s)) [<] 
                   ( (((fst(a)))[*]((fst(a)))) [+] 
                   (((Real 2)[*](Real minA))[*]((fst (snd (snd (a))))))))
                   [&] (checkS ((ma), v, s)))" 

definition B0 :: "fform" where
"B0 == ((vel[>=] Real 0) [|] ((acc) [>=] Real 0) [|] (( ct) [<] (( Temp_t0) [+] (Real t_delay))))"

definition B1 :: "fform" where
"B1 == ( (checkV2 (MA, vel)) [|] ((acc) [<] Real 0) [|] (( ct) [<] (( Temp_t1) [+] (Real t_delay))))"

definition B2 :: "fform" where
"B2 ==  ((checkV1 (MA, vel)) [&] (checkS (MA, vel, sf))) [|]  (acc [=] Real (- (minA))) "

definition B4 :: "fform" where
"B4 == (([~](level [=] (Real 2.5))) [|] (sf [<=] x2))"

(*Use pre-defined function hd.*)
definition B5 :: "fform" where
"B5 == (md [=] (snd ( snd ( snd (hd(MA))))))"

definition B6 :: "fform" where
"B6 == (([~](level [=] (Real 3))) 
    [|] ([~] (String ''CO'' [=]  (snd ( snd ( snd (hd( tl (MA))))))))
    [|] (br [=] Bool True)
    [|] ((((fst (snd (snd (hd (MA))))) [-] sf) [>] Real 0) [&] 
           (((fst (snd (snd (hd (MA))))) [-] sf) [<] Real 300))
    [|] ((ct) [<] (Temp_t2 [+] Real t_delay)))"

definition B :: fform where
"B == (B1 [&] B2 [&] B4 [&] B5 [&] B6)"

(*Invariant for Train movement*)
definition inv :: fform where 
"inv == (checkS (MA, vel, sf))"

(*Precondition*)
definition Pre :: fform where
"Pre == (level [=] Real 2.5)
      [&] (((fst (snd (snd (seg1))))) [=] x2)
      [&] (((snd (snd (snd (seg1))))) [=] (String ''FS''))
      [&] (((snd (snd (snd (seg2))))) [=] (String ''CO''))
      [&] (((fst (seg1))) [=] Real 0)"
definition Init :: fform where
"Init == (x2 [-] sf [>] Real 300) [&] B1 [&] B2
      [&] (checkS (MA, vel, sf)) "

(*The following presents the proof of the example.*)

(*The continuous part*)
definition Move :: proc where
"Move == <inv && B> : (l [>] Real 0)"

(*P_train includes six sub-processes in sequence.*)
definition P1 :: proc where
"P1 == (IF B6 chw !! (Bool False)); (WTrue, WTrue); (IF ([~] B6) chw!! (Bool True))"

(*For this case, B6 is True.*)
(*Add {*assert B6*} before this process. This is proved in Assert1*)
definition SP1 :: proc where
"SP1 ==  chw !! (Bool False)"

(*Variable c, used in Q12.*)
definition cv :: "exp" where
"cv == RVar ''cv''"
definition Q11 :: proc where
"Q11 == (IF ([~]B0) ( ((Temp_t0 := ct); (Pre [&] sf [<=] x2, l [=] (Real 0)); 
         NON R ''cv'' : (cv [>] Real 0 [&] (cv [<] Real maxA)) acc := cv) ))"

definition Q12 :: proc where
"Q12 == (IF ([~] B1) ((Temp_t1 := ct); (Pre [&] sf [<=] x2, l [=] (Real 0)); 
         NON R ''cv'' : ((cv [>] Real (-minA)) [&] (cv [<] Real maxA)) acc := (cv)) )"

definition Q13 :: proc where
"Q13 == (IF ([~] B2) acc := (Real (- minA)))"

definition Q3 :: proc where
"Q3 == (IF ([~] B4) level := (Real 3))"

definition Q4 :: proc where
"Q4 == (IF ([~] B5) ((md) := ((snd (snd (snd (hd (MA))))))))"

definition Q5 :: proc where
"Q5 == (IF ([~] B6) ((Temp_t2) := (ct); (WTrue, WTrue);chd ?? br; (WTrue, WTrue); 
       (IF (br [=] Bool True) ((fst (hd (tl (MA)))) := (Real 40)))))"

definition Imd :: mid where
"Imd == (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))))"

definition Train :: proc where
"Train == ((Move; (Pre [&] sf [<=] x2,  (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
          (Q11; Imd; Q12; Imd; Q13; Imd; Q3; Imd; Q4)); Imd; SP1); 
          (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));Q5"
 
definition System :: proc where
"System == (Train)* || (Driver)*"

(***********************************************************)
(***********************************************************)
(* Process definition finished, proof part starts. *)
(***********************************************************)
(***********************************************************)

(*********************************)
(**for differential equation**)

lemma assist_cont_1 : "|- Init [-->] inv"
apply (simp add:Init_def inv_def)
apply (rule impR)
apply fast
done

lemma assist_cont_2_a: "[|s <= t; t < (u::real)|] ==> (s < u)"
apply (auto)
done

lemma assist_cont_2_b: "[|s <= t; s ~=u; t = (u::real)|] ==> (s < u)"
apply (auto)
done

lemma assist_cont_2_c: "2 * minA * rvar(''s'') <= rvar(''v'') * rvar(''v'') + 2 * minA * rvar(''s'')"
apply (auto)
done

lemma assist_cont_2: "close(checkS(MA, vel, sf)), Pre |- sf [<=] x2"
apply (unfold MA_def Pre_def,auto)
apply (rule conjL)+
apply (cut_tac P="vel [*] vel [+] (Real 2 [*] Real minA) [*] sf [<]
    fst(seg2) [*] fst(seg2) [+] (Real 2 [*] Real minA) [*] fst(snd(snd(seg2))) [|]
    vel [*] vel [+] (Real 2 [*] Real minA) [*] sf [=]
    fst(seg2) [*] fst(seg2) [+] (Real 2 [*] Real minA) [*] fst(snd(snd(seg2)))" in thinL,auto)
apply (cut_tac P="close(checkS(MA_n, vel, sf))" in thinL,auto)
apply (cut_tac P="level [=] Real 5 / 2" in thinL,auto)
apply (cut_tac P="fst(snd(snd(seg1))) [=] x2" in thinL,auto)
apply (cut_tac P="snd(snd(snd(seg1))) [=] String ''FS''" in thinL,auto)
apply (cut_tac P="snd(snd(snd(seg2))) [=] String ''CO''" in thinL,auto)
apply (unfold seg1_def seg2_def level_def x2_def sf_def vel_def equal_less_def)
apply (rule Trans2,auto)
apply (subgoal_tac "2 * minA * rvar(''s'') < 2 * minA * rvar(''x2'') & minA >0",auto)
apply (cut_tac s="2 * minA * rvar(''s'')"
    and t="rvar(''v'') * rvar(''v'') + 2 * minA * rvar(''s'')"
    and u="2 * minA * rvar(''x2'')" in assist_cont_2_a,auto)
apply (rule assumpMinA)
apply (subgoal_tac "2 * minA * rvar(''s'') < 2 * minA * rvar(''x2'')")
apply (subgoal_tac "minA >0", simp)
apply (rule assumpMinA)
apply (cut_tac s="2 * minA * rvar(''s'')"
    and t="rvar(''v'') * rvar(''v'') + 2 * minA * rvar(''s'')"
    and u="2*minA * rvar(''x2'')" in assist_cont_2_b)
apply (rule assist_cont_2_c, auto)
apply (subgoal_tac "minA >0", simp)
apply (rule assumpMinA)
done

lemma step_continuous: "{Init [&] Pre} Move {Pre [&] sf [<=] x2; (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))}"
apply (simp add:Move_def)
apply (cut_tac Init = "Init" and p = "Pre" and FF = "inv" and b = "B" and 
               Rg = "(l [>] Real 0)" and q = "Pre [&] sf [<=] x2" and 
               G = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" in Continue,auto)
apply (rule conjR)
apply (rule assist_cont_1)
apply (rule conjR)
apply (rule impR)
apply (rule conjR)
apply fast
apply (rule conjL)+
apply (cut_tac P="NotForm(B)" in thinL,auto)
apply (simp add: inv_def)
apply (rule exchL)
apply (rule assist_cont_2)
apply (rule impR)
apply (rule conjL)
apply (rule disjL)
apply fast
apply (rule exchL)
apply (rule thinL)
apply (rule disjR)
apply (rule thinR)
apply (cut_tac s = "close(inv) [&] Pre [&] close(B)" and t= "Pre [&] sf [<=] x2" in DC18,auto)
apply (rule conjL)+
apply (rule conjR)
apply fast
apply (cut_tac P="close(B)" in thinL,auto)
apply (simp add:inv_def)
apply (rule assist_cont_2)
done


(**********************************)
(**for Q11****)

lemma assist_Q11_1_a : "substF([(Temp_t0, ct)], Pre) = Pre"
apply (simp add: Temp_t0_def ct_def Pre_def seg1_def)
apply (simp add: level_def x2_def seg2_def)
done

lemma assist_Q11_1_b : "substF([(Temp_t0, ct)], sf [<=] x2) = (sf [<=] x2)"
apply (simp add: Temp_t0_def ct_def equal_less_def)
apply (simp add: sf_def x2_def)
done

lemma assist_Q11_1 : "{Pre [&] sf [<=] x2}(Temp_t0) := (ct) {Pre [&] sf [<=] x2; l [=]Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "Temp_t0" and 
               f = "ct" and q = "Pre [&] sf [<=] x2" and 
               G = "l [=] Real 0" in Assign,auto)
prefer 3
apply (rule conjR)
apply (simp add: assist_Q11_1_a assist_Q11_1_b)
apply fast+
apply (unfold Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def,auto)
done


lemma assist_Q11_2_a : "substF([(acc, cv)], Pre) = Pre"
apply (simp add:acc_def cv_def Pre_def)
apply (simp add:level_def x2_def seg1_def seg2_def)
done

lemma assist_Q11_2_b : "substF([(acc, cv)], sf [<=] x2) = (sf [<=] x2)"
apply (simp add:acc_def cv_def equal_less_def)
apply (simp add:sf_def x2_def)
done

lemma assist_Q11_2 : "{Pre [&] sf [<=] x2} acc := (cv){Pre [&] sf [<=] x2; l [=] Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "acc" and 
               f = "cv" and q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in Assign,auto)
prefer 3
apply (simp add: assist_Q11_2_a assist_Q11_2_b)
apply fast
apply (unfold Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def,auto)
done

lemma assist_Q11_3 : "{Pre [&] sf [<=] x2} NON R ''cv'': (cv [>] Real 0 [&] cv [<]  Real maxA) 
       CTCS_Conversion.acc := cv{Pre [&] sf [<=] x2;l [=] Real 0}"
apply (cut_tac p = "Pre [&] sf [<=] x2" and q = "Pre [&] sf [<=] x2" and 
               G = "l [=] Real 0" and b = "cv [>] Real 0 [&] cv [<]  Real maxA"and 
               P = "acc := (cv)" in Nondeterministic,auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] cv [>] Real 0 [&] cv [<] Real maxA" and
               q = "Pre [&] sf [<=] x2" and H= "l [=] Real 0" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "l [=] Real 0" and P = "acc := (cv)" in ConsequenceS, auto)
apply (rule assist_Q11_2)
apply fast
done

lemma step_Q11 : "{Pre [&] sf [<=] x2} Q11 {Pre [&] sf [<=] x2; (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))} "
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [=] Real 0)" and 
               P = "Q11" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q11_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B0" and 
P = "Temp_t0 := ct; (Pre [&] sf [<=] x2, l [=] Real 0) ; NON R ''cv'' : (cv [>]
        Real 0 [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv"
and q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in Condition, auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B0" and b = "[~] B0"
           and P = "(Temp_t0 := ct; (Pre [&] sf [<=] x2, l [=] Real 0);
             NON R ''cv'' : (cv [>] Real 0 [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv)"
           and q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in ConditionT, auto)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B0" and q = "Pre [&] sf [<=] x2" and 
               H = "l [=] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [=] Real 0" and 
               P = "Temp_t0 := ct; (Pre [&] sf [<=] x2, l [=] Real 0) ; 
                NON R ''cv'' : (cv [>] Real 0 [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv" 
                in ConsequenceS, auto)
apply (cut_tac P = "(Temp_t0) := (ct)" and Q = "NON R ''cv'' : (cv [>] Real 0 [&] cv [<] Real maxA) 
                 acc := (cv)" and p = "Pre [&] sf [<=] x2" and m = "Pre [&] sf [<=] x2" and
               H = "l [=] Real 0" and q = "Pre [&] sf [<=] x2" and 
               G = "l [=] Real 0" in Sequence )
apply (rule assist_Q11_1)
apply (rule assist_Q11_3)
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "l [=] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [=] Real 0 [^] l [=] Real 0" and 
               P = "Temp_t0 := ct; (Pre [&] sf [<=] x2, l [=] Real 0) ; 
                NON R ''cv'' : (cv [>] Real 0 [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv" 
                in ConsequenceS, auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule LL4)
apply (rule basic)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] [~] B0" and b = "[~] B0"
           and P = "((Temp_t0) := (ct); (Pre [&] sf [<=] x2,l [=] Real 0) ; 
                NON R ''cv'' : (cv [>] Real 0 [&] cv [<] Real maxA) acc := (cv))"
           and q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in ConditionF, auto)
apply fast+
done

(*************************************)
(*for Q12*)

lemma assist_Q12_1_a : "substF([(Temp_t1, ct)], Pre) = Pre"
apply (simp add: Temp_t1_def ct_def Pre_def seg1_def)
apply (simp add: level_def x2_def seg2_def)
done

lemma assist_Q12_1_b : "substF([(Temp_t1, ct)], sf [<=] x2) = (sf [<=] x2)"
apply (simp add: Temp_t1_def ct_def equal_less_def)
apply (simp add: sf_def x2_def)
done

lemma assist_Q12_1 : "{Pre [&] sf [<=] x2}(Temp_t1) := (ct) {Pre [&] sf [<=] x2; l [=]Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "Temp_t1" and 
               f = "ct" and q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in Assign,auto)
prefer 3
apply (rule conjR)
apply (simp add: assist_Q12_1_a assist_Q12_1_b)
apply fast+
apply (unfold Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def,auto)
done

lemma assist_Q12_2 : "{Pre [&] sf [<=] x2} NON R ''cv'': (cv [>] Real - minA [&] cv [<] Real maxA) acc := (cv){Pre [&] sf [<=] x2;l [=] Real 0}"
apply (cut_tac p = "Pre [&] sf [<=] x2" and q = "Pre [&] sf [<=] x2" and 
               G = "l [=] Real 0" and b = "cv [>] Real - minA [&] cv [<] Real maxA" and
               P = "acc := (cv)" in Nondeterministic,auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] cv [>] Real - minA [&] cv [<] Real maxA" and
               q = "Pre [&] sf [<=] x2" and H= "l [=] Real 0" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "l [=] Real 0" and P = "acc := (cv)" in ConsequenceS, auto)
apply (rule assist_Q11_2)
apply fast
done

lemma step_Q12 : "{Pre [&] sf [<=] x2} Q12 {Pre [&] sf [<=] x2; (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))} "
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [=] Real 0)" and 
               P = "Q12" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q12_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B1" and P = "((Temp_t1) := (ct); 
                 (Pre [&] sf [<=] x2, l [=] Real 0) ; NON R ''cv'': (cv [>] Real - minA [&] 
                 cv [<] Real maxA) acc := cv)" and q = "Pre [&] sf [<=] x2" and 
               G = "l [=] Real 0" in Condition, auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B1" and b = "[~] B1" and
               P = "((Temp_t1) := (ct); (Pre [&] sf [<=] x2,l [=] Real 0);
                 NON R ''cv'': (cv [>] Real - minA [&] cv [<] Real maxA) acc := (cv))"
           and q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in ConditionT, auto)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B1" and q = "Pre [&] sf [<=] x2" and 
               H= "l [=] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [=] Real 0" and
               P = "(Temp_t1) := (ct); (Pre [&] sf [<=] x2,l [=] Real 0); 
                 NON R ''cv'': (cv [>] Real - minA [&] cv [<] Real maxA) acc := (cv)" 
                 in ConsequenceS, auto)
apply (cut_tac P = "(Temp_t1) := (ct)" and Q = "NON R ''cv'': (cv [>] Real - minA [&] 
                 cv [<] Real maxA) acc := (cv)" and p = "Pre [&] sf [<=] x2" and 
               m = "Pre [&] sf [<=] x2" and H = "l [=] Real 0" and
               q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in Sequence )
apply (rule assist_Q12_1)
apply (rule assist_Q12_2)
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "l [=] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [=] Real 0 [^] l [=] Real 0" and 
               P = "Temp_t1 := ct; (Pre [&] sf [<=] x2, l [=] Real 0) ; 
                NON R ''cv'' : (cv [>] Real - minA [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv" 
                in ConsequenceS, auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule LL4)
apply (rule basic)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] [~] B1" and b = "[~] B1" and
               P = "((Temp_t1) := (ct); (Pre [&] sf [<=] x2,l [=] Real 0);
                 NON R ''cv'': (cv [>] Real - minA [&] cv [<] Real maxA) acc := (cv))" and
               q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in ConditionF, auto)
apply fast+
done

(**********************************)
(**for Q13****)

lemma assist_Q13_1_a : "substF([(acc, Real - minA)], Pre) = Pre"
apply (simp add:acc_def Pre_def)
apply (simp add:level_def x2_def seg1_def seg2_def)
done

lemma assist_Q13_1_b : "substF([(acc, Real - minA)], sf [<=] x2) = (sf [<=] x2)"
apply (simp add:acc_def equal_less_def)
apply (simp add:sf_def x2_def)
done


lemma assist_Q13_1 : " {(Pre [&] sf [<=] x2)} acc := (Real - minA) {Pre [&] sf [<=] x2;l [=] Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "acc" and 
               f = "(Real - minA)" and q = "Pre [&] sf [<=] x2" and 
               G = "l [=] Real 0" in Assign)
apply (simp add: Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def)
apply (simp add: assist_Q13_1_a assist_Q13_1_b)
apply fast
apply assumption
done

lemma step_Q13 : "{Pre [&] sf [<=] x2} Q13 {Pre [&] sf [<=] x2; (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))} "
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [=] Real 0)" and 
               P = "Q13" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q13_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B2" and P = "acc := (Real - minA)" and
               q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in Condition, auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2)  [&] [~] B2" and b = "[~] B2" and 
               P = "acc := (Real - minA)" and q = "Pre [&] sf [<=] x2" and 
               G = "l [=] Real 0" in ConditionT, auto)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B2" and q = "Pre [&] sf [<=] x2" and 
               H= "l [=] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [=] Real 0" and
               P = "acc := (Real - minA)" in ConsequenceS, auto)
apply (rule assist_Q13_1)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2)  [&] [~] [~] B2" and b = "[~] B2" and 
               P = "acc := (Real - minA)" and
               q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in ConditionF,auto)
apply fast+
done

(**********************)
(* for Q3 *)

lemma assist_Q3 : "|- Pre [&] sf [<=] x2 [-->] [~] [~] B4"
apply (simp add:Pre_def B4_def)
apply (rule impR)
apply (rule notR)
apply (rule notL)
apply (rule disjR)
apply (rule thinR)
apply fast
done

lemma step_Q3 : "{Pre [&] sf [<=] x2} Q3 {Pre [&] sf [<=] x2; (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [=] Real 0)" and 
               P = "Q3" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q3_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B4" and P = "level := (Real 3)"
           and q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in ConditionF)
apply (rule assist_Q3)
apply (fast)+
apply assumption
done

(**************)
(** for Q4**)

lemma assist_Q4_a : "(substF([(md, snd(snd(snd(hd(MA)))))], Pre)) = (Pre)"
apply (unfold Pre_def md_def)
apply (unfold level_def x2_def MA_def seg1_def seg2_def, auto)
done

lemma assist_Q4_b : "substF([(md, snd(snd(snd(hd(MA)))))], sf [<=] x2) = (sf [<=] x2)"
apply (unfold md_def equal_less_def)
apply (unfold sf_def x2_def MA_def, auto)
done

lemma assist_Q4 : "{(Pre [&] sf [<=] x2)} md := (snd(snd(snd(hd(MA)))))
                     {Pre [&] sf [<=] x2;l [=] Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "md" and 
               f = "snd(snd(snd(hd(MA))))" and q = "Pre [&] sf [<=] x2" and 
               G = "l [=] Real 0" in Assign)
apply (simp add: Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def)
apply (rule conjR)
apply (simp add: assist_Q4_a assist_Q4_b)
apply fast+
apply assumption
done

lemma step_Q4 : "{Pre [&] sf [<=] x2} Q4 {Pre [&] sf [<=] x2; (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [=] Real 0)" and 
               P = "Q4" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q4_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B5" and 
               P = "(md) := (snd(snd(snd(hd(MA)))))" and q = "Pre [&] sf [<=] x2" and 
               G = "l [=] Real 0" in Condition, auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2)  [&] [~] B5" and b = "[~] B5" and 
               P = "(md) := (snd(snd(snd(hd(MA)))))" and
               q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in ConditionT, auto)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B5" and q = "Pre [&] sf [<=] x2" and 
               H= "l [=] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [=] Real 0" and
               P = "md := (snd(snd(snd (hd(MA)))))" in ConsequenceS, auto)
apply (rule assist_Q4)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2)  [&] [~] [~] B5" and b = "[~] B5" and 
               P = "(md) := (snd(snd(snd(hd(MA)))))" and
               q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in ConditionF,auto)
apply fast+
done
(************************)
(** composite: move and Q11-Q4**)

lemma DCR3_assist: "(high D) [^] (high D) |- (high D) [^] (high D) ==> (high D) [^] (high D) |- (high D)"
  apply (rule DCR3)
  apply fast
  done

lemma step_part1_comp_assist: "|- (l [=] Real 0 [|] high(Pre [&] sf [<=] x2)) [^]
                      (l [=] Real 0 [|] high(Pre [&] sf [<=] x2))
                    [-->] l [=] Real 0 [|] high(Pre [&] sf [<=] x2)"
apply (rule impR)
apply (rule LT1)
apply (rule LT1a)
apply (rule LL4)
apply (rule disjR)
apply fast
apply (rule LL3a)
apply (rule disjR)
apply fast
apply (rule LT1a)
apply (rule LL4)
apply (rule disjR)
apply fast
apply (rule disjR)
apply (rule thinR)
apply (cut_tac D="(Pre [&] sf [<=] x2)" in DCR3_assist,auto)
apply fast
done

lemma step_part1_comp : "{Init [&] Pre} 
        Move; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q11; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))) ; 
        Q12; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4 {Pre [&] sf [<=] x2; (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))}"
apply (cut_tac p = "Init [&] Pre" and P = "Move" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q11; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))) ; 
        Q12; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" in Sequence)
apply (rule step_continuous)
apply (cut_tac p = "Pre [&] sf [<=] x2" and P = "Q11" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q12; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" in Sequence)
apply (rule step_Q11)
apply (cut_tac p = "Pre [&] sf [<=] x2" and P = "Q12" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" in Sequence)
apply (rule step_Q12)
apply (cut_tac p = "Pre [&] sf [<=] x2" and P = "Q13" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" in Sequence)
apply (rule step_Q13)
apply (cut_tac p = "Pre [&] sf [<=] x2" and P = "Q3" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q4" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" in Sequence)
apply (rule step_Q3)
apply (rule step_Q4)
apply (rule ConsequenceS,auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule step_part1_comp_assist)
apply (rule ConsequenceS,auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule step_part1_comp_assist)
apply (rule ConsequenceS,auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule step_part1_comp_assist)
apply (rule ConsequenceS,auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule step_part1_comp_assist)
apply (rule ConsequenceS,auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule step_part1_comp_assist)
done

(*********************************)
(**with the communication**)

(*Assert B6 holds.*)
lemma Assert1 : "(Pre [&] sf [<=] x2)|- B6"
apply (rule conjL)
apply (rule exchL)
apply (rule thinL)
apply (simp add:Pre_def B6_def seg1_def level_def x2_def)
apply (rule conjL)
apply (rule exchL)
apply (rule thinL)
apply (rule disjR)
apply (rule exchR)
apply (rule thinR)
apply (rule Trans1,auto)
done

lemma step_parallel: "{Init [&] Pre, WTrue} 
        ((Move; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q11; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))) ; 
        Q12; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4) || Skip) {Pre [&] sf [<=] x2, WTrue;  
                 (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))), (l [=] Real 0)}"
apply (cut_tac px = "Init [&] Pre" and py = "WTrue" and 
        Px = "(Move; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q11; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))) ; 
        Q12; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4)" and Py = "Skip" and 
        qx = "Pre [&] sf [<=] x2" and qy = "WTrue" and 
        Hx = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and 
        Hy = "(l [=] Real 0)" in Parallel2, auto)
apply (rule step_part1_comp)
apply (rule Skip)
  apply fast
    done

(*********************************)
(**communication with sequential composition**)

lemma assist_comm_sequential : "substF([((BVar bw), Bool False)], (BVar bw) [=] (Bool False)) = (Bool False [=] Bool False)"
apply (unfold substF_def, auto)
done

lemma step_comm_sequential: "{Init [&] Pre, WTrue} 
        (((Move; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q11; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))) ; 
        Q12; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4); (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
       (chw !! (Bool False))) || (Skip; (WTrue, l [=] Real 0); chw ?? (BVar bw))) 
       {Pre [&] sf [<=] x2, ((BVar bw) [=] (Bool False));
       (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))), (l [=] Real 0) [|] (high (WTrue))}"
apply (cut_tac 
        Px = "((Move; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q11; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))) ; 
        Q12; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4); (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        (chw !! (Bool False)))" and 
        Py = "Skip; (WTrue, l [=]  Real 0) ; chw??(BVar bw)" and
        p = "Init [&] Pre" and r = "WTrue" and
        q = "Pre [&] sf [<=] x2" and s = "BVar bw [=] Bool False" and
        H = "l [=] Real 0 [|] (high (Pre [&] sf [<=] x2))" and 
        G = "l [=] Real 0 [|] high WTrue" and
        px = "Init [&] Pre" and py = "WTrue" and 
        qx = "Pre [&] sf [<=] x2" and qy = "BVar bw [=] Bool False" and 
        Hx = " (l [=] Real 0 [|] (high (Pre [&] sf [<=] x2))) [&] WTrue" and 
        Hy = "(l [=] Real 0 [|] high WTrue) [&] WTrue" in ConsequenceP, auto) 
apply (cut_tac px = "Init [&] Pre" and py = " WTrue" and
        Px = "Move; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q11; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))) ; 
        Q12; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4" and qx = "Pre [&] sf [<=] x2" and
        Hx = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and
        Py = " Skip" and qy = "WTrue" and
        Hy = "l [=] Real 0" and ch = "chw" and x = "(BVar bw)" and e = "Bool False" and
        rx = "Pre [&] sf [<=] x2" and ry = "((BVar bw) [=] (Bool False))" and
        Gx = " (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and 
        Gy = "(l [=] Real 0) [|] (high (WTrue))" and
        H = "WTrue" in Communication)
defer
apply (rule step_parallel)
apply (rule conjR)
apply fast
apply (rule impR)
apply (simp add:assist_comm_sequential)
apply fast
apply (rule conjR)
apply (rule impR)
apply (rule disjR)
apply (rule thinR)
apply (rule LT1)
apply (rule LL3a)
apply fast
apply (cut_tac S = "Pre [&] sf [<=] x2" in DCL3,auto)
apply (rule basic)
apply (rule impR)
apply (rule disjR)
apply (rule LL3a)
apply (fast)
apply (rule impR)
apply fast
apply (rule conjR)
apply fast
apply (rule conjR)
apply fast
apply (rule conjR)
apply fast
apply (rule conjR)
apply fast
apply (rule conjR)
apply fast+
done

(**************)
(** for Q5**)

lemma assist_Q5 : "|- Pre [&] sf [<=] x2 [-->] [~] [~] B6"
apply (rule impR)
apply (rule notR)
apply (rule notL)
apply (simp add:Pre_def B6_def level_def)
apply (rule disjR)
apply (rule exchR)
apply (rule thinR)
apply (rule conjL)
apply (rule exchL)
apply (rule conjL)
apply (rule thinL)
apply (rule exchL)
apply (rule thinL)
apply (rule Trans1,auto)
done

lemma step_Q5 : "{Pre [&] sf [<=] x2} Q5 {Pre [&] sf [<=] x2; (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))} "
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [=] Real 0)" and 
               P = "Q5" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q5_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B6" and 
               P = "((Temp_t2) := (ct); (WTrue, WTrue) ; chd??br; (WTrue,
                       WTrue) ; IF (br [=] Bool True) (fst(hd(tl(MA)))) := (Real 40))"
           and q = "Pre [&] sf [<=] x2" and G = "l [=] Real 0" in ConditionF,auto)
apply (rule assist_Q5)
apply fast+
done


(*************************)
(**for driver process**)

lemma step_driver : "{BVar bw [=] (Bool False)} P {BVar bw [=] (Bool False); (l [=] Real 0) [|] (high WTrue)}"
apply (cut_tac p = "BVar bw [=] (Bool False)" and q = "BVar bw [=] (Bool False)" and 
               H = "(l [=] Real 0) [|] (high WTrue)" and 
               px = "BVar bw [=] (Bool False)" and qx = "BVar bw [=] (Bool False)" and 
               Hx = "(l [=] Real 0)" and 
               P = "P" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:P_def)
apply (cut_tac p = "BVar bw [=] Bool False" and b = "(BVar bw [=] Bool True)" and 
               P = "(chd!!(Bool True)[[chd!!(Bool False))" and
               q = "BVar bw [=] Bool False" and G = "l [=] Real 0" in ConditionF)
apply (rule impR)
apply (rule Trans1,auto)
apply fast+
done


(***************************)
(**for once, repetition in the following**)


lemma assist_System_proof : "|- (l [=] Real 0 [|] high (p)) [^] (l [=] Real 0 [|] high (p)) [-->] (l [=] Real 0 [|] high (p))"
apply (rule impR)
apply (rule LT1)
apply (rule LT1a)
apply (rule LL4)
apply fast
apply (rule LL3a)
apply fast
apply (rule LT1a)
apply (rule LL4)
apply fast
apply (rule disjR)
apply (rule thinR)
apply (cut_tac S = "p" in DCL3,auto)
apply (rule basic)
done

lemma step_System_once : "{Init [&] Pre, WTrue} Train||Driver {Pre [&] sf [<=] x2, WTrue;  
                     (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))), (l [=] Real 0) [|] (high (WTrue))}"
apply (cut_tac p = "Init [&] Pre" and r = "WTrue" and
               Px = "Train" and Py = "Driver" and
               q = "Pre [&] sf [<=] x2" and s = "WTrue" and 
               H = "l [=] Real 0 [|] high (Pre [&] sf [<=] x2)" and 
               G = "l [=] Real 0 [|] high (WTrue)" and px = "Init [&] Pre" and 
               py = "WTrue" and qx = "Pre [&] sf [<=] x2" and  
               qy = "BVar bw [=] Bool False" and  
               Hx = "(l [=] Real 0 [|] high (Pre [&] sf [<=] x2)) [^] 
                     (l [=] Real 0 [|] high (Pre [&] sf [<=] x2))" and  
               Hy = "(l [=] Real 0 [|] high (WTrue)) [^] (l [=] Real 0 [|] high (WTrue))"  
               in ConsequenceP,auto)
apply (simp add:Train_def Driver_def Imd_def SP1_def)
apply (cut_tac px = "Init [&] Pre" and py = "WTrue" and
        Px = "((Move; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q11; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q12; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q13; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))));
        Q3; (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
        Q4); (Pre [&] sf [<=] x2, (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))); 
       (chw !! (Bool False)))" and 
        qx = "Pre [&] sf [<=] x2" and
        Hx = "l [=] Real 0 [|] high (Pre [&] sf [<=] x2)" and Qx = "Q5" and
        Py = "Skip; (WTrue, l [=] Real 0) ; chw??(BVar bw)" and 
        qy = "BVar bw [=] Bool False" and
               Hy = " l [=] Real 0 [|] high (WTrue)" and Qy = "P" and
               rx = "Pre [&] sf [<=] x2" and ry = "BVar bw [=] Bool False" and
               Gx = "l [=] Real 0 [|] high (Pre [&] sf [<=] x2)" and 
               Gy = " l [=] Real 0 [|] high (WTrue)" in Parallel1)
apply (rule step_comm_sequential)
apply (rule step_Q5)
apply (rule step_driver)
apply assumption
apply (rule conjR)
apply fast
apply (rule conjR)
apply fast
apply (rule conjR)
apply fast
apply (rule conjR)
apply fast
apply (rule conjR)
apply (rule assist_System_proof)
apply (rule assist_System_proof)
done

(***************************)
(**for repetition**)

(* All the fact* are create to support the steps, and all the 10 steps fforms the proof.*)
lemma System_proof : "{Init [&] Pre, WTrue} System {Pre [&] sf [<=] x2, 
       WTrue; (l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2))), 
       (l [=] Real 0) [|] (high (WTrue))}"
  apply (simp add:System_def)
  (*  {px, py}Px* || Py*{px, py ; Hx, Hy} *)
  thm Repetition[no_vars]
apply (cut_tac px = "Init [&] Pre" and py = "WTrue" and 
               Px = "Train" and Py = "Driver" and 
               qx = "Pre [&] sf [<=] x2" and qy = "WTrue" and 
               Hx = "(l [=] Real 0) [|] (high (Pre [&] (sf [<=] x2)))" and 
               Hy = "l [=] Real 0 [|] (high WTrue)" in Repetition,auto)
apply (rule step_System_once)
apply (rule assist_System_proof)
apply (rule assist_System_proof)
done

end
