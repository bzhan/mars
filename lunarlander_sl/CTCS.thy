theory CTCS
  imports BigStep
begin


definition var2exp :: "var \<Rightarrow> exp" where
  "var2exp x = (\<lambda>s. s x)"

definition fAnd :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixr "[&]" 35) where
  "P [&] Q \<equiv> \<lambda>s. P s \<and> Q s"
definition fNot :: "fform \<Rightarrow> fform"  ("[\<not>]_" [40] 40) where
  "[\<not>]P \<equiv> \<lambda>s. \<not> P s"

 
type_synonym  segT = "var * var * exp * exp" \<comment> \<open>Each segment contains v1, v2, s, and mode\<close>
type_synonym  MAT = "segT list"

consts
bw  :: var  \<comment> \<open>boolean variable recording Bi\<close>
MA_n :: "MAT"
minA :: real \<comment> \<open>Min acceleration, CONSTANT\<close>
maxA :: real \<comment> \<open>Max acc, CONSTANT\<close>
level :: var
md :: var \<comment> \<open>mode of current segment\<close>
lub :: var \<comment> \<open>whether driver confirms the level upgrade from Train\<close>
x :: var
y :: var

br :: var  \<comment> \<open>whether the driver confirms\<close>
seg_cur :: segT  \<comment> \<open>current segment of MA\<close>
eoa1 :: var  \<comment> \<open>end of current MA in RBC\<close>
eoa2 :: var  \<comment> \<open>end of current MA in TCC\<close>
eoa :: var  \<comment> \<open>end of current MA in Train\<close>


text \<open>record the boolean values of B3, B6 and B7\<close>
consts
b3 :: var
b6 :: var
b7 :: var

definition vel :: var where "vel = CHR ''v''"
definition acc :: var where "acc = CHR ''a''"
definition sf :: var where "sf = CHR ''s''"
definition x2 :: var where "x2 = CHR ''x''"
\<comment> \<open>Channel sending from train to driver\<close>
definition ch_T2D :: "cname" where "ch_T2D = ''t2d''" 
\<comment> \<open>Channel sending from driver to train\<close>
definition ch_D2T :: "cname" where "ch_D2T = ''d2t''"  
\<comment> \<open>sending from train to RBC for level upgrade\<close>
definition ch_T2R :: "cname" where "ch_T2R = ''t2r''"  
\<comment> \<open>sending from train to RBC for MA extension\<close>
definition ch_T2R1 :: "cname" where "ch_T2R1 = ''t2r1''" 
\<comment> \<open>sending from train to RBC for MA extension\<close>
definition ch_T2R2 :: "cname" where "ch_T2R2 = ''t2r2''" 
\<comment> \<open>sending from RBC to train for level upgrade\<close>
definition ch_R2T :: "cname" where "ch_R2T = ''r2t''"
\<comment> \<open>sending from RBC to train for level upgrade\<close>
definition ch_R2T1 :: "cname" where "ch_R2T1 = ''r2t1''" 
\<comment> \<open>sending from RBC to train for MA extension\<close>
definition ch_R2T2 :: "cname" where "ch_R2T2 = ''r2t2''"
\<comment> \<open>sending from Train to TCC\<close>
definition ch_T2T1 :: "cname" where "ch_T2T1 = ''t2t1''"
\<comment> \<open>sending from TCC to Train\<close>
definition ch_T2T2 :: "cname" where "ch_T2T2 = ''t2t2''"
\<comment> \<open>sending from TCC to Train\<close>
definition ch_T2T3 :: "cname" where "ch_T2T3 = ''t2t3''"



consts
v11 :: var
v12 :: var
v21 :: var
v22 :: var
definition seg1 :: "segT" where
  "seg1 = (v11, v12, \<lambda> _ .300, \<lambda> _. 0)"
definition seg2 :: "segT" where
  "seg2 = (v21, v22, \<lambda> _. 600, \<lambda> _. 1)"
definition MA :: "MAT" where
  "MA = seg1 # seg2 # MA_n"

fun end_of_MA :: "MAT \<Rightarrow> state \<Rightarrow> real" where
  "end_of_MA [] s = 0" |
  "end_of_MA [(a, b, c, d)] s = c s" |
  "end_of_MA (ma # MAs) s = (if (MAs = []) then end_of_MA [ma] s
                               else end_of_MA MAs s)"

 
fun seg_equal :: "segT \<Rightarrow> segT \<Rightarrow> fform" where
  "seg_equal (a1, b1, c1, d1) (a2, b2, c2, d2) = (\<lambda> s. s a1  = s a2  \<and> s b1  = s b2  \<and>
      c1 s = c2 s \<and> d1 s = d2 s)"

(* The driver process*)
(****************)
definition P :: "proc" where
  "P =  (IF (\<lambda> s. s bw = 1) 
           IChoice [Cm (ch_D2T[!] (\<lambda> _. 1)), Cm (ch_D2T[!] (\<lambda> _. 0))]
           Skip
        )"

definition Driver :: "proc" where
  "Driver = Cm (ch_T2D [?] bw);  P"

text \<open>The RBC process for level upgrade\<close>
definition RBC_lu :: proc where
  "RBC_lu = Cm (ch_T2R [?] bw); 
            IF (\<lambda> s. s bw = 1)
              (IChoice [Cm (ch_R2T[!] (\<lambda> _. 1)), Cm (ch_R2T[!](\<lambda> _. 0))]; Cm (ch_R2T1[!] (\<lambda> _. 300)); Cm (ch_R2T1[!] (\<lambda> _. 600))) 
              Skip"




(* The train process*)
(****************)

text \<open>checkV1, checkV2: check the given speed is less than v1 and v2 of current segment.\<close>
fun checkV1 :: "segT => var => fform" where
  "checkV1 (a, b, c, d) v = (\<lambda> s. s v < s a)" 
 
fun checkV2 :: "segT => var => fform" where
  "checkV2 (a, b, c, d) v = (\<lambda> s. s v < s b)" 
 

fun checkS :: "segT => var => var => fform" where
  "checkS (a, b, c, d) v f = ((\<lambda> s. (s v * s v + 2 * minA * s f < s a * s a
             + 2 * minA * fst (snd (snd seg_cur)) s)))"
 
definition B0 :: "fform" where
  "B0 = (\<lambda> s. s vel \<ge> 0 \<or> s acc > 0)"

definition P0 :: "proc" where
  "P0 = (acc ::= (\<lambda> _. maxA))"

definition B1 :: "fform" where
  "B1 = (\<lambda> s. (checkV2 seg_cur vel) s \<or> s acc < 0)"

definition P1 :: "proc" where
  "P1 = (acc ::= (\<lambda> _. -minA))"

definition B2 :: "fform" where
  "B2 = (\<lambda> s. ((checkV1 seg_cur vel) s & (checkS seg_cur vel sf) s) \<or> s acc = -minA)" 

definition P2 :: "proc" where
  "P2 = (acc ::= (\<lambda> _. -minA))"

definition B3 :: "fform" where
  "B3 = (\<lambda> s. s level \<noteq> 2)"

definition P3 :: proc where 
  "P3 = Cm (ch_R2T [?] lub);  Cm (ch_R2T1 [?] x);  Cm (ch_R2T1 [?] y); 
        IF (\<lambda> s. s lub = 1) (level ::= (\<lambda> _. 2.5))  Skip"
 
definition B4 :: "fform" where
  "B4 = (\<lambda> s. (s level \<noteq> 2.5) \<or>  (s sf \<le>  s x2))"

definition P4 :: proc where
  "P4 = (level ::= (\<lambda> _.  3))"

definition B5 :: "fform" where
  "B5 = (\<lambda> s. s md =  (snd ( snd ( snd (hd(MA)))) s))"

definition P5 :: proc where
  "P5 = (md ::= (snd (snd (snd seg_cur))))"

definition B6 :: "fform" where
  "B6 == \<lambda> s. \<not> ((s level = 3) \<and>
    ((1 = ((snd (snd (snd (hd (tl (MA))))))) s))
    \<and> (s br = 0)
    \<and> ((((fst (snd (snd (hd (MA))))) s - s sf) > 0)
    \<and> (((fst (snd (snd (hd (MA))))) s - s sf)< 300)))"

definition P6 :: proc where
  "P6 = (Cm (ch_D2T [?] br); IF (\<lambda> s. s br = 1) ((fst (seg2)) ::=  (\<lambda> _. 40)) Skip)"

definition B7 :: fform where
  "B7 = (\<lambda> s. s sf \<le> fst (snd (snd seg_cur)) s)"

text \<open>The RBC process for MA extension\<close>
definition RBC_ma :: proc where
  "RBC_ma = Cm (ch_T2R1 [?] bw); 
            IF (\<lambda> s. s bw = 1) (Cm (ch_T2R2 [?] eoa1); Cm (ch_R2T2[!](\<lambda> s. (s eoa1 + 1000))))
               Skip"

text \<open>The TCC process for MA extension\<close>
definition TCC_ma :: proc where
  "TCC_ma = Cm (ch_T2T1 [?] bw); 
            IF (\<lambda> s. s bw = 1) (Cm (ch_T2T2 [?] eoa2); Cm (ch_T2T3[!](\<lambda> s. (s eoa2 + 1000))))
               Skip"

definition P7 :: proc where
  "P7 = Cm (ch_T2R2 [!] (\<lambda> s. end_of_MA MA s)); Cm (ch_R2T2 [?] eoa);
        Cm (ch_T2T2 [!] (\<lambda> s. end_of_MA MA s)); Cm (ch_T2T3 [?] eoa)"

definition B :: fform where
  "B == (B1 [&] B2 [&] B3 [&] B4 [&] B5 [&] B6 [&] B7)"


text \<open>Invariant for Train movement\<close>
definition inv :: fform where 
  "inv = (checkS seg_cur vel sf)"

text \<open>Precondition\<close>
definition Pre :: fform where
  "Pre = (\<lambda> s. (s level = 2.5)
      \<and> (((fst (snd (snd (seg1))))) s = s x2)
      \<and> (((snd (snd (snd (seg1))))) s = 0)
      \<and> (((snd (snd (snd (seg2))))) s = 1)
      \<and> ((s (fst (seg2)))  = 0)
      \<and> (s (fst (seg1)) = 200)
      \<and> (s (fst (snd (seg1))) = 250))"
definition Init :: fform where
  "Init = ((\<lambda> s. (s x2 - s sf > 300)) [&] B1 [&] B2 [&] checkS seg2 vel sf [&] (seg_equal seg_cur seg1))"
 
text \<open>The continuous part\<close>
definition Move :: proc where
  "Move = Cont (ODE (\<lambda> x. if x = sf then (var2exp vel)
                          else if x = vel then (var2exp acc)
                          else (\<lambda>_. 0))) B"
 
definition Train :: proc where
  "Train = Move; (IF B3 b3 ::= (\<lambda>_. 0)  b3 ::= (\<lambda>_. 1)); Cm (ch_T2R [!] (\<lambda> s. s b3));
           (IF B6 b6 ::= (\<lambda>_. 0)  b6 ::= (\<lambda>_. 1)); Cm (ch_T2D [!] (\<lambda> s. s b6));
           (IF B7 b7 ::= (\<lambda>_. 0)  b7 ::= (\<lambda>_. 1)); Cm (ch_T2R2 [!] (\<lambda> s. s b7)); Cm (ch_T2T1 [!] (\<lambda> s. s b7));
          (IF ([\<not>]B0) P0 Skip);
          (IF ([\<not>]B1) P1 Skip); 
          (IF ([\<not>]B2) P2 Skip);
          (IF ([\<not>]B3) P3 Skip);
          (IF ([\<not>]B4) P4 Skip);
          (IF ([\<not>]B5) P5 Skip);
          (IF ([\<not>]B6) P6 Skip);
          (IF ([\<not>]B7) P7 Skip)"

definition CTCS :: pproc where
  "CTCS = PProc [Rep Train, Rep Driver, Rep TCC_ma, Rep RBC_ma, Rep RBC_lu]"



fun state_of_trace :: "trace \<Rightarrow> time \<Rightarrow> state" where
  "state_of_trace (Trace s blks) t = state_of_blocks s blks t"


theorem CTCS_conversion:
  "ParValid 
     (\<lambda> t. ((t = ParTrace sl []) \<and> Pre (hd(sl)) \<and> Init (hd(sl))))
     (CTCS)
     (\<lambda> t. \<exists> tr. combine_par_trace tr t \<and> (\<forall> a. (\<lambda> s. s sf \<le> s x2) (state_of_trace (hd (tr)) a)))"

  sorry
end