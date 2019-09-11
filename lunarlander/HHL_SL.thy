section \<open>Abstract syntax for Hybrid CSP.\<close>

theory HHL_SL
  imports Op_SL
begin

type_synonym now_dash = real
type_synonym 'a dform = "'a history \<Rightarrow> now \<Rightarrow> now_dash \<Rightarrow> bool"

(*
definition semd :: "'a history \<Rightarrow> now \<Rightarrow> now_dash \<Rightarrow> 'a dform \<Rightarrow> bool" ("_, [_, _] |= _" 50) where
  "h, [n, m] |= H \<equiv> H h n m"
*)

text \<open>The dform formula is only decided by the interval between now and now_dash\<close>
definition well_DC :: "'a dform \<Rightarrow> bool" where
"well_DC df == (\<forall> now now' h h'. (now \<le> now' \<and> (\<forall>t. t > now \<and> t < now' \<longrightarrow> h t = h' t)) \<longrightarrow> df h now now' = df h' now now')" 
 
subsection \<open>Duration Calculus operators and lemmas proved\<close>
text \<open>almost P, P holds everywhere except for the rightmost point, not almost everywhere, over the interval.
The reason is that, for continuous evolution, it escapes whenever a violation is met.
A special case is that, if using almost everywhere, the differential cut rule will not hold anymore.\<close>
definition almost :: "'a fform \<Rightarrow> 'a dform"  where 
"almost P \<equiv> \<lambda>h n nd. (nd-n > 0) \<and> (\<forall>t. t \<ge> n \<and> t < nd \<longrightarrow> P (h (t)))"

definition chop :: "'a dform \<Rightarrow> 'a dform \<Rightarrow> 'a dform"  (infixr "[^]" 40) where
  "H [^] M \<equiv> \<lambda>h n nd. \<exists>nm. nm \<ge> n \<and> nm \<le> nd \<and> H h n nm \<and> M h nm nd"

text \<open>The length of the interval l is equal to, greater than, less than T.\<close>
definition elE :: "real \<Rightarrow> 'a dform" where
  "elE T \<equiv> \<lambda>h n nd. (nd-n) = T"
definition elG :: "real \<Rightarrow> 'a dform" where
  "elG T \<equiv> \<lambda>h n nd. (nd-n) > T"
definition elL :: "real \<Rightarrow> 'a dform" where
  "elL T \<equiv> \<lambda>h n nd. (nd-n) < T"

definition dAnd :: "'a dform \<Rightarrow> 'a dform \<Rightarrow> 'a dform"  (infixr "[[&]]" 35) where
  "P [[&]] Q \<equiv> \<lambda>h n m. P h n m \<and> Q h n m"
definition dOr :: "'a dform \<Rightarrow> 'a dform \<Rightarrow> 'a dform"  (infixr "[[|]]" 30) where
  "P [[|]] Q \<equiv> \<lambda>h n m. P h n m \<or> Q h n m"
definition dNot :: "'a dform \<Rightarrow> 'a dform"  ("[[\<not>]]_" 40) where
  "[[\<not>]]P \<equiv> \<lambda>h n m. \<not> P h n m"
definition dImp :: "'a dform \<Rightarrow> 'a dform \<Rightarrow> 'a dform"  (infixr "[[\<longrightarrow>]]" 25) where
  "P [[\<longrightarrow>]] Q \<equiv> \<lambda>h n m. P h n m \<longrightarrow> Q h n m"

declare almost_def [simp]
declare chop_def [simp]
declare elE_def [simp]
declare elG_def [simp]
declare elL_def [simp]

text \<open>True holds almost everywhere\<close>
lemma almostf:
  "\<forall>h n nd. nd - n \<le> 0 \<or> almost fTrue h n nd"
  apply simp
  by (metis dense not_le)

text \<open>almost P \<Leftrightarrow> chop almost P almost P\<close>
lemma chopfb:
  "chop (almost P) (almost P) h n nd \<Longrightarrow> almost P h n nd"
  unfolding chop_def almost_def
  apply (rule conjI, auto)
  by (metis (poly_guards_query) less_eq_real_def less_trans not_less)

text \<open>chop (almost P \/ l = 0) (almost P \/ l = 0) ==> almost P \/ l = 0 \<close>
lemma chopfor:
  "chop (elE 0 [[|]] almost P) (elE 0 [[|]] almost P) h n nd \<Longrightarrow> (elE 0 [[|]] almost P) h n nd"
  unfolding dOr_def
  apply (rule disjCI, auto)
  by (metis less_eq_real_def less_trans not_less)

lemma chopf:
  "almost P h n nd \<Longrightarrow> chop (almost P) (almost P) h n nd"
  unfolding almost_def chop_def
  apply (rule exI[where x = "(n+nd)/2"])
  by auto

lemma chop0L: "chop (almost P) (elE 0) h n nd \<Longrightarrow> almost P h n nd"
  by auto

lemma chop0R: "almost P h n nd \<Longrightarrow> chop (almost P) (elE 0) h n nd"
  by auto

lemma chop_well_DC: "well_DC Ha \<Longrightarrow> well_DC Hb \<Longrightarrow> well_DC (Ha [^] Hb)"
  unfolding chop_def well_DC_def
  apply auto
  apply smt
  apply smt
  done 
 
text \<open>Monotonicity: s \<Rightarrow> t \<Longrightarrow> almost s \<Rightarrow> almost t\<close>
lemma almostmono:
  "\<forall>s. P s \<longrightarrow> Q s \<Longrightarrow> \<forall>h n nd. almost P h n nd \<longrightarrow> almost Q h n nd"
  apply auto
  by (metis old.prod.exhaust)
 
lemma almostint:
  "now < nowf \<Longrightarrow> \<forall>t. (t\<ge>now \<and> t<nowf) \<longrightarrow> P (f t) \<Longrightarrow> almost P f now nowf"
  by auto



subsection \<open>Inference rules for Hybrid CSP: Hybrid Hoare Logic rules\<close>

text \<open>Specification\<close>
definition Valid :: "'a :: finite fform \<Rightarrow> 'a proc \<Rightarrow> 'a fform \<Rightarrow> 'a dform \<Rightarrow> bool" ("\<Turnstile> {_}_{_; _}" 80) where
  "\<Turnstile> {p} c {q; H} \<longleftrightarrow> (\<forall>now h now' h'. semB c now h now' h' \<longrightarrow> p (h now) \<longrightarrow> (q (h' now') \<and> H h' now now'))"

definition ValidP :: "'a :: finite fform \<Rightarrow> 'a fform \<Rightarrow> 'a procP \<Rightarrow> 'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a dform \<Rightarrow> 'a dform \<Rightarrow> bool"
  ("\<Turnstile> {_, _}_{_, _; _, _}" 80) where
  "\<Turnstile> {pa, pb} c {qa, qb; Ha, Hb} \<longleftrightarrow> (\<forall>nowp nowq fp fq nowp' nowq' fp' fq'.
    semBP c nowp fp nowq fq nowp' fp' nowq' fq'  \<longrightarrow> 
    pa (fp(nowp)) \<longrightarrow> pb (fq(nowq)) \<longrightarrow> 
    qa (fp'(nowp')) \<and> qb (fq'(nowq')) \<and> (Ha fp' nowp nowp') \<and> (Hb fq' nowq nowq'))"

 
text \<open>Partial correctness rules\<close>
inductive HHL_partial :: "'a :: finite fform \<Rightarrow> 'a proc \<Rightarrow> 'a fform \<Rightarrow> 'a dform \<Rightarrow> bool" ("\<turnstile> {_}_{_; _}" 80) where
  skipR: "\<forall> s h now now'. (p s \<longrightarrow> q s) \<and> ((elE 0) h now now'\<longrightarrow> H h now now') \<Longrightarrow> well_DC H \<Longrightarrow>
         \<turnstile>{p} Skip {q; H}"
| assignR:"(\<forall> s. p s \<longrightarrow> (q (update_fst s x (evalE e s))))
               \<and> (\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')) \<Longrightarrow> well_DC H \<Longrightarrow>
         \<turnstile> {p} (x := e) {q; H}"
| seqR: "\<turnstile> {p} P {m; H} \<Longrightarrow> \<turnstile> {m} Q {q; G} ==> (\<forall> h m n. (H [^] G) h m n \<longrightarrow> M h m n) \<Longrightarrow> well_DC M \<Longrightarrow>
         \<turnstile> {p} P;  Q {q; M}"  
| condTR: " ((\<forall> s. p s \<longrightarrow> ( b s)) \<and> \<turnstile> {p} P {q; H}) \<Longrightarrow> \<turnstile> {p} IF b P {q; H}"
| condFR: "((\<forall> s. p s \<longrightarrow> (q s \<and> (\<not>   b s))) \<and> (\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')))
            \<Longrightarrow> well_DC H ==> \<turnstile> {p} IF b P {q; H}"
| IChoiceR: "\<turnstile> {p} P {m; H} \<Longrightarrow> \<turnstile> {p} Q {q; G} ==> \<turnstile> {p} P \<sqinter> Q {m [|] q; H [[|]] G}"




| repetR: "\<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m \<Longrightarrow> \<turnstile> {I} P {I; H}  \<Longrightarrow> 
           \<turnstile> {I} P*&&I {I; (H [[|]] (elE 0))} "

| consequenceR: "\<turnstile> {px} P {qx; Hx} \<Longrightarrow> (\<forall> s. p s \<longrightarrow> px s) \<Longrightarrow> (\<forall> s. qx s \<longrightarrow> q s) \<Longrightarrow>
                 (\<forall> h n m. Hx h n m \<longrightarrow> H h n m) \<Longrightarrow> well_DC H \<Longrightarrow> \<turnstile> {p} P {q; H}"

| continTR: "\<forall> s. (Inv [&][\<not>]b) s \<longrightarrow> q s \<Longrightarrow>
             \<forall> s. p s  \<longrightarrow> ODE_inv_in_dom ode s b Inv \<Longrightarrow>
             \<forall> h now now'. (almost (Inv [&]  b) [[|]] elE 0) h now now' \<longrightarrow>
               H h now now' \<Longrightarrow> well_DC H  \<Longrightarrow> 
             \<turnstile> {p} <ode && Inv&b> {q; H}"

|diffCut: "\<turnstile> {p} <ode && Inv&b> {I; almost I [[|]] elE 0} \<Longrightarrow> 
               \<turnstile> {p} <ode && Inv&(b[&]I)> {q; H} \<Longrightarrow>
               \<turnstile> {p} <ode && Inv&b> {q; H}"

(*
Different from Platzer's: This is not valid when b always be true. 
|diffCut2: "\<turnstile> {p} <ode && Inv&b> {I; almost I [[|]] elE 0} \<Longrightarrow> 
                \<turnstile> {p} <ode && Inv&b> {q; H} \<Longrightarrow>
                \<turnstile> {p} <ode && Inv&(b[&]I)> {q; H}"
*)

(*This is different from Platzer's: not b holds at the termination.*)
|diffWeak: "\<forall> h now now'. (almost b [[|]] elE 0) h now now' \<longrightarrow>
            H h now now' \<Longrightarrow> well_DC H \<Longrightarrow> \<turnstile> {p} <ode && Inv&b> {[\<not>]b; H}"

|diffE: "\<turnstile> {p} <odeone x e && Inv & b>; DAss x e {b; H} \<Longrightarrow> DE_free e \<Longrightarrow>
         \<turnstile> {p} <odeone x e && Inv & b> {b; H}"

|diffE2: "\<turnstile> {p} <odeone x e && Inv & b> {b; H} \<Longrightarrow> DE_free e \<Longrightarrow>
          \<turnstile> {p} <odeone x e && Inv & b>; DAss x e {b; H}"
(*
|diffSol: "\<forall> s. \<forall> t\<ge>0 .\<forall> u. u\<ge>0 \<and> u\<le>t \<longrightarrow> b(s) \<Longrightarrow> well
           \<turnstile> {p} <odeone x e && Inv & b> {b; H}"
*)

|diffInvGE: "\<forall> s. b s \<longrightarrow> q s \<Longrightarrow> 
           \<turnstile> {p} <odeone x e && Inv & b> {(Diff f1) [\<ge>] (Diff f2); (almost ((Diff f1) [\<ge>] (Diff f2)) [[|]] elE 0)} \<Longrightarrow>
           \<forall> h now now'. (almost (f1 [\<ge>] f2) [[|]] elE 0) h now now' \<longrightarrow>
            H h now now' \<Longrightarrow> well_DC H \<Longrightarrow>
           \<turnstile> {p} <odeone x e && Inv & b> {f1 [\<ge>] f2; H}"

|diffInvG: "\<forall> s. b s \<longrightarrow> q s \<Longrightarrow> 
           \<turnstile> {p} <odeone x e && Inv & b> {(Diff f1) [>] (Diff f2); (almost ((Diff f1) [>] (Diff f2)) [[|]] elE 0)} \<Longrightarrow>
           \<forall> h now now'. (almost (f1 [>] f2) [[|]] elE 0) h now now' \<longrightarrow>
            H h now now' \<Longrightarrow> well_DC H \<Longrightarrow>
           \<turnstile> {p} <odeone x e && Inv & b> {f1 [>] f2; H}"

|diffGhost: "\<forall> s. b s \<longrightarrow> q s \<Longrightarrow> 
           \<turnstile> {p} <odeone x e && Inv & b> {q; (almost q [[|]] elE 0)} \<Longrightarrow>
           \<forall> h now now'. (almost q [[|]] elE 0) h now now' \<longrightarrow>
            H h now now' \<Longrightarrow> well_DC H \<Longrightarrow>
           \<turnstile> {p} <odeone x e && Inv & b> {q; H}"

|caseR: "\<turnstile> {p [&] pb} P {q; H} \<Longrightarrow> \<turnstile> {(p [&] ([\<not>]pb))} P {q; H} \<Longrightarrow>
             \<turnstile> {p} P {q; H}"


 
text \<open>When two independent P and Q are put in parallel, \<close>
text \<open>and when a communication follows P and Q,\<close>
text \<open>and when P and Q contain communication, and U V not.\<close>
inductive HHL_para :: "'a :: finite fform \<Rightarrow> 'a fform \<Rightarrow> 'a procP \<Rightarrow> 
  'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a dform \<Rightarrow> 'a dform \<Rightarrow> bool" ("\<turnstile> {_, _}_{_, _; _, _}" 70) where
  parallelR: "chanset P = {} \<and> chanset Q = {} \<Longrightarrow> \<turnstile> {pp} P {qp; Hp} \<Longrightarrow> \<turnstile> {pq} Q {qq; Hq}
                       \<Longrightarrow> \<turnstile> {pp, pq} P||Q {qp, qq; Hp, Hq}"

| commR: "\<turnstile> {px, py} (P || Q) {qx, qy; Hx, Hy} \<Longrightarrow>  
         (\<forall> s. qx s \<longrightarrow> (rx (update_fst s x (evalE e s)))) \<Longrightarrow>
         (\<forall> s. qy s \<longrightarrow> ry s) \<Longrightarrow>
         (\<forall> h n m. (Hx[^](elE 0 [[|]] almost qx)) h n m \<longrightarrow> Gx h n m) \<Longrightarrow>
         (\<forall> h n m. (Hy[^](elE 0 [[|]] almost qy)) h n m \<longrightarrow> Gy h n m) \<Longrightarrow>
          well_DC Gx \<and> well_DC Gy \<Longrightarrow>
          \<turnstile> {px, py} (P; Cm (ch[?]x))||(Q; (Cm (ch[!]e))) {rx, ry; Gx, Gy}"

| parallel2R: "\<turnstile> {pp, pq} P||Q {qp, qq; Hp, Hq}  \<Longrightarrow> chanset P \<noteq> {} \<and> chanset Q \<noteq> {} \<Longrightarrow> 
               \<turnstile> {qp} U {qu; Hu} \<Longrightarrow> \<turnstile> {qq} V {qv; Hv} \<Longrightarrow> chanset U = {} \<and> chanset V = {} 
              \<Longrightarrow> \<turnstile> {pp, pq} P; U||Q; V {qu, qv; Hp [^] Hu, Hq [^] Hv}"


lemma hhl_well_DC : "\<turnstile> {p} P {q; H} \<Longrightarrow> well_DC H"
proof (induction rule: HHL_partial.induct)
  case (IChoiceR p P m H Q q G)
  then show ?case
    unfolding dOr_def well_DC_def
    by blast

next
  case (repetR H I P)
  then show ?case
    unfolding well_DC_def dOr_def
    by (metis (mono_tags, lifting) elE_def)

qed auto


lemma hhl_well_DC_par : "\<turnstile> {pp, pq} P||Q {qp, qq; Hp, Hq}  \<Longrightarrow> well_DC Hp \<and> well_DC Hq"
proof (induction rule: HHL_para.induct)
case (parallelR P Q pp qp Hp pq qq Hq)
  then show ?case
    using hhl_well_DC by auto
next
  case (commR px py P Q qx qy Hx Hy rx x e ry Gx Gy ch)
  then show ?case by auto
next
  case (parallel2R pp pq P Q qp qq Hp Hq U qu Hu V qv Hv)
  then have Hpq: "well_DC Hp \<and> well_DC Hq" 
    and Huv: "well_DC Hu \<and> well_DC Hv" using hhl_well_DC by auto
  show ?case using Hpq Huv chop_well_DC by auto
qed

(*Sequential*)
lemma Sequential_aux : 
  assumes "well_DC H" and "\<turnstile> {p} P {m; H}" and "\<turnstile> {m} Q {q; G}" and 
    "\<Turnstile> {p} P {m; H}" and "\<Turnstile> {m} Q {q; G}"
  shows "\<Turnstile> {p} P;  Q {q; H [^] G}" 
proof -
  have "\<forall>now h now' h'. semB (P; Q) now h now' h' \<longrightarrow> p (h now) \<longrightarrow> 
    q (h' now') \<and> (\<exists>nm\<ge>now. nm \<le> now' \<and> H h' now nm \<and> G h' nm now')"
  proof -
    {
      fix now h now' h' 
      assume PQ: "semB (P; Q) now h now' h'" and pre: "p (h now)"
      obtain now'a f' where sP: "semB P now h now'a f'" and sQ: "semB Q now'a f' now' h'" 
        using PQ by clarsimp
      have post: "m (f' now'a) \<and> H f' now now'a \<and> q (h' now') \<and> G h' now'a now'" 
        using sP sQ pre assms unfolding Valid_def by auto 
      have nowa: "now \<le> now'a" using sP by (simp add: sem1)
      moreover have hf: "(now'a \<le> now' \<and> (\<forall>t. t < now'a \<or> t > now' \<longrightarrow> f' t = h' t))"
        using sQ by (simp add: sem1 sem2)
      ultimately have "now \<le> now' \<and> (\<forall>t. now < t \<and> t < now'a \<longrightarrow> f' t = h' t)" by auto
      then have "H h' now now'a" using assms(1) post nowa unfolding well_DC_def by auto
      then have "q (h' now') \<and> (\<exists>nm\<ge>now. nm \<le> now' \<and> H h' now nm \<and> G h' nm now')"
        using post hf nowa by blast       
    }
    then show ?thesis by auto
  qed
  then show ?thesis  unfolding Valid_def chop_def by auto
qed

lemma repetitionN_0:
  " \<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m \<Longrightarrow>
    \<turnstile> {I}P{I; H} \<Longrightarrow>
   \<forall>now h now' h'. semB P now h now' h' \<longrightarrow> I (h now) \<longrightarrow> I (h' now') \<and> H h' now now' \<Longrightarrow>
    semB (P* NUM 0) now h now' h' \<Longrightarrow> I (h now) \<Longrightarrow> I (h' now') \<and> (H h' now now' \<or> elE 0 h' now now')"
  apply (ind_cases "semB (P* NUM 0) now h now' h'")
  unfolding elE_def
  by fastforce

lemma repetitionN_Suc: 
assumes incN: "(\<And>now h now' h'.
           \<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m \<Longrightarrow>
           \<turnstile> {I}P{I; H} \<Longrightarrow>
           \<forall>now h now' h'. semB P now h now' h' \<longrightarrow> I (h now) \<longrightarrow> I (h' now') \<and> H h' now now' \<Longrightarrow>
           semB (P* NUM N) now h now' h' \<Longrightarrow> I (h now) \<Longrightarrow> I (h' now') \<and> (H h' now now' \<or> elE 0 h' now now'))"
  and chopH: "\<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m"
  and rP: "\<turnstile> {I} P {I; H}"
  and semBP: "\<forall>now h now' h'. semB P now h now' h' \<longrightarrow> I (h now) \<longrightarrow> I (h' now') \<and> H h' now now'"
(*  and semBPP: "semB (P* NUM Suc N) now h now' h'"
  and pre: "I (h now)"
shows "I (h' now') \<and> (H h' now now' \<or> elE 0 h' now now')"
*)
shows "semB (P* NUM Suc N) now h now' h' \<Longrightarrow> I (h now) \<Longrightarrow> I (h' now') \<and> (H h' now now' \<or> elE 0 h' now now')"
proof (ind_cases "semB (P* NUM Suc N) now h now' h'")
  have wellH: "well_DC H" using hhl_well_DC rP by auto
  have Pf: "\<And>now_d f_d. I (h now) \<Longrightarrow> semB P now h now_d f_d \<Longrightarrow>  I (f_d now_d) \<and> H f_d now now_d"
    using semBP by auto

   have PNf: "\<And>now_d f_d. semB (P* NUM N) now_d f_d now' h' \<Longrightarrow> I (f_d now_d) \<Longrightarrow> I (h' now') \<and> (H h' now_d now' \<or> elE 0 h' now_d now')"
     using incN[of _ _ now' h'] chopH rP semBP by metis
   have PPNf: "\<And>now_d f_d. semB P now h now_d f_d \<Longrightarrow> semB (P* NUM N) now_d f_d now' h' \<Longrightarrow> H f_d now now_d = H h' now now_d"
     using wellH unfolding well_DC_def 
     by (simp add: sem1 sem2)
   have "\<And>now_d f_d. I (h now) \<Longrightarrow> semB P now h now_d f_d \<Longrightarrow> semB (P* NUM N) now_d f_d now' h'\<Longrightarrow> I (h' now') \<and> H h' now now'" 
     using PNf Pf PPNf chopH unfolding elE_def chop_def 
     by (metis eq_iff le_iff_diff_le_0 sem1)
   then show "\<And>now_d f_d. I (h now) \<Longrightarrow> semB P now h now_d f_d \<Longrightarrow> semB (P* NUM (Suc N - Suc 0)) now_d f_d now' h' 
              \<Longrightarrow> I (h' now') \<and> (H h' now now' \<or> elE 0 h' now now')"
     by auto
 qed

lemma repetitionN_sound: 
  "\<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m \<Longrightarrow>
       \<turnstile> {I}P{I; H} \<Longrightarrow>
       \<forall>now h now' h'. semB P now h now' h' \<longrightarrow> I (h now) \<longrightarrow> I (h' now') \<and> H h' now now' \<Longrightarrow>
       semB (P* NUM N) now h now' h' \<Longrightarrow> I (h now) \<Longrightarrow> I (h' now') \<and> (H [[|]] elE 0) h' now now'"
  unfolding dOr_def
  apply (induction N arbitrary: now h now' h')
  subgoal
  using repetitionN_0[of H I P] by metis
  using repetitionN_Suc[of H I P]
  by smt 
      
lemma diffCut_aux : 
  assumes I: "\<turnstile> {p}<ode&&Inv&b>{I; almost I [[|]] elE 0}" 
    and vI: "\<Turnstile> {p}<ode&&Inv&b>{I; almost I [[|]] elE 0}"
    and C: "\<turnstile> {p}<ode&&Inv&(b [&] I)>{q; H}"
    and vC: "\<Turnstile> {p}<ode&&Inv&(b [&] I)>{q; H}"
  shows "\<Turnstile> {p} <ode&&Inv&b> {q; H}"
proof (simp add:Valid_def) 
  have "\<forall>now h now' h'. semB (<ode&&Inv&b>) now h now' h' \<longrightarrow> p (h now) 
    \<longrightarrow> I (h' now') \<and> (almost I [[|]] elE 0) h' now now'"
    using vI unfolding Valid_def by auto
  have semI: "semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> semB (<ode&&Inv&(b [&] I)>) now h now' h'"
    for now h now' h'
    apply (ind_cases "semB (<ode&&Inv&b>) now h now' h'")
    subgoal for d sol
    proof -
      assume a: "p (h now)" and b: "now' = now + d"  
        and c: "h' = (\<lambda>t. if t \<le> now + d \<and> now \<le> t then  execute_ODE ode (h now) (sol (t - now)) else h t)"
        and d: "0 \<le> d" 
        and s: "ODE_solution ode d (h now) sol"
        and e: "(\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (execute_ODE ode (h now) (sol t)))"
        and f: "\<not> b (execute_ODE ode (h now) (sol d)) "
      show "semB (<ode&&Inv&(b [&] I)>) now h now' h'"
      proof -
        have "semB (<ode&&Inv&b>) now h (now + d) h'" 
          using b c d e s f continuous by auto
        then have almostI: "I (h' now') \<and> (almost I [[|]] elE 0) h' now now'" 
          using a vI b unfolding Valid_def by auto
        have "\<not> (b [&] I) (execute_ODE ode (h now) (sol d))"
          using e d c f unfolding fNot_def fAnd_def by auto
        moreover have "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> (b [&] I) (execute_ODE ode (h now) (sol t))"
          using almostI  d b e c unfolding almost_def fAnd_def Let_def dOr_def elE_def 
          by smt
        ultimately have "(\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (execute_ODE ode (h now) (sol t)) \<and> 
          I (execute_ODE ode (h now) (sol t))) \<and>
          \<not> (b (execute_ODE ode (h now) (sol d)) \<and> I (execute_ODE ode (h now) (sol d)))" 
          unfolding fAnd_def by auto      
        then show ?thesis        
          using b s c d continuous[of d ode h now sol "b[&]I" Inv]  unfolding Let_def fAnd_def
          by auto       
     qed
    qed
    done

  have "semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> q (h' now') \<and> H h' now now'"
    for now h now' h'
    using vC semI unfolding Valid_def by meson
  then show "\<forall>now h now' h'. semB (<ode&&Inv&b>) now h now' h' \<longrightarrow> p (h now) \<longrightarrow> q (h' now') \<and> H h' now now'"
    by auto
qed 

lemma has_vderiv_on_zero_partial_constant:
  fixes f :: "real \<Rightarrow> ('a :: finite) state"
  assumes solv: "(f has_vderiv_on (\<lambda>xa. \<chi> i. if i = x then M (f xa) else 0)) {0..d}"
    and xi:  "i \<noteq> x"
    and tv: "t \<ge> 0  & t \<le> d"
  shows "f t $ i = f 0 $ i"
  sorry

lemma ODE_only_changes_not_zero_deriv: 
  assumes "ODE_solution (odeone x e) d (aa, bb) sol"
    and tv: "t \<ge> 0  & t \<le> d"
  shows "sol t = fst (execute_ODE (odeone x e) (aa, bb) (sol t))"
proof -
  have "sol t = fst (concrete_sol (odeone x e) (aa, bb) (sol t))"
    using assms 
    unfolding ODE_solution_def concrete_sol_def ODE_pair_state_def 
    apply auto
    using vec_eq_iff[of "sol t" "(\<chi> i. (if i = x then sol t else fst (aa, bb)) $ i)"]
    apply auto
    subgoal for i
      using has_vderiv_on_zero_partial_constant[of sol x _ d i t]  by auto
    done
  then show ?thesis using execute_ODE_concrete by metis   
qed

  
lemma diffE_lemma: 
  fixes e :: "('a :: finite) exp"
    and aa bb :: "'a state"
    and sol :: "real \<Rightarrow> 'a state"
  assumes DEf: "DE_free e"
    and solx: "ODE_solution (odeone x e) d (aa, bb) sol"
    and tv: "t \<ge> 0  & t \<le> d"
  shows "evalE e (execute_ODE (odeone x e) (aa, bb) (sol t)) =
            snd (execute_ODE (odeone x e) (aa, bb) (sol t)) $ x"
proof -
  have agree: "Vagree (execute_ODE (odeone x e) (aa, bb) (sol t)) (ODE_pair_state (odeone x e) (sol t)) {x}"
    using execute_ODE_agree[of "odeone x e" "(aa, bb)" "sol t"]
    by auto
  then have "snd (execute_ODE (odeone x e) (aa, bb) (sol t)) $ x = 
             ODE_sem (odeone x e) (sol t) $ x"
    unfolding Vagree_def ODE_pair_state_def by auto
  moreover have "ODE_sem (odeone x e) (sol t) $ x = evalE_df e (sol t)"
    by auto
  moreover have "evalE e (execute_ODE (odeone x e) (aa, bb) (sol t)) =
        evalE_df e (fst (execute_ODE (odeone x e) (aa, bb) (sol t)))"
    using DEf by (simp add: DE_free_evalE)
  moreover have "fst (execute_ODE (odeone x e) (aa, bb) (sol t)) = sol t"
    using ODE_only_changes_not_zero_deriv[of x e d _ _ sol t] solx tv  by auto
  ultimately show ?thesis by auto
qed
 
lemma diffE_aux: 
  assumes "\<turnstile> {p}<odeone x e&&Inv&b>; DAss x e{b; H}"
    and "DE_free e"
    and "\<Turnstile> {p}<odeone x e&&Inv&b>; DAss x e{b; H}"
  shows "\<Turnstile> {p}<odeone x e&&Inv&b>{b; H}"
proof -
  have "DE_free e \<Longrightarrow> semB (<odeone x e&&Inv&b>) now h now' h' \<Longrightarrow>
    semB (<odeone x e&&Inv&b>; DAss x e) now h now' h'"
    for now h now' h'
  proof -
    assume semode: "semB (<odeone x e&&Inv&b>) now h now' h'" and DEe: "DE_free e"
    show "semB (<odeone x e&&Inv&b>; DAss x e) now h now' h'"
    using semode DEe apply auto
    subgoal for d sol 
  proof -
    assume de: "DE_free e"
      and hi: "h' = (\<lambda>t. if t \<le> now + d \<and> now \<le> t then execute_ODE (odeone x e) (h now) (sol (t - now)) else h t)"
      and d0: "0 \<le> d" and solx: "ODE_solution (odeone x e) d (h now) sol"
      and dom: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (execute_ODE (odeone x e) (h now) (sol t))"
      and dom2: "\<not> b (execute_ODE (odeone x e) (h now) (sol d))" and nowd: "now' = now + d"
    show "semB (<odeone x e&&Inv&b>; DAss x e) now h (now + d) (\<lambda>t. if t \<le> now + d \<and> now \<le> t 
      then execute_ODE (odeone x e) (h now) (sol (t - now)) else h t)"
    proof -
      have nowode: "now \<le> now'" using nowd d0 by auto
      have ex: "evalE e (execute_ODE (odeone x e) (h now) (sol (now' - now))) =
            snd (execute_ODE (odeone x e) (h now) (sol (now' - now))) $ x"
        using diffE_lemma[of e x d _ _ sol "now'-now"] de solx nowd nowode
        by (metis add.commute add_left_cancel d0 diff_add_cancel order_refl prod.exhaust_sel)
      from ex have "update_snd (h' now') x (evalE e (h' now')) =  h' now'"
        using nowode hi nowd
        apply auto
        by (smt eq_snd_iff fst_conv vec_lambda_unique)        
      then have "h' = (\<lambda>t. if t = now' then update_snd (h' t) x (evalE e (h' t)) else h' t)"
        by auto 
      then have dasem: "semB (DAss x e) now' h' now' h'" 
        using DassignB[of x e now' h'] by auto
      then have "semB (<odeone x e&&Inv&b>) now h now' h' \<Longrightarrow> semB (DAss x e) now' h' now' h'"
        by auto
      then show ?thesis using sequenceB[of "<odeone x e&&Inv&b>" now h now' h' "DAss x e" now' h'] 
        hi nowd semode by auto      
    qed
  qed
  done
  qed
  then show ?thesis using assms unfolding Valid_def
    by meson
qed 

lemma diffE2_aux: 
  assumes "\<turnstile> {p}<odeone x e&&Inv&b>{b; H}"
    and "DE_free e"
    and "\<Turnstile> {p}<odeone x e&&Inv&b>{b; H}"
  shows "\<Turnstile> {p}<odeone x e&&Inv&b>; DAss x e{b; H}"
proof -
  
  have "DE_free e \<Longrightarrow> semB (<odeone x e&&Inv&b>; DAss x e) now h now' h' \<Longrightarrow>
    semB (<odeone x e&&Inv&b>) now h now' h'"
    for now h now' h'
    apply auto
    using if_split
    sorry
  then show ?thesis sorry
qed


lemma diffInvGE_aux: 
  assumes "\<forall>s. b s \<longrightarrow> q s"
    and "\<turnstile> {p}<odeone x e&&Inv&b>{Diff f1 [\<ge>] Diff f2; almost (Diff f1 [\<ge>] Diff f2) [[|]] elE 0}"
    and "\<forall>h now now'. (almost (f1 [\<ge>] f2) [[|]] elE 0) h now now' \<longrightarrow> H h now now'"
    and "well_DC H" 
    and "\<Turnstile> {p}<odeone x e&&Inv&b>{Diff f1 [\<ge>] Diff f2; almost (Diff f1 [\<ge>] Diff f2) [[|]] elE 0}"
  shows "\<Turnstile> {p}<odeone x e&&Inv&b>{f1 [\<ge>] f2; H}"
  sorry

lemma diffInvG_aux: 
  assumes "\<forall>s. b s \<longrightarrow> q s"
    and "\<turnstile> {p}<odeone x e&&Inv&b>{Diff f1 [>] Diff f2; almost (Diff f1 [>] Diff f2) [[|]] elE 0}"
    and "\<forall>h now now'. (almost (f1 [>] f2) [[|]] elE 0) h now now' \<longrightarrow> H h now now'"
    and "well_DC H" 
    and "\<Turnstile> {p}<odeone x e&&Inv&b>{Diff f1 [>] Diff f2; almost (Diff f1 [>] Diff f2) [[|]] elE 0}"
  shows "\<Turnstile> {p}<odeone x e&&Inv&b>{f1 [>] f2; H}"
  sorry

lemma diffGhost_aux:
  assumes "\<forall>s. b s \<longrightarrow> q s"
    and "\<turnstile> {p}<odeone x e&&Inv&b>{q; almost q [[|]] elE 0}"
    and "\<forall>h now now'. (almost q [[|]] elE 0) h now now' \<longrightarrow> H h now now'"
    and "well_DC H"
    and "\<Turnstile> {p}<odeone x e&&Inv&b>{q; almost q [[|]] elE 0}"
  shows "\<Turnstile> {p}<odeone x e&&Inv&b>{q; H}"
  sorry



theorem HHL_partial_sound : 
  "\<turnstile> {p} P {q; H} \<Longrightarrow> \<Turnstile> {p} P {q; H}"
proof (induction rule: HHL_partial.induct)
  case (skipR p q H)
  then show ?case 
    apply (simp add:Valid_def, auto)
    by (metis surj_pair)

next
  case (assignR p q x e H)
  then show ?case
    apply (simp add:Valid_def, auto)
    by (metis (no_types, lifting) Cart_lambda_cong eq_snd_iff)

next
  case (seqR p P m H Q q G M)
   then have "\<Turnstile> {p} P;  Q {q; H [^] G} \<and> (\<forall>h m n. (H[^]G) h m n \<longrightarrow> M h m n) " 
     using Sequential_aux hhl_well_DC by blast
   then show ?case unfolding Valid_def by auto 

next
  case (condTR p b P q H)
  then show ?case
    unfolding Valid_def 
    using condTR.IH 
    apply blast
    done
  next
  case (condFR p q b H P)
  then show ?case 
    unfolding Valid_def
    apply auto
    apply (simp add: condFR.hyps)+
    done 
     
next
  case (IChoiceR p P m H Q q G)
  then show ?case
    unfolding Valid_def dOr_def fOr_def
    by auto

next
  case (repetR H I P)
  then show ?case 
    unfolding Valid_def 
    apply clarify
    using repetitionN_sound[of H I P] 
    by metis

next
  case (consequenceR px P qx Hx p q H)
  then show ?case
    unfolding Valid_def
    apply auto
    using consequenceR.hyps(2) consequenceR.hyps(3) apply blast
    using consequenceR.hyps(2) consequenceR.hyps(3) apply blast
    done

next
  case (continTR Inv b q p ode H)
  show ?case 
    unfolding Valid_def
    apply auto
    subgoal for now h d sol
    proof -
      assume d: "0 \<le> d" and s: "ODE_solution ode d (h now) sol" and 
        dom: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> 
          b (execute_ODE ode (h now) (sol t))" and dom2: " \<not> b (execute_ODE ode (h now) (sol d))"
       and prep: "p (h now)" 
      show "q (execute_ODE ode (h now) (sol d))"  
      proof -
        define S where "S = (execute_ODE ode (h now) (sol d))"
        have "Inv S" using continTR.hyps(2) prep dom dom2 s d
          unfolding ODE_inv_in_dom_def Let_def
          using S_def by blast
        moreover have "([\<not>] b) S" using dom dom2
          unfolding fNot_def S_def Let_def by auto
        ultimately show ?thesis using continTR.hyps(1) 
          unfolding fAnd_def S_def by blast
      qed
    qed
    subgoal for now h d sol
    proof -
      assume d: "0 \<le> d" and s: "ODE_solution ode d (h now) sol" and
        dom: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> 
          b (execute_ODE ode (h now) (sol t))" and dom2: "\<not> b (execute_ODE ode (h now) (sol d))"
       and prep: "p (h now)"
      show "H (\<lambda>t. if t \<le> now + d \<and> now \<le> t then execute_ODE ode (h now) (sol (t - now)) else h t) now (now + d)"
     proof -
       define P where "P = (\<lambda>t. if t \<le> now + d \<and> now \<le> t then 
          execute_ODE ode (h now) (sol (t - now)) else h t)"
       have "(almost (Inv [&] b) [[|]] elE 0) P now (now + d)"
         unfolding dOr_def almost_def fAnd_def elE_def
         apply auto
         using d apply auto
         prefer 2
         using dom unfolding P_def Let_def
          apply simp
         using dom dom2 s continTR.hyps(2) prep d unfolding ODE_inv_in_dom_def Let_def 
         apply auto
         using d by (smt prod.collapse)
       then show ?thesis using continTR.hyps(3) using P_def by auto
     qed
   qed
   done
 
next
  case (diffCut p ode Inv b I q H)
  then show ?case using diffCut_aux by auto

next
  case (diffWeak b H p ode Inv)
  then show ?case
    unfolding Valid_def
    apply auto
    unfolding fNot_def Let_def
     apply blast
    unfolding dOr_def by smt
 
next
  case (diffE p x e Inv b H)
  then show ?case using diffE_aux by blast
next
  case (diffE2 p x e Inv b H)
  then show ?case using diffE2_aux by blast
next
  case (diffInvGE b q p x e Inv f1 f2 H)
  then show ?case using diffInvGE_aux by blast
next
  case (diffInvG b q p x e Inv f1 f2 H)
  then show ?case using diffInvG_aux by blast
next
  case (diffGhost b q p x e Inv H)
  then show ?case using diffGhost_aux by blast
 
next
  case (caseR p pb P q H)
  then show ?case
    unfolding Valid_def fNot_def fAnd_def
    apply auto
    apply blast
    apply blast
    done
qed 

lemma communication_aux:
  assumes PQ: "\<turnstile> {px, py}P || Q{qx, qy; Hx, Hy}"
    and postx: "\<forall>s. qx s \<longrightarrow> rx (update_fst s x (evalE e s))"
    and posty: "\<forall>s. qy s \<longrightarrow> ry s"
    and postHx: "\<forall>h n m. (Hx [^] (elE 0 [[|]] almost qx)) h n m \<longrightarrow> Gx h n m"
    and postHy: "\<forall>h n m. (Hy [^] (elE 0 [[|]] almost qy)) h n m \<longrightarrow> Gy h n m"
    and vPQ: "\<forall>nowp nowq fp fq nowp' nowq' fp' fq'.
          semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<longrightarrow> px (fp nowp) \<longrightarrow> py (fq nowq) \<longrightarrow>
           qx (fp' nowp') \<and> qy (fq' nowq') \<and> Hx fp' nowp nowp' \<and> Hy fq' nowq nowq'"
  shows "semBP (P; Cm (ch[?]x) || Q; Cm (ch[!]e)) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
        px (fp nowp) \<Longrightarrow> py (fq nowq) \<Longrightarrow> 
        rx (fp' nowp') \<and> ry (fq' nowq') \<and> Gx fp' nowp nowp' \<and> Gy fq' nowq nowq'"
apply (ind_cases "semBP (P; Cm (ch[?]x) || Q; Cm (ch[!]e)) nowp fp nowq fq nowp' fp' nowq' fq'")
apply (simp add:chanset_def) 
apply (simp add:chanset_def)
  subgoal for nowp'a fp'a nowq'a fq'a
  proof -
    assume 1: "px (fp nowp)" and 2: "py (fq nowq)" and 3: "nowp' = max nowp'a nowq'a"
      and 4: "fp' = (\<lambda>t. if nowp'a < t \<and> t < max nowp'a nowq'a then fp'a nowp'a
         else if t = max nowp'a nowq'a then update_fst (fp'a nowp'a) x (evalE e (fp'a nowp'a)) else fp'a t)"
      and 5: "nowq' = max nowp'a nowq'a" 
      and 6: "fq' = (\<lambda>t. if nowq'a < t \<and> t \<le> max nowp'a nowq'a then fq'a nowq'a else fq'a t)"
      and 7: "semBP (P || Q) nowp fp nowq fq nowp'a fp'a nowq'a fq'a" and 8: "ch = ch"
    show "rx (fp' nowp') \<and> ry (fq' nowq') \<and> Gx fp' nowp nowp' \<and> Gy fq' nowq nowq'"
    proof -
      have postPQ: "qx (fp'a nowp'a) \<and> qy (fq'a nowq'a) \<and> Hx fp'a nowp nowp'a \<and> Hy fq'a nowq nowq'a"
        using 7 PQ vPQ 1 2 by auto
      then have postp: "rx (fp' nowp')" using 3 4 postx by fastforce
      have postq: "ry (fq' nowq')" using postPQ 5 6 posty  
        by (simp add: posty max.strict_order_iff)
      have "Hx fp' nowp nowp'a" using postPQ semB1[of P Q nowp fp nowq fq nowp'a fp'a nowq'a fq'a] 
        hhl_well_DC_par[of px py P Q qx qy Hx Hy] PQ 4 7
        unfolding well_DC_def by smt
      moreover have "(elE 0 [[|]] almost qx) fp' nowp'a nowp'"
        unfolding chop_def almost_def dOr_def elE_def 4 3 
        using postPQ by auto
      ultimately have postpH: "(Hx [^] (elE 0 [[|]] almost qx)) fp' nowp nowp'"
        unfolding chop_def using 3 
        by (meson "7" max.cobounded1 semB1)

      have "Hy fq' nowq nowq'a" using postPQ semB1[of P Q nowp fp nowq fq nowp'a fp'a nowq'a fq'a] 
        hhl_well_DC_par[of px py P Q qx qy Hx Hy] PQ 6 7
        unfolding well_DC_def by smt
      moreover have "(elE 0 [[|]] almost qy) fq' nowq'a nowq'"
        unfolding chop_def almost_def dOr_def elE_def 5 6
        using postPQ by auto
      ultimately have postqH: "(Hy [^] (elE 0 [[|]] almost qy)) fq' nowq nowq'"
        unfolding chop_def using 5 
        by (meson "7" max.cobounded2 semB1)

      from postp postq postpH postqH postHx postHy show ?thesis by auto
    qed
  qed
  done
  

lemma parallel_aux: 
  " \<turnstile> {pp, pq}P || Q{qp, qq; Hp, Hq} \<Longrightarrow>
       \<turnstile> {qp}U{qu; Hu} \<Longrightarrow>
       \<turnstile> {qq}V{qv; Hv} \<Longrightarrow>
       \<forall>nowp nowq fp fq nowp' nowq' fp' fq'.
          semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<longrightarrow> pp (fp nowp) \<longrightarrow> pq (fq nowq) \<longrightarrow>
          qp (fp' nowp') \<and> qq (fq' nowq') \<and> Hp fp' nowp nowp' \<and> Hq fq' nowq nowq' \<Longrightarrow>
       chanset P \<noteq> {} \<Longrightarrow>
       chanset Q \<noteq> {} \<Longrightarrow>
       chanset U = {} \<Longrightarrow>
       chanset V = {} \<Longrightarrow>
       semBP (P; U || Q; V) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
       pp (fp nowp) \<Longrightarrow> pq (fq nowq) \<Longrightarrow> 
       qu (fp' nowp') \<and> qv (fq' nowq') \<and> (Hp [^] Hu) fp' nowp nowp' \<and> (Hq [^] Hv) fq' nowq nowq'"
apply (ind_cases "semBP (P; U || Q; V) nowp fp nowq fq nowp' fp' nowq' fq'")
apply (simp add:chanset_def)
prefer 2 apply (simp add:chanset_def)
prefer 2 apply (simp add:chanset_def)
  subgoal for nowp'a fp'a nowq'a fq'a 
  proof -
    assume 1: "\<turnstile> {pp, pq}P || Q{qp, qq; Hp, Hq}"
      and 2: "\<turnstile> {qp}U{qu; Hu}" and 3: "\<turnstile> {qq}V{qv; Hv}"
      and 4: "\<forall>nowp nowq fp fq nowp' nowq' fp' fq'.  
           semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<longrightarrow> pp (fp nowp) \<longrightarrow> pq (fq nowq) \<longrightarrow>
            qp (fp' nowp') \<and> qq (fq' nowq') \<and> Hp fp' nowp nowp' \<and> Hq fq' nowq nowq'"
      and 5: "chanset P \<noteq> {}" and 6: "chanset Q \<noteq> {}" and 7: "chanset U = {}" and 8: "chanset V = {}"
      and 9: "pp (fp nowp)" and 10: "pq (fq nowq)"
      and 11: "semBP (P || Q) nowp fp nowq fq nowp'a fp'a nowq'a fq'a"
      and 12: "semB U nowp'a fp'a nowp' fp'" and 13: "semB V nowq'a fq'a nowq' fq'"
    and "chanset P \<noteq> {}" and "chanset Q \<noteq> {}" and "chanset U = {}" and "chanset V = {}"  
     show "qu (fp' nowp') \<and> qv (fq' nowq') \<and> (Hp [^] Hu) fp' nowp nowp' \<and> (Hq [^] Hv) fq' nowq nowq'"
     proof -
       have wpq: "qp (fp'a nowp'a) \<and> qq (fq'a nowq'a) \<and> Hp fp'a nowp nowp'a \<and> Hq fq'a nowq nowq'a"
         using 4 11 9 10 by auto
       moreover have "\<Turnstile> {qp}U{qu; Hu} \<and> \<Turnstile> {qq}V{qv; Hv}"
         using 2 3 HHL_partial_sound by auto
       ultimately have wuv: "qu (fp' nowp') \<and> qv (fq' nowq') \<and> Hu fp' nowp'a nowp' \<and> Hv fq' nowq'a nowq'" 
         unfolding Valid_def using 12 13 by auto

       have "Hp fp' nowp nowp'a \<and> Hq fq' nowq nowq'a"
         using wpq sem2 well_DC_def[of Hp] hhl_well_DC_par[of pp pq P Q qp qq Hp Hq] 1
           well_DC_def[of Hq] semB1 semB2
         by (smt "11" "12" "13")
       then show ?thesis unfolding chop_def using wpq wuv
         by (meson "11" "12" "13" sem1 semB1)
     qed
   qed
   done
 

theorem HHL_para_sound : 
  "\<turnstile> {pp, pq} P||Q {qp, qq; Hp, Hq} \<Longrightarrow>  \<Turnstile> {pp, pq} P||Q {qp, qq; Hp, Hq}" 
proof (induction rule: HHL_para.induct)
  case (parallelR P Q pp qp Hp pq qq Hq)
  then have chs: "chanset P = {} \<and> chanset Q = {}"
    and vP: "\<Turnstile> {pp} P {qp; Hp}" and vQ: "\<Turnstile> {pq} Q {qq; Hq}"
    using HHL_partial_sound by auto
  show ?case
    unfolding ValidP_def
    apply clarify
    subgoal for nowp nowq fp fq nowp' nowq' fp' fq' 
    proof -
      assume PQ: "semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq'" and 
             preP: "pp (fp nowp)" and preQ: "pq (fq nowq)"
      show "qp (fp' nowp') \<and> qq (fq' nowq') \<and> Hp fp' nowp nowp' \<and> Hq fq' nowq nowq'"
      proof -
        have "semB P nowp fp nowp' fp' \<and> semB Q nowq fq nowq' fq'"
          using PQ semB3 chs by metis
        then show ?thesis using vP vQ preP preQ unfolding Valid_def by metis
      qed
    qed
  done

next
  case (commR px py P Q qx qy Hx Hy rx x e ry Gx Gy ch)
  then show ?case
    unfolding ValidP_def
    apply clarify
    using communication_aux[of px py P Q qx qy Hx Hy rx x e ry Gx Gy ch]
    by presburger 

next
  case (parallel2R pp pq P Q qp qq Hp Hq U qu Hu V qv Hv)
  then show ?case 
    unfolding ValidP_def
    apply clarify 
    using parallel_aux[of pp pq P Q qp qq Hp Hq U qu Hu V qv Hv]
    by presburger
qed
 
declare almost_def [simp del]
declare chop_def [simp del]
 
 
end
