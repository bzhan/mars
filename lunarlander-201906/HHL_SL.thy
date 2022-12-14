section {* Abstract syntax for Hybrid CSP. *}

theory HHL_SL
  imports Op_SL
begin

type_synonym now_dash = real
type_synonym dform = "history \<Rightarrow> now \<Rightarrow> now_dash \<Rightarrow> bool"

definition semd :: "history \<Rightarrow> now \<Rightarrow> now_dash \<Rightarrow> dform \<Rightarrow> bool" ("_, [_, _] |= _" 50) where
  "h, [n, m] |= H \<equiv> H h n m"

text \<open>One axiom stating that the dform formula is only decided by the interval between now and now_dash\<close>
axiomatization where
  DC : "now \<le> now' \<Longrightarrow> (\<forall>t. t > now \<and> t < now' \<longrightarrow> h t = h' t) \<Longrightarrow> (df :: dform) h now now' = df h' now now'"

subsection \<open>Duration Calculus operators and lemmas proved\<close>

text \<open>Special assertions \<and> lemmas proved\<close>

text \<open>almost P, P holds everywhere except for the rightmost point, not almost everywhere, over the interval.
The reason is that, for continuous evolution, it escapes whenever a violation is met.
A special case is that, if using almost everywhere, the differential cut rule will not hold anymore.\<close>
definition almost :: "fform \<Rightarrow> dform" where
(*"almost P \<equiv> % h n nd. (nd-n>0) & (\<not>(\<exists> a b.(n\<le>a & a<b & b\<le>nd) & (\<forall> t. t>a & t<b \<longrightarrow> \<not>P(h(t)))))"*)
(*An alternative definition of almost*)
(*"almost P \<equiv> \<lambda>h n nd. (nd-n>0) \<and> (\<forall>a\<ge>n. \<forall>b\<le>nd. a < b \<longrightarrow> (\<exists>t. t>a \<and> t<b \<and> P(h(t))))"*)
"almost P \<equiv> \<lambda>h n nd. (nd-n>0) \<and> (\<forall>t. t\<ge>n \<and> t < nd \<longrightarrow> P (h (t)))"

definition chop :: "dform \<Rightarrow> dform \<Rightarrow> dform"  ("_[^]_" 80) where
  "chop H M \<equiv> \<lambda>h n nd. \<exists>nm. nm \<ge> n \<and> nm \<le> nd \<and> H h n nm \<and> M h nm nd"

text \<open>The length of the interval l is equal to, greater than, less than T.\<close>
definition elE :: "real \<Rightarrow> dform" where
  "elE T \<equiv> \<lambda>h n nd. (nd-n) = T"
definition elG :: "real \<Rightarrow> dform" where
  "elG T \<equiv> \<lambda>h n nd. (nd-n) > T"
definition elL :: "real \<Rightarrow> dform" where
  "elL T \<equiv> \<lambda>h n nd. (nd-n) < T"

definition dAnd :: "dform \<Rightarrow> dform \<Rightarrow> dform"  (infixl "[[&]]" 79) where
  "P [[&]] Q \<equiv> \<lambda>h n m. P h n m \<and> Q h n m"
definition dOr :: "dform \<Rightarrow> dform \<Rightarrow> dform"  (infixl "[[|]]" 79) where
  "P [[|]] Q \<equiv> \<lambda>h n m. P h n m \<or> Q h n m"
definition dNot :: "dform \<Rightarrow> dform"  ("[[\<not>]]_" 79) where
  "[[\<not>]]P \<equiv> \<lambda>h n m. \<not> P h n m"
definition dImp :: "dform \<Rightarrow> dform \<Rightarrow> dform"  (infixl "[[\<longrightarrow>]]" 79) where
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

lemma chopfor:
  "chop (elE 0 [[|]]almost P) (elE 0 [[|]]almost P) h n nd \<Longrightarrow> (elE 0 [[|]]almost P) h n nd"
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

text \<open>Monotonicity: s \<Rightarrow> t \<Longrightarrow> almost s \<Rightarrow> almost t\<close>
lemma almostmono:
  "\<forall>s. P s \<longrightarrow> Q s \<Longrightarrow> \<forall>h n nd. almost P h n nd \<longrightarrow> almost Q h n nd"
  apply auto
  done 

lemma almostint:
  "now < nowf \<Longrightarrow> \<forall>t. (t\<ge>now \<and> t<nowf) \<longrightarrow> P (f t) \<Longrightarrow> almost P f now nowf"
  apply auto
  done  

subsection \<open>Inference rules for Hybrid CSP: Hybrid Hoare Logic rules\<close>

text \<open>Specification\<close>
definition Valid :: "fform \<Rightarrow> proc \<Rightarrow> fform \<Rightarrow> dform \<Rightarrow> bool" ("{_}_{_; _}" 80) where
  "Valid p c q H \<equiv> \<forall>now h now' h'. semB c now h now' h' \<longrightarrow> p (h now) \<longrightarrow> (q (h' now') \<and> H h' now now')"

definition ValidP :: "fform \<Rightarrow> fform \<Rightarrow> procP \<Rightarrow> fform \<Rightarrow> fform \<Rightarrow> dform \<Rightarrow> dform \<Rightarrow> bool"
  ("{_, _}_{_, _; _, _}" 80) where
  "ValidP pa pb c qa qb Ha Hb == (\<forall> nowp nowq fp fq nowp' nowq' fp' fq'.
    semBP c nowp fp nowq fq nowp' fp' nowq' fq'  \<longrightarrow> 
    pa (fp(nowp)) \<longrightarrow>pb (fq(nowq)) \<longrightarrow> 
    (qa (fp'(nowp'))\<and> qb (fq'(nowq'))\<and> (Ha fp' nowp nowp') \<and> (Hb fq' nowq nowq')))"

subsection{*Inference rules proved sound*} 


(*Skip rule*)
lemma SkipRule : "\<forall> s h now now'. (p s \<longrightarrow> q s) \<and> ((elE 0) h now now'\<longrightarrow> H h now now')
         \<Longrightarrow> {p} Skip {q; H}"
by (auto simp add:Valid_def)
 
(*Assignment rule*)
lemma AssignRRule  :" (\<forall> s. p s \<longrightarrow> (q (% y. if (y = x) then (evalE f s) else s y)))
                   \<and> (\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')) ==>
       {p} ((RVar x) := f) {q; H}"
apply (simp add:Valid_def, auto)
done

(*Sequential rule*)
(*The proof is complicated because of the existence of chop operator.*)
lemma SequentialRule_aux : " {p} P {m; H} \<Longrightarrow> {m} Q {q; G} ==>
             {p} P;  Q {q; H [^] G}" 
apply  (simp add:Valid_def, auto)
apply (subgoal_tac "now \<le> now'a \<and> now'a \<le> now'\<and> H h' now now'a = H f' now now'a")
apply metis
apply (rule conjI)
apply (cut_tac P = "P" and now = now and  now'=now'a and f = "h" and f' = "f'" in sem1, simp)
apply metis
apply (rule conjI)
apply (cut_tac P = "Q" and now = now'a and  now'=now' and f = "f'" and f' = "h'" in sem1, simp)
apply metis
apply (cut_tac P = "P" and now = now and  now'=now'a and f = "h" and f' = "f'" in sem1, simp)
apply (cut_tac df = H and now = now and now' = now'a and h = h' and h' = f' in DC, auto)
apply (cut_tac P = Q in  sem2, auto)
done

lemma SequentialRule : " {p} P {m; H} \<Longrightarrow> {m} Q {q; G} ==> (\<forall> h m n. (H [^] G) h m n \<longrightarrow> M h m n) \<Longrightarrow>
             {p} P;  Q {q; M}" 
apply (cut_tac P = P and  Q = Q  and  p = p and  q =q and m = m and H = H  and  G = G in  SequentialRule_aux, auto)
apply (simp add:Valid_def)
done


(*Conditional rule*)
lemma ConditionTRule : " ((\<forall> s. p s \<longrightarrow> ( b s)) \<and> {p} P {q; H})
             ==> {p} IF b P {q; H}"
apply (simp add:Valid_def, auto)
done

lemma ConditionFRule : " ((\<forall> s. p s \<longrightarrow> (q s \<and> (\<not>   b s))) \<and> (\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')))
                          ==> {p} IF b P {q; H}"
apply (simp add:Valid_def, auto)
done

lemma ConditionGRule : " {p [&] b} P {q; H} \<and> {p [&] ([\<not>]b)} Q {q; H}
             ==> {p} IFELSE b P Q{q; H}"
apply (simp add:Valid_def fAnd_def fNot_def, auto)
done

declare almost_def [simp del]
declare chop_def [simp del]
(*Assume v'=E is the differential equation for the continuous evolution.*)
(*This proof takes most effort for solving the invariant-related constraints, which will be passed to an 
external oracle for invariant generation in fact. So don't worry.*)
lemma ContinuousRule : 
"\<forall> s u. ( ( \<forall> y. y \<noteq> v \<longrightarrow> s y = u y) \<longrightarrow> (p s) \<longrightarrow> (p u)) \<and>
 ( \<forall> s.  Init s \<longrightarrow>  Inv s)
 \<and> (\<forall> s.  (p [&] (Inv) [&] ([\<not>]b)) s \<longrightarrow> q s)
 \<and> (\<forall> s. (exeFlow (<[v]:E&&Inv&b>) (Inv)) s \<longrightarrow> Inv s)
 \<and>  (\<forall> h now now'. ((elE 0) h now now' \<or> (almost (Inv [&] p  [&] b)) h now now') \<longrightarrow>
                  H h now now')
 ==> {Init [&] (p::fform)} <[v]:E&&Inv&(b)> {q; H}"
apply (simp add:Valid_def) apply clarify
apply (subgoal_tac "\<forall> t. t\<ge>now & t\<le>now' \<longrightarrow> exeFlow (<[v]:E&&Inv&b>) (Inv) (h'(t))")
prefer 2
apply (simp add:exeFlow_def)
apply (metis fAnd_def)
apply auto
apply (metis fAnd_def)
apply (subgoal_tac "(p [&] Inv) (\<lambda> y. if y = v then Solution (Flow [v] E) (h now) (now + d - now) else h now y)")
apply (simp add:fAnd_def)+
apply (rule conjI, auto)
apply (subgoal_tac "\<forall> y.  y \<noteq> v \<longrightarrow> (h(now)) y = ((\<lambda> y. if y = v 
   then Solution (Flow [v] E) (h now) (now + d - now) else h now y)) y")
apply smt     
apply auto 
apply (subgoal_tac "exeFlow (<[v]:E&&Inv&b>) (Inv)
                    (\<lambda> y. if y =  v 
        then Solution (Flow [v] E) (h now) (now+d - now) else h now y)")
apply (metis (no_types, lifting))
apply (drule_tac x = "now +d" in spec, auto)
apply (subgoal_tac "almost (Inv [&] p [&] b) 
(\<lambda>t. if t \<le> now + d \<and> now < t then \<lambda> y. if y = v 
then Solution (Flow [v] E) (h now) (t - now) else h now y else h t) now (now+d)", auto)
apply (rule almostint, auto)
apply (simp add:fAnd_def)
apply (rule conjI)
apply (subgoal_tac "exeFlow (<[v]:E&&Inv&b>) (Inv)
                    (\<lambda> y. if y = v 
        then Solution (Flow [v] E) (h now) (t - now) else h now y)")
apply (metis (no_types, lifting)) 
apply (drule_tac x = "t" in spec, auto)
apply (subgoal_tac "\<forall> y. y \<noteq> v \<longrightarrow> (h(now)) y = ((\<lambda> y. if y = v 
   then Solution (Flow [v] E) (h now) (t - now) else h now y)) y")
apply smt
apply auto
by (smt fAnd_def) 

(*We simple extend the above rule to the general case where the continuous are a list of variables not just one.
The proof can be given in the same way.*)
primrec notcontain :: "string \<Rightarrow> string list \<Rightarrow> bool" 
where
"notcontain a ([]) = True" |
"notcontain a (e # Elist) = (if a = e then False else (notcontain a Elist))"

axiomatization where ContinuousRuleGT:
" (\<forall> s. (p) s --> b s)
\<and> ( \<forall> s.  p s \<longrightarrow>  Inv s)
 \<and> (\<forall> s.  ((Inv) [&] (close (b)) [&] (close([\<not>]b))) s \<longrightarrow> q s)
 \<and> (\<forall> s. (exeFlow (<V:E&&Inv&b>) (Inv)) s \<longrightarrow> Inv s)
 \<and>  (\<forall> h now now'. ((elE 0) h now now' \<or> (almost (Inv [&]  close(b))) h now now') \<longrightarrow>
                  H h now now')
 ==> {p} <V:E&&Inv&(b)> {q; H}"

axiomatization where ContinuousRuleGF:
" \<forall> s. p s \<longrightarrow> (([\<not>] b) [&]q) s
 ==> {p} <V:E&&Inv&(b)> {q; elE 0}"


text \<open>Shallow definition: a variable does not affect the formula \<close>
definition not_in_fform:: "string \<Rightarrow> fform \<Rightarrow> bool"  where
  "not_in_fform w P = (\<forall> s u. ((\<forall> y. y \<noteq> w \<longrightarrow> s y = u y)) \<longrightarrow> (P s \<longleftrightarrow> P u))"

definition not_in_dform:: "string \<Rightarrow> dform \<Rightarrow> bool"  where
  "not_in_dform w Q = (\<forall>h l n nd. ((\<forall> y. y \<noteq> w \<longrightarrow> (\<forall> t. t \<ge> n \<and> t \<le> nd \<longrightarrow> h(t) y = l(t) y)))
  \<longrightarrow> ((Q h n nd \<longrightarrow> Q l n nd) \<and> (Q l n nd \<longrightarrow> Q h n nd)))"

lemma not_in_fform_update:
  "not_in_fform w P \<Longrightarrow> P (\<lambda>y. if y \<noteq> w then s y else c) \<longleftrightarrow> P s"
  by (simp add: not_in_fform_def)

lemma not_in_dform_update:
  "not_in_dform w Q \<Longrightarrow> Q (\<lambda>t. if t \<le> nd \<and> n \<le> t then \<lambda>y. if y \<noteq> w then h t y else l t y else h t) n nd \<longleftrightarrow> Q h n nd"
  apply (simp add:not_in_dform_def)
  by smt

text \<open>Ghost rule for continuous evolution\<close>
lemma GhostRule : 
  assumes "(w \<notin> set VL)"
    and "not_in_fform w p"
    and "not_in_fform w q"
    and "not_in_dform w H"    
    and "{pre} <(VL@[w]):(EL@[F])&&Inv&(b)> {post; HF}"
    and " \<forall> s. \<exists> a. (let sa = (\<lambda> y. (if y \<noteq> w then s y else a)) in p s \<longleftrightarrow>  pre sa)"
    and "\<forall> s. \<exists> a. (let sa = (\<lambda> y. (if y \<noteq> w then s y else a)) in  q s \<longleftrightarrow> post sa)"
    and "\<forall>h n nd. \<exists> xa. (let ha = (\<lambda>t. if t \<le> nd \<and> n \<le> t then (\<lambda> y. (if y \<noteq> w then h t y else xa t y)) else h t)
           in  H h n nd \<longleftrightarrow> HF ha n nd)"
  shows "{p} <VL:EL&&Inv&(b)> {q; H}"
  sorry
(*
proof -
  have "\<forall>now h now' h'.
       semB (<[v, w]:[E, F]&&Inv&b>) now h now' h' \<longrightarrow>
       (Init [&] p) (h now) \<longrightarrow> q (h' now') \<and> H h' now now'"
    using assms(4) unfolding Valid_def by auto
  have "\<forall>now h now' h'.
       semB (<[v]:[E]&&Inv&b>) now h now' h' \<longrightarrow> (Init [&] p) (h now) \<longrightarrow> q (h' now') \<and> H h' now now'"
  proof -
    {
      fix now h now' h'
      assume semE: "semB (<[v]:[E]&&Inv&b>) now h now' h'"
        and Init: "(Init [&] p) (h now)" 
      define nowf where "nowf = now'"
      
      have semEF: "\<exists> hf. semB (<[v, w]:[E, F]&&Inv&b>) now h nowf hf \<and> 
        ((\<forall> y i.(y, i) \<noteq> (fst (w), snd (w)) \<longrightarrow> (\<forall> t. t \<ge> now \<and> t \<le> nowf \<longrightarrow> hf(t) (y, i) = h'(t) (y, i))))"
        sorry 
      then obtain hf where 
        EF: "semB (<[v, w]:[E, F]&&Inv&b>) now h nowf hf"
        and hfh: "((\<forall> y i.(y, i) \<noteq> (fst (w), snd (w)) \<longrightarrow> (\<forall> t. t \<ge> now \<and> t \<le> nowf \<longrightarrow> hf(t) (y, i) = h'(t) (y, i))))"
        and post: "q (hf nowf) \<and> H hf now nowf"
        using assms(4) Init unfolding Valid_def by auto
      have  "((\<forall> y i.(y, i) \<noteq> (fst (w), snd (w)) \<longrightarrow> hf(nowf) (y, i) = h'(nowf) (y, i)))"
      proof -
        {
          fix y i assume yi: "(y, i) \<noteq> (fst (w), snd (w))"
          have "(\<forall> t. t \<ge> now \<and> t \<le> nowf \<longrightarrow> hf(t) (y, i) = h'(t) (y, i))" using hfh yi by auto
          then have "hf(nowf) (y, i) = h'(nowf) (y, i)" using EF sem1 by auto
        }
        then show ?thesis by auto
      qed
      then have qf: "q (h' now')" using post assms(2) not_in_fform_def unfolding nowf_def by auto
      then have Hf: "q (h' now') \<and> H h' now now'" using assms(3) hfh post unfolding not_in_dform_def nowf_def by blast
    }
    then show ?thesis by auto
  qed
  then show ?thesis unfolding Valid_def by auto
qed
*)

lemma DiffCutRule : 
  assumes I: "{p} <[v]:E&&Inv&(b)> {I; almost I [[|]] elE 0}"
    and C: "{p} <[v]:E&&Inv&(b[&]I)> {q; H}"
  shows "{p} <[v]:E&&Inv&(b)> {q; H}"
proof (simp add:Valid_def, clarify)  
  have "\<forall>now h now' h'. semB (<[v]:E&&Inv&b>) now h now' h' \<longrightarrow> p (h now) 
    \<longrightarrow> I (h' now') \<and> (almost I [[|]] elE 0) h' now now'"
    using I unfolding Valid_def by auto
  have semI: "semB (<[v]:E&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> semB (<[v]:E&&Inv&b [&] I>) now h now' h'"
    for now h now' h'
    apply (ind_cases "semB (<[v]:E&&Inv&b>) now h now' h'")
    subgoal 
    proof -
      assume a: "p (h now)" and b: "now' = now" and c: "h' = h" and d: "([\<not>]b) (h now)"
      show "semB (<[v]:E&&Inv&b [&] I>) now h now' h'"
      proof -
        have "([\<not>] (b [&] I)) (h now)" using d unfolding fNot_def fAnd_def by auto
        then show ?thesis
          by (simp add: b c continuousBF)
      qed
    qed
    subgoal for d
    proof -
      assume a: "p (h now)" and b: "now' = now + d"  
        and c: "h' = (\<lambda>t. if t \<le> now + d \<and> now < t then \<lambda> y. if y = v then Solution (Flow [v] E) (h now) (t - now) else h now y else h t)"
        and d: "0 < d" and e: "\<forall>m. m < now + d \<and> now \<le> m \<longrightarrow>
          b (if now < m then \<lambda> y. if y = v then Solution (Flow [v] E) (h now) (m - now) else h now y else h m)"
        and f: "([\<not>]b) (\<lambda> y. if y = v then Solution (Flow [v] E) (h now) (now + d - now) else h now y)"
      show "semB (<[v]:E&&Inv&b [&] I>) now h now' h'"
      proof -
        have "semB (<[v]:E&&Inv&b>) now h (now + d) h'" 
          using b c d e f continuousBT[of d now v  E h b Inv] by auto
        then have "I (h' now') \<and> (almost I [[|]] elE 0) h' now now'" 
          using a I b unfolding Valid_def by auto
        then have almostI: "I (h' now') \<and> (almost I) h' now now'" 
          using b c d unfolding elE_def dOr_def by auto
        have "([\<not>] (b [&] I))(h' (now + d))"
          using f d c unfolding fNot_def fAnd_def by auto
        moreover have "\<forall>m. m < now + d \<and> now \<le> m \<longrightarrow> (b [&] I) (h' (m))"
          using almostI b e c unfolding almost_def fAnd_def by auto
        ultimately show ?thesis using b c d continuousBT[of d now v  E h "b[&]I" Inv] unfolding Let_def 
          by auto
      qed
    qed
    done

  have "semB (<[v]:E&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> q (h' now') \<and> H h' now now'"
    for now h now' h'
    using C semI unfolding Valid_def by meson
  then show "\<And>now h now' h'. semB (<[v]:E&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> q (h' now') \<and> H h' now now'"
    by auto
qed 

(*There are three rules for parallel  composition, which covers all the cases.*)
(*Parallel rule for the case without communication*)
lemma Parallel1Rule : "chanset P = {} \<and> chanset Q = {} \<Longrightarrow> {pp} P {qp; Hp} \<Longrightarrow> {pq} Q {qq; Hq}
                       \<Longrightarrow> {pp, pq} P||Q {qp, qq; Hp, Hq}"
apply (clarsimp simp:Valid_def ValidP_def)
by (meson semB3)

(*Parallel rule for the case with communication at the end.*)
lemma Communication_aux: 
"  semBP (P; Cm (ch??(RVar x)) || Q; Cm (ch!!e)) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
    \<forall> nowp nowq fp fq nowp' nowq' fp' fq'.
          semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<longrightarrow>
          px (fp nowp) \<longrightarrow> py (fq nowq) \<longrightarrow> qx (fp' nowp') \<and> qy (fq' nowq') \<and> Hx fp' nowp nowp' \<and> Hy fq' nowq nowq' \<Longrightarrow>
       \<forall>s. qx s \<longrightarrow> rx (\<lambda> y. if y = x then evalE e s else s y) \<Longrightarrow>
       \<forall>s. qy s \<longrightarrow> ry s \<Longrightarrow>
       \<forall>h n m. (Hx[^](elE 0 [[|]]almost qx)) h n m \<longrightarrow> Gx h n m \<Longrightarrow>
       \<forall>h n m. (Hy[^](elE 0 [[|]]almost qy)) h n m \<longrightarrow> Gy h n m \<Longrightarrow>      
       px (fp nowp) \<Longrightarrow> py (fq nowq) \<Longrightarrow> rx (fp' nowp') \<and> ry (fq' nowq') \<and> Gx fp' nowp nowp' \<and> Gy fq' nowq nowq'"
apply (ind_cases "semBP (P; Cm (ch??(RVar x)) || Q; Cm (ch!!e)) nowp fp nowq fq nowp' fp' nowq' fq'")
apply (simp add:chanset_def) 
apply (simp add:chanset_def) 
apply (subgoal_tac " qx (fp'a nowp'a) \<and> qy (fq'a nowq'a) \<and> Hx fp'a nowp nowp'a \<and> Hy fq'a nowq nowq'a")
prefer 2
apply metis
apply (rule conjI) 
apply (subgoal_tac "fp' nowp' = (\<lambda> y. if y = x then evalE e (fp'a nowp'a) else (fp'a nowp'a) y)", simp)
apply (metis less_irrefl)
apply (rule conjI)
apply (metis max.cobounded1 max_def_raw not_less)
apply (rule conjI)
(*to prove GX*)
apply (subgoal_tac "(Hx[^](elE 0 [[|]] almost qx)) fp' nowp nowp'", simp)
apply (subgoal_tac "Hx fp' nowp nowp'a",simp)
prefer 2 
apply (subgoal_tac "Hx fp'a nowp nowp'a = Hx fp' nowp nowp'a", simp)
apply (smt DC semB1) 
apply (smt almostint chop_def dOr_def semB1)
(*to prove Gy, just copy the proof for Gx with a little adaption*)
apply (subgoal_tac "(Hy[^](elE 0 [[|]] almost qy)) fq' nowq nowq'", simp)
apply (subgoal_tac "Hy fq' nowq nowq'a",simp)
prefer 2 
apply (subgoal_tac "Hy fq'a nowq nowq'a = Hy fq' nowq nowq'a", simp)
apply (smt DC semB1)
by (smt almostint chop_def dOr_def semB1)

lemma CommunicationRule : 
  " ({px, py} (P || Q) {qx, qy; Hx, Hy}) \<Longrightarrow>  
   (\<forall> s. qx s \<longrightarrow> (rx (% y. if (y=x) then (evalE e s) else s y)))
 \<and> (\<forall> s. qy s \<longrightarrow> ry s)
 \<and> (\<forall> h n m. (Hx[^](elE 0 [[|]]almost qx)) h n m \<longrightarrow> Gx h n m) \<and> 
   (\<forall> h n m. (Hy[^](elE 0 [[|]]almost qy)) h n m \<longrightarrow> Gy h n m)
  ==>
{px, py} (P;Cm (ch??(RVar (x))))||(Q; (Cm (ch!!e))) {rx, ry; Gx, Gy}"
  apply (clarsimp simp:ValidP_def) 
  apply (cut_tac P = P and Q = Q and ch = ch and px = px and py = py and rx = rx and ry = ry and
    Gx = Gx and Gy = Gy in Communication_aux, auto)
  done  

(*Parallel rule for the case with non-communication process at the end.*)
lemma Parallel2_aux : "semBP (P; U || Q; V) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
        \<forall>nowp nowq fp fq nowp' nowq' fp' fq'.
          semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<longrightarrow>
          pp (fp nowp) \<longrightarrow> pq (fq nowq) \<longrightarrow> qp (fp' nowp') \<and> qq (fq' nowq') \<and> 
        Hp fp' nowp nowp' \<and> Hq fq' nowq nowq' \<Longrightarrow>
       \<forall>now h now' h'. semB U now h now' h' \<longrightarrow> qp (h now) \<longrightarrow> qu (h' now') \<and> Hu h' now now' \<Longrightarrow>
       \<forall>now h now' h'. semB V now h now' h' \<longrightarrow> qq (h now) \<longrightarrow> qv (h' now') \<and> Hv h' now now' \<Longrightarrow>
       chanset P \<noteq> {} \<Longrightarrow> chanset Q \<noteq> {} \<Longrightarrow> chanset U = {} \<Longrightarrow> chanset V = {} \<Longrightarrow>
       pp (fp nowp) \<Longrightarrow> pq (fq nowq) \<Longrightarrow> qu (fp' nowp') \<and> qv (fq' nowq') \<and> 
             (Hp[^]Hu) fp' nowp nowp' \<and> (Hq[^]Hv) fq' nowq nowq'"
apply (ind_cases "semBP (P; U || Q; V) nowp fp nowq fq nowp' fp' nowq' fq'")
apply (simp add:chanset_def)
prefer 2 apply (simp add:chanset_def)
prefer 2 apply (simp add:chanset_def)
apply (subgoal_tac "qp (fp'a nowp'a) \<and> qq (fq'a nowq'a) \<and> Hp fp'a nowp nowp'a \<and> Hq fq'a nowq nowq'a")
prefer 2
apply metis
apply (rule conjI) apply metis
apply (rule conjI) apply metis
apply (subgoal_tac "(Hu) fp' nowp'a nowp' ")
apply (subgoal_tac "(Hv) fq' nowq'a nowq'")
prefer 2 apply metis prefer 2 apply metis
apply (subgoal_tac " Hq fq' nowq nowq'a")
apply (subgoal_tac " Hp fp' nowp nowp'a ")
apply (rule conjI)
apply (unfold chop_def)
apply (metis sem1 semB1)
apply (metis sem1 semB1)
apply (subgoal_tac "Hp fp'a nowp nowp'a = Hp fp' nowp nowp'a", simp)
apply (smt DC sem2 semB1) 
apply (subgoal_tac " Hq fq'a nowq nowq'a =  Hq fq' nowq nowq'a", simp) 
by (smt DC sem2 semB1)


lemma Parallel2Rule : "{pp, pq} P||Q {qp, qq; Hp, Hq}  \<Longrightarrow> chanset P \<noteq> {} \<and> chanset Q \<noteq> {} \<Longrightarrow> 
                          {qp} U {qu; Hu} \<Longrightarrow> {qq} V {qv; Hv} \<Longrightarrow> chanset U = {} \<and> chanset V = {} 
                       \<Longrightarrow> {pp, pq} P; U||Q; V {qu, qv; Hp [^] Hu, Hq [^] Hv}"
apply (clarsimp simp:Valid_def ValidP_def)
apply (rule Parallel2_aux)
apply simp+
done
 
(*Repetition rule*)
  
  
lemma Repetition_aux_1: " semB (P* NUM 0) now h now' h' \<Longrightarrow>
       \<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m \<Longrightarrow>
       \<forall>now h now' h'. semB P now h now' h' \<longrightarrow> Inv (h now) \<longrightarrow> Inv (h' now') \<and> H h' now now' \<Longrightarrow>
       Inv (h now) \<Longrightarrow> Inv (h' now') \<and> (H h' now now' \<or> now' = now)"
  apply (ind_cases "semB (P* NUM 0) now h now' h'", auto)
  done
    
    
lemma Repetition_aux_2: " (\<And>now h now' h'. semB (P* NUM N) now h now' h' \<Longrightarrow> Inv (h now) \<Longrightarrow> Inv (h' now') \<and> (H h' now now' \<or> now' = now)) \<Longrightarrow>
       semB (P* NUM Suc N) now h now' h' \<Longrightarrow>
       \<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m \<Longrightarrow>
       \<forall>now h now' h'. semB P now h now' h' \<longrightarrow> Inv (h now) \<longrightarrow> Inv (h' now') \<and> H h' now now' \<Longrightarrow>
       Inv (h now) \<Longrightarrow> Inv (h' now') \<and> (H h' now now' \<or> now' = now)"
  apply (ind_cases "semB (P* NUM Suc N) now h now' h'")
  apply simp
  by (smt DC chop_def sem1 sem2)

lemma Repetition_aux: "semB (P* NUM N) now h now' h' \<Longrightarrow> 
                     \<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m \<Longrightarrow>
                     \<forall>now h now' h'. semB P now h now' h' \<longrightarrow> Inv (h now) \<longrightarrow> Inv (h' now') \<and> H h' now now' \<Longrightarrow>
                     Inv (h now) \<Longrightarrow> Inv (h' now') \<and> (H [[|]] (\<lambda>h n nd. nd = n)) h' now now'"
apply (simp add:dOr_def)
apply (induction N arbitrary: now h now' h')
apply (cut_tac H = H and P = P and now = now and h = h and now' = now' and h' = h' in Repetition_aux_1) 
apply simp+
apply (cut_tac P = P and N = N and now = now and h = h and h' = h' and Inv = Inv in Repetition_aux_2, auto)
done

lemma RepetitionRule: "\<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m \<Longrightarrow> {I} P {I; H}  
                      ==>  {I} P*&&I {I; (H [[|]] (elE 0))} "
  apply (simp add:Valid_def) apply clarify 
  apply (rule Repetition_aux)
   apply simp+
  done

   
lemma JoinRule : "{p} P {m; H} \<Longrightarrow> {p} Q {q; G} ==>
             {p} P [[ Q {m [|] q; H [[|]] G}"
  apply (simp add:Valid_def fOr_def dOr_def, auto)
    done



(*Consequence rule*)
lemma ConsequenceRule : "{px} P {qx; Hx} 
                  \<and> (\<forall> s. p s \<longrightarrow> px s) \<and> (\<forall> s. qx s \<longrightarrow> q s)
                  \<and> (\<forall> h n m. Hx h n m \<longrightarrow> H h n m)
            ==> {p} P {q; H}"
apply (simp add:Valid_def)
done

lemma RepetitionRule_a :  "\<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m \<Longrightarrow> {I} P {I; H}  
                      ==>  {I} P*&&I {I; ((elE 0) [[|]] H)} "
                      apply (cut_tac px = "I" and qx = I and Hx = "(H [[|]] (elE 0))" in ConsequenceRule, auto)
                      apply (cut_tac RepetitionRule, auto)
                      using dOr_def by auto
 
(*Case analysis rule*)
lemma CaseRule : "{p [&] pb} P {q; H} \<and> {(p [&] ([\<not>]pb))} P {q; H}
   ==> {p} P {q; H}"
apply (simp add:Valid_def fAnd_def fNot_def, auto)
apply metis+
  done


lemma interrupt1R: "{px, py} (P || Q) {qx, qy; Hx, Hy} \<Longrightarrow>  
         (\<forall> s. qx s \<longrightarrow> (rx (% y. if (y=x) then (evalE e s) else s y))) \<Longrightarrow>
         (\<forall> s. qy s \<longrightarrow> ry s) \<Longrightarrow>
         (\<forall> h n m. (Hx[^](elE 0 [[|]] almost Inv)) h n m \<longrightarrow> Gx h n m) \<Longrightarrow>
         (\<forall> h n m. (Hy[^](elE 0 [[|]] almost qy)) h n m \<longrightarrow> Gy h n m) \<Longrightarrow>
          {px, py} (P; ((<VL:EL && Inv&b>)[[ ((ch??(RVar x))) \<rightarrow> Skip))||(Q; (Cm (ch!!e))) {rx, ry; Gx, Gy}"
  sorry


lemma interrupt2R: "{px, py} (P || Q) {qx, qy; Hx, Hy} \<Longrightarrow>  
         (\<forall> s. qy s \<longrightarrow> (ry (% y. if (y=x) then (evalE e s) else s y))) \<Longrightarrow>
         (\<forall> s. qx s \<longrightarrow> rx s) \<Longrightarrow>
         (\<forall> h n m. (Hx[^](elE 0 [[|]] almost Inv)) h n m \<longrightarrow> Gx h n m) \<Longrightarrow>
         (\<forall> h n m. (Hy[^](elE 0 [[|]] almost qy)) h n m \<longrightarrow> Gy h n m) \<Longrightarrow>
          {px, py} (P; ((<VL:EL && Inv&b>)[[ ((ch!!e)) \<rightarrow> Skip))||(Q; (Cm (ch??(RVar x)))) {rx, ry; Gx, Gy}"
  sorry



end
