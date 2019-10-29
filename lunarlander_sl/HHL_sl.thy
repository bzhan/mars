section \<open>Inference rules for Hybrid CSP: Hybrid Hoare Logic rules\<close>

theory HHL_sl
  imports syntax_sl
begin

text \<open>Specification\<close>
definition Valid :: "'a :: finite fform \<Rightarrow> 'a proc \<Rightarrow> 'a fform \<Rightarrow> 'a dform \<Rightarrow> bool" ("\<Turnstile> {_}_{_; _}" 80) where
  "\<Turnstile> {p} c {q; H} \<longleftrightarrow> (\<forall>now h now' h'. semB c now h now' h' \<longrightarrow> p (h now) \<longrightarrow> (q (h' now') \<and> H h' now now'))"

definition ValidP :: "'a :: finite fform \<Rightarrow> 'a fform \<Rightarrow> 'a procP \<Rightarrow> 'a fform \<Rightarrow> 'a fform \<Rightarrow> 'a dform \<Rightarrow> 'a dform \<Rightarrow> bool"
  ("\<Turnstile> {_, _}_{_, _; _, _}" 80) where
  "\<Turnstile> {pa, pb} c {qa, qb; Ha, Hb} \<longleftrightarrow> (\<forall>nowp nowq fp fq nowp' nowq' fp' fq'.
    semBP c nowp fp nowq fq nowp' fp' nowq' fq'  \<longrightarrow> 
    pa (fp(nowp)) \<longrightarrow> pb (fq(nowq)) \<longrightarrow> 
    qa (fp'(nowp')) \<and> qb (fq'(nowq')) \<and> (Ha fp' nowp nowp') \<and> (Hb fq' nowq nowq'))"

text \<open>HHL rules\<close>

lemma SkipR:
  assumes "\<forall> s h now now'. (p s \<longrightarrow> q s) \<and> ((elE 0) h now now'\<longrightarrow> H h now now') "
  shows "\<Turnstile> {p} Skip {q; H}"
  using assms
  unfolding Valid_def  elE_def by auto

lemma AssignR:
  assumes"(\<forall> s. p s \<longrightarrow> (q (update s x ( e s))))
               \<and> (\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')) " 
  shows "\<Turnstile> {p} (x ::= e) {q; H}"
  using assms
  unfolding Valid_def elE_def by auto

lemma SeqR:
  assumes "\<Turnstile> {p} P {m; H} " 
  and "\<Turnstile> {m} Q {q; G}"
  and "well_DC H"
shows "\<Turnstile> {p} P;  Q {q; H[^]G}"
proof-
   have "semB (P; Q) now h now' h' \<longrightarrow> p (h now) \<longrightarrow> 
    q (h' now') \<and> (\<exists>nm\<ge>now. nm \<le> now' \<and> H h' now nm \<and> G h' nm now')" for now h now' h'
   proof-
   {
     assume pq:"semB (P; Q) now h now' h'"
     and pre:"p (h now)"
     obtain now'' h'' where p:"semB P now h now'' h''" and q:"semB Q now'' h'' now' h'"using pq by auto 
     have step1:"m (h'' now'')"using p pre assms unfolding Valid_def by auto  
     have step2:"H h'' now now''" using p pre assms unfolding Valid_def by auto
     have step3:"q (h' now')" using step1 q assms unfolding Valid_def by auto 
     have step4:"G h' now'' now'" using step1 q assms unfolding Valid_def by auto
     have step5: "(now'' \<le> now' \<and> (\<forall>t. t < now'' \<or> t > now' \<longrightarrow> h'' t = h' t))"
       using q by (simp add: sem1 sem2)
     have step6:"(\<forall>t. now < t \<and> t < now'' \<longrightarrow> h'' t = h' t)" using step5 by auto
     have step7:"now \<le> now''" using p sem1 by metis
     have step8:"H h' now now''" using assms(3) step2 step6 step7 unfolding well_DC_def by auto
     have step9:"q (h' now') \<and> (\<exists>nm\<ge>now. nm \<le> now' \<and> H h' now nm \<and> G h' nm now')" using step3 step4 step8 step5 step7 by blast
   }
   then show ?thesis by auto
 qed
  then show ?thesis 
    unfolding Valid_def chop_def by blast
qed

lemma CondTR: 
  assumes"\<forall> s. p s \<longrightarrow> ( b s)"
      and"\<Turnstile> {p} P {q; H} "
    shows"\<Turnstile> {p} IF b P {q; H}"
  using assms unfolding Valid_def by auto


lemma CondFR: 
  assumes"\<forall> s. p s \<longrightarrow> (q s \<and> (\<not> b s))" 
      and"\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')"
    shows"\<Turnstile> {p} IF b P {q; H}"
  using assms
  unfolding elE_def Valid_def by auto

lemma IChoiceR: 
  assumes"\<Turnstile> {p} P {m; H} "
      and"\<Turnstile> {p} Q {q; G}"
    shows"\<Turnstile> {p} P \<sqinter> Q {m [\<or>] q; H [[\<or>]] G}"
  using assms
  unfolding Valid_def fOr_def dOr_def by auto

lemma repetitionNR: 
  assumes "\<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m "
      and "\<Turnstile> {I}P{I; H}"
      and "well_DC H "
    shows "\<Turnstile> {I}(P* NUM N) {I; H [[\<or>]] elE 0}"
  unfolding Valid_def
  apply (induction N) 
  apply clarify
  subgoal  premises pre1 for now h now' h'
  proof-
    {
      assume cond1:"semB (P* NUM 0) now h now' h'"
         and cond2:"I (h now)"
        have step1:"now' = now" and "h' = h"
          using cond1 by auto
        then have step2:"I (h' now')" using cond2 by auto
        have step3:"elE 0 h' now now'"
          using step1 unfolding elE_def by auto
        have step4:"I (h' now') \<and> (H [[\<or>]] elE 0) h' now now'"
          using step2 step3 unfolding dOr_def by auto
    }
    then show ?thesis using pre1 by auto 
  qed
  apply clarify
  subgoal premises pre2 for N nowa ha now'a h'a
  proof-
    {
      assume cond1:" \<forall>now h now' h'.
          semB (P* NUM N) now h now' h' \<longrightarrow> I (h now) \<longrightarrow> I (h' now') \<and> (H [[\<or>]] elE 0) h' now now' "
         and cond2:" semB (P* NUM Suc N) nowa ha now'a h'a"
         and cond3:"I (ha nowa)"
      have step1:"Suc N >0" by auto
      obtain nowd and hd where PR:"semB P nowa ha nowd hd" and PNR:"semB (P* NUM  N ) nowd hd now'a h'a"
        using cond2 step1 
        using RepNE [where P="P" and now="nowa" and f="ha" and now'= "now'a" and f'="h'a" and N="Suc N" and Pa="thesis"]
        by simp
      have step2:"I (hd nowd)" using cond3 PR assms(2) unfolding Valid_def by auto
      have step3:"H hd nowa nowd" using cond3 PR assms(2) unfolding Valid_def by auto
      have step4:"I (h'a now'a)" using PNR step2 cond1  by metis
      have step5:"(H [[\<or>]] elE 0) h'a nowd now'a" using PNR step2 cond1  by metis
      have step6:"H h'a nowa nowd" using PR PNR sem1 sem2 step3 assms(3) unfolding well_DC_def by metis
      have step7:"H h'a nowa now'a" using step5 step6 assms(1) unfolding dOr_def chop_def elE_def
        by (metis PNR PR eq_iff_diff_eq_0 sem1)
      have step8:"I (h'a now'a) \<and> (H [[\<or>]] elE 0) h'a nowa now'a" using step4 step7 unfolding dOr_def by auto
    }
    then show ?thesis using pre2 by auto
  qed
  done

lemma  repetR: 
  assumes "\<forall>h n m. (H[^]H) h n m \<longrightarrow> H h n m "
      and "\<Turnstile> {I}P{I; H}"
      and "well_DC H "
    shows "\<Turnstile> {I} P*&&I {I; (H [[\<or>]] (elE 0))}"
  apply(subgoal_tac"\<forall>N. \<Turnstile> {I}(P* NUM N) {I; H [[\<or>]] elE 0}")
  subgoal
    unfolding Valid_def  by force
  using repetitionNR assms by metis

lemma continTR: 
  assumes"\<forall> s. (Inv [&][\<not>]b) s \<longrightarrow> q s "
     and "\<forall> tr d. ((ODEsol ode tr d \<and> p (tr 0))\<longrightarrow> INV Inv tr d) " 
     and "\<forall> h now now'. (almost (Inv [&]  b) [[\<or>]] elE 0) h now now' \<longrightarrow>H h now now' " 
   shows "\<Turnstile> {p} <ode && Inv&b> {q; H}"
  unfolding Valid_def 
  apply auto
  subgoal
    using assms unfolding fAnd_def fNot_def INV_def ODEsol_def apply auto
    done
  subgoal premises pre for now h d pa
  proof-
    {
      assume cond1:"0 \<le> d " 
      and cond2:"ODEsol ode pa d " 
      and cond3:"\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (pa t) "
      and cond4:"\<not> b (pa d) " 
      and cond5:"h now = pa 0 " 
      and cond6:"p (pa 0) "
      then have step1:"(almost (Inv [&]  b) [[\<or>]] elE 0) (\<lambda>t. if t \<le> now + d \<and> now \<le> t then pa (t - now) else h t) now (now + d)"
        using assms(2) unfolding dOr_def almost_def fAnd_def elE_def INV_def by force 
      then have step2:" H (\<lambda>t. if t \<le> now + d \<and> now \<le> t then pa (t - now) else h t) now (now + d)"
        using assms(3) by blast
    }
    then show ?thesis using pre by auto
  qed
  done

lemma diffCut: 
  assumes "\<Turnstile> {p} <ode && Inv&b> {I; almost I [[\<or>]] elE 0} " 
      and "\<Turnstile> {p} <ode && Inv&(b[&]I)> {q; H} " 
    shows "\<Turnstile> {p} <ode && Inv&b> {q; H}" 
proof (simp add:Valid_def) 
  have step1:"\<forall>now h now' h'. semB (<ode&&Inv&b>) now h now' h' \<longrightarrow> p (h now) 
    \<longrightarrow> I (h' now') \<and> (almost I [[\<or>]] elE 0) h' now now'"
    using assms(1) unfolding Valid_def by auto
  have step2: "semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> I (h' now')"
    for now h now' h'
    using step1 by auto
  have step3: "semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> (almost I [[\<or>]] elE 0) h' now now'"
    for now h now' h'
    using step1 by auto
  have step4: "semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> semB (<ode&&Inv&(b [&] I)>) now h now' h'"
    for now h now' h'
    using step2 [of now h now' h'] step3 [of now h now' h'] 
    unfolding almost_def dOr_def elE_def apply simp
    apply (ind_cases "semB (<ode&&Inv&b>) now h now' h'") 
    apply auto
    subgoal premises pre1 for d pa
    proof-
      {
        assume cond1:"p (pa 0) " 
           and cond2:"I (pa d)"
           and cond3:"now' = now + d " 
           and cond4:"h' = (\<lambda>t. if t \<le> now + d \<and> now \<le> t then pa (t - now) else h t) "
           and cond5:"ODEsol ode pa d " 
           and cond6:" \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (pa t) " 
           and cond7:"\<not> b (pa d) " 
           and cond8:"h now = pa 0 "
           and cond9:"0 < d" 
           and cond10:"\<forall>t. now \<le> t \<and> t < now + d \<longrightarrow> I (pa (t - now))"
        have step1:"d\<ge>0" using cond9 by auto
        have step2:" \<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> (b [&] I) (pa t) " unfolding fAnd_def using cond6 cond10 by smt
        have step3:" \<not> (b [&] I) (pa d) " unfolding fAnd_def using cond7 by auto
        have step4:"0 \<le> d \<and> ODEsol ode pa d \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> (b [&] I) (pa t)) \<and>
    \<not> (b [&] I) (pa d) \<and> h now = pa 0 "
          using step1 step2 step3 cond5 cond8 by auto

      }
      then show ?thesis using pre1 continuous[of d ode pa "b [&] I" h now Inv ] by auto
    qed
    subgoal premises pre2 for pa
    proof-
      {
        assume cond1:"p (pa 0)"
           and cond2:"I (pa 0)" 
           and cond3:"now' = now"
           and cond4:"h' = (\<lambda>t. if t \<le> now \<and> now \<le> t then pa (t - now) else h t)"
           and cond5:"ODEsol ode pa 0"
           and cond6:"\<forall>t. 0 \<le> t \<and> t < 0 \<longrightarrow> b (pa t)"
           and cond7:"\<not> b (pa 0)"
           and cond8:"h now = pa 0"
        have step1:"\<forall>t. 0 \<le> t \<and> t < 0 \<longrightarrow> (b [&] I) (pa t)" by auto
        have step2:" \<not> (b [&] I) (pa 0)" unfolding fAnd_def using cond7 by auto
        have step3:"(0 :: real) \<le> 0" by auto 
        have step4:"(0 :: real) \<le> 0 \<and> ODEsol ode pa 0 \<and>(\<forall>t. 0 \<le> t \<and> t < 0 \<longrightarrow> (b [&] I) (pa t)) \<and>\<not> (b [&] I) (pa 0) \<and> h now = pa 0 "
          using step1 step2 step3 cond5 cond8 by auto
      }
      then show ?thesis using  pre2 continuous[of 0 ode pa "b [&] I" h now Inv ] by auto
    qed
    done
    have step5:"semB (<ode&&Inv&b>) now h now' h' \<Longrightarrow> p (h now) \<Longrightarrow> q (h' now') \<and> H h' now now'"
    for now h now' h'
    using assms(2) step4 unfolding Valid_def by meson
    then show "\<forall>now h now' h'. semB (<ode&&Inv&b>) now h now' h' \<longrightarrow> p (h now) \<longrightarrow> q (h' now') \<and> H h' now now'"
    by auto
qed 

lemma diffWeak: 
  assumes "\<forall> h now now'. (almost b [[\<or>]] elE 0) h now now' \<longrightarrow> H h now now' " 
    shows "\<Turnstile> {p} <ode && Inv&b> {[\<not>]b; H}"
  unfolding Valid_def apply clarify 
  unfolding fNot_def apply simp
  subgoal for now h  d pa
    apply (subgoal_tac "(almost b [[\<or>]] elE 0)(\<lambda>t. if t \<le> now + d \<and> now \<le> t then pa (t - now) else h t) now (now + d)")
    using assms(1) apply auto
    unfolding almost_def dOr_def elE_def by auto
  done




end