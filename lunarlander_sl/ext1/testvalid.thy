theory testvalid
  imports ext_Complementlemma
begin

inductive out_tassn :: "cname \<Rightarrow> real \<Rightarrow> 'a tassn" where
  "(out_tassn ch v) [OutBlock ch v]"

inductive in_tassn :: "cname \<Rightarrow> real \<Rightarrow> 'a tassn " where
  "(in_tassn ch v) [InBlock ch v]"

inductive wait_tassn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> 'a tassn" where
  "d \<le> 0 \<Longrightarrow> (wait_tassn d p rdy) []"
| "d > 0 \<Longrightarrow> (wait_tassn d p rdy) [WaitBlk d p rdy]"

inductive wait_le_out_tassn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> 'a tassn" where
  "d = 0 \<Longrightarrow> d\<le>T \<Longrightarrow> (wait_le_out_tassn T p rdy ch v) [OutBlock ch (v 0)]"
| "d > 0 \<Longrightarrow> d\<le>T \<Longrightarrow>(wait_le_out_tassn T p rdy ch v) [WaitBlk d p rdy, OutBlock ch (v d)]"

theorem send1:
  assumes "d\<ge>0"
  shows "\<Turnstile> {\<lambda>s t. P s t}
       Cm (ch[!]e)
     {\<lambda>s t. (P s @\<^sub>t (((\<exists>\<^sub>t \<tau> . \<up>(\<tau>\<in>{0..d}) \<and>\<^sub>t (wait_tassn \<tau> (\<lambda>_ .EState s) ({ch}, {}) @\<^sub>t out_tassn ch (e s)))) \<or>\<^sub>t (\<exists>\<^sub>t \<tau> . \<up>(\<tau>\<in>{d<..}) \<and>\<^sub>t (wait_assn \<tau> (\<lambda>_ . EState s) ({ch}, {}))) @\<^sub>t true\<^sub>A)) t}"
  unfolding Valid_def
  apply auto
  apply(elim sendE)
  unfolding join_assn_def disj_assn_def
  subgoal for a b tr1 aa ba tr2
    apply(rule exI[where x="tr1"])
    apply(rule exI[where x="tr2"])
    apply simp
    apply(rule disjI1)
    unfolding ex_assn_def conj_assn_def pure_assn_def
    apply(rule exI[where x="0"])
    using assms
    apply auto
    apply(rule exI[where x="[]"])
    apply auto
     apply(rule )
    apply auto
    apply(rule )
    done
  subgoal for a b tr1 aa ba tr2 da
    apply(cases "da\<le>d")
    subgoal
      apply(rule exI[where x="tr1"])
      apply(rule exI[where x="tr2"])
      apply simp
      unfolding ex_assn_def conj_assn_def pure_assn_def
      apply(rule disjI1)
      apply(rule exI[where x="da"])
      apply auto
      apply(rule exI[where x="[WaitBlk da (\<lambda>_. EState (a, b)) ({ch}, {})]"])
      apply auto
       apply (rule)
       apply auto
      apply(rule )
      done
    apply(cases "da>d")
    subgoal
      apply(rule exI[where x="tr1"])
      apply(rule exI[where x="tr2"])
      apply simp
      unfolding ex_assn_def conj_assn_def pure_assn_def
      apply(rule disjI2)
      apply auto
      apply(rule exI[where x="[WaitBlk da (\<lambda>_. EState (a, b)) ({ch}, {})]"])
      apply auto
       apply(rule exI[where x="da"])
      apply auto
      apply(rule )
      by(auto simp add: true_assn_def)
    by auto
  done




lemma t:
"(\<exists>\<^sub>t \<tau>. \<up>(\<tau>\<in>{0..T}) \<and>\<^sub>t (wait_tassn \<tau> p rdy @\<^sub>t out_tassn ch (v \<tau>))) = wait_le_out_tassn T p rdy ch v"
  apply(rule ext)
  apply(auto simp add: ex_assn_def pure_assn_def conj_assn_def join_assn_def)
  subgoal for t tr1 tr2
    apply(cases rule:wait_tassn.cases[of t p rdy tr1])
      apply auto
    subgoal
      apply(cases rule:out_tassn.cases[of ch "(v 0)" tr2])
       apply auto
      apply(rule )
      by auto
    subgoal
      apply(cases rule:out_tassn.cases[of ch "(v t)" tr2])
       apply auto
      apply(rule wait_le_out_tassn.intros(2))
      by auto
    done
  subgoal for tr
    apply(cases rule: wait_le_out_tassn.cases[of T p rdy ch v tr])
      apply auto
    subgoal
      apply(rule exI[where x=0])
      apply auto
      apply(rule exI[where x="[]"])
      apply auto
       apply(rule)
       apply auto
      apply(rule)
      done
    subgoal for d
      apply(rule exI[where x="d"])
      apply auto
      apply(rule exI[where x="[WaitBlk d p rdy]"])
      apply auto
       apply(rule)
       apply auto
      apply(rule)
      done
    done
  done




theorem true:
  assumes "d\<ge>0"
  shows "\<Turnstile> {\<lambda>s t. (P s @\<^sub>t true\<^sub>A) t}
       H
     {\<lambda>s t. ((\<exists>\<^sub>t s. P s) @\<^sub>t true\<^sub>A) t}"
unfolding Valid_def
  apply auto
  unfolding join_assn_def true_assn_def ex_assn_def
  apply auto 
  subgoal for a b aa ba tr2 tr1a tr2a
    apply(rule exI[where x="tr1a"])
    by auto
  done

lemma ex_tran:
  assumes "\<And>x. P x \<Longrightarrow>\<^sub>t R x"
  shows "(\<exists>\<^sub>t x. P x) \<Longrightarrow>\<^sub>t (\<exists>\<^sub>t x. R x)"
  using assms by (auto simp add: ex_assn_def entails_tassn_def)


lemma pure_tran:
  assumes "P \<Longrightarrow>\<^sub>t R "
  shows "(\<up>b \<and>\<^sub>t P) \<Longrightarrow>\<^sub>t (\<up>b \<and>\<^sub>t R)"
  using assms by (auto simp add: pure_assn_def entails_tassn_def conj_assn_def)

lemma pure_simp:
"(\<up>b1 \<and>\<^sub>t \<up>b2 \<and>\<^sub>t P) = (\<up>(b1 \<and> b2) \<and>\<^sub>t P)"
by (auto simp add: pure_assn_def entails_tassn_def conj_assn_def)

lemma combine_ex_left:
"combine_assn chs (\<exists>\<^sub>t v. p v) (q) = (\<exists>\<^sub>t v. combine_assn chs (p v) q)"
  unfolding combine_assn_def ex_assn_def entails_tassn_def 
  by auto

lemma combine_ex_right:
"combine_assn chs (q) (\<exists>\<^sub>t v. p v) = (\<exists>\<^sub>t v. combine_assn chs q (p v))"
  unfolding combine_assn_def ex_assn_def entails_tassn_def 
  by auto

lemma combine_pure_left:
"combine_assn chs (\<up>b \<and>\<^sub>t p) (q) = (\<up>b \<and>\<^sub>t combine_assn chs p q)"
  unfolding combine_assn_def pure_assn_def entails_tassn_def  conj_assn_def
  by auto

lemma combine_pure_right:
"combine_assn chs (q) (\<up>b \<and>\<^sub>t p) = (\<up>b \<and>\<^sub>t combine_assn chs q p)"
  unfolding combine_assn_def pure_assn_def entails_tassn_def  conj_assn_def
  by auto






end