theory testvalid
  imports ext_Complementlemma
begin


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
  thm disjE
  by auto


lemma entails_disjE:
"P \<Longrightarrow>\<^sub>A R \<Longrightarrow> Q \<Longrightarrow>\<^sub>A R \<Longrightarrow> (\<lambda> (a,s)  t. P  (a,s) t \<or> Q  (a,s) t) \<Longrightarrow>\<^sub>A R"
  unfolding entails_def by auto

lemma entails_disjE':
"P \<Longrightarrow>\<^sub>A R \<Longrightarrow> Q \<Longrightarrow>\<^sub>A R \<Longrightarrow> (\<lambda> s  t. P  s t \<or> Q  s t) \<Longrightarrow>\<^sub>A R"
  unfolding entails_def by auto

lemma entails_disjI1':
"P \<Longrightarrow>\<^sub>A R1 \<Longrightarrow> P \<Longrightarrow>\<^sub>A (\<lambda> s t. R1 s t \<or> R2 s t)"
  unfolding entails_def by auto

lemma entails_disjI2':
"P \<Longrightarrow>\<^sub>A R2 \<Longrightarrow> P \<Longrightarrow>\<^sub>A (\<lambda> s t. R1 s t \<or> R2 s t)"
  unfolding entails_def by auto

lemma join_disj_assn:
"P @\<^sub>t (Q1 \<or>\<^sub>t Q2) = ((P @\<^sub>t Q1) \<or>\<^sub>t (P @\<^sub>t Q2))"
  unfolding join_assn_def disj_assn_def join_assn_def by blast

lemma Valid_true:
"\<Turnstile> {\<lambda> s t. P t} p {\<lambda> s t. (P @\<^sub>t true\<^sub>A) t}"
  unfolding Valid_def join_assn_def true_assn_def by auto


inductive out_0assn :: "cname \<Rightarrow> real \<Rightarrow> 'a tassn" ("Out0\<^sub>t") where
  "Out0\<^sub>t ch v [OutBlock ch v]"

inductive wait_passn :: "(real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> 'a tassn" ("Waitp\<^sub>t") where
  "d > 0 \<Longrightarrow> Waitp\<^sub>t p rdy [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy]"

theorem Valid_send_sp_assm0:
  "\<Turnstile> {\<lambda>s t. P s t}
       Cm (ch[!]e)
     {\<lambda>s t. (P s @\<^sub>t (Out0\<^sub>t ch (e s) \<or>\<^sub>t Waitp\<^sub>t (\<lambda> _. EState s) ({ch},{}) @\<^sub>t true\<^sub>A)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send)
  apply (auto simp add: entails_def magic_wand_assn_def join_assn_def disj_assn_def true_assn_def)
    subgoal for a b tr
      apply(rule exI[where x= tr])
      using out_0assn.intros(1) by auto
    subgoal for a b tr d
      apply(rule exI[where x= tr])
      apply(rule conjI)
      apply simp
      apply(rule exI[where x="[WaitBlk d (\<lambda>_. EState (a, b)) ({ch}, {}), OutBlock ch (e (a, b))]"])
      apply(rule conjI)
       apply(rule disjI2)
      using wait_passn.intros(1)[of d]
       apply fastforce
      by auto
    done

lemma tassn_to_assn:
"P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> (\<lambda> s. P) \<Longrightarrow>\<^sub>A (\<lambda> s. Q)"
  unfolding entails_def entails_tassn_def
  by auto


end