theory Repetition
  imports BigStepSimple
begin

subsection \<open>Alternative rule for repetition\<close>

theorem Valid_frame:
  assumes "Valid (\<lambda>s tr. P s \<and> tr = []) c (\<lambda>s tr. Q s \<and> R tr)"
  shows "Valid (\<lambda>s tr. P s \<and> R' tr) c (\<lambda>s tr. Q s \<and> (R' @\<^sub>t R) tr)"
  using assms unfolding Valid_def
  by (auto simp add: join_assn_def)

theorem Valid_loop2:
  assumes "\<And>a tr1 tr2. Q a tr1 \<Longrightarrow> P (f a) tr2 \<Longrightarrow> P a (tr1 @ tr2)"
    and "\<And>a. Valid (\<lambda>s tr. R a s \<and> tr = []) c (\<lambda>s tr. R (f a) s \<and> Q a tr)"
  shows "Valid (\<lambda>s tr. \<exists>b. R b s \<and> (P b @- P a) tr) c (\<lambda>s tr. \<exists>b. R b s \<and> (P b @- P a) tr)"
  apply (rule Valid_ex_pre)
  subgoal for b
    apply (rule Valid_ex_post) apply (rule exI[where x="f b"])
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_frame[OF assms(2)])
    apply (auto simp add: entails_def)
    using assms(1) by (auto simp add: join_assn_def magic_wand_assn_def)
  done

theorem Valid_loop3:
  assumes "\<And>a. P a []"
  assumes "\<And>a tr1 tr2. Q a tr1 \<Longrightarrow> P (f a) tr2 \<Longrightarrow> P a (tr1 @ tr2)"
    and "\<And>a. Valid (\<lambda>s tr. R a s \<and> tr = []) c (\<lambda>s tr. R (f a) s \<and> Q a tr)"
  shows "Valid (\<lambda>s tr. R a s \<and> tr = []) (Rep c) (\<lambda>s tr. \<exists>b. R b s \<and> P a tr)"
  apply (rule Valid_weaken_pre)
  prefer 2 apply (rule Valid_strengthen_post)
    prefer 2 apply (rule Valid_rep[where P="\<lambda>s tr. \<exists>b. R b s \<and> (P b @- P a) tr"])
    apply (rule Valid_loop2[of Q P f])
  using assms apply auto
  using assms(1) apply (auto simp add: entails_def magic_wand_assn_def)
  by fastforce


end
