theory BigStepWp
  imports BigStepSimple
begin


definition subst_assn :: "assn \<Rightarrow> var \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> assn" ("_ {_ := _}" [90,90,90] 91) where 
  "P {var := e} = (\<lambda>s tr. P (s(var := e s)) tr)"

theorem Valid_skip:
  "\<Turnstile> {P} Skip {P}"
  unfolding Valid_def
  by (auto elim: skipE)

theorem Valid_assign:
  "\<Turnstile> {Q {var := e} } var ::= e {Q}"
  unfolding Valid_def
  by (auto simp: subst_assn_def elim: assignE)

theorem Valid_seq:
  assumes "\<Turnstile> {Q} c2 {R}"
    and "\<Turnstile> {P} c1 {Q}"
  shows "\<Turnstile> {P} c1; c2 {R}"
  using assms unfolding Valid_def
  by (metis append.assoc seqE)

theorem Valid_rep:
  assumes "\<Turnstile> {P} c {P}"
  shows "\<Turnstile> {P} Rep c {P}"
proof -
  have "big_step p s1 tr2 s2 \<Longrightarrow> p = Rep c \<Longrightarrow> \<forall>tr1. P s1 tr1 \<longrightarrow> P s2 (tr1 @ tr2)" for p s1 s2 tr2
    apply (induct rule: big_step.induct, auto)
    by (metis Valid_def append.assoc assms)
  then show ?thesis
    using assms unfolding Valid_def by auto
qed

text \<open>State and trace satisfies P after receiving input\<close>
definition wait_in :: "cname \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> assn) \<Rightarrow> assn" where
  "wait_in ch P = (\<lambda>s tr. (\<forall>v. P 0 v s (tr @ [InBlock ch v])) \<and>
                          (\<forall>d>0. \<forall>v. P d v s (tr @ [WaitBlk d (\<lambda>_. State s) ({}, {ch}), InBlock ch v])))"

theorem Valid_receive:
  "\<Turnstile> {wait_in ch (\<lambda>d v. P {var := (\<lambda>_. v)})}
        Cm (ch[?]var)
      {P}"
  unfolding Valid_def wait_in_def
  by (auto simp: subst_assn_def elim: receiveE)

definition wait_out :: "cname \<Rightarrow> (state \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> assn) \<Rightarrow> assn" where
  "wait_out ch e P = (\<lambda>s tr. (P 0 s (tr @ [OutBlock ch (e s)])) \<and>
                             (\<forall>d>0. P d s (tr @ [WaitBlk d (\<lambda>_. State s) ({ch}, {}), OutBlock ch (e s)])))"

lemma wait_in_forall:
  "wait_in ch (\<lambda>d v. \<forall>\<^sub>a n. P d v n) = (\<forall>\<^sub>a n. wait_in ch (\<lambda>d v. P d v n))"
  unfolding wait_in_def forall_assn_def
  apply (rule ext) apply (rule ext) by auto

lemma wait_out_forall:
  "wait_out ch e (\<lambda>d. \<forall>\<^sub>a n. P d n) = (\<forall>\<^sub>a n. wait_out ch e (\<lambda>d. P d n))"
  unfolding wait_out_def forall_assn_def
  apply (rule ext) apply (rule ext) by auto

lemma subst_forall:
  "(\<forall>\<^sub>a n. P n) {var := e} = (\<forall>\<^sub>a n. P n {var := e})"
  unfolding subst_assn_def forall_assn_def
  apply (rule ext) apply (rule ext) by auto

theorem Valid_send:
  "\<Turnstile> {wait_out ch e (\<lambda>d. P)}
        Cm (ch[!]e)
      {P}"
  unfolding Valid_def wait_out_def
  by (auto elim: sendE)

subsection \<open>Examples\<close>

lemma ex1a:
  "\<Turnstile> {wait_in ch1 (\<lambda>d v. (wait_out ch2 (\<lambda>s. s X + 1) (\<lambda>d. P)) {X := (\<lambda>_. v)})}
        Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. s X + 1))
      {P}"
  apply (rule strengthen_pre)
   apply (rule Valid_seq)
    apply (rule Valid_send)
   apply (rule Valid_receive)
  by (rule entails_triv)

lemma ex1b:
  "\<Turnstile> {wait_out ch1 (\<lambda>_. 3) (\<lambda>d. P)}
       Cm (ch1[!](\<lambda>_. 3))
      {P}"
  apply (rule strengthen_pre)
   apply (rule Valid_send)
  by (rule entails_triv)

fun rinv :: "nat \<Rightarrow> cname \<Rightarrow> assn \<Rightarrow> assn" where
  "rinv 0 ch Q = Q"
| "rinv (Suc n) ch Q = wait_out ch (\<lambda>s. s A) (\<lambda>d. (rinv n ch Q) {B := (\<lambda>s. s B + 1)})"
declare rinv.simps [simp del]

lemma ex2':
  "\<Turnstile> {\<forall>\<^sub>a n. rinv n ch1 Q}
        Cm (ch1[!](\<lambda>s. s A)); B ::= (\<lambda>s. s B + 1)
      {\<forall>\<^sub>a n. rinv n ch1 Q}"
  apply (rule strengthen_pre)
  apply (rule Valid_seq)
    apply (rule Valid_assign)
   apply (rule Valid_send)
  unfolding entails_def apply auto
  subgoal premises pre for s tr
  proof -
    have "(\<forall>\<^sub>an. rinv (Suc n) ch1 Q) s tr"  
      using pre unfolding forall_assn_def by auto
    then show ?thesis
      unfolding rinv.simps subst_forall wait_out_forall
      by auto
  qed
  done

lemma ex2:
  "\<Turnstile> {\<forall>\<^sub>a n. rinv n ch1 P}
        Rep (Cm (ch1[!](\<lambda>s. s A)); B ::= (\<lambda>s. s B + 1))
      {P}"
  apply (rule weaken_post)
  apply (rule Valid_rep)
   apply (rule ex2')
  unfolding entails_def apply auto
  by (metis forall_assn_def rinv.simps(1))

fun linv :: "nat \<Rightarrow> cname \<Rightarrow> assn \<Rightarrow> assn" where
  "linv 0 ch Q = Q"
| "linv (Suc n) ch Q = wait_in ch (\<lambda>d v. (linv n ch Q) {Y := (\<lambda>s. s Y + s X)} {X := (\<lambda>_. v)})"
declare linv.simps [simp del]

lemma ex3':
  "\<Turnstile> {\<forall>\<^sub>a n. linv n ch1 Q}
        Cm (ch1[?]X); Y ::= (\<lambda>s. s Y + s X)
      {\<forall>\<^sub>a n. linv n ch1 Q}"
  apply (rule strengthen_pre)
  apply (rule Valid_seq)
  apply (rule Valid_assign)
   apply (rule Valid_receive)
  unfolding entails_def apply auto
  subgoal premises pre for s tr
  proof -
    have "(\<forall>\<^sub>an. linv (Suc n) ch1 Q) s tr"
      using pre unfolding forall_assn_def by auto
    then show ?thesis
      unfolding linv.simps subst_forall wait_in_forall
      by auto
  qed
  done

lemma ex3:
  "\<Turnstile> {\<forall>\<^sub>a n. linv n ch1 P}
        Rep (Cm (ch1[?]X); Y ::= (\<lambda>s. s Y + s X))
      {P}"
  apply (rule weaken_post)
   apply (rule Valid_rep)
  apply (rule ex3')
  unfolding entails_def apply auto
  by (metis forall_assn_def linv.simps(1))

end

