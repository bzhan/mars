theory BigStepEx
  imports BigStepSimple
begin

subsection \<open>Examples\<close>

definition A :: char where "A = CHR ''a''"
definition B :: char where "B = CHR ''b''"
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"
definition ch1 :: cname where "ch1 = ''ch1''"
definition ch2 :: cname where "ch2 = ''ch2''"

subsubsection \<open>Example 1\<close>

text \<open>
   ch1?X; ch2!(X+1)
|| ch1!3
\<close>
definition ex1a :: "'a proc" where
  "ex1a = (Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. val s X + 1)))"

definition ex1b :: "'a proc" where
  "ex1b = (Cm (ch1[!](\<lambda>_. 3)))"

lemma ex1a_sp:
  "spec_of ex1a
           (wait_in_c ch1 (\<lambda>d v. wait_out_c ch2 (\<lambda>s. val s X + 1) (\<lambda>d. init) {{ X := (\<lambda>_. v) }}))"
  unfolding ex1a_def
  apply (rule Valid_receive_sp)
  apply (rule spec_of_send)
  done

lemma ex1b_sp:
  "spec_of ex1b
           (wait_out_c ch1 (\<lambda>_. 3) (\<lambda>d. init))"
  unfolding ex1b_def
  apply (rule spec_of_send)
  done

lemma ex1:
  "spec_of_global
    (Parallel (Single ''a'' ex1a) {ch1}
              (Single ''b'' ex1b))
    (sync_gassn {ch1} {''a''} {''b''}
      (single_assn ''a'' (wait_in_c ch1 (\<lambda>d v. wait_out_c ch2 (\<lambda>s. val s X + 1) (\<lambda>d. init) {{ X := (\<lambda>_. v) }} )))
      (single_assn ''b'' (wait_out_c ch1 (\<lambda>_. 3) (\<lambda>d. init))))"
  apply (rule spec_of_parallel)
     apply (rule spec_of_single)
     apply (rule ex1a_sp)
    apply (rule spec_of_single)
    apply (rule ex1b_sp)
  by auto

lemma ex1':
  "spec_of_global
    (Parallel (Single ''a'' ex1a) {ch1}
              (Single ''b'' ex1b))
    (sync_gassn {ch1} {''a''} {''b''}
      (wait_in_cg ch1 (\<lambda>d v. wait_out_cg ch2 ''a'' (\<lambda>s. val s X + 1) (\<lambda>d. init_single {''a''}) {{X := (\<lambda>_. v)}}\<^sub>g at ''a''))
      (wait_out_cg ch1 ''b'' (\<lambda>_. 3) (\<lambda>d. init_single {''b''})))"
  apply (rule spec_of_global_post)
   apply (rule ex1) apply clarify subgoal for s0
    apply (auto simp: single_assn_wait_in single_assn_wait_out updg_subst2 single_assn_init)
    by (rule entails_g_triv)
  done

lemma ex1'':
  "spec_of_global
    (Parallel (Single ''a'' ex1a) {ch1}
              (Single ''b'' ex1b))
    (\<lambda>s0. wait_out_cg ch2 ''a'' (\<lambda>s. val s X + 1) (\<lambda>d. init_single {''a'', ''b''})
          (updg s0 ''a'' X 3))"
  apply (rule spec_of_global_post)
   apply (rule ex1') apply auto subgoal for s0
    apply (rule entails_g_trans)
     apply (rule sync_gassn_in_out) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply simp
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_out_emp)
      apply (auto simp add: ch1_def ch2_def)
    apply (rule wait_out_cg_entails)
    subgoal for d s0
      apply (rule sync_gassn_emp) by auto
    done
  done

subsubsection \<open>Example 2\<close>

text \<open>
   ch1!X; ch2?Y
|| ch1?Z; ch2!(Z+1)
\<close>

definition ex2a :: "'a proc" where
  "ex2a = (Cm (ch1[!](\<lambda>s. val s X)); Cm (ch2[?]Y))"

lemma ex2a_sp:
  "spec_of ex2a
           (wait_out_c ch1 (\<lambda>s. val s X) (\<lambda>d. wait_in_c ch2 (\<lambda>d v. init {{Y := (\<lambda>_. v)}})))"
  unfolding ex2a_def
  apply (rule Valid_send_sp)
  apply (rule spec_of_receive)
  done

definition ex2b :: "'a proc" where
  "ex2b = (Cm (ch1[?]Z); Cm (ch2[!](\<lambda>s. val s Z + 1)))"

lemma ex2b_sp:
  "spec_of ex2b
           (wait_in_c ch1 (\<lambda>d v. wait_out_c ch2 (\<lambda>s. val s Z + 1) (\<lambda>d. init) {{Z := (\<lambda>_. v)}}))"
  unfolding ex2b_def
  apply (rule Valid_receive_sp)
  apply (rule spec_of_send)
  done

lemma ex2:
  "spec_of_global
    (Parallel (Single ''a'' ex2a)
              {ch1, ch2}
              (Single ''b'' ex2b))
    (\<lambda>s0. init_single {''b'', ''a''}
     (updg (updg s0 ''b'' Z (valg s0 ''a'' X)) ''a'' Y
       (valg s0 ''a'' X + 1)))"
proof -
  have eq: "valg (updg s0 ''b'' Z (valg s0 ''a'' X)) ''b'' Z + 1 =
        valg s0 ''a'' X + 1" for s0::"'a gstate"
    by auto
  show ?thesis
  (* Stage 1: merge ex2_c and ex2_c' *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule spec_of_single)
      apply (rule ex2a_sp)
  apply (rule spec_of_single)
     apply (rule ex2b_sp)
    apply simp apply simp
  (* Stage 2: rewrite the assertions*)
  apply auto subgoal for s0
    apply (auto simp: single_assn_wait_in single_assn_wait_out updg_subst2 single_assn_init)
  (* Stage 3: combine the two assertions *)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_out_in) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_right) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_in_out) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
       apply (rule sync_gassn_emp) apply simp
      apply (simp only: valg_def[symmetric] eq)
      by (rule entails_g_triv)
    done
qed

subsubsection \<open>Example 3\<close>

text \<open>
   (ch1!A; B := B + 1)*
|| (ch1?X; Y := Y + X)*
\<close>
definition ex3a :: "'a proc" where
  "ex3a = (Rep (Cm (ch1[!](\<lambda>s. val s A)); B ::= (\<lambda>s. val s B + 1)))"

fun rinv_c :: "nat \<Rightarrow> ('a estate \<Rightarrow> 'a assn) \<Rightarrow> ('a estate \<Rightarrow> 'a assn)" where
  "rinv_c 0 Q = Q"
| "rinv_c (Suc n) Q = wait_out_c ch1 (\<lambda>s. val s A) (\<lambda>d. rinv_c n Q {{ B := (\<lambda>s0. val s0 B + 1) }})"

lemma ex3a_sp:
  "spec_of ex3a
           (\<lambda>s0. \<exists>\<^sub>an. rinv_c n init s0)"
  unfolding ex3a_def
  apply (rule spec_of_rep)
  subgoal for n
    apply (induction n)
     apply simp apply (rule spec_of_skip)
    subgoal premises pre for n
      apply simp apply (rule spec_of_post)
       apply (subst spec_of_seq_assoc)
       apply (rule Valid_send_sp)
       apply (rule Valid_assign_sp)
       apply (rule pre) apply clarify
      by (rule entails_triv)
    done
  done

definition ex3b :: "'a proc" where
  "ex3b = (Rep (Cm (ch1[?]X); Y ::= (\<lambda>s. val s Y + val s X)))"

fun linv_c :: "nat \<Rightarrow> ('a estate \<Rightarrow> 'a assn) \<Rightarrow> ('a estate \<Rightarrow> 'a assn)" where
  "linv_c 0 Q = Q"
| "linv_c (Suc n) Q = wait_in_c ch1 (\<lambda>d v. linv_c n Q {{Y := (\<lambda>s. val s Y + val s X)}} {{X := (\<lambda>_. v)}} )"

lemma ex3b_sp:
  "spec_of ex3b
           (\<lambda>s0. \<exists>\<^sub>an. linv_c n init s0)"
  unfolding ex3b_def
  apply (rule spec_of_rep)
  subgoal for n
    apply (induction n)
     apply simp apply (rule spec_of_skip)
    subgoal premises pre for n
      apply simp apply (rule spec_of_post)
       apply (subst spec_of_seq_assoc)
       apply (rule Valid_receive_sp)
       apply (rule Valid_assign_sp)
       apply (rule pre) apply clarify
      apply (rule entails_triv)
      done
    done
  done

definition ex3_inv :: "'a gstate \<Rightarrow> bool" where
  "ex3_inv s0 \<longleftrightarrow> (valg s0 ''b'' Y = valg s0 ''a'' A * valg s0 ''a'' B)"

lemma ex3':
  assumes "ex3_inv s0"
  shows
  "\<exists>s1. ex3_inv s1 \<and>
   (sync_gassn {ch1} {''a''} {''b''}
     (single_assn ''a'' (rinv_c (Suc n1) init))
     (single_assn ''b'' (linv_c (Suc n2) init)) s0 \<Longrightarrow>\<^sub>g
    sync_gassn {ch1} {''a''} {''b''}
     (single_assn ''a'' (rinv_c n1 init))
     (single_assn ''b'' (linv_c n2 init)) s1)"
proof -
  have eq1: "updg (updg s0 ''b'' X (valg s0 ''a'' A)) ''a'' B
              ((valg (updg s0 ''b'' X (valg s0 ''a'' A)) ''a'' B) + 1) =
             updg (updg s0 ''b'' X (valg s0 ''a'' A)) ''a'' B (valg s0 ''a'' B + 1)"
    by auto
  let ?s1 = "updg (updg (updg s0 ''b'' X (valg s0 ''a'' A)) ''a'' B (valg s0 ''a'' B + 1)) ''b'' Y
               (valg s0 ''b'' Y + valg s0 ''a'' A)"
  show ?thesis
  apply (rule exI[where x="?s1"])
  apply (rule conjI)
    subgoal using assms unfolding ex3_inv_def
      apply (auto simp add: A_def B_def X_def Y_def)
      by (auto simp add: algebra_simps)
  subgoal
    apply simp
    apply (auto simp: single_assn_wait_in single_assn_wait_out updg_subst2)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_out_in) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_right) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply simp
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (simp only: valg_def[symmetric]) apply (subst eq1)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_right) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule sync_gassn_triv)
    apply (simp only: valg_def[symmetric])
    by (auto simp add: X_def A_def B_def Y_def)
  done
qed

lemma ex3'':
  "ex3_inv s0 \<Longrightarrow>
   \<exists>s1. ex3_inv s1 \<and>
    (sync_gassn {ch1} {''a''} {''b''}
      (single_assn ''a'' (rinv_c n1 init))
      (single_assn ''b'' (linv_c n2 init)) s0 \<Longrightarrow>\<^sub>g
    init_single {''b'', ''a''} s1)"
proof (induction n1 n2 arbitrary: s0 rule: diff_induct)
  case (1 n1)
  show ?case
  proof (cases n1)
    case 0
    show ?thesis
      apply (subst 0)
      apply (rule exI[where x=s0])
      apply (rule conjI) using 1 apply simp
      apply (rule entails_g_trans)
      apply (auto simp add: single_assn_init)
       apply (rule sync_gassn_emp) apply auto
      by (rule entails_g_triv)
  next
    case (Suc n1)
    show ?thesis
      apply (subst Suc)
      apply (rule exI[where x=s0])
      apply (rule conjI) using 1 apply simp
      apply auto
       apply (auto simp add: single_assn_init single_assn_wait_out)
       apply (rule sync_gassn_out_emp_unpair)
      by auto
  qed
next
  case (2 y)
  show ?case
    apply (rule exI[where x=s0])
    apply (rule conjI) using 2 apply simp
    apply auto
    apply (auto simp add: single_assn_init single_assn_wait_in)
    apply (rule sync_gassn_emp_in_unpair)
    by auto
next
  case (3 n1 n2)
  obtain s1 where s1: "ex3_inv s1"
    "sync_gassn {ch1} {''a''} {''b''}
      (single_assn ''a'' (rinv_c (Suc n1) init))
      (single_assn ''b'' (linv_c (Suc n2) init)) s0 \<Longrightarrow>\<^sub>g
     sync_gassn {ch1} {''a''} {''b''}
      (single_assn ''a'' (rinv_c n1 init))
      (single_assn ''b'' (linv_c n2 init)) s1"
    using ex3' 3 by blast
  obtain s2 where s2: "ex3_inv s2"
    "sync_gassn {ch1} {''a''} {''b''} (single_assn ''a'' (rinv_c n1 init))
       (single_assn ''b'' (linv_c n2 init)) s1 \<Longrightarrow>\<^sub>g
     init_single {''b'', ''a''} s2"
    using 3 s1(1) by blast 
  show ?case
    apply (rule exI[where x=s2])
    apply (rule conjI) apply (rule s2)
    apply (rule entails_g_trans)
     apply (rule s1)
    by (rule s2)
qed

lemma ex3''':
  "spec_of_global
    (Parallel (Single ''a'' ex3a)
              {ch1}
              (Single ''b'' ex3b))
    (\<lambda>s0. \<exists>\<^sub>gn1 n2. sync_gassn {ch1} {''a''} {''b''}
                    (single_assn ''a'' (rinv_c n1 init))
                    (single_assn ''b'' (linv_c n2 init)) s0)"
  (* Stage 1: merge ex3_c and ex4_c *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule spec_of_single)
  apply (rule ex3a_sp)
     apply (rule spec_of_single)
  apply (rule ex3b_sp) apply auto
  apply (auto simp add: single_assn_exists sync_gassn_exists_left sync_gassn_exists_right)
  by (rule entails_g_triv)

lemma ex3:
  "ex3_inv s0 \<Longrightarrow>
    \<Turnstile>\<^sub>p {init_global s0}
        (Parallel (Single ''a'' ex3a)
                  {ch1}
                  (Single ''b'' ex3b))
       {\<exists>\<^sub>gs1. (\<lambda>s tr. ex3_inv s1 \<and> init_single {''b'', ''a''} s1 s tr)}"
  apply (rule weaken_post_global[where R="\<exists>\<^sub>gn1 n2. sync_gassn {ch1} {''a''} {''b''}
                    (single_assn ''a'' (rinv_c n1 init))
                    (single_assn ''b'' (linv_c n2 init)) s0"])
  subgoal by (auto simp: ex3'''[unfolded spec_of_global_def])
  apply (auto simp add: exists_gassn_def entails_g_def)
  subgoal for s tr n1 n2
    using ex3''[of s0 n1 n2] unfolding entails_g_def
    by auto
  done

subsubsection \<open>Example 5\<close>

text \<open>
  We analyze the following program for transmitting a list
  to another process.

  ( ch1!hd(ls); ls := tl ls )*
    ||
  ( ch1?X; ls := X # ls )*
\<close>

type_synonym ex5_state = "real list"

definition ex5_left :: "ex5_state proc" where
  "ex5_left = Rep (IF (\<lambda>s. epart s \<noteq> []) THEN
                     (Cm (ch1[!](\<lambda>s. hd (epart s))); Basic (\<lambda>s. tl (epart s)))
                   ELSE Skip FI)"

fun ex5_linv_c :: "nat \<Rightarrow> ex5_state assn2 \<Rightarrow> ex5_state assn2" where
  "ex5_linv_c 0 Q = Q"
| "ex5_linv_c (Suc n) Q =
   (IFA (\<lambda>s. epart s \<noteq> []) THEN
      wait_out_c ch1 (\<lambda>s. hd (epart s)) (\<lambda>d. ex5_linv_c n Q {{ (\<lambda>s0. tl (epart s0)) }})
    ELSE ex5_linv_c n Q FI)"

lemma ex5_c:
  "spec_of (RepN n (IF (\<lambda>s. epart s \<noteq> []) THEN
                      (Cm (ch1[!](\<lambda>s. hd (epart s))); Basic (\<lambda>s. tl (epart s)))
                    ELSE Skip FI))
           (ex5_linv_c n init)"
  apply (induction n)
   apply simp apply (rule spec_of_skip)
  subgoal premises pre for n
    apply simp
    apply (subst spec_of_cond_distrib)
    apply (rule spec_of_cond)
    subgoal
      apply (rule spec_of_post)
      apply (subst spec_of_seq_assoc)
       apply (rule Valid_send_sp)
       apply (rule Valid_basic_sp)
      apply (rule pre) apply clarify
      by (rule entails_triv)
    subgoal
      apply (rule spec_of_post)
      apply (rule Valid_skip_sp)
       apply (rule pre) apply clarify
      by (rule entails_triv)
    done
  done

definition ex5_right :: "ex5_state proc" where
  "ex5_right = Rep (Cm (ch1[?]X); Basic (\<lambda>s. val s X # epart s))"

fun ex5_rinv_c :: "nat \<Rightarrow> ex5_state assn2 \<Rightarrow> ex5_state assn2" where
  "ex5_rinv_c 0 Q = Q"
| "ex5_rinv_c (Suc n) Q =
   wait_in_c ch1 (\<lambda>d v. ex5_rinv_c n Q {{ (\<lambda>s. val s X # epart s) }} {{ X := (\<lambda>_. v) }})"

lemma ex5_c2:
  "spec_of (RepN n (Cm (ch1[?]X); Basic (\<lambda>s. val s X # epart s)))
           (ex5_rinv_c n init)"
  apply (induction n)
   apply simp apply (rule spec_of_skip)
  subgoal premises pre for n
    apply simp
    apply (subst spec_of_seq_assoc)
    apply (rule spec_of_post)
     apply (rule Valid_receive_sp)
     apply (rule Valid_basic_sp)
     apply (rule pre) apply clarify
    apply (rule entails_triv)      
    done
  done


end
