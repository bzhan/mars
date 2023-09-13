theory BigStepEx
  imports BigStepParallel
begin

subsection \<open>Examples\<close>

definition A :: pname where "A = ''a''"
definition B :: pname where "B = ''b''"
definition C :: pname where "C = ''c''"
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"
definition ch1 :: cname where "ch1 = ''ch1''"
definition ch2 :: cname where "ch2 = ''ch2''"

lemma pname_neq [simp]: "A \<noteq> B" "B \<noteq> A"
  by (auto simp add: A_def B_def)

lemma cname_neq [simp]: "ch1 \<noteq> ch2" "ch2 \<noteq> ch1"
  by (auto simp add: ch1_def ch2_def)

subsubsection \<open>Example 1\<close>

text \<open>
   ch1?X; ch2!(X+1)
|| ch1!3
\<close>
definition ex1a :: "'a proc" where
  "ex1a = (Cm (ch1[?]X); Cm (ch2[!](\<lambda>s. val s X + 1)))"

definition ex1b :: "'a proc" where
  "ex1b = (Cm (ch1[!](\<lambda>_. 3)))"

lemma ex1a:
  "spec_of ex1a
    (wait_in_c single_id_inv ch1
      (\<lambda>d v. wait_out_cv (\<lambda>s0 t s. s = upd s0 X v) ch2 (\<lambda>s0. v + 1)
         (\<lambda>d. init {{ X := (\<lambda>_. v) }})))"
  unfolding ex1a_def
  apply (rule spec_of_post)
   apply (rule Valid_receive_sp)
   apply (rule spec_of_send) apply clarify
  apply (rule wait_in_c_mono)
  apply (rule entails_trans)
   apply (rule wait_out_cv_upd)
  apply simp by (rule entails_triv)

lemma ex1:
  "spec_of_global
    (Parallel (Single A ex1a) {ch1}
              (Single B ex1b))
    (wait_out_cgv (single_inv A (\<lambda>s0 t s. s = upd s0 X 3)) ch2 {B, A} A (\<lambda>_. 4)
                  (\<lambda>d. init_single {A, B} {{X := (\<lambda>_. 3)}}\<^sub>g at A))"
  apply (rule spec_of_global_post)
  (* Stage 1: obtain spec for both sides *)
   apply (rule spec_of_parallel)
    (* ex1a *)
      apply (rule spec_of_single)
      apply (rule ex1a)
    (* ex1b *)
     apply (rule spec_of_single) unfolding ex1b_def
     apply (rule spec_of_send)
    apply simp apply simp apply auto
  (* Stage 2: simplify assertion *)
  subgoal for s0
    apply (auto simp: single_assn_simps)
  (* Stage 3: perform merge *)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_in_outv) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_outv_emp) apply auto
    apply (rule wait_out_cgv_mono) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply auto
    apply (rule updg_mono)
    apply (rule sync_gassn_emp) by auto
  done

subsubsection \<open>Example 2\<close>

text \<open>
   ch1!X; ch2?Y
|| ch1?Z; ch2!(Z+1)
\<close>

definition ex2a :: "'a proc" where
  "ex2a = (Cm (ch1[!](\<lambda>s. val s X)); Cm (ch2[?]Y))"

definition ex2b :: "'a proc" where
  "ex2b = (Cm (ch1[?]Z); Cm (ch2[!](\<lambda>s. val s Z + 1)))"

lemma ex2a:
  "spec_of ex2a
    (wait_out_cv single_id_inv ch1 (\<lambda>s. val s X)
      (\<lambda>d. wait_in_c single_id_inv ch2 (\<lambda>d v. init {{Y := (\<lambda>_. v)}})))"
  unfolding ex2a_def
  apply (rule spec_of_post)
  apply (rule Valid_send_sp)
  apply (rule spec_of_receive)
  apply auto by (rule entails_triv)

lemma ex2b:
  "spec_of ex2b
    (wait_in_c single_id_inv ch1
      (\<lambda>d v. wait_out_cv (\<lambda>s0 t s. s = upd s0 Z v) ch2 (\<lambda>s0. v + 1)
         (\<lambda>d. init {{Z := (\<lambda>_. v)}})))"
  unfolding ex2b_def
  apply (rule spec_of_post)
  apply (rule Valid_receive_sp)
   apply (rule spec_of_send) apply clarify
  apply (rule wait_in_c_mono)
  apply (rule entails_trans)
   apply (rule wait_out_cv_upd)
  apply simp by (rule entails_triv)

lemma ex2:
  "spec_of_global
    (Parallel (Single A ex2a)
              {ch1, ch2}
              (Single B ex2b))
    (\<lambda>s0. ((init_single {B, A} {{Z := (\<lambda>_. valg s0 A X)}}\<^sub>g at B)
                               {{Y := (\<lambda>_. valg s0 A X + 1)}}\<^sub>g at A) s0)"
  (* Stage 1: merge ex2a_sp and ex2b_sp *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
    (* ex2a *)
      apply (rule spec_of_single) apply (rule ex2a)
    (* ex2b *)
     apply (rule spec_of_single) apply (rule ex2b)
    apply simp apply simp
    (* Stage 2: rewrite the assertions *)
  apply auto subgoal for s0
    apply (auto simp: single_assn_simps)
      (* Stage 3: combine the two assertions *)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_outv_in) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_in_outv) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply (auto simp add: valg_def[symmetric])
    apply (rule updg_mono)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_right) apply auto
    apply (rule updg_mono)
     apply (rule sync_gassn_emp) by simp
  done

subsubsection \<open>Example 3\<close>

text \<open>
  We analyze the following parallel program. The eventual aim
  is to show that the invariant Y = A * B is preserved.

   (ch1!X; Y := Y + 1)*
|| (ch1?X; Y := Y + X)*
\<close>
definition ex3a :: "'a proc" where
  "ex3a = (Rep (Cm (ch1[!](\<lambda>s. val s X)); Y ::= (\<lambda>s. val s Y + 1)))"

fun ex3a_c :: "nat \<Rightarrow> 'a assn2" where
  "ex3a_c 0 = init"
| "ex3a_c (Suc n) =
    wait_out_cv single_id_inv ch1 (\<lambda>s. val s X)
      (\<lambda>d. ex3a_c n {{ Y := (\<lambda>s. val s Y + 1) }})"

lemma ex3a_sp:
  "spec_of ex3a
           (\<exists>\<^sub>an. ex3a_c n)"
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

fun ex3b_c :: "nat \<Rightarrow> 'a assn2" where
  "ex3b_c 0 = init"
| "ex3b_c (Suc n) =
    wait_in_c single_id_inv ch1
     (\<lambda>d v. ex3b_c n {{Y := (\<lambda>s. val s Y + val s X)}} {{X := (\<lambda>_. v)}} )"

lemma ex3b_sp:
  "spec_of ex3b
           (\<exists>\<^sub>an. ex3b_c n)"
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
  "ex3_inv s \<longleftrightarrow> (valg s B Y = valg s A X * valg s A Y)"

definition ex3_one_step :: "'a gstate \<Rightarrow> 'a gstate" where
  "ex3_one_step s =
      updg (updg (updg s B X (valg s A X))
                         A Y (valg s A Y + 1))
                         B Y (valg s B Y + valg s A X)"

text \<open>This is the crucial lemma, stating that from a starting state s0
  satisfying invariant ex3_inv, there is another state s1 also satisfying
  invariant ex3_inv, that is reached after one iteration on both left
  and right sides.
\<close>
lemma ex3':
  assumes "ex3_inv s0"
  shows
  "\<exists>s1. ex3_inv s1 \<and>
   (sync_gassn {ch1} {A} {B}
     (single_assn A (ex3a_c (Suc n1)))
     (single_assn B (ex3b_c (Suc n2))) s0 \<Longrightarrow>\<^sub>g
    (sync_gassn {ch1} {A} {B}
     (single_assn A (ex3a_c n1))
     (single_assn B (ex3b_c n2))) s1)"
  apply (rule exI[where x="ex3_one_step s0"])
  apply (rule conjI)
  subgoal using assms unfolding ex3_one_step_def ex3_inv_def
    apply (auto simp add: X_def Y_def)
    by (auto simp add: algebra_simps A_def B_def)
  subgoal
    apply (auto simp: single_assn_simps)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_outv_in) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_right) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply simp
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (simp only: valg_def[symmetric]) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_right) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule sync_gassn_triv)
    apply (simp only: valg_def[symmetric])
    by (auto simp add: ex3_one_step_def X_def Y_def A_def B_def)
  done

lemma ex3'':
  "ex3_inv s0 \<Longrightarrow>
   \<exists>s1. ex3_inv s1 \<and>
    (sync_gassn {ch1} {A} {B}
      (single_assn A (ex3a_c n1))
      (single_assn B (ex3b_c n2)) s0 \<Longrightarrow>\<^sub>g
    init_single {B, A} s1)"
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
      apply (auto simp add: single_assn_simps)
       apply (rule sync_gassn_emp) apply auto
      by (rule entails_g_triv)
  next
    case (Suc n1)
    show ?thesis
      apply (subst Suc)
      apply (rule exI[where x=s0])
      apply (rule conjI) using 1 apply simp
      apply auto
       apply (auto simp add: single_assn_simps)
       apply (rule sync_gassn_outv_emp_unpair)
      by auto
  qed
next
  case (2 n2)
  show ?case
    apply (rule exI[where x=s0])
    apply (rule conjI) using 2 apply simp
    apply auto
    apply (auto simp add: single_assn_simps)
    apply (rule sync_gassn_emp_in_unpair)
    by auto
next
  case (3 n1 n2)
  obtain s1 where s1: "ex3_inv s1"
    "sync_gassn {ch1} {A} {B}
      (single_assn A (ex3a_c (Suc n1)))
      (single_assn B (ex3b_c (Suc n2))) s0 \<Longrightarrow>\<^sub>g
     sync_gassn {ch1} {A} {B}
      (single_assn A (ex3a_c n1))
      (single_assn B (ex3b_c n2)) s1"
    using ex3' 3 by blast
  obtain s2 where s2: "ex3_inv s2"
    "sync_gassn {ch1} {A} {B}
       (single_assn A (ex3a_c n1))
       (single_assn B (ex3b_c n2)) s1 \<Longrightarrow>\<^sub>g
     init_single {B, A} s2"
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
    (Parallel (Single A ex3a)
              {ch1}
              (Single B ex3b))
    (\<exists>\<^sub>gn1 n2. sync_gassn {ch1} {A} {B}
                (single_assn A (ex3a_c n1))
                (single_assn B (ex3b_c n2)))"
  (* Stage 1: merge ex3a_c and ex3b_c *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule spec_of_single)
  apply (rule ex3a_sp)
     apply (rule spec_of_single)
  apply (rule ex3b_sp) apply auto
  apply (auto simp add: single_assn_simps sync_gassn_exists_left)
  apply (auto simp add: sync_gassn_exists_right)
  by (rule entails_g_triv)

lemma ex3:
  "spec_of_global_gen ex3_inv
    (Parallel (Single A ex3a)
              {ch1}
              (Single B ex3b))
    (\<lambda>s0 s tr. ex3_inv s)"
  unfolding spec_of_global_gen_def apply auto
  apply (rule weaken_post_global)
   apply (rule spec_of_globalE[OF ex3''']) apply simp
  apply (rule exists_gassn_elim)
  apply (rule exists_gassn_elim)
  subgoal premises pre for s0 n1 n2
  proof -
    obtain s1 where s1: "ex3_inv s1"
     "sync_gassn {ch1} {A} {B} (single_assn A (ex3a_c n1)) (single_assn B (ex3b_c n2)) s0 \<Longrightarrow>\<^sub>g
      init_single {B, A} s1"
      using ex3''[of s0 n1 n2] pre by auto
    show ?thesis
      apply (rule entails_g_trans)
       apply (rule s1(2))
      unfolding entails_g_def apply auto
      apply (elim init_single.cases) apply auto
      using s1 by auto
  qed
  done

subsubsection \<open>Example 5\<close>

text \<open>
  We analyze the following program for transmitting a list
  to another process.

  ( ch1!hd(ls); ls := tl ls )*
    ||
  ( ch1?X; ls := X # ls )*

  The eventual goal is to show that the invariant
  A.ls @ rev(B.ls) = ls0
\<close>

type_synonym ex5_state = "real list"

definition ex5a :: "ex5_state proc" where
  "ex5a = Rep (IF (\<lambda>s. epart s \<noteq> []) THEN
                 (Cm (ch1[!](\<lambda>s. hd (epart s))); Basic (\<lambda>s. tl (epart s)))
               ELSE Error FI)"

fun ex5a_c :: "nat \<Rightarrow> ex5_state assn2" where
  "ex5a_c 0 = init"
| "ex5a_c (Suc n) =
   (IFA (\<lambda>s. epart s \<noteq> []) THEN
      wait_out_cv single_id_inv ch1 (\<lambda>s. hd (epart s)) (\<lambda>d. ex5a_c n {{ (\<lambda>s0. tl (epart s0)) }}\<^sub>e)
    ELSE false_assn2 FI)"

lemma ex5a_sp:
  "spec_of ex5a
           (\<exists>\<^sub>an. ex5a_c n)"
  unfolding ex5a_def
  apply (rule spec_of_rep)
  subgoal for n
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
         apply (rule Valid_error_sp)
        apply clarify
        by (rule entails_triv)
      done
    done
  done

definition ex5b :: "ex5_state proc" where
  "ex5b = Rep (Cm (ch1[?]X); Basic (\<lambda>s. val s X # epart s))"

fun ex5b_c :: "nat \<Rightarrow> ex5_state assn2" where
  "ex5b_c 0 = init"
| "ex5b_c (Suc n) =
   wait_in_c single_id_inv ch1 (\<lambda>d v. ex5b_c n {{ (\<lambda>s. val s X # epart s) }}\<^sub>e {{ X := (\<lambda>_. v) }})"

lemma ex5b_sp:
  "spec_of ex5b
           (\<exists>\<^sub>an. ex5b_c n)"
  unfolding ex5b_def
  apply (rule spec_of_rep)
  subgoal for n
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
  done

definition ex5_inv :: "real list \<Rightarrow> ex5_state gstate \<Rightarrow> bool" where
  "ex5_inv ls gs \<longleftrightarrow> (rev (epartg gs B) @ epartg gs A = ls)"

text \<open>This function models update to the whole state in one step\<close>
definition ex5_one_step :: "ex5_state gstate \<Rightarrow> ex5_state gstate" where
  "ex5_one_step gs = (if epartg gs A \<noteq> [] then
      updeg (updg (updeg gs A (tl (epartg gs A)))
                            B X (hd (epartg gs A)))
                            B (hd (epartg gs A) # epartg gs B) else gs)"

text \<open>Preservation of invariant\<close>
lemma ex5_inv_preserve:
  assumes "ex5_inv ls gs"
    and "epartg gs A \<noteq> []"
  shows "ex5_inv ls (ex5_one_step gs)"
  using assms unfolding ex5_one_step_def ex5_inv_def
  by (auto simp add: A_def B_def)

lemma ex5':
  assumes "ex5_inv ls s0"
  shows
  "\<exists>s1. ex5_inv ls s1 \<and>
   (sync_gassn {ch1} {A} {B}
     (single_assn A (ex5a_c (Suc n1)))
     (single_assn B (ex5b_c (Suc n2))) s0 \<Longrightarrow>\<^sub>g
   (sync_gassn {ch1} {A} {B}
     (single_assn A (ex5a_c n1))
     (single_assn B (ex5b_c n2))) s1)"
  apply (rule exI[where x="ex5_one_step s0"])
  apply (rule conjI)
  subgoal using assms unfolding ex5_one_step_def ex5_inv_def by auto
  apply (auto simp: single_assn_cond)
  apply (rule sync_gassn_ifg_left)
  subgoal
    apply (auto simp add: single_assn_simps)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_outv_in) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subste_left) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subste)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_right) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subste_right) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subste)
    apply (rule sync_gassn_triv)
    apply (simp only: valg_def[symmetric] epartg_def[symmetric])
    unfolding ex5_one_step_def by (auto simp add: A_def B_def)
  subgoal unfolding single_assn_false
    using sync_gassn_false_left by auto
  subgoal by auto
  done

lemma ex5'':
  "ex5_inv ls s0 \<Longrightarrow>
   \<exists>s1. ex5_inv ls s1 \<and>
   (sync_gassn {ch1} {A} {B}
    (single_assn A (ex5a_c n1))
    (single_assn B (ex5b_c n2)) s0 \<Longrightarrow>\<^sub>g
   init_single {B, A} s1)"
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
      apply (auto simp add: single_assn_simps)
       apply (rule sync_gassn_emp) apply auto
      by (rule entails_g_triv)
  next
    case (Suc n1)
    show ?thesis
      apply (subst Suc)
      apply (rule exI[where x=s0])
      apply (rule conjI) using 1 apply simp
      apply auto
      apply (auto simp add: single_assn_simps)
      apply (rule sync_gassn_ifg_left)
      subgoal apply (rule sync_gassn_outv_emp_unpair) by auto
      subgoal using sync_gassn_false_left by auto
      subgoal by auto
      done
  qed
next
  case (2 n2)
  show ?case
    apply (rule exI[where x=s0])
    apply (rule conjI) using 2 apply simp
    apply auto
    apply (auto simp add: single_assn_simps)
    apply (rule sync_gassn_emp_in_unpair)
    by auto
next
  case (3 n1 n2)
  obtain s1 where s1: "ex5_inv ls s1"
    "sync_gassn {ch1} {A} {B}
      (single_assn A (ex5a_c (Suc n1)))
      (single_assn B (ex5b_c (Suc n2))) s0 \<Longrightarrow>\<^sub>g
     sync_gassn {ch1} {A} {B}
      (single_assn A (ex5a_c n1))
      (single_assn B (ex5b_c n2)) s1"
    using ex5' 3 by blast
  obtain s2 where s2: "ex5_inv ls s2"
    "sync_gassn {ch1} {A} {B}
       (single_assn A (ex5a_c n1))
       (single_assn B (ex5b_c n2)) s1 \<Longrightarrow>\<^sub>g
     init_single {B, A} s2"
    using 3 s1(1) by blast
  show ?case
    apply (rule exI[where x=s2])
    apply (rule conjI) apply (rule s2)
    apply (rule entails_g_trans)
     apply (rule s1)
    by (rule s2)
qed

lemma ex5''':
  "spec_of_global
    (Parallel (Single A ex5a)
              {ch1}
              (Single B ex5b))
    (\<exists>\<^sub>gn1 n2. sync_gassn {ch1} {A} {B}
                (single_assn A (ex5a_c n1))
                (single_assn B (ex5b_c n2)))"
  (* Stage 1: merge ex5a_c and ex5b_c *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule spec_of_single[OF ex5a_sp])
     apply (rule spec_of_single[OF ex5b_sp])
    apply auto
  apply (auto simp add: single_assn_exists sync_gassn_exists_left)
  apply (auto simp add: sync_gassn_exists_right)
  by (rule entails_g_triv)

lemma ex5:
  "spec_of_global_gen (ex5_inv ls)
     (Parallel (Single A ex5a)
               {ch1}
               (Single B ex5b))
     (\<lambda>s0 s tr. ex5_inv ls s)"
  unfolding spec_of_global_gen_def apply auto
  apply (rule weaken_post_global)
   apply (rule spec_of_globalE[OF ex5''']) apply simp
  apply (rule exists_gassn_elim)
  apply (rule exists_gassn_elim)
  subgoal premises pre for s0 n1 n2
  proof -
    obtain s1 where s1: "ex5_inv ls s1"
     "sync_gassn {ch1} {A} {B} (single_assn A (ex5a_c n1)) (single_assn B (ex5b_c n2)) s0 \<Longrightarrow>\<^sub>g
      init_single {B, A} s1"
      using ex5''[of _ s0 n1 n2] pre by auto
    show ?thesis
      apply (rule entails_g_trans)
       apply (rule s1(2))
      unfolding entails_g_def apply auto
      apply (elim init_single.cases) apply auto
      using s1 by auto
  qed
  done

subsubsection \<open>Example 6\<close>

text \<open>This example tests unmatched communications, and
  preliminary use of assume-guarantee.

   ch2?X; wait(1); ch1!X
|| wait(1); ch1?X

  ch2?X receives value from a third process. Complications
  would arise if it does not occur immediately. Hence we
  assume that it does.
\<close>

definition ex6a :: "'a proc" where
  "ex6a = (Cm (ch2[?]X); Wait (\<lambda>_. 1); Cm (ch1[!](\<lambda>s. val s X)))"

lemma ex6a_sp':
  "spec_of ex6a
    (wait_in_c0 single_id_inv ch2 (\<lambda>v.
      wait_c single_id_inv (\<lambda>_. 1) (\<lambda>_.
       wait_out_cv single_id_inv ch1 (\<lambda>s. val s X) (\<lambda>d. init)) {{ X := (\<lambda>_. v) }}))"
  unfolding ex6a_def
  apply (rule spec_of_post)
   apply (rule Valid_receive_sp)
   prefer 2 apply clarify
  unfolding wait_in_c0_def
   apply (rule wait_in_c_mono)
   apply (rule entails_assumption)
  apply (rule Valid_wait_sp)
  apply (rule spec_of_send)
  done

lemma ex6a_sp:
  "spec_of ex6a
    (wait_in_c0 single_id_inv ch2 (\<lambda>v.
      wait_c (\<lambda>s0 t s. s = upd s0 X v) (\<lambda>_. 1) (\<lambda>_.
       wait_out_cv (\<lambda>s0 t s. s = upd s0 X v) ch1 (\<lambda>_. v) (\<lambda>d. init {{ X := (\<lambda>_. v) }}))))"
  apply (rule spec_of_post)
   apply (rule ex6a_sp') apply clarify
  apply (rule wait_in_c0_mono)
  apply (rule entails_trans)
   apply (rule wait_c_upd)
  apply simp apply (rule wait_c_mono)
  apply (rule entails_trans)
   apply (rule wait_out_cv_upd)
  apply simp apply (rule wait_out_cv_mono)
  by (rule entails_triv)

definition ex6b :: "'a proc" where
  "ex6b = (Wait (\<lambda>_. 1); Cm (ch1[?]X))"

lemma ex6b_sp:
  "spec_of ex6b
    (wait_c single_id_inv (\<lambda>_. 1)
      (\<lambda>_. wait_in_c single_id_inv ch1 (\<lambda>d v. init {{ X := (\<lambda>_. v) }})))"
  unfolding ex6b_def
  apply (rule Valid_wait_sp)
  apply (rule spec_of_receive)
  done

lemma ex6:
  "spec_of_global
    (Parallel (Single A ex6a)
              {ch1}
              (Single B ex6b))
    (wait_in_cg_alt (id_inv {B, A}) ch2 B (\<lambda>_. 1)
      (\<lambda>d v. IFG [A] (\<lambda>s. d = 0) THEN
               ((wait_cg (merge_inv (single_inv A (\<lambda>s0 t s. s = upd s0 X v)) (id_inv {B})) A (\<lambda>_. 1)
                   (\<lambda>_. (init_single {B, A} {{X := (\<lambda>_. v)}}\<^sub>g at A) {{X := (\<lambda>_. v)}}\<^sub>g at B)))
             ELSE true_gassn {B, A} FI)
      (\<lambda>v. true_gassn {B, A}))"
  (* Stage 1: merge ex6a_sp and ex6b_sp *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule spec_of_single)
      apply (rule ex6a_sp)
     apply (rule spec_of_single)
     apply (rule ex6b_sp)
    apply simp apply simp
  (* Stage 2: rewrite the assertions *)
  apply auto subgoal for s0
    apply (auto simp add: single_assn_simps)
  (* Stage 3: combine the two assertions *)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_out_unpair_wait0)
            apply (auto simp add: ch1_def ch2_def A_def B_def)[8]
    apply simp
    apply (rule wait_in_cg_alt_mono)
    subgoal for d v
      apply (rule cond_gassn_mono)
      subgoal
        apply (rule entails_g_trans)
        apply (rule entails_g_trans)
         apply (rule sync_gassn_wait_same) apply auto
         apply (rule wait_cg_mono)
        apply (rule entails_g_trans)
         apply (rule sync_gassn_outv_in) apply auto
         apply (rule sync_gassn_subst_right) apply auto
        apply (rule wait_cg_mono)
        apply (rule updg_mono)
        apply (rule entails_g_trans)
         apply (rule sync_gassn_subst_left) apply auto
        apply (rule updg_mono)
        apply (rule sync_gassn_emp) by auto
      by (rule entails_g_triv)
    subgoal for d
      by (rule entails_g_triv)
    done
  done

text \<open>
  We next compose the above example with ch2!1. The overall program is

   ch2?X; wait(1); ch1!X  (A)
|| wait(1); ch1?X         (B)
|| ch2!v; wait(1)         (C)

   The result assigns value v to variable X in A and (after
   waiting for 1 time unit) in B.
\<close>
lemma ex6_full:
  "spec_of_global
    (Parallel (Parallel (Single A ex6a) {ch1} (Single B ex6b))
              {ch2}
              (Single C (Cm (ch2[!](\<lambda>_. v)); Wait (\<lambda>_. 1))))
    (wait_cg (merge_inv (merge_inv (
                single_inv A (\<lambda>s0 t s. s = upd s0 X v))
                (id_inv {B})) (id_inv {C})) A (\<lambda>_. 1)
            (\<lambda>_. (init_single {C, B, A} {{X := (\<lambda>_. v)}}\<^sub>g at A) {{X := (\<lambda>_. v)}}\<^sub>g at B))"
  (* Stage 1: merge with ex6 *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule ex6)
     apply (rule spec_of_single)
     apply (rule Valid_send_sp)
     apply (rule spec_of_wait)
    apply simp apply simp
  (* Stage 2: rewrite the assertions *)
  apply auto subgoal for s0
    apply (auto simp add: single_assn_simps)
  (* Stage 3: combine the two assertions *)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_in_alt_outv) apply (auto simp add: A_def B_def C_def)[6]
    apply (rule entails_g_trans)
     apply (rule sync_gassn_wait_same) apply (auto simp add: A_def B_def C_def)[1]
    apply (rule wait_cg_mono)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply auto
    apply (rule updg_mono)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply auto
    apply (rule updg_mono)
     apply (rule sync_gassn_emp) by auto
  done

end
