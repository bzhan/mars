theory BigStepEx
  imports BigStepSimple
begin

subsection \<open>Examples\<close>

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

lemma ex1:
  "spec_of_global
    (Parallel (Single ''a'' ex1a) {ch1}
              (Single ''b'' ex1b))
    (\<lambda>s0. wait_out_cg ''a'' ch2 (\<lambda>s. val s X + 1) (\<lambda>d. init_single {''a'', ''b''})
          (updg s0 ''a'' X 3))"
  apply (rule spec_of_global_post)
  (* Stage 1: obtain spec for both sides *)
   apply (rule spec_of_parallel)
    (* ex1a *)
      apply (rule spec_of_single) unfolding ex1a_def
      apply (rule Valid_receive_sp)
      apply (rule spec_of_send)
    (* ex1b *)
     apply (rule spec_of_single) unfolding ex1b_def
     apply (rule spec_of_send)
    apply simp apply simp apply auto
  (* Stage 2: simplify assertion *)
  subgoal for s0
    apply (auto simp: single_assn_wait_in single_assn_wait_out updg_subst2 single_assn_init)
  (* Stage 3: perform merge *)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_in_out) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply simp
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_out_emp)
      apply (auto simp add: ch1_def ch2_def)
    apply (rule wait_out_cg_mono)
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

definition ex2b :: "'a proc" where
  "ex2b = (Cm (ch1[?]Z); Cm (ch2[!](\<lambda>s. val s Z + 1)))"

lemma ex2:
  "spec_of_global
    (Parallel (Single ''a'' ex2a)
              {ch1, ch2}
              (Single ''b'' ex2b))
    (\<lambda>s0. init_single {''b'', ''a''}
       (updg (updg s0 ''b'' Z (valg s0 ''a'' X))
                      ''a'' Y (valg s0 ''a'' X + 1)))"
  (* Stage 1: merge ex2a_sp and ex2b_sp *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
    (* ex2a *)
      apply (rule spec_of_single) unfolding ex2a_def
      apply (rule Valid_send_sp)
      apply (rule spec_of_receive)
    (* ex2b *)
     apply (rule spec_of_single) unfolding ex2b_def
     apply (rule Valid_receive_sp)
     apply (rule spec_of_send)
    apply simp apply simp
    (* Stage 2: rewrite the assertions *)
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
    apply (simp only: valg_def[symmetric]) apply auto
    by (rule entails_g_triv)
  done

subsubsection \<open>Example 3\<close>

text \<open>
  We analyze the following parallel program. The eventual aim
  is to show that the invariant Y = A * B is preserved.

   (ch1!A; B := B + 1)*
|| (ch1?X; Y := Y + X)*
\<close>
definition ex3a :: "'a proc" where
  "ex3a = (Rep (Cm (ch1[!](\<lambda>s. val s X)); Y ::= (\<lambda>s. val s Y + 1)))"

fun rinv_c :: "nat \<Rightarrow> ('a estate \<Rightarrow> 'a assn) \<Rightarrow> ('a estate \<Rightarrow> 'a assn)" where
  "rinv_c 0 Q = Q"
| "rinv_c (Suc n) Q = wait_out_c ch1 (\<lambda>s. val s X) (\<lambda>d. rinv_c n Q {{ Y := (\<lambda>s0. val s0 Y + 1) }})"

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
  "ex3_inv s0 \<longleftrightarrow> (valg s0 ''b'' Y = valg s0 ''a'' X * valg s0 ''a'' Y)"

definition ex3_one_step :: "'a gstate \<Rightarrow> 'a gstate" where
  "ex3_one_step s0 =
      updg (updg (updg s0 ''b'' X (valg s0 ''a'' X))
                          ''a'' Y (valg s0 ''a'' Y + 1))
                          ''b'' Y (valg s0 ''b'' Y + valg s0 ''a'' X)"

text \<open>This is the crucial lemma, stating that from a starting state s0
  satisfying invariant ex3_inv, there is another state s1 also satisfying
  invariant ex3_inv, that is reached after one iteration on both left
  and right sides.
\<close>
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
  apply (rule exI[where x="ex3_one_step s0"])
  apply (rule conjI)
  subgoal using assms unfolding ex3_one_step_def ex3_inv_def
    apply (auto simp add: X_def Y_def)
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
    apply (simp only: valg_def[symmetric]) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_right) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule sync_gassn_triv)
    apply (simp only: valg_def[symmetric])
    by (auto simp add: ex3_one_step_def X_def Y_def)
  done

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
  case (2 n2)
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
    "sync_gassn {ch1} {''a''} {''b''}
       (single_assn ''a'' (rinv_c n1 init))
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
  apply (rule weaken_post_global)
  apply (rule spec_of_globalE[OF ex3'''])
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

  The eventual goal is to show that the invariant
  A.ls @ rev(B.ls) = ls0
\<close>

type_synonym ex5_state = "real list"

definition ex5a :: "ex5_state proc" where
  "ex5a = Rep (IF (\<lambda>s. epart s \<noteq> []) THEN
                 (Cm (ch1[!](\<lambda>s. hd (epart s))); Basic (\<lambda>s. tl (epart s)))
               ELSE Error FI)"

fun ex5a_c :: "nat \<Rightarrow> ex5_state assn2 \<Rightarrow> ex5_state assn2" where
  "ex5a_c 0 Q = Q"
| "ex5a_c (Suc n) Q =
   (IFA (\<lambda>s. epart s \<noteq> []) THEN
      wait_out_c ch1 (\<lambda>s. hd (epart s)) (\<lambda>d. ex5a_c n Q {{ (\<lambda>s0. tl (epart s0)) }})
    ELSE false_assn2 FI)"

lemma ex5a_sp:
  "spec_of ex5a
           (\<lambda>s0. \<exists>\<^sub>an. ex5a_c n init s0)"
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

fun ex5b_c :: "nat \<Rightarrow> ex5_state assn2 \<Rightarrow> ex5_state assn2" where
  "ex5b_c 0 Q = Q"
| "ex5b_c (Suc n) Q =
   wait_in_c ch1 (\<lambda>d v. ex5b_c n Q {{ (\<lambda>s. val s X # epart s) }} {{ X := (\<lambda>_. v) }})"

lemma ex5b_sp:
  "spec_of ex5b
           (\<lambda>s0. \<exists>\<^sub>an. ex5b_c n init s0)"
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
  "ex5_inv ls gs \<longleftrightarrow> (rev (epartg gs ''b'') @ epartg gs ''a'' = ls)"

text \<open>This function models update to the whole state in one step\<close>
definition ex5_one_step :: "ex5_state gstate \<Rightarrow> ex5_state gstate" where
  "ex5_one_step gs =
    updeg (updg (updeg gs ''a'' (tl (epartg gs ''a'')))
                          ''b'' X (hd (epartg gs ''a'')))
                          ''b'' (hd (epartg gs ''a'') # epartg gs ''b'')"

text \<open>Preservation of invariant\<close>
lemma ex5_inv_preserve:
  assumes "ex5_inv ls gs"
    and "epartg gs ''a'' \<noteq> []"
  shows "ex5_inv ls (ex5_one_step gs)"
  using assms unfolding ex5_one_step_def ex5_inv_def
  by auto

lemma ex5':
  assumes "ex5_inv ls s0"
  shows
  "(sync_gassn {ch1} {''a''} {''b''}
    (single_assn ''a'' (ex5a_c (Suc n1) init))
    (single_assn ''b'' (ex5b_c (Suc n2) init)) s0 \<Longrightarrow>\<^sub>g
   (\<exists>\<^sub>gs1. (!\<^sub>g[ex5_inv ls s1]) \<and>\<^sub>g
      sync_gassn {ch1} {''a''} {''b''}
        (single_assn ''a'' (ex5a_c n1 init))
        (single_assn ''b'' (ex5b_c n2 init)) s1))"
  apply (auto simp: single_assn_cond)
  apply (rule sync_gassn_ifg_left)
  subgoal
    apply (rule exists_gassn_intro)
    apply (rule exI[where x="ex5_one_step s0"])
    apply (rule conj_gassn_intro)
     apply (rule pure_gassn_intro)
    subgoal using ex5_inv_preserve[OF assms]
      unfolding epartg_def by auto
    subgoal
      unfolding single_assn_wait_out single_assn_wait_in updg_subst2 updeg_subst2
      apply (rule entails_g_trans)
       apply (rule sync_gassn_out_in) apply auto
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
      unfolding ex5_one_step_def by auto
    done
  subgoal unfolding single_assn_false
    using sync_gassn_false_left by auto
  subgoal by auto
  done

lemma ex5'':
  "ex5_inv ls s0 \<Longrightarrow>
  (sync_gassn {ch1} {''a''} {''b''}
    (single_assn ''a'' (ex5a_c n1 init))
    (single_assn ''b'' (ex5b_c n2 init)) s0 \<Longrightarrow>\<^sub>g
  (\<exists>\<^sub>gs1. (!\<^sub>g[ex5_inv ls s1]) \<and>\<^sub>g
         init_single {''b'', ''a''} s1))"
proof (induction n1 n2 arbitrary: s0 rule: diff_induct)
  case (1 n1)
  show ?case
    apply (rule exists_gassn_intro)
    apply (rule exI[where x=s0])
    unfolding ex5b_c.simps single_assn_init
  proof (induction n1)
    case 0
    show ?case
      apply (rule conj_gassn_intro)
       apply (rule pure_gassn_intro)
      using 1 apply simp
      apply (rule entails_g_trans)
      apply (auto simp add: single_assn_init)
       apply (rule sync_gassn_emp) apply auto
      by (rule entails_g_triv)
  next
    case (Suc n1)
    show ?case
      apply (auto simp add: single_assn_init single_assn_cond single_assn_wait_out)
      apply (rule sync_gassn_ifg_left)
      subgoal apply (rule sync_gassn_out_emp_unpair) by auto
      subgoal apply (simp only: single_assn_false)
        using sync_gassn_false_left by auto
      subgoal by auto
      done
  qed
next
  case (2 n2)
  show ?case
    apply (rule exists_gassn_intro)
    apply (rule exI[where x=s0])
    apply (auto simp add: single_assn_init single_assn_wait_in)
    apply (rule sync_gassn_emp_in_unpair)
    by auto
next
  case (3 n1 n2)
  show ?case
    apply (rule entails_g_trans)
     apply (rule ex5')
    apply (rule 3(2))
    apply (rule exists_gassn_elim)
    subgoal for s1
      apply (rule conj_pure_gassn_elim)
      apply (rule 3(1))
      by auto
    done
qed

lemma ex5''':
  "spec_of_global
    (Parallel (Single ''a'' ex5a)
              {ch1}
              (Single ''b'' ex5b))
    (\<lambda>s0. \<exists>\<^sub>gn1 n2. sync_gassn {ch1} {''a''} {''b''}
                    (single_assn ''a'' (ex5a_c n1 init))
                    (single_assn ''b'' (ex5b_c n2 init)) s0)"
  (* Stage 1: merge ex5a_c and ex5b_c *)
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule spec_of_single[OF ex5a_sp])
     apply (rule spec_of_single[OF ex5b_sp])
  apply auto
  apply (auto simp add: single_assn_exists sync_gassn_exists_left sync_gassn_exists_right)
  by (rule entails_g_triv)

lemma ex5:
  "ex5_inv ls s0 \<Longrightarrow>
    \<Turnstile>\<^sub>p {init_global s0}
         (Parallel (Single ''a'' ex5a)
                   {ch1}
                   (Single ''b'' ex5b))
        {\<exists>\<^sub>gs1. !\<^sub>g[ex5_inv ls s1] \<and>\<^sub>g init_single {''b'', ''a''} s1}"
  apply (rule weaken_post_global)
   apply (rule spec_of_globalE[OF ex5'''])
  apply (rule exists_gassn_elim)
  apply (rule exists_gassn_elim)
  using ex5'' by auto

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

lemma ex6a_sp:
  "spec_of ex6a
    (wait_in_c0 ch2 (\<lambda>v.
     (wait_c (\<lambda>_. 1) (wait_out_c ch1 (\<lambda>s. val s X) (\<lambda>d. init)) {{ X := (\<lambda>_. v) }})))"
  unfolding ex6a_def
  apply (rule spec_of_post)
   apply (rule Valid_receive_sp)
   prefer 2 apply clarify
  unfolding wait_in_c0_gen_def
   apply (rule wait_in_c_mono)
   apply (rule entails_assumption)
  apply (rule Valid_wait_sp)
  apply (rule spec_of_send)
  done

definition ex6b :: "'a proc" where
  "ex6b = (Wait (\<lambda>_. 1); Cm (ch1[?]X))"

lemma ex6b_sp:
  "spec_of ex6b
    (wait_c (\<lambda>_. 1) (wait_in_c ch1 (\<lambda>d v. init {{ X := (\<lambda>_. v) }})))"
  unfolding ex6b_def
  apply (rule Valid_wait_sp)
  apply (rule spec_of_receive)
  done

lemma ex6:
  "spec_of_global
    (Parallel (Single ''a'' ex6a)
              {ch1}
              (Single ''b'' ex6b))
    (wait_in_cg_alt ch2 ''b'' (\<lambda>_. 1)
      (\<lambda>d v. IFG [''a''] (\<lambda>s. d = 0) THEN
               ((wait_cg ''a'' (\<lambda>_. 1)
                   (init_single {''b'', ''a''} {{X := (\<lambda>_. v)}}\<^sub>g at ''b'')
                   {{ X := (\<lambda>_. v) }}\<^sub>g at ''a''))
             ELSE true_gassn {''b'', ''a''} FI)
      (\<lambda>v. true_gassn {''b'', ''a''}))"
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
    apply (auto simp add: single_assn_wait_in0 single_assn_wait updg_subst2
                          single_assn_wait_out single_assn_wait_in single_assn_init)
  (* Stage 3: combine the two assertions *)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_out_unpair_wait0)
    apply (auto simp add: ch1_def ch2_def)
    subgoal for v
      apply (rule proc_set_updg_subst)
       apply (rule proc_set_wait_cg)
       apply (rule proc_set_wait_out_cg_gen)
      apply (rule proc_set_init_single) by auto
    subgoal
      apply (rule proc_set_wait_in_cg_gen)
      apply (rule proc_set_updg_subst)
       apply (rule proc_set_init_single) by auto
    apply (rule wait_in_cg_alt_mono)
    subgoal for d v s0
      apply (rule cond_gassn_mono)
      subgoal
        apply (rule entails_g_trans)
         apply (rule sync_gassn_subst_left) apply auto
        apply (rule updg_mono)
        apply (rule entails_g_trans)
         apply (rule sync_gassn_wait_same) apply auto
         apply (rule wait_cg_mono)
        apply (rule entails_g_trans)
         apply (rule sync_gassn_out_in) apply auto
        apply (rule entails_g_trans)
         apply (rule sync_gassn_subst_right) apply auto
        apply (simp only: valg_def[symmetric]) apply auto
        apply (rule updg_mono)
        apply (rule sync_gassn_emp) by auto
      by (rule entails_g_triv)
    subgoal for d s0
      by (rule entails_g_triv)
    done
  done

text \<open>
  We next compose the above example with ch2!1. The overall program is

   ch2?X; wait(1); ch1!X  (''a'')
|| wait(1); ch1?X         (''b'')
|| ch2!v; wait(1)         (''c'')

   The result assigns value v to variable X in ''a'' and (after
   waiting for 1 time unit) in ''b''.
\<close>
lemma ex6_full:
  "spec_of_global
    (Parallel (Parallel (Single ''a'' ex6a) {ch1} (Single ''b'' ex6b))
              {ch2}
              (Single ''c'' (Cm (ch2[!](\<lambda>_. v)); Wait (\<lambda>_. 1))))
    (\<lambda>s0. wait_cg ''a'' (\<lambda>_. 1) (init_single {''c'', ''b'', ''a''} {{X := (\<lambda>_. v)}}\<^sub>g at ''b'')
        (updg s0 ''a'' X v))"
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
    apply (auto simp add: single_assn_wait_out single_assn_wait single_assn_init)
  (* Stage 3: combine the two assertions *)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_in_alt_out) apply auto
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply auto
    apply (rule entails_g_trans)
     apply (rule gassn_subst)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_wait_same) apply auto
    apply (rule wait_cg_mono)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_subst_left) apply auto
    apply (rule updg_mono)
    apply (rule entails_g_trans)
     apply (rule sync_gassn_emp) apply auto
    by (rule entails_g_triv)
  done

end
