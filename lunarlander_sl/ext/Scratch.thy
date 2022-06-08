theory Scratch
  imports AssumeGuarantee
begin

datatype n = None

definition X :: char where "X = CHR ''x''"

definition P1 :: "n proc" where 
"P1 = Rep (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_ . 1)))) (\<lambda>_ . True) [(''ch1''[!](\<lambda> (a,s). s X) ,Cm (''ch2''[?]X))])"

definition P2 :: "n proc" where
"P2 = Rep (Wait (\<lambda> s. 1);Cm (''ch1''[?]X);Cm (''ch2''[!](\<lambda> (a,s). s X - 1)))"

inductive p1_assn :: "state \<Rightarrow> (real \<times> real) list \<Rightarrow> n tassn" where
  "p1_assn s [] []"
| "(d = 1 \<and> x = s X) \<longrightarrow> p1_assn (s(X := x)) rest tr3 \<Longrightarrow>
   (WaitOut\<^sub>t d None (\<lambda> t. s(X := s X + t)) (''ch1'') (\<lambda> (a,s). s X) ({''ch1''},{}) tr1 \<and>
   In\<^sub>t (EState (None,s(X := s X + d))) (''ch2'') x tr2) \<Longrightarrow>
   p1_assn s ((d,x)#rest) (tr1@tr2@tr3)"


lemma p1_0:
"p1_assn s [] = emp\<^sub>t"
   using p1_assn.cases
   apply(auto simp add: emp_assn_def)
   using p1_assn.intros(1) by blast

lemma p1_1:
  assumes "d = 1 \<and> x = s X"
  shows "p1_assn s ((d,x)#rest) = 
    WaitOut\<^sub>t d None (\<lambda> t. s(X := s X + t)) (''ch1'') (\<lambda> (a,s). s X) ({''ch1''},{}) @\<^sub>t
    In\<^sub>t (EState (None,s(X := s X + d))) (''ch2'') x @\<^sub>t 
    p1_assn (s(X := x)) rest"
  apply (rule ext)
  subgoal for tr
  proof-
    have 1:"p1_assn s ((d, x) # rest) tr \<Longrightarrow>
    (WaitOut\<^sub>t d n.None (\<lambda>t. s(X := s X + t)) ''ch1'' (\<lambda>(a, s). s X) ({''ch1''}, {}) @\<^sub>t
     In\<^sub>t (EState (n.None, s(X := s X + d))) ''ch2'' x @\<^sub>t p1_assn (s(X := x)) rest) tr "
      apply(rule p1_assn.cases[of s "((d, x) # rest)" tr])
      by (auto simp add: assms join_assn_def) 
    have 2:"(WaitOut\<^sub>t d n.None (\<lambda>t. s(X := s X + t)) ''ch1'' (\<lambda>(a, s). s X) ({''ch1''}, {}) @\<^sub>t
     In\<^sub>t (EState (n.None, s(X := s X + d))) ''ch2'' x @\<^sub>t p1_assn (s(X := x)) rest) tr 
            \<Longrightarrow> p1_assn s ((d, x) # rest) tr"
      apply (auto simp add: join_assn_def)
      subgoal for tr1 tr2 tr3
        using p1_assn.intros(2)[of d x s rest tr3 tr1 tr2]
        using assms by auto
      done
    show ?thesis 
      using 1 2 by auto
  qed
  done


lemma p1_3:
  "p1_assn s ((d,x)#rest) = 
   WaitOut\<^sub>t d None (\<lambda> t. s(X := s X + t)) (''ch1'') (\<lambda> (a,s). s X) ({''ch1''},{}) @\<^sub>t
   In\<^sub>t (EState (None,s(X := s X + d))) (''ch2'') x @\<^sub>t 
   (\<up>(d = 1 \<and> x = s X) \<longrightarrow>\<^sub>t p1_assn (s(X := x)) rest)"
  apply(rule ext)
  subgoal for tr
  proof-
    have 1:"p1_assn s ((d, x) # rest) tr \<Longrightarrow>
    (WaitOut\<^sub>t d n.None (\<lambda>t. s(X := s X + t)) ''ch1'' (\<lambda>(a, s). s X) ({''ch1''}, {}) @\<^sub>t
     In\<^sub>t (EState (n.None, s(X := s X + d))) ''ch2'' x @\<^sub>t
     (\<up> (d = 1 \<and> x = s X) \<longrightarrow>\<^sub>t p1_assn (s(X := x)) rest)) tr "
      apply(rule p1_assn.cases[of s "(d, x) # rest" tr])
        apply simp
      subgoal by auto
      by (auto simp add: pure_assn_def imp_assn_def join_assn_def)
    have 2:"(WaitOut\<^sub>t d n.None (\<lambda>t. s(X := s X + t)) ''ch1'' (\<lambda>(a, s). s X) ({''ch1''}, {}) @\<^sub>t
     In\<^sub>t (EState (n.None, s(X := s X + d))) ''ch2'' x @\<^sub>t
     (\<up> (d = 1 \<and> x = s X) \<longrightarrow>\<^sub>t p1_assn (s(X := x)) rest)) tr 
          \<Longrightarrow> p1_assn s ((d, x) # rest) tr "
      apply(auto simp add:join_assn_def)
      subgoal for tr1 tr2 tr3
        using p1_assn.intros(2)[of d x s rest tr3 tr1 tr2]
        by(auto simp add: pure_assn_def imp_assn_def)
      done
    show ?thesis
      using 1 2 by auto
  qed
  done

lemma P1_rep:
"\<Turnstile> {\<lambda> s tr. s = (None,ss) \<and> emp\<^sub>t tr}
    P1
    {\<lambda> s tr. \<exists> l. s = (None,ss(X := snd(last ((0,ss X)#l)))) \<and> p1_assn ss l tr}"
  unfolding P1_def
  apply(rule Valid_weaken_pre)
  prefer 2
   apply(rule Valid_rep)
  subgoal
    apply(rule Valid_ex_pre)
    subgoal for l
      sorry
    done
  sorry

      

inductive p2_assn :: "state \<Rightarrow> real list \<Rightarrow> n tassn" where
  "p2_assn s [] []"
| "p2_assn (s(X:=x)) rest tr4 \<Longrightarrow>
   Wait\<^sub>t 1 (\<lambda> _ . EState (None,s)) ({},{}) tr1 \<and> 
   In\<^sub>t (EState (None,s)) (''ch1'') x tr2 \<and>
   Out\<^sub>t (EState (None,s(X:=x))) (''ch2'') (x-1) tr3 \<Longrightarrow>
   p2_assn s (x#rest)(tr1@tr2@tr3@tr4)"


lemma p2_0:
"p2_assn s [] = emp\<^sub>t"
   using p2_assn.cases
   apply(auto simp add: emp_assn_def)
   using p2_assn.intros(1) by blast

lemma p2_1: 
"p2_assn s (x#l2) = Wait\<^sub>t 1 (\<lambda> _ . EState (None,s)) ({},{}) @\<^sub>t
   In\<^sub>t (EState (None,s)) (''ch1'') x @\<^sub>t
   Out\<^sub>t (EState (None,s(X:=x))) (''ch2'') (x-1) @\<^sub>t
   p2_assn (s(X:=x)) l2"
  apply(rule ext)
  subgoal for tr
  proof-
    have 1:"p2_assn s (x # l2) tr \<Longrightarrow>
    (Wait\<^sub>t 1 (\<lambda>_. EState (n.None, s)) ({}, {}) @\<^sub>t
     In\<^sub>t (EState (n.None, s)) ''ch1'' x @\<^sub>t
     Out\<^sub>t (EState (n.None, s(X := x))) ''ch2'' (x - 1) @\<^sub>t p2_assn (s(X := x)) l2) tr"
      apply(rule p2_assn.cases[of s "(x # l2)" tr])
        apply auto
      apply(auto simp add:join_assn_def) by blast
    have 2:"(Wait\<^sub>t 1 (\<lambda>_. EState (n.None, s)) ({}, {}) @\<^sub>t
     In\<^sub>t (EState (n.None, s)) ''ch1'' x @\<^sub>t
     Out\<^sub>t (EState (n.None, s(X := x))) ''ch2'' (x - 1) @\<^sub>t p2_assn (s(X := x)) l2) tr 
            \<Longrightarrow> p2_assn s (x # l2) tr"
      apply (auto simp add: join_assn_def)
      subgoal for tr1 tr2 tr3 tr4
        using p2_assn.intros(2)[of s x l2 tr4 tr1 tr2 tr3] by auto
      done
    show ?thesis using 1 2 by auto
  qed
  done

inductive t_assn :: "state \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> n tassn" where
  "t_assn s s' 0 []"
| "t_assn s (s'(X := s X + 1)) m tr4 \<Longrightarrow>
   Wait\<^sub>t 1 (\<lambda> t . ParState (EState (None,s(X:= s X + t))) (EState (None,s'))) ({''ch1''},{}) tr1 \<and> 
   IO\<^sub>t (''ch1'') (s X + 1) tr2 \<and>
   IO\<^sub>t (''ch2'') (s X) tr3 \<Longrightarrow>
   t_assn s s' (m+1) (tr1@tr2@tr3@tr4)"

lemma t_0:
"t_assn s s' 0 = emp\<^sub>t"
   using t_assn.cases
   apply(auto simp add: emp_assn_def)
   using t_assn.intros(1) by blast

lemma t_1:
"t_assn s s' (Suc n) = 
   Wait\<^sub>t 1 (\<lambda> t . ParState (EState (None,s(X:= s X + t))) (EState (None,s'))) ({''ch1''},{}) @\<^sub>t
   IO\<^sub>t (''ch1'') (s X + 1) @\<^sub>t
   IO\<^sub>t (''ch2'') (s X) @\<^sub>t
   t_assn s (s'(X := s X + 1)) n"
  apply(rule ext)
  subgoal for tr
  proof-
    have 1:"t_assn s s' (Suc n) tr \<Longrightarrow>
    (Wait\<^sub>t 1 (\<lambda>t. ParState (EState (n.None, s(X := s X + t))) (EState (n.None, s')))
      ({''ch1''}, {}) @\<^sub>t
     IO\<^sub>t ''ch1'' (s X + 1) @\<^sub>t IO\<^sub>t ''ch2'' (s X) @\<^sub>t t_assn s (s'(X := s X + 1)) n)tr "
      apply(rule t_assn.cases[of s s'"Suc n" tr])
        apply(auto simp add:join_assn_def) by blast
    have 2:"(Wait\<^sub>t 1 (\<lambda>t. ParState (EState (n.None, s(X := s X + t))) (EState (n.None, s')))
      ({''ch1''}, {}) @\<^sub>t
     IO\<^sub>t ''ch1'' (s X + 1) @\<^sub>t IO\<^sub>t ''ch2'' (s X) @\<^sub>t t_assn s (s'(X := s X + 1)) n) tr
            \<Longrightarrow> t_assn s s' (Suc n) tr"
      apply(auto simp add: join_assn_def)
      subgoal for tr1 tr2 tr3 tr4
        using t_assn.intros(2)[of s s' n tr4 tr1 tr2 tr3]
        by auto
      done
    show ?thesis
      using 1 2 by auto
  qed
  done

lemma combine:
"combine_assn {''ch1'',''ch2''} (p1_assn s l1) (p2_assn s' l2) \<Longrightarrow>\<^sub>t t_assn s s' (length l1)"
proof(induction l1 arbitrary: s s' l2)
  case Nil
  then show ?case 
  proof(cases l2)
    case Nil
    then show ?thesis 
      apply (auto simp add:entails_tassn_def)
      subgoal for tr
        using p1_0 p2_0 t_0  by simp
      done
  next
    case (Cons a list)
    then show ?thesis
      apply (auto simp add:p1_0 p2_1)
      apply (subst combine_assn_emp_wait)
      apply simp
      by (rule false_assn_entails)
  qed
next
  case (Cons a l1')
  note Cons1 = Cons
  then show ?case 
  proof (cases l2)
    case Nil
    then show ?thesis 
      apply(cases a)
      apply(auto simp add:p1_3 p2_0)
      apply(rule entails_tassn_trans)
       apply(rule combine_assn_waitout_emp)
      by auto
  next
    case (Cons b l2')
    then show ?thesis
      apply auto
      apply(cases a)
      subgoal for d x
        apply (auto simp add:p1_3 p2_1 t_1)
        apply(rule entails_tassn_trans)
         apply(rule combine_assn_waitout_wait)
           apply auto
        apply(rule entails_tassn_cancel_left)
        apply(rule entails_tassn_trans)
         apply(rule combine_assn_waitout_in)
          apply auto
        apply(rule entails_tassn_cancel_left)
        apply(rule entails_tassn_trans)
         apply(rule combine_assn_in_out)
         apply auto
        apply(rule entails_tassn_cancel_left)
        using Cons1[of s "(s'(X := s X + 1))" l2']
        apply (auto simp add: pure_assn_def imp_assn_def) 
        using \<open>combine_assn {''ch1'', ''ch2''} (p1_assn s l1') (p2_assn (s'(X := s X + 1)) l2') \<Longrightarrow>\<^sub>t t_assn s (s'(X := s X + 1)) (length l1')\<close> by force
      done
  qed
qed


fun p1_assn' :: "nat \<Rightarrow> state \<Rightarrow> n tassn" where
  "p1_assn' 0 s tr \<longleftrightarrow> (emp\<^sub>t tr)"
| "p1_assn' (Suc k) s tr \<longleftrightarrow>
   waitout_assm_assn {1} (\<lambda>t. EState(None, s(X := s X + t))) ({''ch1''},{}) ''ch1'' (\<lambda>_ .1)
   (in_orig_assn ''ch2'' 0 (EState(None,s(X := s X + 1))) (p1_assn' k (s(X:=0)))) tr"

fun p2_assn' :: "nat \<Rightarrow> state \<Rightarrow> n tassn" where
  "p2_assn' 0 s tr \<longleftrightarrow> (emp\<^sub>t tr)"
| "p2_assn' (Suc k) s tr \<longleftrightarrow>
   wait_orig_assn 1 (\<lambda> _ . EState (None,s)) ({},{}) 
   (in_orig_assn ''ch1'' 1 (EState (None,s)) (out_orig_assn ''ch2'' 0 (EState (None,s(X:=1))) (p2_assn' k (s(X:=1))))) tr
   "

fun t_assn' :: "nat \<Rightarrow> state \<Rightarrow> state \<Rightarrow> n tassn" where
  "t_assn' 0 s s' tr \<longleftrightarrow> (emp\<^sub>t tr)"
| "t_assn' (Suc k) s s' tr \<longleftrightarrow>
   wait_orig_assn 1 (\<lambda> t . ParState (EState(None, s(X := s X + t))) (EState (None,s'))) ({''ch1''},{}) 
   (io_orig_assn ''ch1'' 1  
   (io_orig_assn ''ch2'' 0 (t_assn' k (s(X:=0)) (s'(X:=1))))) tr
   "



lemma combine':
"combine_assn {''ch1'',''ch2''} (p1_assn' m1 s1) (p2_assn' m2 s2) \<Longrightarrow>\<^sub>t t_assn' m1 s1 s2"
proof(induction m1 arbitrary: s1 s2 m2)
  case 0
  then show ?case 
  proof(cases m2)
    case 0
    then show ?thesis 
      by auto 
  next
    case (Suc nat)
    then show ?thesis 
      apply auto 
      apply(rule combine_emp_wait_orig1)
      by auto
  qed
next
  case (Suc m1)
  note suc = Suc
  then show ?case
  proof(cases m2)
    case 0
    then show ?thesis
      apply auto
      apply(rule combine_waitout_assm_emp1)
      by auto
  next
    case (Suc nat)
    then show ?thesis 
      apply auto 
      apply(subst wait_orig_to_guard)
      apply(rule entails_tassn_trans)
       apply(rule combine_waitout_assm_wait_guar1)
        apply auto
      apply(subst wait_orig_to_guard')
      apply(rule wait_guar'_assn_tran)
      apply auto
      apply(rule entails_tassn_trans)
       apply(rule combine_waitout_assm_in_orig1)
      apply(auto simp add:wait_set_minus_def)
      apply(rule io_orig_assn_tran)
      apply(rule entails_tassn_trans)
       apply(rule combine_in_orig_out_orig1)
      apply auto
      apply(rule io_orig_assn_tran)
      using suc by auto
  qed
qed



end