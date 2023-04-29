(*  Title:      HOL/Library/Permutation.thy
    Author:     Lawrence C Paulson and Thomas M Rasmussen and Norbert Voelker
*)

section \<open>Permutations\<close>

theory Permutation
imports Main
begin

inductive perm :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infixr \<open><~~>\<close> 50)
where
  Nil [intro!]: "[] <~~> []"
| swap [intro!]: "y # x # l <~~> x # y # l"
| Cons [intro!]: "xs <~~> ys \<Longrightarrow> z # xs <~~> z # ys"
| trans [intro]: "xs <~~> ys \<Longrightarrow> ys <~~> zs \<Longrightarrow> xs <~~> zs"

proposition perm_refl [iff]: "l <~~> l"
  by (induct l) auto


subsection \<open>Some examples of rule induction on permutations\<close>

proposition perm_empty_imp: "[] <~~> ys \<Longrightarrow> ys = []"
  by (induction "[] :: 'a list" ys pred: perm) simp_all


text \<open>\medskip This more general theorem is easier to understand!\<close>

proposition perm_length: "xs <~~> ys \<Longrightarrow> length xs = length ys"
  by (induct pred: perm) simp_all

proposition perm_sym: "xs <~~> ys \<Longrightarrow> ys <~~> xs"
  by (induct pred: perm) auto


subsection \<open>Ways of making new permutations\<close>

text \<open>We can insert the head anywhere in the list.\<close>

proposition perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
  by (induct xs) auto

proposition perm_append_swap: "xs @ ys <~~> ys @ xs"
  by (induct xs) (auto intro: perm_append_Cons)

proposition perm_append_single: "a # xs <~~> xs @ [a]"
  by (rule perm.trans [OF _ perm_append_swap]) simp

proposition perm_rev: "rev xs <~~> xs"
  by (induct xs) (auto intro!: perm_append_single intro: perm_sym)

proposition perm_append1: "xs <~~> ys \<Longrightarrow> l @ xs <~~> l @ ys"
  by (induct l) auto

proposition perm_append2: "xs <~~> ys \<Longrightarrow> xs @ l <~~> ys @ l"
  by (blast intro!: perm_append_swap perm_append1)


subsection \<open>Further results\<close>

proposition perm_empty [iff]: "[] <~~> xs \<longleftrightarrow> xs = []"
  by (blast intro: perm_empty_imp)

proposition perm_empty2 [iff]: "xs <~~> [] \<longleftrightarrow> xs = []"
  using perm_sym by auto

proposition perm_sing_imp: "ys <~~> xs \<Longrightarrow> xs = [y] \<Longrightarrow> ys = [y]"
  by (induct pred: perm) auto

proposition perm_sing_eq [iff]: "ys <~~> [y] \<longleftrightarrow> ys = [y]"
  by (blast intro: perm_sing_imp)

proposition perm_sing_eq2 [iff]: "[y] <~~> ys \<longleftrightarrow> ys = [y]"
  by (blast dest: perm_sym)


subsection \<open>Removing elements\<close>

proposition perm_remove: "x \<in> set ys \<Longrightarrow> ys <~~> x # remove1 x ys"
  by (induct ys) auto



text \<open>\medskip Congruence rule\<close>

proposition perm_remove_perm: "xs <~~> ys \<Longrightarrow> remove1 z xs <~~> remove1 z ys"
  by (induct pred: perm) auto

proposition remove_hd [simp]: "remove1 z (z # xs) = xs"
  by auto

proposition cons_perm_imp_perm: "z # xs <~~> z # ys \<Longrightarrow> xs <~~> ys"
  by (drule perm_remove_perm [where z = z]) auto

proposition cons_perm_eq [iff]: "z#xs <~~> z#ys \<longleftrightarrow> xs <~~> ys"
  by (meson cons_perm_imp_perm perm.Cons)

proposition append_perm_imp_perm: "zs @ xs <~~> zs @ ys \<Longrightarrow> xs <~~> ys"
  by (induct zs arbitrary: xs ys rule: rev_induct) auto

proposition perm_append1_eq [iff]: "zs @ xs <~~> zs @ ys \<longleftrightarrow> xs <~~> ys"
  by (blast intro: append_perm_imp_perm perm_append1)

proposition perm_append2_eq [iff]: "xs @ zs <~~> ys @ zs \<longleftrightarrow> xs <~~> ys"
  by (meson perm.trans perm_append1_eq perm_append_swap)

proposition prem_seteq: "xs <~~> ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> set ys"
proof(induct xs arbitrary:ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof(cases "x = a")
    case True
    then show ?thesis using Cons 
      by (metis (no_types, opaque_lifting) dual_order.refl impossible_Cons perm_length 
          perm_remove_perm remove1_idem remove_hd)
  next
    case False
    have 1: "x \<in> set xs"
      using False Cons by simp
    have 2: "xs <~~> remove1 a ys"
      using Cons(2) perm_remove_perm by (metis remove_hd)
    then show ?thesis using 1 Cons(1) by (metis notin_set_remove1)
  qed
qed

proposition distinct_perm: "xs <~~> ys \<Longrightarrow> distinct xs \<Longrightarrow> distinct ys"
proof(induct xs arbitrary:ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have tmp1: "xs <~~> remove1 x ys"
    using Cons(2) perm_remove_perm by (metis remove_hd)
  have tmp2: "distinct (remove1 x ys)"
    using Cons(1,3) tmp1 by auto
  have tmp3: "x \<notin> set xs"
    using Cons by simp
  have tmp4: "x \<notin> set (remove1 x ys)"
    using Cons tmp1 by (meson perm_sym prem_seteq tmp3)
  have tmp5: "x \<in> set ys"
    using Cons(2) by (simp add: prem_seteq)
  have tmp6: "set (x#(remove1 x ys)) = set ys"
    using tmp4 tmp5 
    by (metis (mono_tags, opaque_lifting) equalityI insert_subset list.set(2) 
        perm_remove prem_seteq set_remove1_subset subsetI)
  then show ?case using tmp2 tmp3 tmp4 tmp5
    by (metis Cons.prems(1) card_distinct distinct.simps(2) distinct_card length_Cons perm_length tmp1)
    
qed

lemma perm_remove2: "x \<in> set ys \<Longrightarrow> xs <~~> remove1 x ys \<Longrightarrow> x#xs <~~> ys"
proof(induct ys arbitrary:xs)
  case Nil
  then show ?case using perm_remove by fastforce
next
  case (Cons a ys)
  then show ?case
  proof(cases "x = a")
    case True
    then show ?thesis using Cons(3) unfolding remove1.simps by auto
  next
    case False
    then show ?thesis using Cons by (meson perm.Cons perm.trans perm_remove perm_sym)
  qed
qed

lemma perm_remove3: "x \<in> set ys \<Longrightarrow> ys@xs <~~> (remove1 x ys)@xs@[x]"
proof(induct ys)
  case Nil
  then show ?case using perm_remove by fastforce
next
  case (Cons a ys)
  then show ?case
  proof(cases "x = a")
    case True
    then show ?thesis unfolding remove1.simps by (metis (mono_tags, lifting) append_Cons 
          append_eq_appendI perm_append_single)
  next
    case False
    then show ?thesis using Cons by simp
  qed
qed

end
