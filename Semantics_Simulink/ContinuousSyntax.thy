theory ContinuousSyntax
  imports DiscreteSyntax
begin

\<comment> \<open>a continuous can be a general calculation block or a integrator block
it also defined as a block while sample_time = 0.
note: In continuous blocks, offset list has other meanings which deciding the corresponding
outupd is a math operation, integrator or derivative
offset = 0: math operation
offset = 1: integrator
note: In a block b, offsets is a list which may contain both math operation and integrator.
So we limit "set (get_offsets b) = {0}" for math operations and "set (get_offsets b) = {1}" 
for integrator\<close>

type_synonym DisBlk = block
type_synonym ConBlk = block

\<comment> \<open>return the computational blocks in the continuous blocks\<close>
fun getCalBlks :: "ConBlk list \<Rightarrow> ConBlk list" where
  "getCalBlks [] = []" |
  "getCalBlks (b#bl) = (if (set (get_offsets b)) = {0} then b#getCalBlks bl
  else getCalBlks bl)"

lemma getCalBlks_last: "getCalBlks (bl@[b]) = 
(if (set (get_offsets b)) = {0} then getCalBlks bl@[b] else getCalBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding getCalBlks.simps by auto
next
  case (Cons a bl)
  then show ?case
  proof(cases "(set (get_offsets a)) = {0}")
    case True
    then show ?thesis unfolding getCalBlks.simps using Cons by auto
  next
    case False
    then show ?thesis unfolding getCalBlks.simps using Cons by auto
  qed
qed

lemma getCalBlks_rev: "getCalBlks (rev bl) = 
rev (getCalBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding getCalBlks.simps by auto
next
  case (Cons a bl)
  then show ?case using getCalBlks_last by simp
qed

lemma getCalBlksSubset : "Outputs (getCalBlks bl) \<subseteq> Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case by auto
qed

lemma getCalBlksSubset2 : "set (getCalBlks bl) \<subseteq> set bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case by auto
qed

lemma getCalBlksSubset3 : "Inputs (getCalBlks bl) \<subseteq> Inputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case by auto
qed

lemma getCalBlksPerm : "bl1 <~~> bl2 \<Longrightarrow> 
(getCalBlks bl1) <~~> (getCalBlks bl2)"
proof(induction bl1 arbitrary:bl2)
  case Nil
  then show ?case by simp
next
  case (Cons b1 bl1)
  have 1: "b1 \<in> set bl2"
    using Cons(2) by (simp add: prem_seteq)
  have 2: "bl1 <~~> remove1 b1 bl2"
    using Cons(2) 1 by (metis perm_remove_perm remove_hd)
  have 3: "getCalBlks bl1 <~~> getCalBlks (remove1 b1 bl2)"
    using Cons 2 by simp
  then show ?case
  proof(cases "set (get_offsets b1) = {0}")
    case True
    have 4: "getCalBlks (remove1 b1 bl2) = remove1 b1 (getCalBlks bl2)"
    using True proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case
      proof(cases "a = b1")
        case True
        then show ?thesis unfolding getCalBlks.simps using Cons(2) by simp
      next
        case False
        then show ?thesis unfolding getCalBlks.simps using Cons by simp
      qed
    qed
    have 5: "b1 \<in> set (getCalBlks bl2)"
      using 1 True
    proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case by auto
    qed
    then show ?thesis unfolding getCalBlks.simps using True 3 4 perm_remove2 by fastforce
  next
    case False
    have 5: "getCalBlks (remove1 b1 bl2) = getCalBlks bl2"
    using False proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons b2 bl2)
      then show ?case
      proof(cases "b1 = b2")
        case True
        then show ?thesis unfolding getCalBlks.simps using Cons(2) by simp
      next
        case False
        then show ?thesis unfolding getCalBlks.simps using Cons by simp
      qed
    qed
    then show ?thesis unfolding getCalBlks.simps using Cons 3 False by presburger
  qed
qed

lemma getCalBlks_distinct: "distinct bl \<Longrightarrow> 
distinct (getCalBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding getCalBlks.simps by auto
next
  case (Cons a bl)
  then show ?case
  proof(cases "(set (get_offsets a)) = {0}")
    case True
    then show ?thesis unfolding getCalBlks.simps using Cons
      using getCalBlksSubset2 by auto
  next
    case False
    then show ?thesis unfolding getCalBlks.simps using Cons by auto
  qed
qed

\<comment> \<open>limitation for a continuous block;
1. length outputs = length offsets = length outupds;
2. Outputs uniqueness in a block
3. "set (get_offsets b) = {0}" for math operations and "set (get_offsets b) = {1}" for integrator
4. no loop for a computational block\<close>
definition "Available' b = ((length (get_offsets b)) = (length (get_outputs b))
    \<and> ((length (get_outputs b)) = (length (get_outupd b)))
    \<and> (\<forall>i j. i < j \<and> j < (length (get_outputs b)) \<and> j \<ge> 0 
  \<longrightarrow> (nth (get_outputs b) i) \<noteq> (nth (get_outputs b) j))  \<and> 
  ({0} = set (get_offsets b) \<or> {1} = set (get_offsets b) \<or> {} = set (get_offsets b)) 
  \<and> (get_sample_time b = 0) \<and>
  (1 \<notin> set (get_offsets b) \<longrightarrow> (set (get_outputs b) \<inter> set (get_inputs b) = {})))"

definition "wf2 bl = ((Unique bl) \<and> (Graph (set bl)) \<and> (\<forall>b \<in> set bl. 
Available' b))"

lemma wf2_lemma : "wf2 (b#bl) \<Longrightarrow> wf2 bl"
  unfolding wf2_def Unique_def Graph_def by (smt (verit, best) Suc_leI le_imp_less_Suc 
      length_Cons less_imp_le_nat nth_Cons_Suc set_subset_Cons subsetD)

lemma wf2_lemma2: "wf2 bl1 \<Longrightarrow> bl1 <~~> bl2 \<Longrightarrow> wf2 bl2"
  subgoal premises pre
proof -
  have 1: "Unique bl2"
    using pre Unique_Permutation unfolding wf2_def by auto
  have 2: "set bl1 = set bl2"
    using pre(2) by (meson perm_sym prem_seteq subsetI subset_antisym)
  show ?thesis using 1 2 unfolding wf2_def using wf2_def pre(1) by presburger
qed
  done

lemma wf2_remove: "b \<in> set bl \<Longrightarrow> wf2 bl \<Longrightarrow> wf2 (remove1 b bl)"
  subgoal premises pre
proof -
  have 1: "Unique (remove1 b bl)"
    using pre by (simp add: wf2_def Unique_remove)
  show ?thesis using 1 unfolding wf2_def using wf2_def pre(1)
    by (metis wf2_lemma wf2_lemma2 perm_remove pre(2))
qed
  done

lemma wf2_rev: "wf2 bl \<Longrightarrow> wf2 (rev bl)"
  subgoal premises pre
proof -
  have 1: "Unique (rev bl)"
    using pre by (simp add: wf2_def Unique_rev)
  show ?thesis using 1 pre unfolding wf2_def using wf2_def by simp
qed
  done


\<comment> \<open>besorted for continuous blocks(and only for computational blocks);
unlike the "besorted" for discrete blocks, offsets here is always 0(vs Unit Delay)\<close>
fun besorted2 :: "block list \<Rightarrow> bool" where
"besorted2 [] = True" |
"besorted2 (b # bl) = (besorted2 bl \<and> (\<forall> a. a \<in> set bl \<longrightarrow> 
            (set (get_outputs a) \<inter> set (get_inputs b) = {})))"


lemma besorted2_is_besorted : "besorted2 bl \<Longrightarrow> besorted bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case unfolding besorted2.simps besorted.simps
    by (metis check_offset.elims(2))
qed

lemma besorted2_last : "besorted2 (bl@[a]) \<Longrightarrow> besorted2 bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding besorted2.simps by simp
qed

lemma besorted2_remove: "Unique bl \<Longrightarrow>besorted2 bl \<Longrightarrow> besorted2 (remove1 a bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case
  proof(cases "a = b")
    case True
    then show ?thesis using Cons(3) by simp
  next
    case False
    have tmp1: "besorted2 (remove1 a bl)"
      using Cons unfolding Unique_def
      by (meson Cons.IH Cons.prems(1) Unique_lemma besorted2.simps(2))
    then show ?thesis using Cons(3) 
      by (metis besorted2.simps(2) notin_set_remove1 remove1.simps(2))
  qed
qed

lemma besorted2_remove2: "besorted2 (al@bl) \<Longrightarrow> besorted bl"
proof(induction al)
  case Nil
  then show ?case by (simp add: besorted2_is_besorted)
next
  case (Cons a al)
  then show ?case by simp
qed

lemma besorted2_lemma: "besorted2 (bl@[a]@[b]) \<Longrightarrow> set (get_outputs b) \<inter> set (get_inputs a) = {}"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case by simp
qed

lemma besortedTobesorted2 : "besorted bl \<Longrightarrow> \<forall>b \<in> set bl. (set (get_offsets b) = {0})
  \<Longrightarrow> besorted2 bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "besorted2 bl"
    using Cons(2) unfolding besorted.simps using Cons(1,3) by auto
  have 2: "\<forall>a. a \<in> set bl \<longrightarrow> set (get_outputs a) \<inter> set (get_inputs b) = {}"
    using Cons(2) unfolding besorted.simps using Cons(3)
    by (smt (verit) Int_commute boolean_algebra.conj_zero_right check_offset.elims(1) 
        disjoint_insert(2) insertI1 list.set(1) list.set_intros(1))
  then show ?case unfolding besorted2.simps using 1 by simp
qed

lemma sort_is_sorted2 : "cl = (getCalBlks bl) \<Longrightarrow> sortDiag (rev cl) = rev cl  
\<Longrightarrow> wf2 bl \<Longrightarrow> besorted2 (rev cl)"
  subgoal premises pre
proof -
  have 1: "set cl \<subseteq> set bl"
    using pre(1)
  proof(induction bl arbitrary:cl)
    case Nil
    then show ?case by simp
  next
    case (Cons b bl)
    then show ?case unfolding getCalBlks.simps 
    proof(cases "set (get_offsets b) = {0}")
      case True
      then show ?thesis using Cons(1)[of "getCalBlks bl"] Cons(2)
        unfolding getCalBlks.simps by auto
    next
      case False
      then show ?thesis using Cons(1)[of "getCalBlks bl"] Cons(2)
        unfolding getCalBlks.simps by auto
    qed
  qed
  have 2: "(\<forall>i j. i < j \<and> j < length bl \<and> 0 \<le> i \<longrightarrow> bl ! i \<noteq> bl ! j)"
    using 1 pre(3) unfolding wf2_def Unique_def by simp
  have 3: "Unique cl"
    using pre(1) 2 unfolding Unique_def
  proof(induction bl arbitrary:cl)
    case Nil
    then show ?case by simp
  next
    case (Cons b bl)
    then show ?case unfolding getCalBlks.simps
    proof(cases "set (get_offsets b) = {0}")
      case True
      have tmp1: "\<forall>i j. i < j \<and> j < length (getCalBlks bl) \<and> 0 \<le> i 
        \<longrightarrow> getCalBlks bl ! i \<noteq> getCalBlks bl ! j"
        using Cons(1,3) by (metis Unique_def Unique_lemma)
      have tmp2: "\<exists>c. c \<in> set (getCalBlks bl) \<and> c = b \<Longrightarrow> 
  \<forall>i j. i < j \<and> j < length (b # bl) \<and> 0 \<le> i \<longrightarrow> (b # bl) ! i \<noteq> (b # bl) ! j \<Longrightarrow> False"
        apply clarify subgoal premises pre for c
      proof -
        have tmp2_1: "\<forall>c. c \<in> set (getCalBlks bl) \<longrightarrow> c \<in> set bl"
          apply clarify subgoal for c
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons d dl)
          then show ?case unfolding getCalBlks.simps
            by (smt (verit, best) list.set_intros(1) list.set_intros(2) set_ConsD)
        qed
        done
      have tmp2_2 : "b \<in> set bl"
        using tmp2_1 pre(2) by simp 
      show ?thesis using tmp2_2 pre(1) by (metis Suc_leI bot_nat_0.extremum in_set_conv_nth 
            le_imp_less_Suc length_Cons nth_Cons_0 nth_Cons_Suc)
      qed
      done
    have tmp3: "\<forall>i. i < length (getCalBlks bl) \<and> 0 \<le> i \<longrightarrow> 
          (getCalBlks bl) ! i \<noteq> b"
      using tmp2 Cons(3) using nth_mem by blast
    then show ?thesis using Cons(2) True unfolding getCalBlks.simps apply simp
        using tmp1 using less_Suc_eq_0_disj by fastforce
    next
      case False
      then show ?thesis using Cons unfolding getCalBlks.simps
        by (metis Unique_def Unique_lemma)
    qed
  qed
  have 4: "Unique (rev cl)"
    using 3 Unique_rev by blast
  have 5: "Graph (set (rev cl))"
  proof -
    have tmp: "set (rev cl) \<subseteq> set bl"
      using 1 by simp
    show ?thesis using pre(3) tmp unfolding wf2_def Graph_def by (meson subsetD)
  qed
  have 6: "besorted (rev cl)"
    using 4 5 pre(2) sort_is_sorted by force
  have 7: "\<forall>b \<in> set (rev cl). (set (get_offsets b) = {0})"
    using pre(1)
  proof(induction bl arbitrary:cl)
    case Nil
    then show ?case by simp
  next
    case (Cons b bl)
    then show ?case unfolding getCalBlks.simps
    proof(cases "set (get_offsets b) = {0}")
      case True
      then show ?thesis using Cons unfolding getCalBlks.simps by simp
    next
      case False
      then show ?thesis using Cons(1)[of cl] Cons(2) 
        unfolding getCalBlks.simps by presburger
    qed
    
  qed
  show ?thesis using 6 7 besortedTobesorted2 by presburger
qed
  done

text \<open>Delete those discrete blocks in a Simulink graph.\<close>
fun deleteDisBlks :: "block list \<Rightarrow> block list" where
  "deleteDisBlks [] = []" |  
  "deleteDisBlks (a#al) = (if (get_sample_time a > 0) then deleteDisBlks al
  else (a#(deleteDisBlks al)))"

\<comment> \<open>return the integrator blocks in the continuous blocks\<close>
fun findIntegBlks :: "block list \<Rightarrow> block list" where
  "findIntegBlks [] = []" |
  "findIntegBlks (b#bl) = (if (set (get_offsets b) = {1}) then 
b#(findIntegBlks bl) else findIntegBlks bl)"

lemma findIntegBlks_last: "findIntegBlks (bl@[b]) = 
(if (set (get_offsets b)) = {1} then findIntegBlks bl@[b] else findIntegBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding findIntegBlks.simps by auto
next
  case (Cons a bl)
  then show ?case
  proof(cases "(set (get_offsets a)) = {1}")
    case True
    then show ?thesis unfolding findIntegBlks.simps using Cons by auto
  next
    case False
    then show ?thesis unfolding findIntegBlks.simps using Cons by auto
  qed
qed

lemma findIntegBlks_rev: "findIntegBlks (rev bl) = 
rev (findIntegBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding findIntegBlks.simps by auto
next
  case (Cons a bl)
  then show ?case using findIntegBlks_last by simp
qed

lemma findIntegBlksSubset : "Outputs (findIntegBlks bl) \<subseteq> Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding findIntegBlks.simps by auto
qed


lemma findIntegBlksSubset2 : "set bl1 \<subseteq> set bl2 \<Longrightarrow>
Outputs (findIntegBlks bl1) \<subseteq> Outputs (findIntegBlks bl2)"
proof(induction bl1 arbitrary: bl2)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case
  proof(cases "set (get_offsets b) = {1}")
    case True
    have 1: "set (get_offsets b) = {1} \<Longrightarrow> b \<in> set bl2 \<Longrightarrow> set (get_outputs b) \<subseteq> 
        Outputs (findIntegBlks bl2)"
    proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case
      proof(cases "b = a")
        case True
        then show ?thesis unfolding findIntegBlks.simps using Cons(2) by auto
      next
        case False
        have tmp1: "set (get_outputs b) \<subseteq> Outputs (findIntegBlks bl2)"
          using Cons False by simp
        then show ?thesis unfolding findIntegBlks.simps by auto
      qed
    qed
    then show ?thesis unfolding findIntegBlks.simps using Cons True by simp
  next
    case False
    then show ?thesis unfolding findIntegBlks.simps using Cons by simp
  qed
qed

lemma findIntegBlksSubset3 : "set (findIntegBlks bl) \<subseteq> set bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding findIntegBlks.simps by auto
qed

lemma findIntegBlkswf : "wf2 bl \<Longrightarrow> wf2 (findIntegBlks bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case
  proof(cases "set (get_offsets a) = {0}")
    case True
    then show ?thesis unfolding getCalBlks.simps using Cons
      by (simp add: wf2_lemma)
  next
    case False
    have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
      using Cons(2) unfolding wf2_def Unique_def
      by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
    have tmp2: "\<forall>j. j < (length (findIntegBlks bl)) \<and> j \<ge> 0 
      \<longrightarrow> a \<noteq> (nth (findIntegBlks bl) j)"
      using tmp1 findIntegBlksSubset3
      by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
    have tmp3: "Unique (a # findIntegBlks bl)"
      using Cons Unique_add unfolding wf2_def tmp2 by (metis wf2_def wf2_lemma tmp2)
    have tmp4: "Graph (set (a # findIntegBlks bl))"
    proof -
      have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
        using findIntegBlksSubset3 by auto
    show ?thesis using tmp1 Cons(2) unfolding wf2_def by (meson Graph_def subsetD)
    qed
    have tmp5: "Ball (set (a # findIntegBlks bl)) Available' "
    proof -
      have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
        using findIntegBlksSubset3 by auto
      show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
    qed
    show ?thesis using False unfolding findIntegBlks.simps wf2_def apply simp 
      using tmp3 tmp4 tmp5 by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
    qed
qed


lemma IntegInterComputationalBlocks : "wf2 bl \<Longrightarrow>
Outputs (findIntegBlks bl) \<inter> Outputs (getCalBlks bl) = {}"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "Outputs (findIntegBlks bl) \<inter> Outputs (getCalBlks bl) = {}"
    using Cons wf2_lemma by auto
  have 2: "set (get_outputs b) \<inter> Outputs bl = {}"
    using Cons(2) unfolding wf2_def Unique_def Graph_def 
    by (meson wf2_def Cons.prems Graph_lemma2 disjoint_iff)
  then show ?case
  proof(cases "set (get_offsets b) = {1}")
    case True
    have 3: "set (get_outputs b) \<inter> Outputs (getCalBlks bl) = {}"
      using getCalBlksSubset 2 by auto
    show ?thesis using True unfolding findIntegBlks.simps getCalBlks.simps apply simp
      using 1 3 by (simp add: Int_Un_distrib2)
  next
    case False
    then show ?thesis  unfolding findIntegBlks.simps getCalBlks.simps apply simp
      using 1 findIntegBlksSubset 2 by auto
  qed
qed

lemma findIntegBlksPerm : "bl1 <~~> bl2 \<Longrightarrow> (findIntegBlks bl1) <~~> (findIntegBlks bl2)"
proof(induction bl1 arbitrary:bl2)
  case Nil
  then show ?case by simp
next
  case (Cons b1 bl1)
  have 1: "b1 \<in> set bl2"
    using Cons(2) by (simp add: prem_seteq)
  have 2: "bl1 <~~> remove1 b1 bl2"
    using Cons(2) 1 by (metis perm_remove_perm remove_hd)
  have 3: "findIntegBlks bl1 <~~> findIntegBlks (remove1 b1 bl2)"
    using Cons 2 by simp
  then show ?case
  proof(cases "set (get_offsets b1) = {1}")
    case True
    have 4: "findIntegBlks (remove1 b1 bl2) = remove1 b1 (findIntegBlks bl2)"
    using True proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case
      proof(cases "a = b1")
        case True
        then show ?thesis unfolding findIntegBlks.simps using Cons(2) by simp
      next
        case False
        then show ?thesis unfolding findIntegBlks.simps using Cons by simp
      qed
    qed
    have 5: "b1 \<in> set (findIntegBlks bl2)"
      using 1 True
    proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case by auto
    qed
    then show ?thesis unfolding findIntegBlks.simps using True 3 4 perm_remove2 by fastforce
  next
    case False
    have 5: "findIntegBlks (remove1 b1 bl2) = findIntegBlks bl2"
    using False proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons b2 bl2)
      then show ?case
      proof(cases "b1 = b2")
        case True
        then show ?thesis unfolding findIntegBlks.simps using Cons(2) by simp
      next
        case False
        then show ?thesis unfolding findIntegBlks.simps using Cons by simp
      qed
    qed
    then show ?thesis unfolding findIntegBlks.simps using Cons 3 False by presburger
  qed
qed

\<comment> \<open>we classify those blocks by calling function "compute_st_forward" and "compute_st_backward"\<close>

text \<open>Then check the blocks(no blocks whose sample_time = -1) and split them\<close>
fun checkType :: "block list \<Rightarrow> bool" where
  "checkType [] = True" |
  "checkType (b#bl) = (if (get_sample_time b = -1) then False else checkType bl)"

fun classifyBlocks :: "block list \<Rightarrow> DisBlk list \<times> ConBlk list" where
  "classifyBlocks [] = ([],[])" |
  "classifyBlocks (b#bl) = (let x = classifyBlocks bl in 
      (if (get_sample_time b = 0) then (fst x, b#(snd x)) else (b#(fst x), snd x)))"

text \<open>The following functions are for the combination.
note: combine block "a" into block "b"
we call block "b" the basic block and block "a" the additional block\<close>
(*combine the inputs, basic inputs vl1; additional inputs vl2; additional output v
we remain the inputs in vl2 and delete those same inputs and produced inputs for vl1.
note: when calling this function, we have already validated the additional block produces
outputs for the basic block inputs.*)
fun combineInputs :: "var list \<Rightarrow> var list \<Rightarrow> var \<Rightarrow> var list" where
  "combineInputs [] vl2 v = vl2" |
  "combineInputs (v1#vl1) vl2 v = (if v = v1 \<or> v1 \<in> set vl2 then (combineInputs vl1 vl2 v)
  else v1#(combineInputs vl1 vl2 v))"

\<comment> \<open>for ODE\<close>
fun combineInputs2 :: "var list \<Rightarrow> var list \<Rightarrow> var list" where
  "combineInputs2 [] vl2 = vl2" |
  "combineInputs2 (v1#vl1) vl2 = (if v1 \<in> set vl2 then (combineInputs2 vl1 vl2)
  else v1#(combineInputs2 vl1 vl2))"


text\<open>Return the position of "a" in a list bl\<close>
fun findPos :: "'a list \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int" where
  "findPos [] a i = -1" |
  "findPos (b#bl) a i = (if a = b then i else (findPos bl a (i+1)))"

text\<open>f: real list \<Rightarrow> real;
so this function is to update real list in combination(the new real list is for the basic block).
basic inputs vl1; additional inputs vl2; additional output v; basic real list xl1;
additional real list xl2; additional outupd f.
And the result list length = length vl1\<close>
fun replaceInputs :: "var list \<Rightarrow> var list \<Rightarrow> var \<Rightarrow>
real list \<Rightarrow> real list \<Rightarrow> outupd \<Rightarrow> real list" where
  "replaceInputs [] vl2 v xl1 xl2 f = []" |
  "replaceInputs (v1#vl1) vl2 v xl1 xl2 f = (if v1 = v then 
  (f xl2)#(replaceInputs vl1 vl2 v xl1 xl2 f)
  else (if (findPos vl2 v1 0) = -1 then (hd xl1)#(replaceInputs vl1 vl2 v (tl xl2) xl2 f) else 
  (xl2 ! nat (findPos vl2 v1 0))#(replaceInputs vl1 vl2 v xl1 xl2 f)))"

(*from the final real list to the final list for the basic outupd function,
here f is the additional function*)
fun splitInputs :: "var list \<Rightarrow> var list \<Rightarrow> var \<Rightarrow> real list \<Rightarrow> outupd \<Rightarrow> real list" where
  "splitInputs vl1 vl2 v xl f = replaceInputs vl1 vl2 v (take (length xl - length vl2) xl) 
  (drop (length xl - length vl2) xl) f"


text\<open>when combination happens in two ODEs, we don't delete those produced inputs
and just combine those ODEs. So this function is for updating basic outupds when
combination happens in two ODEs.
"combineInputs a1 a2 (CHR '' '')" means that we don't delete those produced inputs and only
delete those same inputs, (CHR '' '') means a useless output not in basic inputs a1.
"(splitInputs a1 a2 (CHR '' '') s (\<lambda>x.0))" return the real list for f which only find the 
inputs for a1, so outupd "(\<lambda>x.0)" is useless.\<close>
fun reviseFun :: "outupd list \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> outupd list" where
  "reviseFun [] a1 a2 = []" |
  "reviseFun (f#fl) a1 a2 = (\<lambda>s. (if length s = length (combineInputs2 a2 a1) then
  (f (splitInputs a1 a2 (CHR '' '') s (\<lambda>x.0))) else 0))#(reviseFun fl a1 a2)"

lemma reviseFunEq: "length (reviseFun fl a1 a2) = length fl"
proof(induction fl)
  case Nil
  then show ?case by simp
next
  case (Cons a fl)
  then show ?case unfolding reviseFun.simps by simp
qed

(*combine the function f1(calculation function) into the function list (f#f2), 
a1 is the initial input list, a2 is the additional input list, v is the output*)
fun updateFunc :: "outupd list \<Rightarrow> var list \<Rightarrow> var \<Rightarrow> outupd \<Rightarrow> var list \<Rightarrow> outupd list" where
  "updateFunc [] a1 v f1 a2 = []" |
  "updateFunc (f#f2) a1 v f1 a2 = (\<lambda>xl. (if length xl = length (combineInputs a1 a2 v)
  then (f (splitInputs a1 a2 v xl f1)) else 0))#(updateFunc f2 a1 v f1 a2)"

lemma updateFuncEq: "length (updateFunc fl a1 v f1 a2) = length fl"
proof(induction fl)
  case Nil
  then show ?case by simp
next
  case (Cons a fl)
  then show ?case unfolding reviseFun.simps by simp
qed

(*combine the function f1(ODE) into the function list (f#f2), 
a1 is the initial input list, a2 is the additional input list*)
fun updateFunc2 :: "outupd list \<Rightarrow> var list \<Rightarrow> outupd \<Rightarrow> var list \<Rightarrow> outupd list" where
  "updateFunc2 fl a1 f1 a2 = reviseFun fl a1 a2 @[(\<lambda>s. (if length s = length (combineInputs2 a2 a1)
   then (f1 (drop (length a2) s)) else 0))]"

value "combineInputs [CHR ''x'', CHR ''c''] [CHR ''a'', CHR ''b''] (CHR ''c'')"
value "splitInputs [CHR ''x'', CHR ''c''] [CHR ''a'', CHR ''b''] (CHR ''c'') [1,2,3] 
(\<lambda>s.(if length s = 2 then (s ! 0) * (s ! 1) else 0) )"

value "hd (updateFunc [\<lambda>s.(if length s = 2 then (s ! 0) + (s ! 1) else 0)] 
[CHR ''x'', CHR ''c''] (CHR ''c'') 
(\<lambda>s.(if length s = 2 then (s ! 0) * (s ! 1) else 0) ) [CHR ''a'', CHR ''b'']) [1,2,3] "

(*Combine the outputs when additional block is a computational block;
c is always 0 in this situation *)
fun combineOneOutput :: "var list \<Rightarrow> var \<Rightarrow> offset \<Rightarrow> outupd \<Rightarrow> 
  ConBlk \<Rightarrow> ConBlk" where
  "combineOneOutput a1 b c f (Block a2 b2 c2 d2 f2) = (if b \<in> set b2 then (Block a2 b2 c2 d2 f2)
else (Block (combineInputs a2 a1 b) b2 c2 0 (updateFunc f2 a2 b f a1)))"

lemma combineOneOutputSubset : "set (get_outputs (combineOneOutput 
a1 b c f (Block a2 b2 c2 d2 f2))) = set b2"
  unfolding combineOneOutput.simps by auto

lemma combineOneOutputSubset2 : "set b2 \<subseteq>set (get_outputs (combineOneOutput 
a1 b c f (Block a2 b2 c2 d2 f2)))"
  unfolding combineOneOutput.simps by auto

lemma combineOneOutputOffsetsEq : "set c2 = {1} \<Longrightarrow> set (get_offsets (combineOneOutput 
a1 b c f (Block a2 b2 c2 d2 f2))) = {1}"
  unfolding combineOneOutput.simps by auto

lemma combineOneOutputEq : "length b2 = length c2 \<and> length b2 = length f2 \<Longrightarrow>
length (get_offsets (combineOneOutput a1 b c f (Block a2 b2 c2 d2 f2))) =
length (get_outputs (combineOneOutput a1 b c f (Block a2 b2 c2 d2 f2))) \<and>
length (get_offsets (combineOneOutput a1 b c f (Block a2 b2 c2 d2 f2))) =
length (get_outupd (combineOneOutput a1 b c f (Block a2 b2 c2 d2 f2)))"
  unfolding combineOneOutput.simps updateFunc.simps using updateFuncEq by force

(*Combine the outputs when additional block is a integrator block;
c is always 1 in this situation, means type integrator*)
fun combineOneOutput2 :: "var list \<Rightarrow> var \<Rightarrow> offset \<Rightarrow> outupd \<Rightarrow> 
  ConBlk \<Rightarrow> ConBlk" where
  "combineOneOutput2 a1 b c f (Block a2 b2 c2 d2 f2) = (if b \<in> set b2 then (Block a2 b2 c2 d2 f2)
else (Block (combineInputs2 a2 a1) (b2@[b]) (c2@[c]) 0 (updateFunc2 f2 a1 f a2)))"

lemma combineOneOutput2Subset : "set (get_outputs (combineOneOutput2 
a1 b c f (Block a2 b2 c2 d2 f2))) = set (b#b2)"
  unfolding combineOneOutput.simps by auto

lemma combineOneOutput2Subset2 : "set b2 \<subseteq> set (get_outputs (combineOneOutput2 
a1 b c f (Block a2 b2 c2 d2 f2)))"
  unfolding combineOneOutput.simps by auto

lemma combineOneOutput2Eq : "length b2 = length c2 \<and> length b2 = length f2 \<Longrightarrow>
length (get_offsets (combineOneOutput2 a1 b c f (Block a2 b2 c2 d2 f2))) =
length (get_outputs (combineOneOutput2 a1 b c f (Block a2 b2 c2 d2 f2))) \<and>
length (get_offsets (combineOneOutput2 a1 b c f (Block a2 b2 c2 d2 f2))) =
length (get_outupd (combineOneOutput2 a1 b c f (Block a2 b2 c2 d2 f2)))"
  unfolding combineOneOutput2.simps updateFunc2.simps using reviseFunEq by force

(*Combine additional block "(Block a1 b1 c1 d1 f1)"
into the basic block "(Block a2 b2 c2 d2 f2)",
note: d1 = d2 = 0*)
fun combineOneBlock :: "var list \<Rightarrow> var list \<Rightarrow> offset list \<Rightarrow> outupd list \<Rightarrow> 
  ConBlk \<Rightarrow> ConBlk" where
  "combineOneBlock a1 [] c1 f1 (Block a2 b2 c2 d2 f2) = (Block a2 b2 c2 0 f2)" |
  "combineOneBlock a1 b1 [] f1 (Block a2 b2 c2 d2 f2) = (Block a2 b2 c2 0 f2)" |
  "combineOneBlock a1 b1 c1 [] (Block a2 b2 c2 d2 f2) = (Block a2 b2 c2 0 f2)" |
  "combineOneBlock a1 (b#b1) (c#c1) (f#f1) (Block a2 b2 c2 d2 f2) = (if c = 1 then
  (combineOneBlock a1 b1 c1 f1 (combineOneOutput2 a1 b c f (Block a2 b2 c2 d2 f2))) 
  else combineOneBlock a1 b1 c1 f1 (combineOneOutput a1 b c f (Block a2 b2 c2 d2 f2)))"

lemma combineOneBlockSubset : "set (get_outputs (combineOneBlock a1 b1 c1 f1 
(Block a2 b2 c2 d2 f2))) \<subseteq> set b1 \<union> set b2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis by (metis "1" combineOneBlock.simps(3) get_outputs.simps 
            subset_refl sup.coboundedI2)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      then show ?thesis
      proof(cases "hd c1 = 1")
        case True
        then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons[of "tl c1" "tl f1" "get_inputs 
              ((combineOneOutput2 a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
              "get_outputs (combineOneOutput2 a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))"] 
            combineOneOutput2Subset by (smt (verit, del_insts) UnE UnI2 Un_commute 
              combineOneOutput2.simps dual_order.trans get_outputs.simps hd_in_set list.discI 
              list.sel(1) local.Cons set_ConsD set_subset_Cons subset_iff sup.orderE sup_mono)
          
      next
        case False
        then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons[of "tl c1" "tl f1" "get_inputs 
              ((combineOneOutput a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
              "get_outputs (combineOneOutput a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))"] 
            combineOneOutputSubset by (metis Un_mono combineOneOutput.simps 
              equalityE local.Cons order_trans set_subset_Cons)
      qed
    qed
  qed
qed

lemma combineOneBlockSubset2 : "set b2 \<subseteq> set (get_outputs (combineOneBlock a1 b1 c1 f1 
(Block a2 b2 c2 d2 f2)))"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis by (metis "1" combineOneBlock.simps(3) get_outputs.simps subset_refl)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      then show ?thesis
      proof(cases "hd c1 = 1")
        case True
        then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons combineOneOutput2Subset2 by force
      next
        case False
        then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons combineOneOutputSubset2 by force 
      qed
    qed
  qed
qed

lemma combineOneBlockSubset3 : "set c1 = {0} \<Longrightarrow>
 set (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = set b2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis by (metis "1" combineOneBlock.simps(3) get_outputs.simps)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 0"
        using Cons(2) by (metis "1" list.set_intros(1) singleton_iff)
      have 4: "set (get_outputs (combineOneOutput a1 b (hd c1) (hd f1) 
    (Block a2 b2 c2 d2 f2))) = set b2"
        using combineOneOutputSubset by simp
      then show ?thesis
      proof(cases "tl c1 = []")
        case True
        note T = True
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by simp
        next
          case False
          then show ?thesis using 1 2 3 4 T combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by (metis combineOneBlock.simps(2) combineOneOutput.simps 
                get_outputs.simps le_zero_eq list.collapse not_one_le_zero)
        qed
      next
        case False
        have 5: "set (tl c1) = {0}"
          using False Cons(2) by (metis "1" set_empty2 set_subset_Cons subset_singletonD)
        then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons by simp
      qed
    qed
  qed
qed

lemma combineOneBlockSubset4 : "set c1 = {} \<Longrightarrow>
 set (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = set b2"
proof(induction b1)
  case Nil
  then show ?case by simp
next
  case (Cons a b1)
  then show ?case using Cons(2) by simp
qed

lemma combineOneBlockSubset5 : "Available' (Block a1 b1 c1 d1 f1) \<Longrightarrow> set c1 = {1} \<Longrightarrow>
 set (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = set b1 \<union> set b2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(2) unfolding Available'_def by simp
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 1"
        using Cons(3) by (metis "1" list.set_intros(1) singleton_iff)
      have 4: "set (get_outputs (combineOneOutput2 a1 b (hd c1) (hd f1) 
    (Block a2 b2 c2 d2 f2))) = set (b#b2)"
        using combineOneOutput2Subset by simp
      then show ?thesis
      proof(cases "tl c1 = []")
        case True
        note T = True
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by auto
        next
          case False                       
          then show ?thesis using 1 2 3 4 T Cons(2) unfolding Available'_def by force
        qed
      next
        case False
        note F1 = False
        have 5: "set (tl c1) = {1}"
          using False Cons(3) by (metis "1" set_empty2 set_subset_Cons subset_singletonD)
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 False Cons(2) unfolding Available'_def by (metis 
                get_offsets.simps get_outputs.simps length_greater_0_conv length_tl list.sel(3))
        next
          case False
          note F2 = False
          then show ?thesis
          proof(cases "tl f1 = []")
            case True
            then show ?thesis using 1 2 3 4 False Cons(2) unfolding Available'_def
              by (metis get_outputs.simps get_outupd.simps length_0_conv length_tl list.sel(3))
          next
            case False
            have 6: "Available' (Block a1 b1 (tl c1) d1 (tl f1))"
              using Cons(2) 1 2 F1 F2 False unfolding Available'_def by (metis "5" Suc_less_eq 
                  bot_nat_0.extremum get_offsets.simps get_outputs.simps get_outupd.simps 
                  get_sample_time.simps insert_iff length_Cons length_tl list.sel(3) nth_Cons_Suc)
            have 7: "set (get_outputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
            (Block a2 b2 c2 d2 f2))) = set b1 \<union> set b2"
              using Cons(1) 5 6 by presburger
            then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] "5" "6" Cons.IH by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma combineOneBlockEq : "length c1 = length b1 \<and> length c1 = length f1  \<Longrightarrow> set c1 = {1} \<Longrightarrow>
 set (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = set b1 \<union> set b2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(2) by force
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 1"
        using Cons(3) by (metis "1" list.set_intros(1) singleton_iff)
      have 4: "set (get_outputs (combineOneOutput2 a1 b (hd c1) (hd f1) 
    (Block a2 b2 c2 d2 f2))) = set (b#b2)"
        using combineOneOutput2Subset by simp
      then show ?thesis
      proof(cases "tl c1 = []")
        case True
        note T = True
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by auto
        next
          case False                       
          then show ?thesis using 1 2 3 4 T Cons(2) unfolding Available'_def by force
        qed
      next
        case False
        note F1 = False
        have 5: "set (tl c1) = {1}"
          using False Cons(3) by (metis "1" set_empty2 set_subset_Cons subset_singletonD)
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 False Cons(2) unfolding Available'_def by (metis 
                length_greater_0_conv length_tl list.sel(3))
        next
          case False
          note F2 = False
          then show ?thesis
          proof(cases "tl f1 = []")
            case True
            then show ?thesis using 1 2 3 4 False Cons(2) unfolding Available'_def
              by (metis length_0_conv length_tl list.sel(3))
          next
            case False
            have 6: "length b1 = length (tl c1) \<and> length b1 = length (tl f1)"
              using Cons(2) 1 2 F1 F2 False by force
            have 7: "set (get_outputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
            (Block a2 b2 c2 d2 f2))) = set b1 \<union> set b2"
              using Cons(1) 5 6 by simp
            then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] "5" "6" Cons.IH by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma combineOneBlockEq2: "length b1 = length c1 \<and> length b1 = length f1 \<Longrightarrow>
length b2 = length c2 \<and> length b2 = length f2 \<Longrightarrow>
length (get_offsets (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = 
length (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) \<and>
length (get_offsets (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = 
length (get_outupd (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)))"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons(2) by simp
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(2) by simp
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      then show ?thesis
      proof(cases "hd c1 = 1")
        case True
        then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons 1 2 combineOneOutput2Eq by (smt (verit, best) 
              combineOneOutput2.simps get_offsets.simps get_outputs.simps get_outupd.simps 
              length_tl list.sel(3))
      next
        case False
        then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons combineOneOutputEq "1" "2" by (metis (no_types, lifting) 
              combineOneOutput.simps length_tl list.sel(3) updateFuncEq)
      qed
    qed
  qed
qed

lemma combineOneBlockOffsetsEq : "set c2 = {1} \<Longrightarrow>
set (get_offsets (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = {1}"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons(2) by simp
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(2) 1 by (metis combineOneBlock.simps(3) get_offsets.simps)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      then show ?thesis 
      proof(cases "hd c1 = 1")
        case True
        then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons 1 2 by auto
      next
        case False
        then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons combineOneOutputOffsetsEq "1" "2" by auto
      qed
    qed
  qed
qed

(*Combine additional block list "al" into a basic block "b"*)
fun combineBlocks :: "ConBlk list \<Rightarrow> ConBlk \<Rightarrow> ConBlk" where
  "combineBlocks [] b = b" |
  "combineBlocks (a#al) b = combineBlocks al (combineOneBlock (get_inputs a) 
  (get_outputs a) (get_offsets a) (get_outupd a) b)"

lemma combineBlocksSubset : "set (get_outputs (combineBlocks al b)) \<subseteq> Outputs (b#al)"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case unfolding combineBlocks.simps using combineOneBlockSubset[of "(get_inputs a)"
        "(get_outputs a)" "(get_offsets a)" "(get_outupd a)" "(get_inputs b)" "(get_outputs b)" 
        "(get_offsets b)" "(get_sample_time b)" "(get_outupd b)"] Cons[of 
        "(combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)"]
    by auto
qed

lemma combineBlocksSubset2 : "\<forall>b \<in> set al. set (get_offsets b) = {0} \<or>
 set (get_offsets b) = {1} \<or> set (get_offsets b) = {} \<Longrightarrow>
set (get_outputs (combineBlocks al b)) \<subseteq> Outputs (b#(findIntegBlks al))"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case 
    proof(cases "set (get_offsets a) = {1}")
      case True
      have 2: "a \<in> set (findIntegBlks (a # al))"
        unfolding findIntegBlks.simps True by simp
      then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset
        by (smt (verit, ccfv_SIG) Outputs.simps(2) True dual_order.trans 
            findIntegBlks.simps(2) le_sup_iff list.set_intros(2) set_eq_subset)
    next
      case False
      note F = False
      then show ?thesis
      proof(cases "set (get_offsets a) = {0}")
        case True
        then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset3
        by (smt (verit, best) False Outputs.elims findIntegBlks.simps(2) list.distinct(1) 
            list.inject list.set_intros(2))
      next
        case False
        have 3: "(get_offsets a) = []"
          using Cons(2) False F by auto
        then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset4
  by (smt (verit, best) F Outputs.simps(2) findIntegBlks.simps(2) list.set_intros(2) set_empty)
      qed
    qed
qed

lemma combineBlocksSubset3 : "set (get_outputs b) \<subseteq> set (get_outputs (combineBlocks al b))"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case unfolding combineBlocks.simps using combineOneBlockSubset2
    by (metis local.Cons subset_trans)
qed

lemma combineBlocksSubset4 : "\<forall>b \<in> set al. set (get_offsets b) = {0} \<or>
 set (get_offsets b) = {1} \<or> set (get_offsets b) = {} \<Longrightarrow> wf2 al \<Longrightarrow>
set (get_outputs (combineBlocks al b)) = Outputs (b#(findIntegBlks al))"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case 
    proof(cases "set (get_offsets a) = {1}")
      case True
      have 2: "a \<in> set (findIntegBlks (a # al))"
        unfolding findIntegBlks.simps True by simp
      have 3: "Available' (Block (get_inputs a) (get_outputs a) 
        (get_offsets a) (get_sample_time a) (get_outupd a))"
        using Cons(3) unfolding wf2_def by (simp add: Available'_def)
      have 4: "set (get_outputs
          (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 
      b)) = set (get_outputs a) \<union> set (get_outputs b)"
        using combineOneBlockSubset5 True 1 3 by metis
      then show ?thesis using 1 unfolding combineBlocks.simps using Cons 
        wf2_lemma True by auto
    next
      case False
      note F = False
      then show ?thesis
      proof(cases "set (get_offsets a) = {0}")
        case True
        then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset3
          by (metis wf2_lemma False Outputs.simps(2) findIntegBlks.simps(2) list.set_intros(2))
      next
        case False
        have 3: "(get_offsets a) = []"
          using Cons(2) False F by auto
        then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset4
   by (metis wf2_lemma F Outputs.simps(2) findIntegBlks.simps(2) list.set_intros(2) set_empty)
      qed
    qed
  qed

lemma combineBlocksEq : "\<forall>b \<in> set al. set (get_offsets b) = {1} \<and> 
length (get_offsets b) = length (get_outputs b) \<and>
length (get_offsets b) = length (get_outupd b) \<Longrightarrow>
set (get_outputs (combineBlocks al b)) = Outputs (b#al)"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case unfolding combineBlocks.simps using combineOneBlockEq Cons by (smt (verit, best) 
        Outputs.simps(2) list.set_intros(1) list.set_intros(2) sup.assoc sup_commute)
qed

lemma combineBlockEq2 : "\<forall>b \<in> set(b#al). length (get_offsets b) = length (get_outputs b) \<and>
length (get_offsets b) = length (get_outupd b) \<Longrightarrow> length (get_offsets 
(combineBlocks al b)) = length (get_outputs (combineBlocks al b)) \<and> length (get_offsets 
(combineBlocks al b)) = length (get_outupd (combineBlocks al b))"
proof(induction al arbitrary: b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case unfolding combineBlocks.simps using combineOneBlockEq2 Cons
    by (metis list.set_intros(1) list.set_intros(2) set_ConsD)
qed

lemma combineBlocksOffsetEq : "set (get_offsets b) = {1} \<Longrightarrow>
set (get_offsets (combineBlocks al b)) = {1}"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  then show ?case unfolding combineBlocks.simps using combineOneBlockOffsetsEq
    by (metis get_offsets.elims)
qed

text\<open>bl: all continuous blocks; c: basic integrator block;
cl: those related blocks of c which have been found before\<close>
fun getOneRelatedBlock :: "ConBlk list \<Rightarrow> ConBlk \<Rightarrow> 
  ConBlk list \<Rightarrow> ConBlk option" where
  "getOneRelatedBlock [] c cl = None" |
  "getOneRelatedBlock (b#bl) c cl = (if (set (get_outputs b) \<inter> set (get_inputs c) \<noteq> {} \<or>
  set (get_outputs b) \<inter> (Inputs cl) \<noteq> {}) then (Some b) else 
  getOneRelatedBlock bl c cl)"

lemma getOneRelatedBlockSubset: "getOneRelatedBlock bl c cl = Some y \<Longrightarrow> y \<in> set bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding getOneRelatedBlock.simps
    by (metis list.set_intros(1) list.set_intros(2) option.inject)
qed

(*give the block list bl, return the related blocks of the integrator block c;
here cl are those related blocks of c which have been found before(initialized to [])*)
function getRelatedBlocks :: "ConBlk list \<Rightarrow> ConBlk \<Rightarrow> 
  ConBlk list \<Rightarrow> ConBlk list" where
  "getRelatedBlocks bl c cl = (if getOneRelatedBlock bl c cl = None 
  then cl else getRelatedBlocks (remove1 (the (getOneRelatedBlock bl c cl)) bl) c 
  (cl@[(the (getOneRelatedBlock bl c cl))]))"
  by pat_completeness auto
termination 
  apply (relation "measures[(\<lambda>(bl::ConBlk list , c::ConBlk,
cl::ConBlk list). length bl)]", auto)
  subgoal premises pre for bl c cl y
  proof -
    show ?thesis using pre getOneRelatedBlockSubset
      by (metis length_Cons lessI perm_length perm_remove)
  qed
  done

lemma getRelatedBlocksSubset : "Outputs (getRelatedBlocks bl c cl) \<subseteq> Outputs bl \<union> Outputs cl"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case 
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    then show ?thesis using getRelatedBlocks.simps[of bl c cl] by auto
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "Outputs (remove1 (the (getOneRelatedBlock bl c cl)) bl) \<union>
    Outputs (cl@[the (getOneRelatedBlock bl c cl)]) = Outputs bl \<union> Outputs cl"
      using False getOneRelatedBlockSubset by (metis (no_types, lifting) "3" Outputs_base 
          Outputs_base2 length_remove1 nat_neq_iff sup.commute sup.left_commute)
    have 5: "Outputs (getRelatedBlocks (remove1 (the (getOneRelatedBlock bl c cl)) bl) c 
    (cl@[the (getOneRelatedBlock bl c cl)])) \<subseteq> Outputs (remove1 (the 
    (getOneRelatedBlock bl c cl)) bl) \<union> Outputs (cl@[the (getOneRelatedBlock bl c cl)])"
      using 2 3 by blast
    then show ?thesis using 4 5 by simp
  qed
qed

lemma getRelatedBlocksSubset2 : "set (getRelatedBlocks bl c cl) \<subseteq> set bl \<union> set cl"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case 
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    then show ?thesis using getRelatedBlocks.simps[of bl c cl] by auto
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "set (remove1 (the (getOneRelatedBlock bl c cl)) bl) \<union>
    set (cl@[the (getOneRelatedBlock bl c cl)]) \<subseteq> set bl \<union> set cl"
      using False getOneRelatedBlockSubset using "3" set_remove1_subset by fastforce
    have 5: "set (getRelatedBlocks (remove1 (the (getOneRelatedBlock bl c cl)) bl) c 
    (cl@[the (getOneRelatedBlock bl c cl)])) \<subseteq> set (remove1 (the 
    (getOneRelatedBlock bl c cl)) bl) \<union> set (cl@[the (getOneRelatedBlock bl c cl)])"
      using 2 3 by blast
    then show ?thesis using 4 5 using False by fastforce
  qed
qed

lemma getRelatedBlocksUnique: "Unique (bl@cl) \<Longrightarrow> Unique (getRelatedBlocks bl c cl)"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    then show ?thesis using 2(2) using getRelatedBlocks.simps[of bl c cl]
      using Unique_Cons by auto
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "Unique ((remove1 (the (getOneRelatedBlock bl c cl)) bl)
        @(cl @ [the (getOneRelatedBlock bl c cl)]))"
    proof -
      have tmp1: "\<forall>j. j < (length (remove1 (the (getOneRelatedBlock bl c cl)) 
        ((remove1 (the (getOneRelatedBlock bl c cl)) bl)@cl))) \<and> j \<ge> 0 \<longrightarrow> 
      (the (getOneRelatedBlock bl c cl)) \<noteq> (nth (remove1 (the (getOneRelatedBlock bl c cl)) 
      ((remove1 (the (getOneRelatedBlock bl c cl)) bl) @cl)) j)"      
        using Unique_k 2(2) by (metis Unique_remove nth_mem remove1_append remove1_idem)
      have tmp2: "(remove1 (the (getOneRelatedBlock bl c cl)) bl)@cl = 
            (remove1 (the (getOneRelatedBlock bl c cl)) (bl@cl))"
        using getOneRelatedBlockSubset by (metis "3" nat_less_le remove1_append remove1_idem)
      show ?thesis using tmp1 tmp2 Unique_remove getOneRelatedBlockSubset Unique_add2
        by (metis "2.prems" Unique_k append.assoc remove1_idem)
    qed
    have 5: "Unique (getRelatedBlocks (remove1 (the (getOneRelatedBlock bl c cl)) bl) c
           (cl @ [the (getOneRelatedBlock bl c cl)]))"
      using 2 3 4 by blast
    then show ?thesis using getRelatedBlocks.simps[of bl c cl] 5 False by presburger
  qed
qed


(*outputs_sorted block list; Integ blocks, Integ outputs vars return the blocks after combination*)
fun combination :: "ConBlk list \<Rightarrow> ConBlk list \<Rightarrow> ConBlk list" where
  "combination bl [] = []" |
  "combination bl (c#cl) = ((combineBlocks (getRelatedBlocks bl c []) c)#
  combination (remove1 c bl) cl)"

lemma combinationEq : "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow>
\<forall>b \<in> set bl. (set (get_offsets b) = {1}) \<longrightarrow> set (get_outputs b) \<subseteq> Outputs cl \<Longrightarrow>
\<forall>c \<in> set cl. (set (get_offsets c) = {1}) \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow>
Outputs (combination bl cl) = Outputs cl"
proof(induction cl arbitrary: bl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  have 1: "Outputs (findIntegBlks (getRelatedBlocks bl c [])) \<subseteq> Outputs (c#cl)"
  proof -
    have tmp1: "Outputs (findIntegBlks bl) \<subseteq> Outputs (c#cl)"
    using Cons(4) proof(induction bl)
      case Nil
      then show ?case by simp
    next
      case (Cons b bl)
      then show ?case
      proof(cases "set (get_offsets b) = {1}")
        case True
        then show ?thesis using Cons unfolding findIntegBlks.simps
          using Cons.IH by auto
      next
        case False
        then show ?thesis unfolding findIntegBlks.simps using Cons by auto
      qed
    qed
    have tmp2: "Outputs (findIntegBlks (c#cl)) \<subseteq> Outputs (c#cl)"
      using findIntegBlksSubset by auto
    show ?thesis using getRelatedBlocksSubset2 tmp1 tmp2 by (metis empty_set 
          findIntegBlksSubset2 subset_eq sup_bot.right_neutral)
  qed
  have 2: "Outputs (combination (remove1 c bl) cl) = Outputs cl"
  proof -
    have tmp1: "c \<in> set bl"
      using Cons(6) by auto
    have tmp2: "wf2 (remove1 c bl)"
      using Cons(2) wf2_remove by (metis remove1_idem)
    have tmp3: "\<forall>b\<in>set (remove1 c bl). set (get_offsets b) = {1} \<longrightarrow> 
      set (get_outputs b) \<inter> (set (get_outputs c)) = {}"
      using Cons(2,3) tmp1 unfolding wf2_def Unique_def Graph_def by (metis wf2_def 
          Cons.prems(1) Unique_k in_set_conv_nth linorder_not_le not_less0 notin_set_remove1)
    have tmp4: "\<forall>b\<in>set (remove1 c bl). set (get_offsets b) = {1} \<longrightarrow> 
      set (get_outputs b) \<subseteq> Outputs cl"
      using Cons(2,4) tmp1 by (smt (verit) Outputs.simps(2) Un_iff disjoint_iff_not_equal 
          in_mono notin_set_remove1 subsetI tmp3)
    have tmp5: "\<forall>c\<in>set cl. set (get_offsets c) = {1}"
      using Cons(5) by auto
    have tmp6: "set cl \<subseteq> set (remove1 c bl)"
      using Cons(3,5) unfolding wf2_def Unique_def Graph_def by (smt (verit, ccfv_threshold) 
          wf2_def Cons.prems(2) Cons.prems(5) Set.set_insert Unique_k in_set_conv_nth 
          in_set_remove1 insert_subset less_nat_zero_code linorder_not_le remove_hd set_subset_Cons subsetI)
    show ?thesis using Cons(1,3) tmp4 tmp2 tmp5 tmp6 using wf2_lemma by presburger
  qed
  have 3: "set (get_outputs (combineBlocks (getRelatedBlocks bl c []) c)) 
      = Outputs (c # findIntegBlks (getRelatedBlocks bl c []))"
  proof -
    have tmp1: "\<forall>b\<in>set (getRelatedBlocks bl c []). 
    set (get_offsets b) = {0} \<or> set (get_offsets b) = {1} \<or> set (get_offsets b) = {}"
      using Cons(2) unfolding wf2_def Available'_def using getRelatedBlocksSubset2
      by (metis empty_set in_mono sup_bot.right_neutral)
    have tmp2: "wf2 (getRelatedBlocks bl c [])"
    proof -
      have tmp1: "Unique (getRelatedBlocks bl c [])"
        using getRelatedBlocksUnique Cons(2) unfolding wf2_def by simp
      show ?thesis using getRelatedBlocksSubset2 tmp1 Cons(2) unfolding wf2_def
        by (smt (verit) Graph_def empty_set subset_code(1) sup_bot.right_neutral)
    qed
    show ?thesis using combineBlocksSubset4 getRelatedBlocksSubset2 tmp2 Cons(2) Cons(2) 
      unfolding wf2_def Available'_def by (metis combineBlocksSubset4 tmp2)
  qed
  then show ?case unfolding combination.simps using 3 by (smt (verit, best) "1" "2" Outputs.simps(2) Outputs_base2 Un_assoc le_iff_sup list.set_intros(1) remove_hd)
qed

lemma combinationOffsetsEq : "
\<forall>c \<in> set cl. (set (get_offsets c) = {1}) \<Longrightarrow> 
\<forall>c \<in> set (combination bl cl). (set (get_offsets c) = {1})"
proof(induction cl arbitrary: bl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  then show ?case unfolding combination.simps using combineBlocksOffsetEq 
    by (metis list.set_intros(1) list.set_intros(2) set_ConsD)
qed

lemma combinationEq2 : "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow> \<forall>c \<in> set (combination bl cl).
length (get_outputs c) = length (get_offsets c) \<and> length (get_offsets c) = length (get_outupd c)"
proof(induction cl arbitrary: bl)
  case Nil
  then show ?case by simp
next
  case (Cons a cl)
  have 1: "wf2 (remove1 a bl)"
    using Cons(2) wf2_remove by (metis remove1_idem)
  have 2: "wf2 cl"
    using Cons(3) wf2_lemma by simp
  have 3: "set cl \<subseteq> set (remove1 a bl)"
    using Cons(2,3,4) unfolding wf2_def Unique_def by (metis wf2_def Cons.prems(2) Unique_k 
        in_set_conv_nth in_set_remove1 less_nat_zero_code linorder_not_less remove_hd 
        set_subset_Cons subset_code(1))
  have 4: "\<forall>c\<in>set (combination (remove1 a bl) cl).
       length (get_outputs c) = length (get_offsets c) \<and>
       length (get_offsets c) = length (get_outupd c)"
    using Cons(1) 1 2 3 by presburger
  have 5: "\<forall>b\<in>set (a#bl).
       length (get_offsets b) = length (get_outputs b) \<and>
       length (get_offsets b) = length (get_outupd b)"
    using Cons(2,3,4) unfolding wf2_def Available'_def
    by (metis list.set_intros(1) set_ConsD)
  then show ?case unfolding combination.simps using combineBlockEq2 4 getRelatedBlocksSubset2 
    by (smt (verit, ccfv_SIG) empty_set empty_subsetI le_supI list.set_intros(1) set_ConsD 
        set_subset_Cons subset_eq)
qed

text\<open>Combine all block list; used for combine all Integrator blocks\<close>
fun Combine :: "ConBlk list \<Rightarrow> ConBlk" where
  "Combine [] = (Block [] [] [] 0 [])" |
  "Combine (b#bl) = combineBlocks bl b"
                             
lemma CombineSubset : "set (get_outputs (Combine bl)) \<subseteq> Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding Combine.simps using combineBlocksSubset by auto
qed

lemma CombineEq : "\<forall>b \<in> set bl. (set (get_offsets b) = {1}) \<and> length (get_offsets b) 
= length (get_outputs b) \<and> length (get_offsets b) = length (get_outupd b) \<Longrightarrow>
set (get_outputs (Combine bl)) = Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding Combine.simps using combineBlocksEq by auto
qed

text \<open>sorted by outputs; get the smallest block\<close>
fun get_first_block :: "ConBlk list \<Rightarrow> ConBlk" where
  "get_first_block [] = undefined" |
  "get_first_block [b] = b" |
  "get_first_block (b#bl) = (if (integer_of_char (hd (get_outputs (get_first_block bl))) \<ge> 
  integer_of_char (hd (get_outputs b))) then b else (get_first_block bl))"

lemma get_first_block_in : "get_first_block (a # cl) \<in> set (a#cl)"
proof(induction cl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  then show ?case unfolding get_first_block.simps using Cons by (smt (verit, ccfv_SIG) 
  getCalBlks.cases get_first_block.simps(2) get_first_block.simps(3) 
  insert_iff list.simps(15))
qed

lemma get_first_block_add: "get_first_block (b#bl) = b \<Longrightarrow>
(integer_of_char (hd (get_outputs c)) \<ge> integer_of_char (hd (get_outputs b))) \<Longrightarrow>
get_first_block (b#c#bl) = b"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "(integer_of_char (hd (get_outputs (get_first_block (a#bl)))) \<ge> 
  integer_of_char (hd (get_outputs b)))"
    using Cons(2) unfolding get_first_block.simps by (metis nle_le)
  then show ?case using Cons(3) unfolding get_first_block.simps by presburger
qed

lemma get_first_block_noteq: "get_first_block (b#bl) \<noteq> b \<Longrightarrow>
(integer_of_char (hd (get_outputs c)) > integer_of_char (hd (get_outputs (get_first_block bl)))) \<Longrightarrow>
get_first_block (b#c#bl) = get_first_block bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case  unfolding get_first_block.simps 
    by (smt (verit, best) linorder_not_less)
qed

lemma get_first_block_reomve1: "get_first_block (b#c#bl) = b \<Longrightarrow>
get_first_block (b#bl) = b"
  subgoal premises pre
proof(cases "bl = []")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis using pre unfolding get_first_block.simps
    by (smt (verit, ccfv_threshold) dual_order.trans get_first_block.simps(3) list.exhaust)
  qed
  done

lemma get_first_block_reomve2: "get_first_block (b#bl) = b \<Longrightarrow>
get_first_block (b#(remove1 c bl)) = b"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "get_first_block (b # remove1 c bl) = b"
    using Cons get_first_block_reomve1 by blast
  have 2: "(integer_of_char (hd (get_outputs a)) \<ge> integer_of_char (hd (get_outputs b)))"
    using Cons(2) unfolding get_first_block.simps
    by (metis get_first_block.simps(3) get_first_block_reomve1 nle_le)
  then show ?case
  proof(cases "c = a")
    case True
    then show ?thesis using Cons by (metis get_first_block_reomve1 remove_hd)
  next
    case False
    have 3: "get_first_block (b # remove1 c (a # bl)) = get_first_block (b # a # remove1 c bl)"
      using False by auto
    then show ?thesis using 1 2 get_first_block_add by presburger
  qed
qed


lemma get_first_block_lemma : "get_first_block (b#bl) = b \<Longrightarrow> \<forall>c \<in> set bl. (integer_of_char 
(hd (get_outputs c)) \<ge> integer_of_char (hd (get_outputs b)))"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case using get_first_block_reomve1 unfolding get_first_block.simps
    by (metis nle_le set_ConsD)
qed

lemma get_first_block_remove3 : "wf2 bl \<Longrightarrow> b \<in> set bl \<Longrightarrow> get_first_block bl =
get_first_block (b#remove1 b bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case
  proof(cases "b = a")
    case True
    then show ?thesis by auto
  next
    case False
    note F1 = False
    have 0 : "wf2 bl"
      using Cons(2) wf2_lemma by simp
    have 1: "get_first_block bl = get_first_block (b # remove1 b bl)"
      using False Cons 0 by simp
    have 2: "bl = hd bl # tl bl"
      using Cons(3) False by (metis hd_Cons_tl in_set_member member_rec(2) set_ConsD)
    have 3: "b \<in> set bl"
      using False Cons by simp
    then show ?thesis
    proof(cases "get_first_block (a # bl) = a")
      case True
      have tmp1: "integer_of_char (hd (get_outputs b))
        \<ge> integer_of_char (hd (get_outputs a))"
        using True get_first_block.simps(3)[of a "hd bl" "tl bl"] get_first_block_lemma 
        3 by presburger
      have tmp2: "get_first_block (b # remove1 b (a # bl)) = get_first_block (b # a # remove1 b bl)"
        using F1 by auto
      have tmp3: "get_first_block (a # remove1 b bl) = a"
        using True get_first_block_reomve2 by presburger
      have tmp4: "set (get_outputs b) \<inter> set (get_outputs a) = {}"
        using Cons(2,3) unfolding wf2_def Graph_def by (metis False True get_first_block_in)
      have tmp5: "(get_outputs b) \<noteq> [] \<and> (get_outputs a) \<noteq> []"
        using Cons(2,3) unfolding wf2_def Available'_def by (metis Graph_def 
            list.set_intros(1) list.size(3) not_gr_zero)
      have tmp6: "hd (get_outputs b) \<noteq> hd (get_outputs a)"
        using tmp4 tmp5 by (simp add: disjoint_iff_not_equal)
      have tmp7: "integer_of_char (hd (get_outputs b))
        \<noteq> integer_of_char (hd (get_outputs a))"
        using tmp6 by (simp add: integer_of_char_def)
      have tmp8: "integer_of_char (hd (get_outputs b))
        > integer_of_char (hd (get_outputs a))"
        using tmp1 tmp7 by simp
      have tmp9: "get_first_block (b # a # remove1 b bl) = a"
        using tmp8 tmp3 unfolding get_first_block.simps by simp
      then show ?thesis using tmp2 tmp9 True by simp
    next
      case False
      note F2 = False
      have tmp1: "get_first_block (a # bl) = get_first_block (b # remove1 b bl)"
        using False 1 2 get_first_block.simps(3)[of a "hd bl" "tl bl"] by presburger
      then show ?thesis
      proof(cases "get_first_block (b # remove1 b bl) = b")
        case True
        then show ?thesis using tmp1 False
          using get_first_block.simps(3) get_first_block_reomve2 by presburger
      next
        case False
        have tmp2: "(integer_of_char (hd (get_outputs a)) > 
          integer_of_char (hd (get_outputs (get_first_block bl))))"
          using F2 2 get_first_block.simps(3)[of a "hd bl" "tl bl"] by (metis linorder_not_le) 
        then show ?thesis using get_first_block_noteq False by (smt (verit, del_insts) 
              get_first_block.elims list.discI list.inject remove1.simps(2) tmp1)
      qed
    qed
  qed
qed

lemma get_first_block_same : "wf2 bl1 \<Longrightarrow> bl1 \<noteq> [] \<Longrightarrow> bl1 <~~> bl2 \<Longrightarrow>
get_first_block bl1 = get_first_block bl2"
proof(induction bl1 arbitrary:bl2)
  case Nil
  then show ?case by simp
next
  case (Cons b1 bl1)
  have 0: "wf2 bl1"
    using Cons(2) wf2_lemma by simp
  then show ?case
  proof(cases "bl1 = []")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    have 1: "bl1 <~~> remove1 b1 bl2"
      using Cons(4) by (metis perm_remove_perm remove_hd)
    have 2: "get_first_block bl1 = get_first_block (remove1 b1 bl2)"
      using Cons(1) 0 1 False by simp
    have 3: "wf2 bl2"
      using wf2_lemma2 Cons(2,4) by auto
    have 4: "get_first_block bl2 = get_first_block (b1#(remove1 b1 bl2))"
      using get_first_block_remove3 3 by (meson Cons.prems(3) list.set_intros(1) prem_seteq)
    then show ?thesis using Cons 2 False unfolding get_first_block.simps
      by (smt (verit, best) "1" get_first_block.elims list.inject perm.Cons perm_sing_eq)
  qed
qed

text \<open>sorted by outputs\<close>
function sort_by_outputs :: "ConBlk list \<Rightarrow> ConBlk list" where
  "sort_by_outputs [] = []" |
  "sort_by_outputs (c#cl) = (let b = get_first_block (c#cl) in 
  b # (sort_by_outputs (remove1 b (c#cl)) ))"
  by pat_completeness auto
termination 
  apply (relation "measures[(\<lambda>(cl::ConBlk list). length cl)]", auto)
  subgoal premises pre for a cl
  proof -
    show ?thesis using get_first_block_in pre using perm_length perm_remove
      by (metis impossible_Cons linorder_not_le set_ConsD)
  qed
  done

lemma sort_by_outputs_Outputs : "Outputs (sort_by_outputs bl) = Outputs bl"
proof(induction bl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "bl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 3: "bl = hd bl # tl bl"
      using False by simp
    have 4: "length (remove1 (get_first_block bl) bl) < length bl"
      using 3 get_first_block_in by (metis length_Cons lessI perm_length perm_remove)
    have 5: "Outputs bl = Outputs ((get_first_block bl)#(remove1 (get_first_block bl) bl))"
      using Outputs_remove 3 get_first_block_in by metis
    have 6: "Outputs (sort_by_outputs bl) = 
    Outputs ((get_first_block bl)#(sort_by_outputs (remove1 (get_first_block bl) bl)))"
      using 3 sort_by_outputs.simps(2)[of "hd bl" "tl bl"] by metis
    have 7: "Outputs (sort_by_outputs (remove1 (get_first_block bl) bl)) 
    = Outputs (remove1 (get_first_block bl) bl)"
      using 4 2 by blast
    then show ?thesis using 5 6 7 by auto
  qed
qed

lemma sort_by_outputs_perm1 : "(sort_by_outputs bl) <~~> bl"
proof(induction bl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "bl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 3: "bl = hd bl # tl bl"
      using False by simp
    have 4: "length (remove1 (get_first_block bl) bl) < length bl"
      using 3 get_first_block_in by (metis length_Cons lessI perm_length perm_remove)
    then show ?thesis by (metis "2" "3" case_prodI get_first_block_in mem_Collect_eq perm_remove2 
          sort_by_outputs.simps(2))
  qed
qed

lemma sort_by_outputs_perm2 : "wf2 bl1 \<Longrightarrow>
bl1 <~~> bl2 \<Longrightarrow> sort_by_outputs bl1 = sort_by_outputs bl2"
proof(induction bl1 arbitrary: bl2 rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def
    using length_induct by auto
next
  case (2 bl1)
  then show ?case
  proof(cases "bl1 = []")
    case True
    then show ?thesis using "2.prems" by blast
  next
    case False
    have 3: "bl1 = hd bl1 # tl bl1"
      using False by simp
    have 4: "bl2 = hd bl2 # tl bl2"
      using False 2(3) using list.exhaust_sel by blast
    have tmp1: "get_first_block bl1 = get_first_block bl2"
      using 3 4 2(2,3) False get_first_block_same by presburger
    have tmp2: "remove1 (get_first_block bl1) bl1 <~~> remove1 (get_first_block bl2) bl2"
      using tmp1 2(3) by (simp add: perm_remove_perm)
    have tmp3: "wf2 (remove1 (get_first_block bl1) bl1)"
      using 2(2) get_first_block_in wf2_remove by (metis remove1_idem)
    have tmp4: "length (remove1 (get_first_block bl1) bl1) < length bl1"
      using get_first_block_in by (metis "3" length_Cons lessI perm_length perm_remove)
    then show ?thesis using 2 tmp2 tmp3 tmp4
      by (metis "3" "4" case_prod_conv mem_Collect_eq sort_by_outputs.simps(2) tmp1)
  qed
qed


(*all continuousBlocks; Integ blocks, return the combined block after combination*)
fun updateIntegBlks :: "ConBlk list \<Rightarrow> ConBlk list \<Rightarrow> ConBlk" where
  "updateIntegBlks bl cl = Combine (combination (sort_by_outputs bl) (sort_by_outputs cl))"

lemma updateIntegBlksSubset : "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow>
\<forall>b \<in> set bl. (set (get_offsets b) = {1}) \<longrightarrow> set (get_outputs b) \<subseteq> Outputs cl \<Longrightarrow>
\<forall>c \<in> set cl. (set (get_offsets c) = {1}) \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow>
set (get_outputs (updateIntegBlks bl cl)) \<subseteq> Outputs cl"
  subgoal premises pre
proof -
  have 1: "wf2 (sort_by_outputs bl)"
    using pre(1) sort_by_outputs_perm1 wf2_lemma2 by (meson perm_sym)
  have 2: "wf2 (sort_by_outputs cl)"
    using pre(2) sort_by_outputs_perm1 wf2_lemma2 by (meson perm_sym)
  then show ?thesis unfolding updateIntegBlks.simps using sort_by_outputs_Outputs
combinationEq[of "sort_by_outputs bl" "sort_by_outputs cl" ] CombineSubset by (smt (verit, best) 
    "1" perm_sym pre(3) pre(4) pre(5) prem_seteq sort_by_outputs_perm1 subset_eq)
qed
  done

\<comment> \<open>Combination doesn't add or delete the outputs\<close>
lemma updateIntegBlksSubset2 : "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow>
\<forall>b \<in> set bl. (set (get_offsets b) = {1}) \<longrightarrow> set (get_outputs b) \<subseteq> Outputs cl \<Longrightarrow>
\<forall>c \<in> set cl. (set (get_offsets c) = {1}) \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow>
set (get_outputs (updateIntegBlks bl cl)) = Outputs cl"
  subgoal premises pre
proof -
  have 1: "wf2 (sort_by_outputs bl)"
    using pre(1) sort_by_outputs_perm1 wf2_lemma2 by (meson perm_sym)
  have 2: "wf2 (sort_by_outputs cl)"
    using pre(2) sort_by_outputs_perm1 wf2_lemma2 by (meson perm_sym)
  have 3: "\<forall>b\<in>set (sort_by_outputs bl).
       set (get_offsets b) = {1} \<longrightarrow> set (get_outputs b) \<subseteq> Outputs (sort_by_outputs cl)"
    using pre(3) by (metis prem_seteq sort_by_outputs_Outputs sort_by_outputs_perm1)
  have 4: "\<forall>c\<in>set (sort_by_outputs cl). set (get_offsets c) = {1}"
    using pre(4) by (meson prem_seteq sort_by_outputs_perm1)
  have 5: "set (sort_by_outputs cl) \<subseteq> set (sort_by_outputs bl)"
    using pre(5) by (meson in_mono perm_sym prem_seteq sort_by_outputs_perm1 subsetI)
  have 6: "\<forall>b\<in>set (combination (sort_by_outputs bl) (sort_by_outputs cl)). 
    set (get_offsets b) = {1}"
    using combinationOffsetsEq 4 by blast
  have 7: "\<forall>b\<in>set (combination (sort_by_outputs bl) (sort_by_outputs cl)).
       set (get_offsets b) = {1} \<and>
       length (get_offsets b) = length (get_outputs b) \<and>
       length (get_offsets b) = length (get_outupd b)"
    using 6 pre(1) combinationEq2 1 2 5 by presburger
  then show ?thesis unfolding updateIntegBlks.simps using sort_by_outputs_Outputs
combinationEq[of "sort_by_outputs bl" "sort_by_outputs cl" ] CombineEq 1 2 3 4 5 6 7 by presburger
qed
  done

lemma updateIntegBlksPerm : "wf2 bl1 \<Longrightarrow> wf2 cl1 \<Longrightarrow> bl1 <~~> bl2 \<Longrightarrow> cl1 <~~> cl2 \<Longrightarrow>
updateIntegBlks bl1 cl1 = updateIntegBlks bl2 cl2"
  unfolding updateIntegBlks.simps using sort_by_outputs_perm2 by presburger


text \<open>Before calculation, we get the min time step based on the discrete 
blocks(greatest common divisor)\<close>
fun commonDivisor:: "int \<Rightarrow> DisBlk list \<Rightarrow> int" where
  "commonDivisor x [] = x" |
  "commonDivisor x (a#al) = commonDivisor (gcd x (get_sample_time a)) al"
fun getTimeStep:: "DisBlk list \<Rightarrow> int" where
  "getTimeStep [] = 1" | 
  "getTimeStep (a#al) = commonDivisor (get_sample_time a) al"

value "getTimeStep [Block ''za'' ''a'' [1] 12 [(\<lambda>s.(if length s = 2 then (s ! 0) + (s ! 1) else 0))]
, Block ''za'' ''a'' [1] 18 [(\<lambda>s.(if length s = 2 then (s ! 0) + (s ! 1) else 0))],
Block ''za'' ''a'' [1] 30 [(\<lambda>s.(if length s = 2 then (s ! 0) + (s ! 1) else 0))]]"

text \<open>State\<close>
type_synonym state = "var \<Rightarrow> real"

text \<open>Expressions\<close>
type_synonym exp = "state \<Rightarrow> real"

definition zeroExp :: "exp" where "zeroExp = (\<lambda>s.0)"

text \<open>States as a vector\<close>
type_synonym vec = "real^(var)"

text \<open>Conversion between state and vector\<close>
definition state2vec :: "state \<Rightarrow> vec" where
  "state2vec s = (\<chi> x. s x)"

definition vec2state :: "vec \<Rightarrow> state" where
  "(vec2state v) x = v $ x"

lemma transform_eq1: "s1 = s2 \<Longrightarrow> state2vec s1 = state2vec s2"
  by simp

lemma transform_eq2: "v1 = v2 \<Longrightarrow> vec2state v1 = vec2state v2"
  by simp

subsection \<open>Definition of ODEs\<close>

type_synonym ODE = "var \<Rightarrow> exp"

(*time; values; derivatives*)
type_synonym ODE' = "real \<Rightarrow> vec \<Rightarrow> vec"

lemma vec_state_map1[simp]: "vec2state (state2vec s) = s"
  unfolding vec2state_def state2vec_def by auto

lemma vec_state_map2[simp]: "state2vec (vec2state s) = s"
  unfolding vec2state_def state2vec_def by auto

lemma vec_eq: "\<forall>x. (v1::vec) $ x = v2 $ x \<Longrightarrow> v1 = v2"
  subgoal premises pre
proof -
  have 1: "\<forall>x. (vec2state v1) x = (vec2state v2) x"
    unfolding vec2state_def using pre by simp
  have 2: "(vec2state v1) = (vec2state v2)"
    using 1 by blast
  show ?thesis using 2 transform_eq1 vec_state_map2 by metis
qed
  done

text \<open>transformation between timed_vars and state\<close>
definition timedVar2timedState :: "timed_vars \<Rightarrow> (real \<Rightarrow> state)" where
  "timedVar2timedState h = (\<lambda>t. (\<lambda>v. (h v t)))"
                                                                  
definition timedVar2State :: "timed_vars \<Rightarrow> real \<Rightarrow> state" where
  "timedVar2State h t = (\<lambda>v. h v t)"

definition timedState2timedVar :: "(real \<Rightarrow> state) \<Rightarrow> timed_vars" where
  "timedState2timedVar p = (\<lambda>v. (\<lambda>t. p t v))"

lemma timedVar_state_map1[simp]: "timedState2timedVar (timedVar2timedState h) = h"
  unfolding timedVar2timedState_def timedState2timedVar_def by simp

lemma timedVar_state_map2[simp]: "timedVar2timedState (timedState2timedVar p) = p"
  unfolding timedVar2timedState_def timedState2timedVar_def by simp


fun exp2ODE :: "var list \<Rightarrow> exp list \<Rightarrow> ODE" where
  "exp2ODE [] Exps s = zeroExp" |
  "exp2ODE xs [] s = zeroExp" |
  "exp2ODE (x#xs) (Exp#Exps) s =(if x = s then Exp else (exp2ODE xs Exps s))"

text \<open>transformation between outupd and expression\<close>
definition outupd2exp :: "outupd \<Rightarrow> var list \<Rightarrow> exp" where
  "outupd2exp f il = (\<lambda>s. (f (map (\<lambda> a. s a) il)) )"

lemma ToExpEq : "\<forall>s. (f1 (map (\<lambda> a. s a) il1)) = (f2 (map (\<lambda> a. s a) il2))
\<Longrightarrow> outupd2exp f1 il1 = outupd2exp f2 il2"
  unfolding outupd2exp_def by simp

value "integer_of_char CHR ''a'' < integer_of_char CHR ''b''"

definition exp2outupd :: "exp \<Rightarrow> var list \<Rightarrow> outupd" where
  "exp2outupd Exp il = undefined"

(*outupd list to expression list*)
fun getExps :: "outupd list \<Rightarrow> var list \<Rightarrow> exp list" where
  "getExps [] il = []" |
  "getExps (f#fl) il = outupd2exp f il # (getExps fl il)"

lemma getExpsPerm : "\<forall>i. i \<ge> 0 \<and> i < length fl1 \<longrightarrow> (\<forall>s. ((fl1 ! i) (map (\<lambda> a. s a) il1)) = 
((fl2 ! i) (map (\<lambda> a. s a) il2))) \<Longrightarrow> length fl1 = length fl2
\<Longrightarrow> getExps fl1 il1 = getExps fl2 il2"
proof(induction fl1 arbitrary:fl2)
  case Nil
  then show ?case by simp
next
  case (Cons f1 fl1)
  have 1: "fl2 = hd fl2 # tl fl2"
    using Cons(3) by (metis length_0_conv list.exhaust_sel neq_Nil_conv)
  have 2: "outupd2exp f1 il1 = outupd2exp (hd fl2) il2"
    using Cons(2) by (metis "1" ToExpEq length_Cons nth_Cons_0 of_nat_0 of_nat_0_le_iff zero_less_Suc)
  have 3: "getExps fl1 il1 = getExps (tl fl2) il2"
    using Cons 1 by (metis (no_types, lifting) Suc_mono length_Cons length_tl linorder_le_cases 
        list.sel(3) not_less_eq_eq nth_tl)
  then show ?case using 1 2 3 getExps.simps(2)[of "hd fl2" "tl fl2" il2] unfolding getExps.simps 
    using \<open>getExps (hd fl2 # tl fl2) il2 = outupd2exp (hd fl2) il2 # getExps (tl fl2) il2\<close> by presburger
qed


fun ODE2vec :: "ODE \<Rightarrow> var list \<Rightarrow> (vec \<Rightarrow> vec)" where
  "ODE2vec ode vl v1 = state2vec (\<lambda>x.(ode x (vec2state v1)))"

fun realvec2realstate :: "(real \<Rightarrow> vec) \<Rightarrow> (real \<Rightarrow> state)" where
  "realvec2realstate p t = vec2state (p t)"

fun realstate2realvec :: "(real \<Rightarrow> state) \<Rightarrow> (real \<Rightarrow> vec)" where
  "realstate2realvec p t = state2vec (p t)"

lemma timedVar_state_map3[simp]: "timedState2timedVar (realvec2realstate
(realstate2realvec (timedVar2timedState h))) = h"
  unfolding timedVar2timedState_def timedState2timedVar_def by simp

lemma timedVar_state_map4[simp]: "(realstate2realvec (timedVar2timedState
          (timedState2timedVar (realvec2realstate p)))) = p"
  unfolding timedVar2timedState_def timedState2timedVar_def realstate2realvec.simps by simp

lemma trans_eq3: "\<forall>x t. (h1::timed_vars) x t = h2 x t \<longrightarrow> 
(realstate2realvec (timedVar2timedState h1)) t $ x =
  (realstate2realvec (timedVar2timedState h2)) t $ x"
  unfolding realstate2realvec.simps timedVar2timedState_def
  using state2vec_def by force

lemma trans_eq4: "\<forall>x t. (h1::timed_vars) x t = v2 t $ x \<longrightarrow> 
(realstate2realvec (timedVar2timedState h1)) t $ x = v2 t $ x"
  unfolding realstate2realvec.simps timedVar2timedState_def
  using state2vec_def by force

lemma trans_eq5: "(realstate2realvec (timedVar2timedState h)) t = 
  state2vec (\<lambda>v. h v t)"
  unfolding realstate2realvec.simps timedVar2timedState_def
  using timedVar2State_def by force

(*update h for the outputs and time interval (t0, t0+t]*)
fun updTimedVar :: "(real \<Rightarrow> vec) \<Rightarrow> var list \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> timed_vars" where
  "updTimedVar p vl h t0 t v tt =(if v \<in> set vl \<and> (tt > t0 \<and> tt \<le> t0+t) 
    then (p tt $ v) else h v tt)"

lemma updTimedVar_eq1 : "\<forall> v tt. v  \<notin> set vl \<or> (tt \<le> t0 \<or> tt > t0 + t) \<longrightarrow> 
      updTimedVar p vl h t0 t v tt = h v tt"
  unfolding updTimedVar.simps by simp

lemma updTimedVar_eq2 : "\<forall> v tt. v  \<in> set vl \<and> (tt > t0 \<and> tt \<le> t0 + t) \<longrightarrow> 
      updTimedVar p vl h t0 t v tt = (p tt $ v)"
  unfolding updTimedVar.simps by simp

lemma updTimedVar_eq3: "updTimedVar p vl h t0 t = (\<lambda>vv tt. (if vv \<in> set vl \<and> (tt > t0 \<and> tt \<le> t0 + t)
  then (p tt $ vv) else h vv tt))"
  using updTimedVar_eq1 updTimedVar_eq2 by fastforce



text \<open>give a block including ODE, return a function(real => ODE => ODE)
) required by the definition of "fixed_point"\<close>
fun block2ODE :: "block \<Rightarrow> ODE'" where
  "block2ODE (Block il vl ol st fl) t v1 = ODE2vec (exp2ODE vl (getExps fl il)) vl v1"

end