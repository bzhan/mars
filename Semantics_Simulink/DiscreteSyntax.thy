theory DiscreteSyntax
  imports Complex_Main
         Permutation
         Ordinary_Differential_Equations.Flow
begin
(*Ordinary_Differential_Equations.Flow*)

subsection \<open>Syntax\<close>

type_synonym sample_time = int
type_synonym var = char 
type_synonym offset = nat
type_synonym outupd = "real list \<Rightarrow> real"

\<comment> \<open>input vars, output vars, input time offsets, sample time, output functions\<close>
datatype block = Block "var list" "var list" "offset list" "sample_time"
         "outupd list" 
(*offset is a para to get pre value, e.g. y(kn) = s((k-1)n).
  we assume each output corresponds to a same offset for all inputs*)



fun get_inputs :: "block \<Rightarrow> var list" where
  "get_inputs (Block a _ _ _ _) = a"

fun get_outputs :: "block \<Rightarrow> var list" where
  "get_outputs (Block _ c _ _ _) = c"

fun get_sample_time :: "block \<Rightarrow> sample_time" where
  "get_sample_time (Block _ _ _ c _) = c"

fun get_offsets :: "block \<Rightarrow> offset list" where 
  "get_offsets (Block _ _ c _ _) = c"

fun get_outupd :: "block \<Rightarrow> outupd list" where
  "get_outupd (Block _ _ _ _ d) = d"


definition "Available b = ((length (get_offsets b)) = (length (get_outputs b))
    \<and> ((length (get_outputs b)) = (length (get_outupd b)))
    \<and> (\<forall>i j. i < j \<and> j < (length (get_outputs b)) \<and> j \<ge> 0 
  \<longrightarrow> (nth (get_outputs b) i) \<noteq> (nth (get_outputs b) j)) \<and> ((\<forall>i. i \<ge> 0 \<and> i < (length (get_offsets b))
  \<longrightarrow>  ((nth (get_offsets b) i) \<ge> 0)) \<and> 
  (set (get_outputs b) \<inter> set (get_inputs b) = {}) \<and> (get_sample_time b \<ge>  0)))"

definition "Unique bl = (\<forall>i j. i < j \<and> j < (length bl) \<and> i \<ge> 0 \<longrightarrow> (nth bl i) \<noteq> (nth bl j))"

definition "Unique' bl = distinct bl"

lemma Unique'_eq: "Unique bl \<Longrightarrow> Unique' bl"
  unfolding Unique_def Unique'_def
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case unfolding distinct.simps
    by (metis Suc_less_eq bot_nat_0.extremum in_set_conv_nth 
        length_Cons nth_Cons_0 nth_Cons_Suc zero_less_Suc)
qed

lemma Unique_eq: "Unique' bl \<Longrightarrow> Unique bl"
  unfolding Unique_def Unique'_def
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case unfolding distinct.simps
    by (metis Cons.prems index_first index_nth_id)
qed

lemma Unique_lemma: "Unique (a#bl) \<Longrightarrow> Unique bl"
  unfolding Unique_def
  by (metis Suc_less_eq bot_nat_0.extremum length_Cons nth_Cons_Suc)

lemma Unique_lemma2: "Unique (bl@[a]) \<Longrightarrow> Unique bl"
  unfolding Unique_def
  by (smt (verit, del_insts) Suc_lessD length_append_singleton lessI less_trans_Suc nth_append)

lemma Unique_remove: "a \<in> set bl \<Longrightarrow> Unique bl \<Longrightarrow> Unique (remove1 a bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case
  proof(cases "a = b")
    case True
    then show ?thesis using Cons(3) Unique_lemma by auto
  next
    case False
    have 1: "Unique (remove1 a bl)"
      using Cons False Unique_lemma by fastforce
    have 2: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> b \<noteq> (nth bl j)"
      using Cons(3) unfolding Unique_def
      by (metis Suc_less_eq bot_nat_0.extremum length_Cons nth_Cons_0 nth_Cons_Suc zero_less_Suc)
    have 3: "\<forall>j. j < (length (remove1 a bl)) \<and> j \<ge> 0 \<longrightarrow> b \<noteq> (nth (remove1 a bl) j)"
      using 2 
      by (metis in_set_conv_nth le0 notin_set_remove1)
    have 4: "remove1 a (b # bl) = b#(remove1 a bl)"
      using False by auto
    have 5: "Unique (b#(remove1 a bl))"
      using 1 3 by (smt (verit, best) Suc_leI Unique_def add_diff_cancel_left' 
          bot_nat_0.extremum le_0_eq le_imp_less_Suc length_Cons less_Suc_eq 
          less_Suc_eq_0_disj nth_Cons' plus_1_eq_Suc)
    then show ?thesis using 4 by auto
  qed
qed

lemma Unique_add: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> b \<noteq> (nth bl j) \<Longrightarrow>
  Unique bl \<Longrightarrow> Unique (b#bl)"
  by (smt (verit, best) Suc_leI Unique_def add_diff_cancel_left' 
          bot_nat_0.extremum le_0_eq le_imp_less_Suc length_Cons less_Suc_eq 
          less_Suc_eq_0_disj nth_Cons' plus_1_eq_Suc)

lemma Unique_add2: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> b \<noteq> (nth bl j) \<Longrightarrow>
  Unique bl \<Longrightarrow> Unique (bl@[b])"
  by (smt (verit, ccfv_threshold) Suc_less_eq Unique_def length_append_singleton 
      less_Suc_eq less_trans_Suc nth_append nth_append_length)

lemma Unique_Cons: "Unique (al@bl) \<Longrightarrow> Unique bl"
proof(induction al)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  then show ?case using Unique_lemma by force
qed

lemma Unique_rev: "Unique bl \<Longrightarrow> Unique (rev bl)"
  unfolding Unique_def using rev_nth apply simp
  by (smt (verit, ccfv_SIG) Suc_lessD diff_less_mono2 less_imp_diff_less 
      less_trans_Suc not_less_eq rev_nth)

lemma Unique_Cons2: "Unique (al@bl) \<Longrightarrow> Unique al"
  subgoal premises pre
proof -
  have 1: "rev (al@bl) = rev bl @ rev al"
    by auto
  have 2: "Unique (rev al)"
    using Unique_rev Unique_Cons 1 pre by fastforce
  then show ?thesis using Unique_rev by force
qed
  done

lemma Unique_k : "b \<in> set bl \<Longrightarrow> Unique bl \<Longrightarrow> 
\<forall>j. j < (length (remove1 b bl)) \<and> j \<ge> 0 \<longrightarrow> b \<noteq> (nth (remove1 b bl) j)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case
  proof(cases "b = a")
    case True
    then show ?thesis apply simp using Cons(3) unfolding Unique_def
      by (metis Suc_less_eq bot_nat_0.extremum length_Cons nth_Cons_0 nth_Cons_Suc zero_less_Suc)
  next
    case False
    have 1: "\<forall>j. j < length (remove1 b bl) \<and> 0 \<le> j \<longrightarrow> b \<noteq> remove1 b bl ! j"
      using Cons False Unique_lemma by (metis set_ConsD)
    then show ?thesis using False
      by (metis bot_nat_0.extremum in_set_conv_nth remove1.simps(2) set_ConsD)
  qed
qed

lemma Unique_perm: "Unique bl \<Longrightarrow> bl <~~> cl \<Longrightarrow> Unique cl"
proof(induction cl arbitrary: bl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  have 1: "Unique cl"
  proof -
    have tmp1: "Unique (remove1 c bl)"
      using Cons by (metis Unique_remove remove1_idem)
    show ?thesis using Cons tmp1 by (metis perm_remove_perm remove_hd)
  qed
  have 2: "\<forall>j. j < (length (remove1 c bl)) \<and> j \<ge> 0 \<longrightarrow> c \<noteq> (nth (remove1 c bl) j)"
    using Unique_k Cons(2,3) by (metis notin_set_remove1 nth_mem)
  have 3: "c \<notin> set cl"
    using Cons(2,3) 1 by (meson Unique'_def Unique'_eq distinct.simps(2) distinct_perm)
  have 4: "\<forall>j. j < (length cl) \<and> j \<ge> 0 \<longrightarrow> c \<noteq> (nth cl j)"
    using 3 by force
  then show ?case using 1 Unique_add by metis
qed


definition "wf0 bl = (Unique bl \<and> (\<forall>b \<in> set bl. Available b))"

lemma wf0_lemma: "wf0 (a#bl) \<Longrightarrow> wf0 bl"
  unfolding wf0_def using Unique_lemma by auto

lemma wf0_Permutation: "bl <~~> bl' \<Longrightarrow> wf0 bl \<Longrightarrow> wf0 bl'"
proof(induction bl arbitrary:bl')
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "bl <~~> remove1 a bl'"
    using Cons(2) perm_remove_perm by (metis remove_hd)
  have 2: "wf0 (remove1 a bl')"
    using 1 Cons wf0_lemma by presburger
  have 3: "a \<notin> set (remove1 a bl')"
    using Cons(2,3) unfolding wf0_def Unique_def apply simp
    by (metis "1" One_nat_def Suc_eq_plus1 Suc_less_eq add_diff_cancel_right' 
        in_set_conv_nth nth_Cons_0 perm_sym prem_seteq zero_less_Suc)
  have 4: "Available a"
    using Cons(3) unfolding wf0_def by simp
  have 5: "\<forall>i. i < length (remove1 a bl') \<and> 0 \<le> i \<longrightarrow> remove1 a bl' ! i \<noteq> a"
    using 3 by (metis nth_mem)
  have 6: "(\<forall>i j. i < j \<and> j < length bl' \<and> 0 \<le> i \<longrightarrow> bl' ! i \<noteq> bl' ! j)"
    using 5 2 apply simp
  proof(induction bl')
    case Nil
    then show ?case by simp
  next
    case (Cons b bl')
    then show ?case
    proof(cases "a = b")
      case True
      have tmp1: "\<forall>i j. i < j \<and> j < length bl' \<longrightarrow> bl' ! i \<noteq> bl' ! j"
        using Cons True by (simp add: wf0_def Unique_def)
      then show ?thesis using Cons(2) True
        using length_Cons less_Suc_eq_0_disj less_nat_zero_code by fastforce
    next
      case False
      have tmp1: "remove1 a (b # bl') = b#(remove1 a bl')"
        using False by simp
      have tmp2: "wf0 (remove1 a bl')"
        using Cons(3) tmp1 by (metis wf0_lemma)
      have tmp3: "\<forall>i<length (remove1 a bl'). remove1 a bl' ! i \<noteq> a"
        using Cons(2) tmp1 by auto
      have tmp4: "\<forall>i j. i < j \<and> j < length bl' \<longrightarrow> bl' ! i \<noteq> bl' ! j"
        using tmp2 tmp3 Cons(1) by simp
      have tmp5: "\<forall>i<length (remove1 a bl'). remove1 a bl' ! i \<noteq>  b"
        using Cons(3) tmp1 
        by (metis wf0_def Suc_leI Unique_def add_diff_cancel_left' bot_nat_0.extremum_unique 
            le_imp_less_Suc length_Cons nth_Cons_0 nth_Cons_pos plus_1_eq_Suc zero_less_Suc)
      have tmp6: "\<forall>i<length bl'. bl' ! i \<noteq>  b"
        using tmp5 False by (metis in_set_conv_nth in_set_remove1)
      then show ?thesis using tmp4 using less_Suc_eq_0_disj by fastforce
    qed
  qed
  then show ?case using Cons(3) 2 unfolding wf0_def Unique_def using 3 4 
    by (meson Cons.prems(1) perm_sym prem_seteq)
qed

lemma wf0_Cons: "wf0 (bl@cl) \<Longrightarrow> wf0 bl"
  unfolding wf0_def using Unique_Cons Unique_Cons2 by auto

lemma Unique_Permutation: "bl <~~> bl' \<Longrightarrow> Unique bl \<Longrightarrow> Unique bl'"
proof(induction bl arbitrary:bl')
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "bl <~~> remove1 a bl'"
    using Cons(2) perm_remove_perm by (metis remove_hd)
  have 2: "Unique (remove1 a bl')"
    using 1 Cons by (meson Unique_lemma)
  have 3: "a \<notin> set (remove1 a bl')"
    using Cons(2,3) unfolding wf0_def Unique_def apply simp
    by (metis "1" One_nat_def Suc_eq_plus1 Suc_less_eq add_diff_cancel_right' 
        in_set_conv_nth nth_Cons_0 perm_sym prem_seteq zero_less_Suc)
  have 5: "\<forall>i. i < length (remove1 a bl') \<and> 0 \<le> i \<longrightarrow> remove1 a bl' ! i \<noteq> a"
    using 3 by (metis nth_mem)
  have 6: "(\<forall>i j. i < j \<and> j < length bl' \<and> 0 \<le> i \<longrightarrow> bl' ! i \<noteq> bl' ! j)"
    using 5 2 apply simp
  proof(induction bl')
    case Nil
    then show ?case by simp
  next
    case (Cons b bl')
    then show ?case
    proof(cases "a = b")
      case True
      have tmp1: "\<forall>i j. i < j \<and> j < length bl' \<longrightarrow> bl' ! i \<noteq> bl' ! j"
        using Cons True by (simp add: wf0_def Unique_def)
      then show ?thesis using Cons(2) True
        using length_Cons less_Suc_eq_0_disj less_nat_zero_code by fastforce
    next
      case False
      have tmp1: "remove1 a (b # bl') = b#(remove1 a bl')"
        using False by simp
      have tmp2: "Unique (remove1 a bl')"
        using Cons(3) tmp1 using Unique_lemma by force
      have tmp3: "\<forall>i<length (remove1 a bl'). remove1 a bl' ! i \<noteq> a"
        using Cons(2) tmp1 by auto
      have tmp4: "\<forall>i j. i < j \<and> j < length bl' \<longrightarrow> bl' ! i \<noteq> bl' ! j"
        using tmp2 tmp3 Cons(1) by simp
      have tmp5: "\<forall>i<length (remove1 a bl'). remove1 a bl' ! i \<noteq>  b"
        using Cons(3) tmp1 
        by (metis Suc_leI Unique_def add_diff_cancel_left' bot_nat_0.extremum_unique 
            le_imp_less_Suc length_Cons nth_Cons_0 nth_Cons_pos plus_1_eq_Suc zero_less_Suc)
      have tmp6: "\<forall>i<length bl'. bl' ! i \<noteq>  b"
        using tmp5 False by (metis in_set_conv_nth in_set_remove1)
      then show ?thesis using tmp4 using less_Suc_eq_0_disj by fastforce
    qed
  qed
  then show ?case using Cons(3) 2 unfolding wf0_def Unique_def using 3 
    by (meson Cons.prems(1) perm_sym prem_seteq)
qed

primrec pair_input_offset :: "var list \<Rightarrow> offset \<Rightarrow> (var \<times> offset) list" where
"pair_input_offset [] os = []" |
"pair_input_offset (v#vl) os = (v, os) # pair_input_offset vl os"

fun Inputs :: "block list \<Rightarrow> var set" where
  "Inputs [] = {}"
| "Inputs (b#bl) = set (get_inputs b) \<union> Inputs bl"

lemma Inputs_base: "Inputs (l@[a]) = Inputs l \<union> set (get_inputs a)"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons b l)
  then show ?case
    by auto
qed

lemma Inputs_Cons: "Inputs (a@b) = Inputs a \<union> Inputs b"
proof(induction a)
  case Nil
  then show ?case by auto
next
  case (Cons b l)
  then show ?case
    by auto
qed

lemma Inputs_base3: "a \<in> set bl \<Longrightarrow>
Inputs (removeAll a bl) \<union> set (get_inputs a) = Inputs bl"
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons b l)
  then show ?case
  proof(cases "a \<notin> set l")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    have 1: "Inputs (removeAll a l) \<union> set (get_inputs a) = Inputs l"
      using False Cons by auto
    then show ?thesis using Cons False by auto
  qed
qed

lemma Inputs_eq: "set al = set bl \<Longrightarrow> Inputs al = Inputs bl"
proof(induction al arbitrary:bl)
  case Nil
  then show ?case by auto
next
  case (Cons a al)
  then show ?case
  proof(cases "a \<in> set al")
    case True
    then show ?thesis using Cons(1)[of bl]
      by (metis Cons.IH Cons.prems insert_absorb list.simps(15))
  next
    case False
    then show ?thesis using Cons(1)[of "removeAll a bl"] Cons(2) Inputs_base3
      by (metis removeAll.simps(2) removeAll_id remove_code(1))
  qed
qed

lemma Inputs_rev : "Inputs (rev bl) = Inputs bl"
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  then show ?case unfolding Inputs.simps rev.simps using Inputs_base by auto
qed

fun Outputs :: "block list \<Rightarrow> var set" where
  "Outputs [] = {}"
| "Outputs (b#bl) = set (get_outputs b) \<union> Outputs bl"

lemma Outputs_base: "Outputs (l@[a]) = Outputs l \<union> set (get_outputs a)"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons b l)
  then show ?case
    by auto
qed

lemma Outputs_Cons: "Outputs (a@b) = Outputs a \<union> Outputs b"
proof(induction a)
  case Nil
  then show ?case by auto
next
  case (Cons b l)
  then show ?case
    by auto
qed

lemma Outputs_base2: "a \<in> set bl \<Longrightarrow>
Outputs (remove1 a bl) \<union> set (get_outputs a) = Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons b l)
  then show ?case
  proof(cases "a = b")
    case True
    then show ?thesis by (simp add: sup_commute)
  next
    case False
    have 1: "Outputs (remove1 a l) \<union> set (get_outputs a) = Outputs l"
      using False Cons by auto
    then show ?thesis using Cons False by auto
  qed
qed

lemma Outputs_base3: "a \<in> set bl \<Longrightarrow>
Outputs (removeAll a bl) \<union> set (get_outputs a) = Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons b l)
  then show ?case
  proof(cases "a \<notin> set l")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    have 1: "Outputs (removeAll a l) \<union> set (get_outputs a) = Outputs l"
      using False Cons by auto
    then show ?thesis using Cons False by auto
  qed
qed

lemma Outputs_eq: "set al = set bl \<Longrightarrow> Outputs al = Outputs bl"
proof(induction al arbitrary:bl)
  case Nil
  then show ?case by auto
next
  case (Cons a al)
  then show ?case
  proof(cases "a \<in> set al")
    case True
    then show ?thesis using Cons(1)[of bl]
      by (metis Cons.IH Cons.prems insert_absorb list.simps(15))
  next
    case False
    then show ?thesis using Cons(1)[of "removeAll a bl"] Cons(2) Outputs_base3
      by (metis removeAll.simps(2) removeAll_id remove_code(1))
  qed
qed

lemma Outputs_remove: "a \<in> set bl \<Longrightarrow>
Outputs (a#(remove1 a bl))  = Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons b l)
  then show ?case
  proof(cases "a = b")
    case True
    then show ?thesis by (simp add: sup_commute)
  next
    case False
    have 1: "Outputs (remove1 a l) \<union> set (get_outputs a) = Outputs l"
      using False Cons by auto
    then show ?thesis using Cons False by auto
  qed
qed

lemma Outputs_perm: "al <~~> bl \<Longrightarrow> Outputs al = Outputs bl"
proof(induction al arbitrary:bl)
  case Nil
  then show ?case by auto
next
  case (Cons a al)
  have 1: "al <~~> remove1 a bl"
    using Cons(2) by (metis perm_remove_perm remove_hd)
  have 2: "a \<in> set bl"
    using Cons(2) by (simp add: prem_seteq)
  then show ?case using Cons(1)[of "remove1 a bl"] 1 Outputs_remove by simp
qed

lemma Outputs_rev : "Outputs (rev bl) = Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  then show ?case unfolding Outputs.simps rev.simps using Outputs_base by auto
qed

fun wf_block :: "block \<Rightarrow> bool" where
  "wf_block (Block a b c d e) = (length b = length c & length c = length e & length b > 0)"
definition "Graph As = (\<forall>b \<in> As. length (get_outputs b) > 0 \<and>
(\<forall>x\<in>As. (\<forall>y\<in>As. (x \<noteq> y \<longrightarrow> ((set (get_outputs x)) \<inter> (set (get_outputs y))= {})))))"

definition "wf1 bl = (wf0 bl \<and> Graph (set bl))"

lemma Graph_lemma: "Graph (set (a # bl)) \<Longrightarrow> Graph (set bl)"
  by (meson Graph_def list.set_intros(2))

lemma Graph_lemma2: "Unique (a#bl) \<Longrightarrow>
Graph (set (a # bl)) \<Longrightarrow> \<forall>x \<in> (Outputs bl). x \<notin> set (get_outputs a)"
  unfolding Graph_def Unique_def
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons b bl)
  have 1: "\<forall>i j. i < j \<and> j < length (a # bl) \<and> 0 \<le> i \<longrightarrow> (a # bl) ! i \<noteq> (a # bl) ! j"
    using Cons(2) 
    by (smt (verit, best) Suc_leI diff_Suc_1 le_eq_less_or_eq le_imp_less_Suc 
        length_Cons nth_Cons' order_le_less_trans)
  have 3: "\<forall>x\<in>set (a # bl). \<forall>y\<in>set (a # bl). x \<noteq> y \<longrightarrow> set (get_outputs x) \<inter> set (get_outputs y) = {}"
    using Cons(3) by simp
  have 4: "\<forall>x\<in>Outputs bl. x \<notin> set (get_outputs a)"
    using 1 3 Cons(1) Cons.prems(2) list.set_intros(1) by auto
  have 5: "set (get_outputs a) \<inter> set (get_outputs b) = {}"
    using Cons(3) 
    by (metis Cons.prems(1) One_nat_def Suc_less_eq length_Cons length_pos_if_in_set 
        list.set_intros(1) list.set_intros(2) nth_Cons_0 nth_Cons_Suc of_nat_0 
        of_nat_0_le_iff zero_less_one)
  then show ?case using 4 by auto
    
qed

lemma Graph_Permutation: "bl <~~> bl' \<Longrightarrow> Graph (set bl) \<Longrightarrow> Graph (set bl')"
  unfolding Graph_def using prem_seteq by (metis perm_sym)

type_synonym sorted_block_list = "block list" 

(*Two blocks A and B, give the outputs of B, the inputs of A and the offsets of A(inputs)*)
fun check_offset :: "var list \<Rightarrow> var list \<Rightarrow> offset list \<Rightarrow> bool" where
"check_offset [] il ol = False" |
"check_offset vl il [] = False" |
"check_offset vl il ol = (if ((set vl) \<inter> (set il) \<noteq> {}) \<and> (\<exists>d \<in> set ol. d = 0) then True 
 else False)"

(*can also defined as a definition*)
fun besorted :: "block list \<Rightarrow> bool" where
"besorted [] = True" |
"besorted (b # bl) = (besorted bl \<and> (\<forall> a. a \<in> set bl \<longrightarrow> 
            (check_offset (get_outputs a) (get_inputs b) (get_offsets b) ) = False))"

lemma besorted_remove1: "besorted (a#bl) \<Longrightarrow> besorted bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding besorted.simps by meson
qed

lemma besorted_remove2: "besorted bl \<Longrightarrow> besorted (remove1 b bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "besorted (remove1 b bl)"
    using besorted_remove1 Cons by simp
  show ?case
  proof(cases "a = b")
    case True
    then show ?thesis using Cons(2) besorted_remove1 by (metis remove_hd)
  next
    case False
    have 2: "besorted (remove1 b (a # bl)) = besorted (a#remove1 b bl)"
      using False by simp
    have 3: "\<forall>x. x \<in> set (remove1 b bl) \<longrightarrow> x \<in> set bl"
      by (meson notin_set_remove1)
    then show ?thesis using Cons(2) 2 unfolding besorted.simps using 1 by blast
  qed
qed

lemma besorted_last: "besorted (bl@[a]) \<Longrightarrow> (\<forall> b. b \<in> set bl \<longrightarrow> 
            (check_offset (get_outputs a) (get_inputs b) (get_offsets b)) = False)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "\<forall>b. b \<in> set bl \<longrightarrow> check_offset (get_outputs a) (get_inputs b) (get_offsets b) = False"
    using Cons by simp
  have 2: "check_offset (get_outputs a) (get_inputs b) (get_offsets b) = False"
    using Cons(2) by simp
  then show ?case using 1 by simp
qed

(*offset < 0 means we have all the inputs in the beginning of the execution cycle, so we remove them
out of the in-degree and only keep those inputs where offset = 0*)

definition get_block_indegree :: "block \<Rightarrow> block list \<Rightarrow> var set" where
  "get_block_indegree b bl = (if 0 \<in> set (get_offsets b) \<or> (get_sample_time b = 0) then 
(set (get_inputs b) - set (get_outputs b)) \<inter> Outputs bl else {})"

lemma get_block_indegree_perm: "bl <~~> bl' \<Longrightarrow> get_block_indegree b bl = get_block_indegree b bl'"
  unfolding get_block_indegree_def using Outputs_perm by presburger


type_synonym indegreeMap = "block \<Rightarrow> var set"

fun get_indegrees :: "block list \<Rightarrow> block list \<Rightarrow> indegreeMap \<Rightarrow> indegreeMap" where
  "get_indegrees [] bl f = f" |
  "get_indegrees (b#bl) cl f = get_indegrees bl cl (f(b := (get_block_indegree b cl)))"

(*give a block "b" and the deleted block list "bl", we delete the inputs from block "b"*)
fun delete_block_indegree :: "block \<Rightarrow> block list \<Rightarrow> indegreeMap \<Rightarrow> var set" where
  "delete_block_indegree b cl f = f b - (Outputs cl)"

(*the first block list "bl" is the remaining blocks and the second block list "cl" is the sorted blocks*)
fun delete_indegrees :: "block list \<Rightarrow> block list \<Rightarrow> indegreeMap \<Rightarrow> indegreeMap" where
  "delete_indegrees [] cl f = f" |
  "delete_indegrees (b#bl) cl f = delete_indegrees bl cl (f(b := (delete_block_indegree b cl f)))"


fun find_0indegree_blocks :: "block list \<Rightarrow> block list \<Rightarrow> sorted_block_list  
   \<Rightarrow> (block option  \<times> block list)" where
  "find_0indegree_blocks al [] cl = (None,[])" |
  "find_0indegree_blocks al (b#bl) cl  = (let x = find_0indegree_blocks al bl cl in 
                      (if (get_block_indegree b al -  (Outputs cl) = {}) then 
                         (Some b, bl) else (fst x, b#(snd x))))"

lemma length_find_0indegree: "(fst (find_0indegree_blocks al bl cl)) \<noteq> None \<Longrightarrow> length (snd (find_0indegree_blocks al bl cl))
                               < length bl"
proof (induction bl arbitrary: cl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  then show ?case 
  proof (cases "(get_block_indegree a al -  (Outputs cl) = {}) ")
    case True
    then show ?thesis using Cons True by auto
  next
    case False
    have 1: "length (snd (find_0indegree_blocks al bl cl)) < length bl"
      using Cons(1,2) False unfolding find_0indegree_blocks.simps by force
    have 2: "length (snd (find_0indegree_blocks al (a # bl) cl)) = length (snd (find_0indegree_blocks al bl cl)) + 1"
      unfolding find_0indegree_blocks.simps using False
      by (smt (verit, best) add.commute length_Cons plus_1_eq_Suc snd_conv)
    then show ?thesis using 1 by simp
  qed
qed

lemma find_0indegree_block_lemma : "find_0indegree_blocks al bl cl = (Some b, dl) \<Longrightarrow>
  get_block_indegree b al -  (Outputs cl) = {}"
proof(induction bl arbitrary: dl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case unfolding find_0indegree_blocks.simps
  proof(cases "get_block_indegree a al - Outputs cl = {}")
    case True
    then show ?thesis using Cons(2) unfolding find_0indegree_blocks.simps by simp
  next
    case False
    have 1: "find_0indegree_blocks al bl cl = (Some b, (remove1 a dl))"
      using Cons(2) unfolding find_0indegree_blocks.simps apply simp
      by (smt (verit) False diff_shunt_var fst_eqD prod.exhaust_sel remove_hd snd_eqD)
    then show ?thesis using Cons(1) by simp
  qed
qed

lemma find_0indegree_block_lemma2 : "find_0indegree_blocks al bl cl = (Some b, dl) \<Longrightarrow>
  dl = (remove1 b bl)"
proof(induction bl arbitrary: dl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case unfolding find_0indegree_blocks.simps
  proof(cases "get_block_indegree a al - Outputs cl = {}")
    case True
    then show ?thesis using Cons(2) unfolding find_0indegree_blocks.simps by simp
  next
    case False
    have 1: "find_0indegree_blocks al bl cl = (Some b, (remove1 a dl))"
      using Cons(2) unfolding find_0indegree_blocks.simps apply simp
      by (smt (verit) False diff_shunt_var fst_eqD prod.exhaust_sel remove_hd snd_eqD)
    have 2: "hd dl = a"
      using Cons(2) unfolding find_0indegree_blocks.simps apply simp
      by (smt (verit, best) False diff_shunt_var list.sel(1) snd_conv)
    have 3: "dl = a # tl dl"
      using 2 1 Cons.prems False list.exhaust_sel by auto
    have 4: "(remove1 a dl) = remove1 b bl"
      using Cons(1) 1 by simp
    then show ?thesis using Cons(1) 3 by (metis "1" False find_0indegree_block_lemma remove1.simps(2))
  qed
qed

lemma find_0indegree_lemma4: "(fst (find_0indegree_blocks al bl cl)) \<noteq> None \<Longrightarrow> 
length (snd (find_0indegree_blocks al bl cl))+1 = length bl"
proof (induction bl arbitrary: cl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  then show ?case 
  proof (cases "(get_block_indegree a al -  (Outputs cl) = {}) ")
    case True
    then show ?thesis using Cons True by auto
  next
    case False
    have 1: "length (snd (find_0indegree_blocks al bl cl))+1 = length bl"
      using Cons(1,2) False unfolding find_0indegree_blocks.simps by force
    have 2: "length (snd (find_0indegree_blocks al (a # bl) cl)) = length (snd (find_0indegree_blocks al bl cl)) + 1"
      unfolding find_0indegree_blocks.simps using False
      by (smt (verit, best) add.commute length_Cons plus_1_eq_Suc snd_conv)
    then show ?thesis using 1 by simp
  qed
qed

lemma find_0indegree_lemma3: "(fst (find_0indegree_blocks al bl cl)) \<noteq> None 
\<Longrightarrow> set (the (fst (find_0indegree_blocks al bl cl))#(snd (find_0indegree_blocks al bl cl)))
                               = set bl"
proof (induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  then show ?case 
  proof (cases "(get_block_indegree a al - (Outputs cl) = {}) ")
    case True
    then show ?thesis using Cons True by auto
  next
    case False
    have 1: "fst (find_0indegree_blocks al bl cl) \<noteq> None"
      using Cons(2) unfolding find_0indegree_blocks.simps using False by auto
    have 2: "set (the (fst (find_0indegree_blocks al bl cl)) # 
      snd (find_0indegree_blocks al bl cl)) = set bl"
      using Cons(1) 1 by simp
    have 3: "the (fst (let x = find_0indegree_blocks al bl cl
                   in if get_block_indegree a al - Outputs cl = {} then (Some a, bl)
                      else (fst x, a # snd x))) = the (fst (find_0indegree_blocks al bl cl))"
      using False by (smt (verit, best) fst_conv)
    have 4: "snd (let x = find_0indegree_blocks al bl cl
              in if get_block_indegree a al - Outputs cl = {} then (Some a, bl)
                 else (fst x, a # snd x)) = a#(snd (find_0indegree_blocks al bl cl))"
      using False by (smt (verit, best) snd_conv)
    have 5: "set (the (fst (let x = find_0indegree_blocks al bl cl
                   in if get_block_indegree a al - Outputs cl = {} then (Some a, bl)
                      else (fst x, a # snd x))) #
         snd (let x = find_0indegree_blocks al bl cl
              in if get_block_indegree a al - Outputs cl = {} then (Some a, bl)
                 else (fst x, a # snd x))) = set (the (fst (find_0indegree_blocks al bl cl))#
        (a#(snd (find_0indegree_blocks al bl cl))))"
      using 3 4 by presburger
    have 6: "set (the (fst (find_0indegree_blocks al bl cl)) # (a#(snd (find_0indegree_blocks al bl cl)))) 
        = set (a#bl)"
      using 2 by auto
    then show ?thesis unfolding find_0indegree_blocks.simps using 5 by auto
  qed
qed



function topological_sort :: "block list \<Rightarrow> block list \<Rightarrow> sorted_block_list \<Rightarrow> sorted_block_list" where
"topological_sort al bl cl = (let x = (find_0indegree_blocks al bl cl) in 
                           (if (fst x = None) then cl else
                                (topological_sort al (snd x) (cl@[the (fst x)]))))"
  by pat_completeness auto 

termination 
  apply (relation "measures[(\<lambda>(a::block list, b::block list, c::block list). length b)]", auto)
  subgoal for al bl cl
    using length_find_0indegree[of al bl cl] 
    by auto
  done
  
lemma "topological_sort [] [] [] = []"
  using topological_sort.psimps by auto

definition besorted_change:: "block list \<Rightarrow> bool"
  where "besorted_change dl =  (\<forall> i j. (i<j \<and> j < (length dl) \<and> j \<ge> 0) \<longrightarrow> 
            (check_offset (get_outputs (dl ! j)) (get_inputs (dl ! i)) (get_offsets (dl ! i))) = False)"

lemma besorted_equiv: "besorted dl \<equiv> besorted_change dl"
proof(induction dl)
  case Nil
  then show ?case unfolding besorted_change_def by simp
next
  case (Cons d dl)
  have 1: "besorted (d # dl) \<Longrightarrow> besorted_change (d # dl)"
    unfolding besorted_change_def besorted.simps apply clarify
    subgoal premises pre for i j
    proof(cases "i = 0")
      case True
      then show ?thesis apply simp using pre(2,3,4,5) by simp
    next
      case False
      have tmp1: "i > 0 \<and> i < length (d # dl)"
        using pre False by simp
      then show ?thesis using Cons pre(1,3,4,5) unfolding besorted_change_def
        using less_Suc_eq_0_disj by force
    qed
    done
  have 2: "besorted_change (d # dl) \<Longrightarrow> besorted (d # dl)"
    subgoal premises pre
    proof -
      have tmp1: "besorted_change dl" 
        using pre unfolding besorted_change_def
        by (metis Suc_less_eq length_Cons nth_Cons_Suc zero_le)
      have tmp2: "besorted dl"
        using Cons tmp1 by simp
      have tmp3: "\<forall>a. a \<in> set dl \<longrightarrow> check_offset (get_outputs a) (get_inputs d) (get_offsets d) = False"
        using pre unfolding besorted_change_def by (metis Suc_leI bot_nat_0.extremum in_set_conv_nth 
            le_imp_less_Suc length_Cons nth_Cons_0 nth_Cons_Suc)
      show ?thesis unfolding besorted.simps using tmp2 tmp3 by simp
    qed
    done
  then show ?case using 1 by blast
qed

definition after_0indegree :: "block list \<Rightarrow> block list \<Rightarrow> bool" where
"after_0indegree al bl = (\<forall> i. (i \<ge> 0 \<and> i < length bl) \<longrightarrow> (get_block_indegree (bl ! i) al -  (Outputs (take i bl)) = {}))"

lemma topo_besorted: "topological_sort al bl cl = dl \<Longrightarrow> after_0indegree al cl
                \<Longrightarrow> besorted_change cl \<Longrightarrow> Outputs al = Outputs bl \<union> Outputs cl \<Longrightarrow>
                \<forall>i j. i\<in> set bl \<and> j \<in> set cl \<longrightarrow> 
    check_offset (get_outputs i) (get_inputs j) (get_offsets j) = False \<Longrightarrow>  Unique (bl@cl)
  \<Longrightarrow> Graph (set (bl@cl)) \<Longrightarrow> besorted_change dl"
proof (induction bl arbitrary: cl dl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def
    by (metis case_prodD length_induct mem_Collect_eq) 
next
  case (2 x)
  then show ?case
  proof (induction x arbitrary: cl dl)
    case Nil
    then show ?case  using topological_sort.psimps by auto
  next
    case (Cons a bl)
     then show ?case using topological_sort.psimps[of al "a#bl" cl]
     proof (cases "fst (find_0indegree_blocks al (a # bl) cl) = None")
      case True
      then show ?thesis using Cons topological_sort.psimps[of al "a#bl" cl] by auto
    next
      case False
      note FF = False
      then show ?thesis using Cons
      proof (cases " (get_block_indegree a al - (Outputs cl) = {})")
        case True
        note FT = True
        have 1: "(find_0indegree_blocks al (a # bl) cl) = (Some a, bl)"
          using True unfolding find_0indegree_blocks.simps by simp
        have 2: "topological_sort al (a # bl) cl = topological_sort al bl (cl@[a])"
          using 1 topological_sort.psimps[of al "a#bl" cl] by simp
        have 3: "topological_sort al bl (cl@[a]) = dl"
          using 2 Cons(3) by simp
        have "besorted_change (cl@[a])" 
        proof -
              have tmp1: "\<forall>b \<in> set cl.
          check_offset (get_outputs a) (get_inputs b) (get_offsets b) = False"
                using Cons(7) by auto
              show ?thesis using Cons(5) tmp1 unfolding after_0indegree_def besorted_change_def
                by (simp add: nth_append)
        qed
        moreover have "after_0indegree al (cl@[a])" using Cons(4,3) True unfolding after_0indegree_def
          by (simp add: nth_append)
        moreover have "(bl, a # bl) \<in> {a. case a of (x, y) \<Rightarrow> length x < length y}"
          by auto
        moreover have " Outputs al = Outputs bl \<union> Outputs (cl @ [a])" using Cons(6) 
          using Outputs.simps(2) Outputs_base by blast
        moreover have "\<forall>i j. i \<in> set bl \<and> j \<in> set (cl @ [a]) \<longrightarrow>
          check_offset (get_outputs i) (get_inputs j) (get_offsets j) = False" 
        proof -
        have tmp1: "0 \<notin> set (get_offsets a) \<Longrightarrow> \<forall>i. i \<in> set bl \<longrightarrow>
        check_offset (get_outputs i) (get_inputs a) (get_offsets a) = False"
          by (metis (mono_tags, opaque_lifting) check_offset.elims(2))
        have tmp2: "Outputs bl \<inter> Outputs cl = {}"
        proof -
          have tmp1: "Unique (bl @ cl)"
            using Cons(8) Unique_lemma by simp
          have tmp2: "Graph (set (bl@cl))"
            using Cons(9) Graph_lemma by (metis Cons_eq_appendI)
          show ?thesis using tmp1 tmp2 apply simp
          proof(induction bl)
            case Nil
            then show ?case by simp
          next
            case (Cons b bl)
            have tmp1: "set (get_outputs b) \<inter> Outputs cl = {}"
            proof -
              have "Graph (set (b#cl))"
                using Cons(3) unfolding Graph_def by auto
              moreover have "\<forall>j. j < (length cl) \<and> j \<ge> 0 \<longrightarrow> b \<noteq> (nth cl j)"
              proof -
                have tmp1: "\<forall>j. j < (length (bl@cl)) \<and> j \<ge> 0 \<longrightarrow> b \<noteq> (nth (bl@cl) j)"
                  using Cons(2) unfolding Unique_def by force
                then show ?thesis by (metis UnI2 in_set_conv_nth set_append zero_le)
              qed
              ultimately show ?thesis apply simp
              proof(induction cl)
                case Nil
                then show ?case by simp
              next
                case (Cons c cl)
                have tmp1: "set (get_outputs b) \<inter> Outputs cl = {}"
                  using Cons unfolding Graph_def 
                  by (metis in_set_conv_nth insert_iff list.simps(15))
                have tmp2: "b \<noteq> c"
                  using Cons(3) by auto
                have tmp3: "set (get_outputs b) \<inter> set (get_outputs c) = {}"
                  using Cons(2) tmp2 unfolding Graph_def 
                  by (meson insertI1 insertI2 list.set_intros(1))
                then show ?case using tmp1 by auto
              qed
            qed
            have tmp2: "Graph (set bl \<union> set cl)"
              using Cons(3) unfolding Graph_def by simp
            have tmp3: "Unique (bl @ cl)"
              using Cons(2) Unique_lemma by simp
            have tmp4: "Outputs bl \<inter> Outputs cl = {}"
              using tmp2 tmp3 Cons(1) by simp
            then show ?case unfolding Outputs.simps using tmp1 by auto
          qed
        qed
        have tmp3_1: "set (get_outputs a) \<inter> (Outputs bl) = {}"
          using Cons(8,9) unfolding Unique_def Graph_def
          by (smt (verit) Cons.prems(7) Graph_def Graph_lemma2 UnI1 Unique_Cons2 
              disjoint_iff_not_equal set_append)
        have tmp3_2: "set (get_outputs a) \<inter> (Outputs cl) = {}"
          using Cons(8,9)
        proof(induction cl)
          case Nil
          then show ?case by simp
        next
          case (Cons c cl)
          have tmp1: "remove1 c ((a # bl) @ c # cl) = (a#bl)@cl"
            using Cons(2) unfolding Unique_def
            by (metis Cons.prems(1) Un_iff Unique_k bot_nat_0.extremum in_set_conv_nth 
                list.set_intros(1) remove1_append remove_hd set_append)
          have tmp2: "Unique ((a # bl) @ cl)"
            using Cons(2) Unique_remove tmp1 by (metis remove1_idem)
          have tmp3: "set (get_outputs a) \<inter> Outputs cl = {}"
            using Cons(1,3) tmp2 unfolding Graph_def by auto
          have tmp4: "set (get_outputs a) \<inter> set (get_outputs c) = {}"
            using Cons(2,3) unfolding Unique_def Graph_def 
            by (metis Cons.prems(1) Unique_k append_Cons bot_nat_0.extremum in_set_conv_decomp 
                length_Cons list.set_intros(1) nth_Cons_0 tmp1 zero_less_Suc)
          then show ?case using tmp3 unfolding Outputs.simps by auto
        qed
          have tmp3: "0 \<in> set (get_offsets a) \<Longrightarrow> set (get_inputs a) \<inter> (Outputs bl) = {}"
            using Cons(6) tmp2 FT tmp3_1 tmp3_2 unfolding get_block_indegree_def Outputs.simps by auto
          have tmp4: "0 \<in> set (get_offsets a) \<Longrightarrow> \<forall>i. i \<in> set bl \<longrightarrow>
        check_offset (get_outputs i) (get_inputs a) (get_offsets a) = False"
            apply clarify subgoal premises pre for i 
            proof(cases "(get_outputs i) = []")
              case True
              then show ?thesis by simp
            next
              case False
              have 1: "(get_outputs i) = hd (get_outputs i) # tl (get_outputs i)"
                using False by simp
              then show ?thesis
              proof(cases "(get_offsets a) = []")
                case True
                then show ?thesis using 1 pre(1) by fastforce
              next
                case False
                have 2: "(get_offsets a) = (hd (get_offsets a)) # (tl (get_offsets a))"
                  using False by simp
                then show ?thesis using check_offset.simps(3)[of "hd (get_outputs i)" 
                      "tl (get_outputs i)" "(get_inputs a)" "hd (get_offsets a)" 
                      "tl (get_offsets a)"] 1 tmp3 pre Outputs_base2 by auto
              qed
            qed
            done
          show ?thesis using FT Cons(7) tmp1 tmp4 unfolding get_block_indegree_def
          using insert_iff list.set(2) set_append by auto
        qed
        moreover have "Unique (bl @ cl @ [a])"
        proof -
          have tmp1: "\<forall>j. j < (length (bl@cl)) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth (bl@cl) j)"
            using Cons(8) unfolding Unique_def by (metis Suc_leI append_Cons 
                le_imp_less_Suc le_zero_eq length_Cons nth_Cons_0 nth_Cons_Suc)
          then show ?thesis using Unique_lemma Cons(8) Unique_add2
            by (metis append.assoc append_Cons)
        qed
        moreover have "Graph (set (bl @ cl @ [a]))" using Cons(9) by simp
        ultimately show ?thesis using Cons(1)[of "cl@[a]" dl] Cons(2) 3 by metis
      next
        case False
        have 1: "\<exists>c. fst (find_0indegree_blocks al (a # bl) cl) = Some c"
          using FF by simp
        show ?thesis using 1 apply clarify
          subgoal premises pre for c
          proof -
            have 2: "get_block_indegree c al - Outputs cl = {}"
              using find_0indegree_block_lemma pre by (metis prod.collapse)
            have 3: "snd (find_0indegree_blocks al (a # bl) cl) = remove1 c (a#bl)"
              using pre find_0indegree_block_lemma2 by (metis prod.exhaust_sel)
            have 4: "topological_sort al (a # bl) cl = topological_sort al (remove1 c (a#bl)) (cl@[c])"
              using topological_sort.psimps[of al "a#bl" cl] pre 3 by simp
            have 5: "topological_sort al (remove1 c (a#bl)) (cl@[c]) = dl"
              using 4 Cons(3) by simp
            have 6: "c \<in> set (a#bl)"
              by (metis "3" FF length_find_0indegree less_irrefl_nat remove1_idem)
            have 7: "(remove1 c (a#bl), a # bl) \<in> {a. case a of (x, y) \<Rightarrow> length x < length y}"
              by (metis "3" FF case_prodI length_find_0indegree mem_Collect_eq)
            have 8: "besorted_change (cl@[c])" 
            proof -
                  have tmp1: "\<forall>b \<in> set cl.
              check_offset (get_outputs c) (get_inputs b) (get_offsets b) = False"
                    using Cons(7) 6 by auto
                  show ?thesis using Cons(5) tmp1 unfolding after_0indegree_def besorted_change_def
                    by (simp add: nth_append)
            qed
            have 9: "after_0indegree al (cl@[c])" using Cons(4,3) 2 unfolding after_0indegree_def
              by (simp add: nth_append)
            have 10: " Outputs al = Outputs (remove1 c (a#bl)) \<union> Outputs (cl @ [c])" using Cons(6) 
              using Outputs.simps(2) Outputs_base2 6 Outputs_base by auto
            have 11: "\<forall>i j. i \<in> set (remove1 c (a#bl)) \<and> j \<in> set (cl @ [c]) \<longrightarrow>
                check_offset (get_outputs i) (get_inputs j) (get_offsets j) = False"
            proof -
              have tmp1: "0 \<notin> set (get_offsets c) \<Longrightarrow> \<forall>i. i \<in> set (remove1 c (a#bl)) \<longrightarrow>
              check_offset (get_outputs i) (get_inputs c) (get_offsets c) = False"
                by (metis (mono_tags, opaque_lifting) check_offset.elims(2))
              have tmp2: "Outputs bl \<inter> Outputs cl = {}"
              proof -
                have tmp1: "Unique (bl @ cl)"
                  using Cons(8) Unique_lemma by simp
                have tmp2: "Graph (set (bl@cl))"
                  using Cons(9) Graph_lemma by (metis Cons_eq_appendI)
                show ?thesis using tmp1 tmp2 apply simp
                proof(induction bl)
                  case Nil
                  then show ?case by simp
                next
                  case (Cons b bl)
                  have tmp1: "set (get_outputs b) \<inter> Outputs cl = {}"
                  proof -
                    have "Graph (set (b#cl))"
                      using Cons(3) unfolding Graph_def by auto
                    moreover have "\<forall>j. j < (length cl) \<and> j \<ge> 0 \<longrightarrow> b \<noteq> (nth cl j)"
                    proof -
                      have tmp1: "\<forall>j. j < (length (bl@cl)) \<and> j \<ge> 0 \<longrightarrow> b \<noteq> (nth (bl@cl) j)"
                        using Cons(2) unfolding Unique_def by force
                      then show ?thesis by (metis UnI2 in_set_conv_nth set_append zero_le)
                    qed
                    ultimately show ?thesis apply simp
                    proof(induction cl)
                      case Nil
                      then show ?case by simp
                    next
                      case (Cons c cl)
                      have tmp1: "set (get_outputs b) \<inter> Outputs cl = {}"
                        using Cons unfolding Graph_def 
                        by (metis in_set_conv_nth insert_iff list.simps(15))
                      have tmp2: "b \<noteq> c"
                        using Cons(3) by auto
                      have tmp3: "set (get_outputs b) \<inter> set (get_outputs c) = {}"
                        using Cons(2) tmp2 unfolding Graph_def 
                        by (meson insertI1 insertI2 list.set_intros(1))
                      then show ?case using tmp1 by auto
                    qed
                  qed
                  have tmp2: "Graph (set bl \<union> set cl)"
                    using Cons(3) unfolding Graph_def by simp
                  have tmp3: "Unique (bl @ cl)"
                    using Cons(2) Unique_lemma by simp
                  have tmp4: "Outputs bl \<inter> Outputs cl = {}"
                    using tmp2 tmp3 Cons(1) by simp
                  then show ?case unfolding Outputs.simps using tmp1 by auto
                qed
              qed
              have tmp3: "set (get_outputs a) \<inter> Outputs cl = {}"
              proof -
                have tmp1: "\<forall>j. j < (length cl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth cl j)"
                proof -
                  have "\<forall>j. j < (length (bl@cl)) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth (bl@cl) j)"
                    using Cons(8) unfolding Unique_def by force
                  then show ?thesis by (metis UnI2 in_set_conv_nth set_append zero_le)
                qed
                have "Unique (a#cl)"
                  using Cons(8) Unique_Cons Unique_add tmp1 by metis
                moreover have "Graph (set (a#cl))"
                  using Cons(9) unfolding Graph_def
                  by (metis UnCI UnI1 list.set_intros(1) set_ConsD set_append)
                ultimately show ?thesis apply simp
                proof(induction cl)
                  case Nil
                  then show ?case by simp
                next
                  case (Cons c cl)
                  have tmp1: "a \<noteq> c"
                    using Cons(2) unfolding Unique_def by (metis Cons.prems(1) Unique_k 
                   length_greater_0_conv list.set_intros(1) neq_Nil_conv nth_Cons_0 remove_hd zero_le)
                  have tmp2: "Unique (a # cl)"
                    using tmp1 Unique_remove Cons(2) by force
                  have tmp3: "Graph (insert a (set cl))"
                    using Cons(3) unfolding Graph_def tmp1 by simp
                  have tmp4: "set (get_outputs a) \<inter> Outputs cl = {}"
                    using Cons(1) tmp2 tmp3 by simp
                  have tmp5: "set (get_outputs a) \<inter> set (get_outputs c) = {}"
                    using Cons(3) unfolding Graph_def
                    by (metis insert_iff list.simps(15) tmp1)
                  then show ?case using tmp4 unfolding Outputs.simps by auto
                qed
              qed
              have tmp4_1: "set (get_outputs c) \<inter> Outputs cl = {}"
                using Cons(8,9) unfolding Unique_def Graph_def 
                by (metis "6" Outputs_base2 UnCI disjoint_iff_not_equal set_ConsD tmp2 tmp3)
              have tmp4_2: "set (get_outputs c) \<inter> (Outputs (remove1 c (a#bl))) = {}" 
                using 6 Cons(8,9)
              proof(induction bl)
                case Nil
                then show ?case by auto
              next
                case (Cons b bl)
                then show ?case
                proof(cases "c = b")
                  case True
                  have tmp1: "remove1 c (a # b # bl) = a#bl"
                    using Cons(3) unfolding Unique_def True by simp
                  have tmp2: "Unique (b # bl)"
                    using Cons(3) Unique_lemma by (metis Unique_Cons2)
                  have tmp3: "Graph (set (b # bl))"
                    using Cons(4) unfolding Graph_def 
                    by (metis UnI1 list.set_intros(2) set_append)
                  have tmp4: "set (get_outputs c) \<inter> Outputs bl = {}"
                    using tmp2 tmp3 True
                  proof(induction bl)
                    case Nil
                    then show ?case by simp
                  next
                    case (Cons d bl)
                    have tmp1: "Unique (b#bl)"
                      using Cons(2) unfolding Unique_def
                      by (metis (no_types, lifting) Unique_def Unique_remove list.set_intros(1) 
                          remove1.simps(2) set_subset_Cons subset_code(1))
                    have tmp2: "Graph (set (b # bl))"
                      using Cons(3) unfolding Graph_def by auto
                    have tmp3: "set (get_outputs c) \<inter> Outputs bl = {}"
                      using Cons(1,4) tmp1 tmp2 by simp
                    then show ?case unfolding Outputs.simps using Cons(2,3) unfolding Unique_def Graph_def
                      by (metis Cons.prems(1) Cons.prems(2) Graph_lemma2 Int_emptyI Outputs.simps(2) True)
                  qed
                  then show ?thesis using True tmp1 
                    using "2" Cons.prems(3) False Graph_def list.set_intros(1) set_append by auto
                next
                  case False
                  note F1 = False
                  have tmp1: "c \<in> set (a # bl)"
                    using Cons(2) False by auto
                  have tmp2: "Unique ((a # bl) @ cl)"
                    using Cons(3) unfolding Unique_def
                    by (smt (z3) Suc_leI add_diff_cancel_left' append_Cons bot_nat_0.extremum 
                        le_imp_less_Suc length_Cons less_Suc_eq nth_Cons_0 nth_Cons_pos plus_1_eq_Suc)
                  have tmp3: "set (get_outputs c) \<inter> Outputs (remove1 c (a # bl)) = {}"
                    using Cons(1,4) tmp1 tmp2 unfolding Graph_def by auto
                  have tmp4: "set (get_outputs c) \<inter> set (get_outputs b) = {}"
                    using False Cons(4) unfolding Graph_def
                    by (metis Cons.prems(1) Un_iff list.set_intros(1) notin_set_remove1 remove_hd set_append)
                  then show ?thesis using False
                  proof(cases "c = a")
                    case True
                    then show ?thesis using tmp3 tmp4 by auto
                  next
                    case False
                    then show ?thesis using F1 tmp3 tmp4 by auto
                  qed
                qed
              qed
              have tmp4: "0 \<in> set (get_offsets c) \<Longrightarrow> 
                set (get_inputs c) \<inter> (Outputs (remove1 c (a#bl))) = {}"
                using Cons(6) 2 tmp2 tmp3 tmp4_1 tmp4_2 unfolding get_block_indegree_def
                by (smt (verit, ccfv_threshold) "6" Diff_Int_distrib2 Diff_iff Int_iff Outputs.simps(2)
                    Outputs_base2 UnCI Un_iff disjoint_iff_not_equal empty_iff)
              have tmp5: "0 \<in> set (get_offsets c) \<Longrightarrow> \<forall>i. i \<in> set (remove1 c (a#bl)) \<longrightarrow>
            check_offset (get_outputs i) (get_inputs c) (get_offsets c) = False"
                apply clarify subgoal premises pre for i 
                proof(cases "(get_outputs i) = []")
                  case True
                  then show ?thesis by simp
                next
                  case False
                  have 1: "(get_outputs i) = hd (get_outputs i) # tl (get_outputs i)"
                    using False by simp
                  then show ?thesis
                  proof(cases "(get_offsets c) = []")
                    case True
                    then show ?thesis using 1 pre(1) by fastforce
                  next
                    case False
                    have 2: "(get_offsets c) = (hd (get_offsets c)) # (tl (get_offsets c))"
                      using False by simp
                    then show ?thesis using check_offset.simps(3)[of "hd (get_outputs i)" 
                          "tl (get_outputs i)" "(get_inputs c)" "hd (get_offsets c)" 
                          "tl (get_offsets c)"] 1 tmp4 pre Outputs_base2 by auto
                  qed
                qed
                done
              show ?thesis using tmp1 tmp5 Cons(7)
                by (metis Un_iff empty_iff list.set(1) notin_set_remove1 set_ConsD set_append)
            qed
            have 12: "Unique ((remove1 c (a#bl)) @ cl @ [c])"
            proof -
              have tmp1: "c \<in> set ((a # bl) @ cl)"
                using 6 by auto
              have tmp2: "(remove1 c (a#bl)) @ cl = remove1 c ((a#bl)@ cl)"
                using 6by (metis remove1_append)
              have tmp3: "\<forall>j. j < (length ((remove1 c (a#bl)) @ cl)) \<and> j \<ge> 0 \<longrightarrow> c \<noteq> (nth ((remove1 c (a#bl)) @ cl) j)"
                using Cons(8) tmp1 Unique_k tmp2 by metis
              have tmp4: "Unique ((remove1 c (a#bl)) @ cl)"
                using Cons(8) Unique_remove tmp1 by (metis tmp2)
              then show ?thesis using tmp3 Unique_add2 by (metis append.assoc)
            qed
            have 13: "Graph (set ((remove1 c (a#bl)) @ cl @ [c]))"
            proof -
              have tmp1: "set ((remove1 c (a#bl))@[c]) = set (a#bl)"
              proof -
                have "\<forall>x \<in> set ((remove1 c (a#bl))@[c]) . x \<in> set (a#bl)"
                  apply clarify subgoal for x using 6
                    by (metis Un_iff empty_iff in_set_remove1 list.set(1) remove_hd set_append)
                  done
                moreover have "\<forall>x \<in> set (a#bl). x \<in> set ((remove1 c (a#bl))@[c])"
                  apply clarify subgoal for x using 6
                    by (metis Un_iff in_set_remove1 list.set_intros(1) set_append)
                  done
                ultimately show ?thesis by auto
              qed
              have tmp2: "set ((remove1 c (a#bl)) @ cl @ [c]) = set ((a # bl) @ cl)"
                using tmp1 using inf_sup_aci(7) by auto
              then show ?thesis using Cons(9) by simp
            qed
            show ?thesis using Cons(2) 7 5 8 9 10 11 12 13 by blast
          qed
          done
      qed
    qed
  qed
qed

 definition sortDiag :: "block list \<Rightarrow> sorted_block_list" where
"sortDiag bl = topological_sort bl bl []"


definition "loop_free bl = (length (sortDiag bl) = length bl)"

declare loop_free_def [simp]

lemma sort_is_sorted : "Unique bl \<Longrightarrow> Graph (set bl) \<Longrightarrow> besorted (sortDiag bl)"
  subgoal premises pre
proof -
  have 1: "after_0indegree bl []"
    unfolding after_0indegree_def get_block_indegree_def by simp
  have 2: "besorted_change []"
    unfolding besorted_change_def by simp
  have 3: "Outputs bl = Outputs bl \<union> Outputs []"
    by simp
  have 4: "\<forall>i j. i \<in> set bl \<and> j \<in> set [] \<longrightarrow>
        check_offset (get_outputs i) (get_inputs j) (get_offsets j) = False"
    by simp
  show ?thesis
    using  topo_besorted[of bl bl "[]"] unfolding sortDiag_def using 1 2 3 4 pre(1,2)
    using besorted_equiv by simp
qed
  done

lemma sort_subset: "length (topological_sort al bl cl) = length (bl@cl) \<Longrightarrow>
set (bl@cl) = set (topological_sort al bl cl)"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def
    by (metis (no_types, lifting) case_prodD length_induct mem_Collect_eq)
next
  case (2 bl)
  then show ?case
  proof(cases "bl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 3: "length (snd (find_0indegree_blocks al bl cl)) < length bl"
      using 2(2) unfolding loop_free_def sortDiag_def using topological_sort.simps[of al bl cl]
      by (smt (verit) False append_Nil append_eq_append_conv length_find_0indegree)
    have 4: "topological_sort al bl cl = (let x = find_0indegree_blocks al bl cl in 
      topological_sort al (snd x) (cl @ [the (fst x)]))"
      using topological_sort.simps[of al bl cl] 2(2) False
      by (smt (verit) append.left_neutral append_eq_append_conv)
    have 5: "fst (find_0indegree_blocks al bl cl) \<noteq> None"
      using 4 topological_sort.simps[of al bl cl] "2.prems" False append_eq_append_conv2 by fastforce
    have 6: "length (bl@cl) = length (let x = find_0indegree_blocks al bl cl in 
      ((snd x)@(cl @ [the (fst x)])))"
      using find_0indegree_lemma4 5 by force
    have 7: "(let x = find_0indegree_blocks al bl cl in length 
      (topological_sort al (snd x) (cl @ [the (fst x)])) = length ((snd x)@(cl @ [the (fst x)])))"
      using 2(2) 4 6 by metis
    have 8: "set (bl) = set (let x = find_0indegree_blocks al bl cl in 
      ((snd x)@([the (fst x)])))"
      using 5 find_0indegree_lemma3 by (metis append_Cons append_Nil inf_sup_aci(5) set_append)
    have 9: "set (bl @ cl) = set (let x = find_0indegree_blocks al bl cl in 
      ((snd x)@(cl@[the (fst x)])))"
      using 8 by (metis append_assoc inf_sup_aci(5) set_append)
    then show ?thesis using 2(1) 3 6 4 7 by (metis case_prodI mem_Collect_eq)
  qed
qed

lemma toposort_perm: "length (topological_sort al bl cl) = length (bl@cl) \<Longrightarrow>
(bl@cl) <~~> (topological_sort al bl cl)"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def
    by (metis (no_types, lifting) case_prodD length_induct mem_Collect_eq)
next
  case (2 bl)
  then show ?case
  proof(cases "bl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 3: "length (snd (find_0indegree_blocks al bl cl)) < length bl"
      using 2(2) unfolding loop_free_def sortDiag_def using topological_sort.simps[of al bl cl]
      by (smt (verit) False append_Nil append_eq_append_conv length_find_0indegree)
    have 4: "topological_sort al bl cl = (let x = find_0indegree_blocks al bl cl in 
      topological_sort al (snd x) (cl @ [the (fst x)]))"
      using topological_sort.simps[of al bl cl] 2(2) False
      by (smt (verit) append.left_neutral append_eq_append_conv)
    have 5: "fst (find_0indegree_blocks al bl cl) \<noteq> None"
      using 4 topological_sort.simps[of al bl cl] "2.prems" False append_eq_append_conv2 by fastforce
    have 6: "length (bl@cl) = length (let x = find_0indegree_blocks al bl cl in 
      ((snd x)@(cl @ [the (fst x)])))"
      using find_0indegree_lemma4 5 by force
    have 7: "length (let x = find_0indegree_blocks al bl cl in snd x @ cl @ [the (fst x)]) = 
      length (let x = find_0indegree_blocks al bl cl in topological_sort al (snd x) (cl @ [the (fst x)]))"
      using 4 6 2(2) by presburger
    have 8: "(let x = find_0indegree_blocks al bl cl in 
      (topological_sort al (snd x) (cl @ [the (fst x)])) <~~> ((snd x)@(cl @ [the (fst x)])))"
      using 2(1) 3 7 by (metis case_prodI mem_Collect_eq perm_sym)
    have 9: "(bl@cl) <~~> (let x = find_0indegree_blocks al bl cl in 
      ((snd x)@(cl @ [the (fst x)])))"
      using find_0indegree_block_lemma2 find_0indegree_lemma4 5 perm_remove3  by (smt (verit, 
        del_insts) find_0indegree_lemma3 list.set_intros(1) option.collapse prod.exhaust_sel)
    then show ?thesis using 4 8 by (metis perm.trans perm_sym)
  qed
qed

lemma sort_perm: "loop_free bl \<Longrightarrow> bl <~~> sortDiag bl"
  using toposort_perm unfolding loop_free_def sortDiag_def
  by (metis append.right_neutral)

type_synonym timed_vars = "var \<Rightarrow> real \<Rightarrow> real"

type_synonym behav = "timed_vars \<Rightarrow> bool"

definition "internal bl = {x . (\<exists> A \<in> set bl . \<exists> B \<in> set bl . x \<in> set (get_outputs A) \<and> x \<in> set (get_inputs B))}"

\<comment> \<open>remove those vars in s in order to find the inputs and outputs for a diagram\<close>
primrec remove_set :: "var set \<Rightarrow> var list \<Rightarrow> var list" where 
"remove_set s [] = []" |
"remove_set s (v#vl) = (if (v \<in> s) then remove_set s vl else (v # remove_set s vl))"

primrec in_blocklist ::  "var set \<Rightarrow> block list \<Rightarrow> var list" where
"in_blocklist vs [] = []" |
"in_blocklist vs (b#bl) = (remove_set vs (get_inputs b)) @ (in_blocklist vs bl)"

\<comment> \<open>The input vars of a diagram\<close>
definition in_diag :: "block list \<Rightarrow> var list" where 
"in_diag bl = in_blocklist (internal bl) bl"

primrec out_blocklist ::  "var set \<Rightarrow> block list \<Rightarrow> var list" where
"out_blocklist vs [] = []" |
"out_blocklist vs (b#bl) = (remove_set vs (get_outputs b)) @ (out_blocklist vs bl)"

\<comment> \<open>The output vars of a digram\<close>
definition out_diag :: "block list \<Rightarrow> var list" where 
"out_diag bl = out_blocklist (internal bl) bl"

definition connected_blocks :: "block \<Rightarrow> block \<Rightarrow> bool" where
"connected_blocks a b = (if (set (get_outputs a) \<inter> set (get_inputs b) \<noteq> {}) \<or> (set (get_outputs b) \<inter> set (get_inputs a) \<noteq> {})
                           then True else False)"

\<comment> \<open>get those blocks whose sample_time = -1 \<close>
primrec get_inherited_blocks :: "block list \<Rightarrow> block list" where
"get_inherited_blocks [] = []" |
"get_inherited_blocks (b#bl) = (if (get_sample_time b = -1) then (b#(get_inherited_blocks bl)) else (get_inherited_blocks bl))"

\<comment> \<open>get those blocks whose sample_time \<noteq> -1 \<close>
primrec get_definite_blocks :: "block list \<Rightarrow> block list" where
"get_definite_blocks [] = []" |
"get_definite_blocks (b#bl) = (if (get_sample_time b \<noteq> -1) then (b#(get_definite_blocks bl)) else (get_definite_blocks bl))"

\<comment> \<open>The sample time of a variable is the same as the sample time of the corresponding block. \<close>
primrec sample_time_var :: "var \<Rightarrow> block list \<Rightarrow> sample_time" where
"sample_time_var x [] = -1" |
"sample_time_var x (b#bl) = (if ((x \<in> set (get_outputs b) \<or> x \<in> set (get_inputs b)) \<and> get_sample_time b \<noteq> -1)
                               then get_sample_time b else sample_time_var x bl)"

\<comment> \<open>True => the sample time of all the vars are unknown\<close>
primrec unknown_st_vars :: "var list \<Rightarrow> block list \<Rightarrow> bool" where
"unknown_st_vars [] bl =  True" |
"unknown_st_vars (a#al) bl = (if sample_time_var a bl \<noteq> -1 then False else unknown_st_vars al bl) "

fun gcd' :: "int \<Rightarrow> int \<Rightarrow> int" where
  "gcd' x y = (if x = 0 \<and> y = 0 then 0 else (if x = -1 then y else (if y = -1 then x
else gcd x y)))"

\<comment> \<open>This function is only used when the sample time of some var is known \<close>
primrec sample_time_vars :: "var list \<Rightarrow> block list \<Rightarrow> sample_time" where
"sample_time_vars [] bl = -1" |
"sample_time_vars (v # vl) bl = (if sample_time_var v bl = -1 then sample_time_vars vl bl 
                                    else gcd' (sample_time_var v bl) (sample_time_vars vl bl))"

definition update_sample_time :: "block \<Rightarrow> sample_time \<Rightarrow> block" where
"update_sample_time b s = Block (get_inputs b) (get_outputs b) (get_offsets b) s (get_outupd b)"

\<comment> \<open>compute the sample time of an inherited block from its inputs\<close>
primrec compute_st_forward :: "block list \<Rightarrow> block list \<Rightarrow> block list" where
"compute_st_forward []  bl = bl" |
"compute_st_forward (a # al) bl = (if (get_sample_time a = -1 \<and> \<not> unknown_st_vars (get_inputs a) bl) 
         then compute_st_forward al (bl@[update_sample_time a (sample_time_vars (get_inputs a) bl)]) 
         else compute_st_forward al (bl@[a]))"

\<comment> \<open>compute the sample time of an inherited block from its outputs backward (reverse blocks at first)\<close>
primrec compute_st_backward :: "block list \<Rightarrow> block list \<Rightarrow> block list" where
"compute_st_backward []  bl = bl" |
"compute_st_backward (a # al) bl = (if (get_sample_time a = -1 \<and> \<not> unknown_st_vars (get_outputs a) bl) 
         then compute_st_backward al (bl@[update_sample_time a (sample_time_vars (get_outputs a) bl)]) 
         else compute_st_backward al (bl@[a]))"

fun compSt :: "block list \<Rightarrow> block list \<Rightarrow> block list" where
"compSt al bl = compute_st_backward (get_inherited_blocks (compute_st_forward al bl)) 
  (get_definite_blocks (compute_st_forward al bl))"

end