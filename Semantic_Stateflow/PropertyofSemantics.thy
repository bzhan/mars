theory PropertyofSemantics
  imports Semantics_Final
begin

thm act_exec_actlist_exec_trans_exec_translist_exec_comp_exit_state_exit_pathlist_exit_comp_entry_state_entry_pathlist_entry_state_exec_comp_exec_pathlist_exec.induct

inductive_cases update_vals: "update_vals2 ([[a1_1, a1_2]]) ([[a2_1, a2_2]]) v1 v2"

inductive_cases act_exec_SkipE: "act_exec env SKIP e scr_p s1 s2 b"
inductive_cases act_exec_AssignE: "act_exec env (x ::= a) e scr_p (Status v1 I) s2 b"
inductive_cases act_exec_On1E: "act_exec env (on1 temporal_logic :: c) e src_p s1 s2 b"
inductive_cases act_exec_On2E: "act_exec env (on2 event :: c) e src_p s1 s2 b"
inductive_cases act_exec_Print1E: "act_exec env (Print1 a) e src_p (Status v1 I) s2 b"
inductive_cases act_exec_Print2E: "act_exec env (Print2 a) e src_p (Status v1 I) s2 b"
inductive_cases act_exec_Send1E: "act_exec env (send1 e False) e0 src_p (Status v1 I1) s2 b"
inductive_cases act_exec_Send2E: "act_exec env (send1 e True) e0 src_p (Status v1 I1) s2 b"
inductive_cases act_exec_Send3E: "act_exec env (send2 e False p) e0 src_p (Status v1 I1) s2 b"
inductive_cases act_exec_Send4E: "act_exec env (send2 e True p) e0 src_p (Status v1 I1) s2 b"
inductive_cases act_exec_Send5E: "act_exec env (send3 m) e0 src_p (Status v1 I1) s2 b"
inductive_cases act_exec_SeqE: "act_exec env (c1;c2) e src_p s1 s3 b"
inductive_cases act_exec_FunappE: "act_exec env (a1 ::= f<a2>) e src_p (Status v1 I1) s2 b"
inductive_cases act_exec_GrafunE: "act_exec env (a1 ::= f<<a2>>) e src_p (Status v1 I1) s2 b"

inductive_cases actlist_exec1: "actlist_exec env [] e src_p s1 s2 b"
inductive_cases actlist_exec2: "actlist_exec env (a#al) e src_p s1 s2 b"

inductive_cases trans_exec1:"trans_exec env t e src_p (Status v1 I1) s2 b a trg"

inductive_cases translist_exec_Termination: "translist_exec env [] e src_p s1 s2 n b ta trg p"
inductive_cases translist_exec_Fail: "translist_exec env [t] e src_p s1 s2 n b ta trg p"
inductive_cases translist_exec_Induction: "translist_exec env (t#T) e src_p s1 s2 n b ta trg p"

inductive_cases state_exit1: "state_exit env No_State e s1 s2 b"
inductive_cases state_exit2: "state_exit env ST e s1 s2 b"

inductive_cases comp_exit1: "comp_exit env No_Composition name e s1 s2 b"
inductive_cases comp_exit2: "comp_exit env C name e s1 s2 b"

inductive_cases emptylist_exit: "pathlist_exit env [] e f s1 s2 b"
inductive_cases pathlist_exit: "pathlist_exit env (pl@[p]) e f s1 s2 b"

inductive_cases state_entry1: "state_entry env No_State e p s1 s2 b"
inductive_cases state_entry2: "state_entry env ST e p s1 s2 b"

inductive_cases comp_entry1: "comp_entry env No_Composition name e p s1 s2 b"
inductive_cases comp_entry2: "comp_entry env C name e p s1 s2 b"

inductive_cases emptylist_entry: "pathlist_entry env [] f e p s1 s2 b"
inductive_cases pathlist_entry: "pathlist_entry env (str#sl) f e p s1 s2 b"

inductive_cases state_exec1: "state_exec env No_State e is_send s1 s2 b"
inductive_cases state_exec2: "state_exec env ST e is_send (Status v1 I1) s2 b"

inductive_cases comp_exec1: "comp_exec env No_Composition name e is_send s1 s2 b"
inductive_cases comp_exec2: "comp_exec env C name e is_send s1 s2 b"

inductive_cases emptylist_exec: "pathlist_exec env [] f e is_send s1 s2 b"
inductive_cases pathlist_exec: "pathlist_exec env (str#strl) f e is_send s1 s2 b"



thm update_vals2.induct

theorem update_vals_determine_aux : 
  "\<forall> v v1 v2. (update_vals2 a1 a2 v v1 \<longrightarrow>
    update_vals2 a1 a2 v v2 \<longrightarrow> v1 = v2)"
  apply auto
proof (induction a1 arbitrary: a2)
  case No_Expr
  then show ?case 
  proof -
      assume 1: "update_vals2 No_Expr a2 v v1" and
             2: "update_vals2 No_Expr a2 v v2"
      have 3: "update_vals2 No_Expr a2 v v1 \<Longrightarrow> v1 = v"
        apply(induct rule: update_vals2.cases, auto)
        done
      have 4: "update_vals2 No_Expr a2 v v2 \<Longrightarrow> v2 = v"
        apply(induct rule: update_vals2.cases, auto)
        done
      from 1 2 3 4 show ?thesis by auto
    qed 
next
  case (Concat x1 a1)
  then show ?case
  proof (cases a2)
    case No_Expr
    assume 1: "(\<And>a2 v v1 v2. update_vals2 a1 a2 v v1 \<Longrightarrow> update_vals2 a1 a2 v v2 \<Longrightarrow> v1 = v2)" 
         "update_vals2 ([[x1,a1]]) a2 v v1" "update_vals2 ([[x1,a1]]) a2 v v2" "a2 = No_Expr"
    have 2: "v1 = v2" 
    proof -
      from 1(2, 4) obtain n1: "v1 = v" by (induct rule: update_vals2.cases, auto)
      from 1(3, 4) obtain n2:  "v2 = v" by (induct rule: update_vals2.cases, auto)
      then show ?thesis using n1 n2 by auto
    qed
    show ?thesis using 2  by auto
  next
    case (Concat x21 x22)
    assume 21: "(\<And>a2 v v1 v2. update_vals2 a1 a2 v v1 \<Longrightarrow> update_vals2 a1 a2 v v2 \<Longrightarrow> v1 = v2)"
         "update_vals2 ([[x1,a1]]) a2 v v1"
         "update_vals2 ([[x1,a1]]) a2 v v2"
         "a2 = ([[x21,x22]])"
    have 22: "v1 = v2"
    proof -
      have 31: "(update_vals2 a1 x22 (update_vals1 x1 x21 v) v1)"
        using 21 update_vals2.simps
        by blast
      have 32:"(update_vals2 a1 x22 (update_vals1 x1 x21 v) v2)"
        using 21 update_vals2.simps
        by blast
      from 31 32 21(1) show ?thesis by auto
    qed 
  then show ?thesis by auto
  qed
qed


theorem update_vals_determine : 
  "(update_vals2 a1 a2 v v1 \<longrightarrow>
    update_vals2 a1 a2 v v2 \<longrightarrow> v1 = v2)"
  using update_vals_determine_aux by auto


lemma test1: "trans_exec env t e src_p s st2 b a trg \<longrightarrow> enable t e s src_p"
proof -
  have 1: "trans_exec env t e src_p s st2 b a trg \<Longrightarrow> enable t e s src_p"
    apply(induct rule: trans_exec.cases, auto)
    done
  show ?thesis
    apply auto using 1 by auto
qed

lemma transition_enable: "\<forall>st2 b a trg. trans_exec env t e src_p s st2 b a trg
  \<longrightarrow> enable t e s src_p "
    apply auto 
    subgoal for st2 b a trg
      using test1 by auto 
    done

theorem determine: 
  "(act_exec en a e s st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. act_exec en a e s st st2 con2 \<longrightarrow>
     st1 = st2 \<and> con1 = con2)) \<and>
   (actlist_exec en al e s st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. actlist_exec en al e s st st2 con2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2)) \<and>
   (trans_exec en t e s st st1 con1 a1 s1 \<longrightarrow>
    (\<forall>st2 con2 a2 s2. trans_exec en t e s st st2 con2 a2 s2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2 \<and> a1 = a2 \<and> s1 = s2)) \<and>
   (translist_exec en trl e s st st1 ts1 con1 ta1 s1 p1 \<longrightarrow>
    (\<forall>st2 ts2 con2 ta2 s2 p2. translist_exec en trl e s st st2 ts2 con2 ta2 s2 p2 \<longrightarrow>
    st1 = st2 \<and> ts1 = ts2 \<and> con1 = con2 \<and> ta1 = ta2 \<and> s1 = s2 \<and> p1 = p2)) \<and>
   (comp_exit en c p e st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. comp_exit en c p e st st2 con2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2)) \<and>
   (state_exit en ST e st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. state_exit en ST e st st2 con2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2)) \<and>
   (pathlist_exit en strl e sts st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. pathlist_exit en strl e sts st st2 con2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2)) \<and>
   (comp_entry en c p e ep st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. comp_entry en c p e ep st st2 con2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2)) \<and>
   (state_entry en ST e p st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. state_entry en ST e p st st2 con2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2)) \<and>
   (pathlist_entry en strl sts e p st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. pathlist_entry en strl sts e p st st2 con2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2)) \<and> 
   (state_exec en ST e iss st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. state_exec en ST e iss st st2 con2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2)) \<and>
   (comp_exec en c p e iss st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. comp_exec en c p e iss st st2 con2 \<longrightarrow>
     st1 = st2 \<and> con1 = con2)) \<and> 
   (pathlist_exec en strl sts e iss st st1 con1 \<longrightarrow>
    (\<forall>st2 con2. pathlist_exec en strl sts e iss st st2 con2 \<longrightarrow>
    st1 = st2 \<and> con1 = con2))"
proof (induct rule: act_exec_actlist_exec_trans_exec_translist_exec_comp_exit_state_exit_pathlist_exit_comp_entry_state_entry_pathlist_entry_state_exec_comp_exec_pathlist_exec.induct)
  case (Skip env e scr_p s)
  then show ?case
    apply (intro allI impI)
    apply (elim act_exec_SkipE)
    by auto
next
  case (Assign v1 h1 h2 h3 output1 output2 v2 x a src_p env e I)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_AssignE)
    using Assign by auto
next
  case (On1 temporal_logic s1 src_p env c e s2 b)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_On1E)
    using On1 apply simp
    by (simp add: On1.hyps(1))
next
  case (On2 temporal_logic s src_p env c e)
  show ?case 
    apply (intro allI impI)
    apply (elim act_exec_On1E)
    using On2 by auto
next
  case (On3 e event env c src_p s1 s2 b)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_On2E)
    using On3(3) apply simp
    using On3(1) apply simp
    done
next
  case (On4 e event env c src_p s)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_On2E)
    using On4 by auto
next
  case (Print1 v1 h1 h2 h3 output1 output2 v2 a env e src_p I)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_Print1E)
    using Print1 by auto
next
  case (Print2 v1 h1 h2 h3 output1 output2 v2 a src_p env e I)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_Print2E)
    using Print2 by auto
next
  case (Send1 env e v1 I1 v2 I2 b src_p b1 str1 str2 e0)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_Send1E)
    using Send1
    by (metis get_ctxt.simps information.inject)
next
  case (Send2 env e v1 I1 v2 I2 b src_p b1 str1 str2 b3 e0)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_Send2E)
    using Send2
    by (metis get_ctxt.simps information.inject)
next
  case (Send3 env p e v1 I1 v2 I2 b src_p b1 str1 str2 e0)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_Send3E)
    using Send3
    by (metis get_ctxt.simps information.inject)
next
  case (Send4 env p e v1 I1 v2 I2 b src_p b1 str1 str2 b3 e0)
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_Send4E)
    using Send4
    by (metis get_ctxt.simps information.inject)
next
  case (Send5 v1 h1 h2 h3 h4 output1 output2 env vname e src_p I)
  then show ?case
    apply (intro allI impI)
    apply (elim act_exec_Send5E)
    by auto
next
  case (Seq1 env c\<^sub>1 e src_p s1 s2 c\<^sub>2 s3 b)
  have a: "\<forall>st2. \<not> act_exec env c\<^sub>1 e src_p s1 st2 False"
      using Seq1(1,2) by auto
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_SeqE)
    using Seq1 apply simp
    using a by auto
next
  case (Seq2 env c\<^sub>1 e src_p s1 s2 c\<^sub>2)
  then show ?case
  apply (intro allI impI)
    apply (elim act_exec_SeqE)
    using Seq2 by auto
next
  case (Funapp fe env a2 f v1 v2 e src_p I1 v3 I2 a1 v4)
  have 1: "get_fenv env f = fe f"
    using Funapp by auto
  have 2: "\<forall>v2a. update_vals2 a2 (fst (snd (fe f))) v1 v2a \<longrightarrow> v2 = v2a"
    using Funapp(2) update_vals_determine[of a2 "(fst (snd (fe f)))" v1 v2]
    by auto
  have 3: "\<forall>v2. update_vals2 (snd (snd (fe f))) a1 v3 v2 \<longrightarrow> v4 = v2"
    using Funapp(5) update_vals_determine[of "(snd (snd (fe f)))" a1 v3 v4]
    by auto
  show ?case
    apply (intro allI impI)
    apply (elim act_exec_FunappE) using 1 apply simp
    using 2 3 Funapp(4) by auto
next
  case (Grafun ge env a2 f v1 v2 src_p I1 v3 I2 trg p a1 v4 e)
  have 1: "get_genv env f = ge f"
    using Grafun by auto
  have 2: "\<forall>v2a. update_vals2 a2 (fst (snd (ge f))) v1 v2a \<longrightarrow> v2a = v2"
    using Grafun(2) update_vals_determine[of a2 "(fst (snd (ge f)))" v1 v2]
    by auto
  have 3: "\<forall>v2. update_vals2 (snd (snd (ge f))) a1 v3 v2 \<longrightarrow> v2 = v4"
    using Grafun(5) update_vals_determine[of "(snd (snd (ge f)))" a1 v3 v4]
    by auto
  have tmp: "\<forall>v3a I2a st2 ts2 con2 ta2 s2 p2.
  st2 = (Status v3a I2a) \<longrightarrow> translist_exec env [fst (ge f)] [] src_p (Status v2 I1) st2 ts2 con2 ta2 s2
      p2 \<longrightarrow>
     v3a = v3 \<and> I2a = I2 \<and> - 1 = ts2 \<and> True = con2 \<and> [] = ta2 \<and> trg = s2 \<and> p = p2"
    apply(intro allI impI) 
    subgoal premises pre for v3a I2a st2 ts2 con2 ta2 s2 p2
    proof -
      have tmp1: "st2 = Status v3 I2"
        using Grafun(4) pre(2) by auto
      have tmp2: "v3a = v3 \<and> I2a = I2"
        using tmp1 pre(1) by auto
      have tmp3: "con2 = True"
        using Grafun(4) pre(2) by (metis)
      show ?thesis 
        using pre Grafun(4) tmp2 tmp3 by auto
    qed
    done
  have 4: "\<forall>v3a I2a trg' p' st2. 
st2 = (Status v3a I2a) \<longrightarrow> translist_exec env [fst (ge f)] [] src_p (Status v2 I1) (Status v3a I2a) (- 1)
        True [] trg' p' \<longrightarrow> v3a = v3 \<and> I2a = I2 \<and> trg' = trg \<and> p' = p"
    apply (intro allI impI) using tmp by auto
  show ?case 
    apply (intro allI impI)
    apply (elim act_exec_GrafunE) using 1 apply simp
    using 2 3 4 by auto
next
  case (ActionList_Execution1 env e src_p s)
  then show ?case 
    apply (intro allI impI)
    apply (elim actlist_exec1)
    by auto
next
  case (ActionList_Execution2 env a e src_p s1 s2 al s3 b)
  have 1: "\<forall>st2. \<not> act_exec env a e src_p s1 st2 False"
    using ActionList_Execution2(1,2) by auto
  show ?case
    apply (intro allI impI)
    apply (elim actlist_exec2)
    using ActionList_Execution2 apply simp
    using 1 by auto
next
  case (ActionList_Execution3 env a e src_p s1 s2 al)
  then show ?case
    apply (intro allI impI)
    apply (elim actlist_exec2)
    using ActionList_Execution3 by auto
next
  case (Trans_Execution1 t e v1 I1 src_p v2 I2 env v3 I3 a trg)
  have 1: "\<forall>v3a I3a. \<not> act_exec env (condition_action t) e src_p (update_status t (Status v1 I1))
        (Status v3a I3a) False"
    using Trans_Execution1(2,3,4) by auto
  show ?case 
    apply (intro allI impI)
    apply (elim trans_exec1)
    using Trans_Execution1 apply simp
    using 1 by auto
next
  case (Trans_Execution2 t e v1 src_p env I1 v2 I2)
  then show ?case
    apply (intro allI impI)
    apply (elim trans_exec1)
    using Trans_Execution2 by auto
next
  case (TLinduction t e s1 src_p s2 T env s3 n b A trg p)
  show ?case 
    apply(intro allI impI)
    apply(elim translist_exec_Induction)
    prefer 2 using TLinduction(3) apply simp
    using transition_enable[of env t e src_p s1]  TLinduction(1)
    apply auto using TLinduction by auto
next
  case (Fail t e s1 src_p s2 env)
  then show ?case
    apply(intro allI impI)
    apply(elim translist_exec_Fail) 
    using Fail apply simp
    using transition_enable[of env t e src_p s1] by auto
next
  case (Termination env e src_p s)
  then show ?case 
    apply(intro allI impI)
    apply(elim translist_exec_Termination) by auto
next
  case (ToState env t e src_p s1 s2 a trg p1 p T)
  show ?case 
    apply(intro allI impI) 
    apply(elim translist_exec_Induction)
    using ToState(1) transition_enable[of env t e src_p s1] apply simp
    using ToState(1) transition_enable[of env t e src_p s1] apply simp
    using ToState by auto
next
  case (ToHistoryJunction env t e src_p v1 I1 v2 I2 a trg p1 p str1 str2 T)
  show ?case
    apply(intro allI impI) 
    apply(elim translist_exec_Induction)
    using ToHistoryJunction(1) transition_enable[of env t e src_p "(Status v1 I1)"] apply simp
    using ToHistoryJunction(1) transition_enable[of env t e src_p "(Status v1 I1)"] apply simp
    using ToHistoryJunction by auto
next
  case (SrcInactive env t e src_p s1 s2 a trg T)
  show ?case
    apply(intro allI impI) 
    apply(elim translist_exec_Induction)
    using SrcInactive(1) transition_enable[of env t e src_p s1] apply simp
    using SrcInactive(1) transition_enable[of env t e src_p s1] apply simp
    using SrcInactive by auto
next
  case (ToJunctionInduction1 env t e src_p s1 s2 a str g s3 A trg2 p1 p2 T)
  show ?case
    apply(intro allI impI) 
    apply(elim translist_exec_Induction)
    using ToJunctionInduction1(1) transition_enable[of env t e src_p s1] apply simp
    using ToJunctionInduction1(1) transition_enable[of env t e src_p s1] apply simp
    
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction1(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction1(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction1(2) pre1 by auto
    qed
    
    subgoal premises pre2 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction1(2) pre2 by auto
      show ?thesis
        using ToJunctionInduction1(3,5,6) 1 pre2 by auto
    qed

    subgoal premises pre3 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction1(2) pre3 by auto
      show ?thesis
        using ToJunctionInduction1(3,5,6) 1 pre3 by(metis)
    qed

    subgoal premises pre4 for st2 ts2 con2 ta2 s2' p2a s2a a' str' s3a
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction1(2) pre4 by auto
      have 2 : "\<forall>n. translist_exec env (get_juncs env str') e src_p s2a s3a n True [] NONE [] \<longrightarrow> n = 1"
        using ToJunctionInduction1(3,5) 1 pre4(2) by auto
      show ?thesis
        using 2 pre4(2) by auto
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction1(2) pre5 by auto
      have 2 : "\<forall>n. translist_exec env (get_juncs env str') e src_p s2a st2 n True [] NONE [] \<longrightarrow> n = 1"
        using ToJunctionInduction1(3,5) 1 pre5(2) by auto
      show ?thesis
        using 2 pre5(7) by auto
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction1(2) pre5 by auto
      have 2 : "\<forall>n. translist_exec env (get_juncs env str') e src_p s2a st2 n True [] NONE [] \<longrightarrow> n = 1"
        using ToJunctionInduction1(3,5) 1 pre5(2) by auto
      show ?thesis
        using 2 pre5(7) by auto
    qed
    done
next
  case (ToJunctionInduction2 env t e src_p s1 s2 a str g s3 n A trg2 p T)
  show ?case
    apply(intro allI impI) 
    apply(elim translist_exec_Induction)
    using ToJunctionInduction2(1) transition_enable[of env t e src_p s1] apply simp
    using ToJunctionInduction2(1) transition_enable[of env t e src_p s1] apply simp
    
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction2(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction2(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction2(2) pre1 by auto
    qed
    
    subgoal premises pre2 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction2(2) pre2 by auto
      show ?thesis
        using ToJunctionInduction2(3,5) 1 pre2 by(metis)
    qed

    subgoal premises pre3 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction2(2) pre3 by auto
      show ?thesis
        using ToJunctionInduction2(3,5) 1 pre3 by(metis)
    qed

    subgoal premises pre4 for st2 ts2 con2 ta2 s2' p2a s2a a' str' s3a
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction2(2) pre4 by auto
      show ?thesis
        using ToJunctionInduction2(3,5) 1 pre4 by(metis)
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction2(2) pre5 by auto
      show ?thesis
        using ToJunctionInduction2(3,5) 1 pre5 by(metis)
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction2(2) pre5 by auto
      show ?thesis
        using ToJunctionInduction2(3,5) 1 pre5 by(metis)
    qed
    done
next
  case (ToJunctionInduction3 env t e src_p s1 s2 a str g s3 T s4 n1 b A trg2 p)
  show ?case
    apply(intro allI impI) 
    apply(elim translist_exec_Induction)
    using ToJunctionInduction3(1) transition_enable[of env t e src_p s1] apply simp
    using ToJunctionInduction3(1) transition_enable[of env t e src_p s1] apply simp
    
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction3(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction3(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction3(2) pre1 by auto
    qed
    
    subgoal premises pre2 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction3(2) pre2 by auto
      have 2 : "\<forall>n Aa s2 p1. translist_exec env (get_juncs env str') e src_p s2a st2 n True Aa s2 p1 \<longrightarrow> n = 0"
        using ToJunctionInduction3(3,5) 1 pre2(6) by auto
      show ?thesis
        using 2 pre2(6) by fastforce
    qed

    subgoal premises pre3 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction3(2) pre3 by auto
      show ?thesis
        using ToJunctionInduction3(3,5,6) 1 pre3 by(metis)
    qed

    subgoal premises pre4 for st2 ts2 con2 ta2 s2' p2a s2a a' str' s3a
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction3(2) pre4 by auto
      have 2 : "s3a = s3"
        using ToJunctionInduction3(3,5) 1 pre4(2) by auto
      show ?thesis
        using ToJunctionInduction3(8) 2 pre4(4) by auto
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      show ?thesis
        using ToJunctionInduction3(6) pre5 by auto
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction3(2) pre5 by auto
      have 2 : "\<forall>n. translist_exec env (get_juncs env str') e src_p s2a st2 n True [] NONE [] \<longrightarrow> n = 0"
        using ToJunctionInduction3(3,5) 1 pre5(2) by auto
      show ?thesis
        using 2 pre5(7) by auto
    qed
    done
next
  case (ToJunctionInduction4 env t e src_p s1 s2 a str g s3)
  show ?case
    apply(intro allI impI) 
    apply(elim translist_exec_Induction)
    using ToJunctionInduction4(1) transition_enable[of env t e src_p s1] apply simp
    using ToJunctionInduction4(1) transition_enable[of env t e src_p s1] apply simp
    
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction4(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction4(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction4(2) pre1 by auto
    qed
    
    subgoal premises pre2 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction4(2) pre2 by auto
      have 2 : "\<forall>n Aa s2 p1. translist_exec env (get_juncs env str') e src_p s2a st2 n True Aa s2 p1 \<longrightarrow> n = 0"
        using ToJunctionInduction4(3,5) 1 pre2(2) by auto
      show ?thesis
        using 2 pre2(6) by fastforce
    qed

    subgoal premises pre3 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction4(2) pre3 by auto
      show ?thesis
        using ToJunctionInduction4(3,5) 1 pre3 by(metis)
    qed

    subgoal premises pre4 for st2 ts2 con2 ta2 s2' p2a s2a a' str' s3a
    proof -
      show ?thesis
      using pre4 by auto
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction4(2) pre5 by auto
      have 2 : "s3 = st2"
        using ToJunctionInduction4(3,5) 1 pre5(7) by auto
      show ?thesis
        using 2 pre5 by auto
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction4(2) pre5 by auto
      have 2 : "\<forall>n. translist_exec env (get_juncs env str') e src_p s2a st2 n True [] NONE [] \<longrightarrow> n = 0"
        using ToJunctionInduction4(3,5) 1 pre5(2) by auto
      show ?thesis
        using 2 pre5(7) by auto
    qed
    done
next
  case (ToJunctionInduction5 env t e src_p s1 s2 a str g s3 T)
  show ?case
    apply(intro allI impI) 
    apply(elim translist_exec_Induction)
    using ToJunctionInduction5(1) transition_enable[of env t e src_p s1] apply simp
    using ToJunctionInduction5(1) transition_enable[of env t e src_p s1] apply simp
    
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction5(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction5(2) pre1 by auto
    qed
    subgoal premises pre1
    proof -
      show ?thesis
        using ToJunctionInduction5(2) pre1 by auto
    qed
    
    subgoal premises pre2 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction5(2) pre2 by auto
      have 2 : "\<forall>n Aa s2 p1. translist_exec env (get_juncs env str') e src_p s2a st2 n True Aa s2 p1 \<longrightarrow> n = -1"
        using ToJunctionInduction5(3,5) 1 pre2(2) by auto
      show ?thesis
        using 2 pre2(6) by fastforce
    qed

    subgoal premises pre3 for st2 ts2 con2 ta2 s2' p2a s2a a' str' Aa p1'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction5(2) pre3 by auto
      show ?thesis
        using ToJunctionInduction5(3,5) 1 pre3 by(metis)
    qed

    subgoal premises pre4 for st2 ts2 con2 ta2 s2' p2a s2a a' str' s3a
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction5(2) pre4 by auto
      have 2 : "\<forall>n. translist_exec env (get_juncs env str') e src_p s2a s3a n True [] NONE [] \<longrightarrow> n = -1"
        using ToJunctionInduction5(3,5) 1 pre4(2) by auto
      show ?thesis
        using 2 pre4(2) by auto
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction5(2) pre5 by auto
      have 2 : "\<forall>n. translist_exec env (get_juncs env str') e src_p s2a st2 n True [] NONE [] \<longrightarrow> n = -1"
        using ToJunctionInduction5(3,5) 1 pre5(2) by auto
      show ?thesis
        using 2 pre5(7) by auto
    qed
    subgoal premises pre5 for st2 ts2 con2 ta2 s2' p2a s2a a' str'
    proof -
      have 1 : "s2a = s2 \<and> a' = a \<and> str' = str"
        using ToJunctionInduction5(2) pre5 by auto
      have 2 : "s3 = st2"
        using ToJunctionInduction5(3,5) 1 pre5(7) by auto
      show ?thesis
        using 2 pre5 by auto
    qed
    done
next
  case (State_Exit1 ST name a1 a2 a3 tl1 tl2 C I1 env e v1 s2 v3 I3 b1 str1 str2 I4)
  have 1: "\<forall>st2 .
       comp_exit env C name e (Status v1 I1) st2 True \<longrightarrow> s2 = st2"
    using State_Exit1(4) by auto
  have 2: "\<forall>st2. \<not> comp_exit env C name e (Status v1 I1) st2 False"
    using State_Exit1(4) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exit2)
    using State_Exit1(1,2,3) 1 apply auto
    subgoal premises pre1 for con2 s2a v3a I3 b1 str1 str2
    proof-
      have 1:"s2a = s2"
        using pre1(3,7) by auto
      show ?thesis
        using pre1(4) State_Exit1(6) 1 by auto
    qed
    subgoal premises pre2 for con2 s2a v3a I3' b1' str1' str2'
    proof -
      have 1:"s2a = s2"
        using pre2(3,7) by auto
      have 2: "I3' = I3"
        using pre2(4) State_Exit1(6,7,8) 1 by auto
      have 3: "str1' = str1 \<and> str2' = str2"
        using pre2(5) 2 State_Exit1(7) by auto
      show ?thesis
        using State_Exit1(8) 2 3 by auto
    qed
    using 2 apply simp
    subgoal premises pre3 for st2 con2 s2a
    proof - 
      have 1: "s2a = s2"
        using pre3(3,6) by auto
      have 2: "\<not> act_exec env a3 e name s2a st2 False"
        using State_Exit1(6) 1 by auto
      show ?thesis
        using pre3(4) 2 by auto
    qed
    done
next
  case (State_Exit2 env e s)
  then show ?case 
    apply(intro allI impI)
    apply(elim state_exit1)
    by auto
next
  case (State_Exit3 ST name a1 a2 a3 tl1 tl2 C I env e v)
  show ?case
    apply(intro allI impI)
    apply(elim state_exit2)
    using State_Exit3 by auto
next
  case (State_Exit4 ST name a1 a2 a3 tl1 tl2 C I1 env e v1 s2)
  have 1: "\<forall>s2. \<not> comp_exit env C name e (Status v1 I1) s2 True"
    using State_Exit4(4) by auto
  show ?case 
    apply(intro allI impI)
    apply(elim state_exit2)
    using State_Exit4(1, 2) 1 apply auto
    using State_Exit4(4) by auto
next
  case (State_Exit5 ST name a1 a2 a3 tl1 tl2 C I1 env e v1 s2 s3)
  have 1: "\<forall>st2. \<not> comp_exit env C name e (Status v1 I1) st2 False"
    using State_Exit5(4) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exit2)
    using State_Exit5(1, 2) apply auto
      prefer 2 using 1 apply simp
    subgoal premises pre1 for con2 s2' v3 I3 b1 str1 str2
    proof -
      have 1:"s2' = s2"
        using pre1(3) State_Exit5(4) by auto
      have 2: "\<not> act_exec env a3 e name s2' (Status v3 I3) True"
        using State_Exit5(6) 1 by auto
      show ?thesis
        using pre1(4) 2 by auto
    qed
    subgoal premises pre1 for st2 con2 s2'
    proof -
      have 1:"s2' = s2"
        using pre1(3) State_Exit5(4) by auto
      show ?thesis
        using pre1(4) 1 State_Exit5(6)  by auto
    qed
    done
next
  case (No_Composition_Exit env name e s)
  then show ?case 
    apply(intro allI impI)
    apply(elim comp_exit1)
    by auto
next
  case (Or_Exit1 C TL b f I1 name b1 str1 str2 env e v1 v2 I2 str2' I3)
  show ?case
    apply(intro allI impI)
    apply(elim comp_exit2)
    using Or_Exit1 by auto
next
  case (Or_Exit2 C TL b f I1 name b1 str1 str2 env e v1 s2)
  have 1 : "\<forall>v2 I2. \<not>state_exit env (f str1) e (Status v1 I1) (Status v2 I2) True"
    using Or_Exit2(4) by auto
  show ?case
    apply(intro allI impI)
    apply(elim comp_exit2)
    using Or_Exit2(1,2) apply auto
    using 1 apply simp
    using Or_Exit2(4) by auto
next
  case (Empty_List_Exit env e f s)
  then show ?case
    apply(intro allI impI)
    apply(elim emptylist_exit)
    by auto
next
  case (List_Exit1 env f str e s1 s2 sl s3 b)
  have 1 : "\<forall>st2. \<not>state_exit env (f str) e s1 st2 False"
    using List_Exit1(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim pathlist_exit)
     prefer 2 using 1 apply simp
    using List_Exit1(2,4) by auto
next
  case (List_Exit2 env f str e s1 s2 sl)
  show ?case
    apply(intro allI impI)
    apply(elim pathlist_exit)
    using List_Exit2 by auto
next
  case (And_Exit1 C sl f env e s1 v2 I2 name)
  show ?case
    apply(intro allI impI)
    apply(elim comp_exit2)
    using And_Exit1 by auto
next
  case (And_Exit2 C sl f env e s1 s2 name)
  have 1 : "\<forall>v2 I2. \<not>pathlist_exit env sl e f s1 (Status v2 I2) True"
    using And_Exit2(3) by auto
  show ?case
    apply(intro allI impI)
    apply(elim comp_exit2)
    using And_Exit2(1) apply auto
    using 1 apply simp
    using And_Exit2(3) by auto
next
  case (State_Entry1 ST name a1 a2 a3 tl1 tl2 C v1 h1 h2 h3 h4 output1 output2 v2 I1 b1 str1 str2 b1' str1' str2' I_tmp I2 env e v3 I3 p v4 I4 b)
  have 1 : "\<forall>st2. \<not>act_exec env a1 e name
        (Status (Vals h1 (h2(name := \<lambda>str. 0)) (h3(name := 0)) h4 (output1, output2))
          (I1(name := Info True str1 str2,
              Semantics_Final.butlast name :=
                Info True (Semantics_Final.last name) str2')))
        st2 False"
    using State_Entry1(3,6,7,9) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_entry2)
    using State_Entry1(1,2,3,4,5,6,7) apply auto
         prefer 5 using 1 apply simp
        prefer 5 using 1 apply simp
    using State_Entry1(9,11) by auto
next
  case (State_Entry2 env e p s)
  then show ?case
    apply(intro allI impI)
    apply(elim state_entry1)
    by auto
next
  case (State_Entry3 ST name a1 a2 a3 tl1 tl2 C v1 h1 h2 h3 h4 output1 output2 v2 I1 b1 str1 str2 b1' str1' str2' I_tmp I2 env e s3 p)
  have 1: "\<forall>v3 I3. \<not>act_exec env a1 e name
        (Status (Vals h1 (h2(name := \<lambda>str. 0)) (h3(name := 0)) h4 (output1, output2))
          (I1(name := Info True str1 str2,
              Semantics_Final.butlast name :=
                Info True (Semantics_Final.last name) str2')))
        (Status v3 I3) True"
    using State_Entry3(3,6,7,9) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_entry2)
    using State_Entry3(1,2,3,4,5,6,7) apply auto
    using 1 apply simp
    using 1 apply simp
    using State_Entry3(9) by auto
next
  case (No_Composition_Entry env name e p s)
  then show ?case
    apply(intro allI impI)
    apply(elim comp_entry1)
    by auto
next
  case (Or_Entry1 C TL b f p env e name s1 s2 n A trg p1 p0 s3 s4 b2)
  have 1 : "\<forall>st2 ts2 A' trg' p1'. \<not> translist_exec env TL e name s1 st2 ts2 False A' trg' p1'"
    using Or_Entry1(5) by (metis)
  show ?case
    apply(intro allI impI)
    apply(elim comp_entry2)
    using Or_Entry1(1) apply simp
            prefer 4 using Or_Entry1(1,3) apply simp
           prefer 4 using Or_Entry1(2) apply simp
          prefer 4 using Or_Entry1(1,3) apply simp
    prefer 4 using Or_Entry1(1,3) apply simp
        prefer 4 using Or_Entry1(1,3) apply simp
       prefer 4 using Or_Entry1(1) apply simp
    using Or_Entry1(1,2,3) apply auto
    using 1 apply auto
        prefer 5
    subgoal premises pre1 for st2 con2 ba s2' n' A' p1 p0
    proof -
      have 1: "A' = A \<and> s2' = s2"
        using Or_Entry1(5) pre1(3) by auto
      have 2 : "\<not> actlist_exec env A' e name s2' st2 False"
        using Or_Entry1(8) 1 by auto
      show ?thesis
        using pre1(4) 2 by auto
    qed
       prefer 4
    subgoal premises pre2 for st2 con2 ba s2' n' A' p1 p0
    proof -
      have 1: "A' = A \<and> s2' = s2"
        using Or_Entry1(5) pre2(3) by auto
      have 2 : "\<not> actlist_exec env A' e name s2' st2 False"
        using Or_Entry1(8) 1 by auto
      show ?thesis
        using pre2(4) 2 by auto
    qed
    subgoal premises pre3 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A' = A \<and> s2' = s2 \<and> P p0 = P p0'"
        using Or_Entry1(5,6) pre3(2) by auto
      have 2: "p0 = p0'"
        using 1 by auto
      have 3: "s3' = s3"
        using Or_Entry1(8) pre3(3) 1 by auto
      show ?thesis
        using Or_Entry1(10) pre3(4) 2 3 by auto
    qed
    subgoal premises pre4 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A' = A \<and> s2' = s2 \<and> P p0 = P p0'"
        using Or_Entry1(5,6) pre4(2) by auto
      have 2: "p0 = p0'"
        using 1 by auto
      have 3: "s3' = s3"
        using Or_Entry1(8) pre4(3) 1 by auto
      show ?thesis
        using Or_Entry1(10) pre4(4,8) 2 3 by(metis)
    qed
    subgoal premises pre5 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A' = A \<and> s2' = s2 \<and> P p0 = P p0'"
        using Or_Entry1(5,6) pre5(2) by auto
      have 2: "p0 = p0'"
        using 1 by auto
      have 3: "s3' = s3"
        using Or_Entry1(8) pre5(3) 1 by auto
      show ?thesis
        using Or_Entry1(10) pre5(4,8) 2 3 by(metis)
    qed
    done
next
  case (Or_Entry2 C TL b f p env e name s1 s2 n A trg p1)
  have 1 : "\<forall>st2 ts2 A' trg' p1'. \<not> translist_exec env TL e name s1 st2 ts2 True A' trg' p1'"
    using Or_Entry2(5) by (metis)
  show ?case
    apply(intro allI impI)
    apply(elim comp_entry2)
    using Or_Entry2(1) apply simp
            prefer 4 using Or_Entry2(1,2,3) apply simp
    prefer 4 using Or_Entry2(1,2,3) apply simp
    prefer 4 using Or_Entry2(1,2,3) apply simp
    prefer 4 using Or_Entry2(1,2,3) apply simp
    prefer 4 using Or_Entry2(1,2,3) apply simp
       prefer 4 using Or_Entry2(1,2,3) apply simp
    using 1 Or_Entry2(1,2,3) apply auto
    using Or_Entry2(5) by auto
next
  case (Or_Entry3 C TL b f p env e name s1 s2 n A trg p1 p0 s3)
  have 1 : "\<forall>st2 ts2 A' trg' p1'. \<not> translist_exec env TL e name s1 st2 ts2 False A' trg' p1'"
    using Or_Entry3(5) by (metis)
  show ?case
    apply(intro allI impI)
    apply(elim comp_entry2)
    using Or_Entry3(1) apply simp
            prefer 4 using Or_Entry3(1,2,3) apply simp
    prefer 4 using Or_Entry3(1,2,3) apply simp
    prefer 4 using Or_Entry3(1,2,3) apply simp
    prefer 4 using Or_Entry3(1,2,3) apply simp
    prefer 4 using Or_Entry3(1,2,3) apply simp
       prefer 4 using Or_Entry3(1,2,3) apply simp
    using Or_Entry3(1,2,3) 1 apply auto
    subgoal premises pre1 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A' = A \<and> s2' = s2"
        using Or_Entry3(5,6) pre1(2) by auto
      have 2: "\<not> actlist_exec env A' e name s2' s3' True"
        using Or_Entry3(8) 1 by auto
      show ?thesis
        using pre1(3) 2 by auto
    qed

    subgoal premises pre2 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A' = A \<and> s2' = s2"
        using Or_Entry3(5,6) pre2(2) by auto
      have 2: "\<not> actlist_exec env A' e name s2' s3' True"
        using Or_Entry3(8) 1 by auto
      show ?thesis
        using pre2(3) 2 by auto
    qed
    using Or_Entry3(5,8) by auto
next
  case (Or_Entry5 C TL b f p str2 name I1 env e v1 s2 b2)
  have 1: "get_Info3 (I1 name) \<noteq> []"
    using Or_Entry5 by auto
  show ?case
    apply(intro allI impI)
    apply(elim comp_entry2)
    using Or_Entry5(1) apply simp
    using Or_Entry5(1,2,3) apply simp
    using Or_Entry5(1,2,3) apply simp
    using Or_Entry5(1,2,3) apply simp
         prefer 2 using Or_Entry5(1,2,3) apply simp
    prefer 2 using 1 apply simp
    prefer 4 using Or_Entry5(1,2,3) apply simp
      prefer 2 using 1 apply simp
     prefer 2 using 1 apply simp
    using Or_Entry5 by auto
next
  case (Or_Entry7 C TL b f p env e s1 s2 b2 name)
  show ?case
    apply(intro allI impI)
    apply(elim comp_entry2)
    using Or_Entry7(1) apply simp
    using Or_Entry7(1,2) apply simp
    using Or_Entry7(1,2) apply simp
    using Or_Entry7(1,2) apply simp
    using Or_Entry7(1,2) apply simp
        prefer 2 using Or_Entry7(1,2) apply simp
    prefer 2 using Or_Entry7(1,2) apply simp
    prefer 2 using Or_Entry7(1,2) apply simp
     prefer 2 using Or_Entry7(1,2) apply simp
    using Or_Entry7 by auto
next
  case (Or_Entry8 C TL b f p str2 name I1 env e v1 s2 n A trg p1 p0 s3 s4 b2)
  have 1: "get_Info3 (I1 name) = []"
    using Or_Entry8(4,5) by auto
  have 2: "\<forall>st2 n A trg p1. \<not>translist_exec env TL e name (Status v1 I1) st2 n False A trg p1"
    using Or_Entry8(7) by(metis)
  show ?case
    apply(intro allI impI)
    apply(elim comp_entry2)
    using Or_Entry8(1,2,3) apply simp
    using Or_Entry8(1,2,3) apply simp
    using Or_Entry8(1,2,3) apply simp
    using Or_Entry8(1,2,3) apply simp
         prefer 2 using Or_Entry8(1,2,3) apply simp
        prefer 5 using Or_Entry8(1,2,3) apply simp
    using 1 apply simp
    using Or_Entry8(1,2,3,4,5) 1 2 apply auto
        prefer 4
    subgoal premises pre1 for st2 con2 ba s2' n' A' p1' p0'
    proof -
      have 1: "A = A' \<and> s2 = s2'"
        using Or_Entry8(7) pre1(4) by auto
      have 2: "\<not>actlist_exec env A' e name s2' st2 False"
        using Or_Entry8(10) 1 by auto
      show ?thesis
        using pre1(5) 2 by auto
    qed
       prefer 4
    subgoal premises pre2 for st2 con2 ba s2' n' A' p1' p0'
    proof -
      have 1: "A = A' \<and> s2 = s2'"
        using Or_Entry8(7) pre2(4) by auto
      have 2: "\<not>actlist_exec env A' e name s2' st2 False"
        using Or_Entry8(10) 1 by auto
      show ?thesis
        using pre2(5) 2 by auto
    qed
    subgoal premises pre3 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A = A' \<and> s2 = s2' \<and> P p0 = P p0'"
        using Or_Entry8(7,8) pre3(3) by auto
      have 2: "p0 = p0'"
        using 1 by auto
      have 3: "s3 = s3'"
        using Or_Entry8(10) pre3(4) 1 by auto
      show ?thesis
        using pre3(5) Or_Entry8(12) 2 3 by auto
    qed
    subgoal premises pre4 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A = A' \<and> s2 = s2' \<and> P p0 = P p0'"
        using Or_Entry8(7,8) pre4(3) by auto
      have 2: "p0 = p0'"
        using 1 by auto
      have 3: "s3 = s3'"
        using Or_Entry8(10) pre4(4) 1 by auto
      show ?thesis
        using pre4 Or_Entry8(12) 2 3 by(metis)
    qed
    subgoal premises pre5 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A = A' \<and> s2 = s2' \<and> P p0 = P p0'"
        using Or_Entry8(7,8) pre5(3) by auto
      have 2: "p0 = p0'"
        using 1 by auto
      have 3: "s3 = s3'"
        using Or_Entry8(10) pre5(4) 1 by auto
      show ?thesis
        using pre5(5) Or_Entry8(12) 2 3 by auto
    qed
    done
next
  case (Or_Entry9 C TL b f p str2 name I1 env e v1 s2 n A trg p1)
  have 1: "get_Info3 (I1 name) = []"
    using Or_Entry9(4,5) by auto
  have 2: "\<forall>st2 n A trg p1. \<not>translist_exec env TL e name (Status v1 I1) st2 n True A trg p1"
    using Or_Entry9(7) by(metis)
  show ?case
    apply(intro allI impI)
    apply(elim comp_entry2)
    using Or_Entry9(1) apply simp
    using Or_Entry9(1,2,3) apply simp
    using Or_Entry9(1,2,3) apply simp
    using Or_Entry9(1,2,3) apply simp
    using Or_Entry9(1,2,3) apply simp
    prefer 2 using Or_Entry9(1,2,3) apply simp
        prefer 5 using Or_Entry9(1,2,3) apply simp
    using 1 apply simp
    using Or_Entry9(1,2,3,4,5) 1 apply auto
    using 2 apply auto
    using Or_Entry9(7) by auto
next
  case (Or_Entry10 C TL b f p str2 name I1 env e v1 s2 n A trg p1 p0 s3)
  have 1: "get_Info3 (I1 name) = []"
    using Or_Entry10(4,5) by auto
  have 2: "\<forall>st2 n A trg p1. \<not>translist_exec env TL e name (Status v1 I1) st2 n False A trg p1"
    using Or_Entry10(7) by(metis)
  show ?case
    apply(intro allI impI)
    apply(elim comp_entry2)
    using Or_Entry10(1) apply simp
    using Or_Entry10(1,2,3) apply simp
    using Or_Entry10(1,2,3) apply simp
    using Or_Entry10(1,2,3) apply simp
         prefer 2 using Or_Entry10(1,2,3) apply simp
        prefer 5 using Or_Entry10(1,2,3) apply simp
    using 1 apply simp
    using Or_Entry10(1,2,3,4,5) 1 2 apply auto
    subgoal premises pre1 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A = A' \<and> s2 = s2'"
        using Or_Entry10(7) pre1(3) by auto
      have 2: "\<not>actlist_exec env A' e name s2' s3' True"
        using Or_Entry10(10) 1 by auto
      show ?thesis
        using pre1(4) 2 by auto
    qed
    subgoal premises pre2 for st2 con2 ba s2' n' A' p1' p0' s3'
    proof -
      have 1: "A = A' \<and> s2 = s2'"
        using Or_Entry10(7) pre2(3) by auto
      have 2: "\<not>actlist_exec env A' e name s2' s3' True"
        using Or_Entry10(10) 1 by auto
      show ?thesis
        using pre2(4) 2 by auto
    qed
    using Or_Entry10(7,8,10) by auto
next
  case (Empty_List_Entry env f e p s)
  then show ?case
    apply(intro allI impI)
    apply(elim emptylist_entry)
    by auto
next
  case (Path_List_Entry1 str p env f e s1 s2 sl s3 b)
  have 1: "\<forall>st2. \<not>state_entry env (f (Semantics_Final.hd p)) e p s1 st2 False"
    using Path_List_Entry1(1,3) by auto
  show ?case
    apply(intro allI impI)
    apply(elim pathlist_entry)
       prefer 3 using Path_List_Entry1(1) apply simp
      prefer 3 using Path_List_Entry1(1) apply simp
     prefer 2 using 1 apply simp
    using Path_List_Entry1(3,5) by auto
next
  case (Path_List_Entry2 str p env f e s1 s2 sl)
  have 1: "\<forall>st2. \<not>state_entry env (f (Semantics_Final.hd p)) e p s1 st2 True"
    using Path_List_Entry2(1,3) by auto
  show ?case
    apply(intro allI impI)
    apply(elim pathlist_entry)
       prefer 3 using Path_List_Entry2(1) apply simp
      prefer 3 using Path_List_Entry2(1) apply simp
    using 1 apply simp
    using Path_List_Entry2 by auto
next
  case (Path_List_Entry4 str p env f e s1 s2 sl s3 b)
  have 1: "\<forall>s2. \<not>state_entry env (f str) e [] s1 s2 False"
    using Path_List_Entry4(1,3) by auto
  show ?case
    apply(intro allI impI)
    apply(elim pathlist_entry)
    using Path_List_Entry4(1) apply simp
    using Path_List_Entry4(1) apply simp
     prefer 2 using 1 apply simp
    using Path_List_Entry4(3,5) by auto
next
  case (Path_List_Entry5 str p env f e s1 s2 sl)
  have 1: "\<forall>s2. \<not>state_entry env (f str) e [] s1 s2 True"
    using Path_List_Entry5(1,3) by auto
  show ?case
    apply(intro allI impI)
    apply(elim pathlist_entry)
    using Path_List_Entry5(1) apply simp
    using Path_List_Entry5(1) apply simp
    using 1 apply simp
    using Path_List_Entry5(3) by auto
next
  case (And_Entry C sl f1 env e p s1 s2 b name)
  show ?case
    apply(intro allI impI)
    apply(elim comp_entry2)
    using And_Entry(1) apply auto
    using And_Entry(2,3) by auto
next
  case (No_Composition_Execution env name e is_send s)
  then show ?case
    apply(intro allI impI)
    apply(elim comp_exec1)
    by auto
next
  case (No_State_Execution env e is_send s)
  then show ?case
    apply(intro allI impI)
    apply(elim state_exec1)
    by auto
next
  case (Inactive_State_Execution ST name a1 a2 a3 tl1 tl2 C I env e is_send v)
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Inactive_State_Execution by auto
next
  case (Outer_Trans_Execution1 ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env v3 I2 A trg path p ex_ST v4 I3 v5 I4 en_ST p1 v6 I5 b)
  have 1: "get_Info1 (I1 name)"
    using Outer_Trans_Execution1(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Outer_Trans_Execution1(1) apply simp
    using Outer_Trans_Execution1(1) 1 apply simp
    prefer 2 
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' trg' path'
      proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
     (Status
       (Vals h1'
         (h2''
          (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4
         (output1', output2'))
       I1)
     (Status v3' I2') n' False A' trg' path'"
        using Outer_Trans_Execution1(8) 1 2 by(metis)
      show ?thesis
        using 1 3 pre1(5) by auto
    qed
            prefer 2
    subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> path' = path"
        using Outer_Trans_Execution1(8) 1 2 pre2(5) by auto
      have 4 : "\<not> comp_exit env
     (FindComposition1
       (if name' = path' then Semantics_Final.butlast name' else lca name' path')
       (get_root env))
     (if name' = path' then Semantics_Final.butlast name' else lca name' path') e
     (Status v3' I2') (Status v4' I3') False"
        using Outer_Trans_Execution1(10,12) pre2(6) 1 3 by auto
      show ?thesis
        using 4 pre2(6) by auto
    qed
           prefer 2
    subgoal premises pre3 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' v5' I4'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre3 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> path' = path \<and> A' = A"
        using Outer_Trans_Execution1(8) 1 2 pre3(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Outer_Trans_Execution1(10,12) 1 3 pre3(6) by auto
      have 5 : "\<not>actlist_exec env A' e name' (Status v4' I3') (Status v5' I4') False"
        using Outer_Trans_Execution1(14) 1 3 4 by auto
      show ?thesis
        using 5 pre3 by auto
    qed
    subgoal premises pre4 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' v5' I4' v6a I5a
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre4 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> path' = path \<and> A' = A \<and> P p' = P p"
        using Outer_Trans_Execution1(8,9) 1 2 pre4(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Outer_Trans_Execution1(10,12) 1 3 pre4(5) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4)"
        using Outer_Trans_Execution1(14) 1 3 4 pre4(6) by auto
      have 6 : "p' = p"
        using 3 by auto
      have 7 : "(Status v6a I5a) = (Status v6 I5) \<and> con2' = b"
        using Outer_Trans_Execution1(15,16,18) pre4(7) 1 3 5 6 by auto
      show ?thesis
        using pre4(2) 7 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' v5' I4' v6a I5a v7 I6 v8 I7
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution1(8,9) 1 2 pre5(4) by auto
      show ?thesis
        using 3 pre5(5) by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution1(8,9) 1 2 pre5(5) by auto
      show ?thesis
        using 3 pre5(6) by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' v5' I4' A2 path p v6a I5a 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution1(8,9) 1 2 pre5 by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' v5' I4' A2 path p v6a I5a 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution1(8,9) 1 2 pre5 by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' v5' I4' A2 path p v6a 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution1(8,9) 1 2 pre5 by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' s2' n' A' path' p' v4' I3' v5' I4' A2 path p v6a I5a 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution1(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution1(8,9) 1 2 pre5 by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    done
next
  case (Outer_Trans_Termination ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env v3 I2 n A trg path)
  have 1: "get_Info1 (I1 name)"
    using Outer_Trans_Termination(2) by auto
  show ?case
  apply(intro allI impI)
    apply(elim state_exec2)
    using Outer_Trans_Termination(1) apply simp
    using Outer_Trans_Termination(1) 1 apply simp
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' v5' I4' v6a I5a
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2')) 
           I1)
         (Status v3' I2') 1 True A' (P p') path'"
        using Outer_Trans_Termination(8) 1 2 pre1(4) by(metis)
      show ?thesis
        using 3 pre1(4) by auto
    qed
    subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' trg' path' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2)"
        using Outer_Trans_Termination(8) 1 2 pre2 by auto
      show ?thesis
        using 3 pre2 by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1)
         (Status v3' I2') 1 True A' (P p') path'"
        using Outer_Trans_Termination(8) 1 2 pre1(4) by(metis)
      show ?thesis
        using 3 pre1 by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1)
         (Status v3' I2') 1 True A' (P p') path'"
        using Outer_Trans_Termination(8) 1 2 pre1(4) by(metis)
      show ?thesis
        using 3 pre1 by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' trg' path' p' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1)
         (Status v3' I2') n' True A' trg' path'"
        using Outer_Trans_Termination(8) 1 2 pre1(4) by(metis)
      show ?thesis
        using 3 pre1 by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' trg' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1)
         (Status v3' I2') n' True A' trg' path'"
        using Outer_Trans_Termination(8) 1 2 pre1(4) by(metis)
      show ?thesis
        using 3 pre1 by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' trg' path' p' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1)
         (Status v3' I2') n' True A' trg' path'"
        using Outer_Trans_Termination(8) 1 2 pre1(4) by(metis)
      show ?thesis
        using 3 pre1 by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' trg' path' p' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1)
         (Status v3' I2') n' True A' trg' path'"
        using Outer_Trans_Termination(8) 1 2 pre1(4) by(metis)
      show ?thesis
        using 3 pre1 by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' trg' path' p' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1)
         (Status v3' I2') n' True A' trg' path'"
        using Outer_Trans_Termination(8) 1 2 pre1(4) by(metis)
      show ?thesis
        using 3 pre1 by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' s2' n' A' trg' path' p' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1)
         s2' n' True A' trg' path'"
        using Outer_Trans_Termination(8) 1 2 pre1(4) by(metis)
      show ?thesis
        using 3 pre1 by auto
    qed
    done
next
  case (Outer_Trans_Execution2 ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env v3 I2 A trg path p ex_ST v4 I3)
  have 1: "get_Info1 (I1 name)"
    using Outer_Trans_Execution2(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Outer_Trans_Execution2(1) apply simp
    using Outer_Trans_Execution2(1) 1 apply simp
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' v5' I4' v6a I5a
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : " (Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> path' = path"
        using Outer_Trans_Execution2(8) 1 2 pre1(4) by auto
      have 4 : "\<not> comp_exit env
     (FindComposition1
       (if name' = path' then Semantics_Final.butlast name' else lca name' path')
       (get_root env))
     (if name' = path' then Semantics_Final.butlast name' else lca name' path') e
     (Status v3' I2') (Status v4' I3') True"
        using Outer_Trans_Execution2(10,12) pre1(5) 1 3 by auto
      show ?thesis
        using 4 pre1(5) by auto
    qed
    subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' trg' path'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1) (Status v3' I2') n' False A' trg' path'"
        using Outer_Trans_Execution2(8) 1 2 pre2(4) by(metis)
      show ?thesis
        using 3 pre2 by auto
    qed
    subgoal premises pre3 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre3 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> path' = path"
        using Outer_Trans_Execution2(8) 1 2 pre3(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3) "
        using Outer_Trans_Execution2(10,12) pre3(6) 1 3 by auto
      show ?thesis
        using 4 pre3 by auto
    qed
    subgoal premises pre4 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre4 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4' 
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> path' = path"
        using Outer_Trans_Execution2(8) 1 2 pre4(5) by auto
      have 4 : "\<not> comp_exit env (FindComposition1
       (if name' = path' then Semantics_Final.butlast name' else lca name' path')
       (get_root env))
     (if name' = path' then Semantics_Final.butlast name' else lca name' path') e
     (Status v3' I2') (Status v4' I3') True"
        using Outer_Trans_Execution2(10,12) pre4(6) 1 3 by auto
      show ?thesis
        using 4 pre4 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution2(8) 1 2 pre5(4) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution2(8) 1 2 pre5(5) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution2(8) 1 2 pre5(5) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution2(8) 1 2 pre5(5) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution2(8) 1 2 pre5(5) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' s2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution2(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution2(8) 1 2 pre5(4) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    done
next
  case (Outer_Trans_Execution3 ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env v3 I2 A trg path p ex_ST v4 I3 v5 I4)
  have 1: "get_Info1 (I1 name)"
    using Outer_Trans_Execution3(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Outer_Trans_Execution3(1) apply simp
    using Outer_Trans_Execution3(1) 1 apply simp
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' v5' I4' v6a I5a
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> path' = path"
        using Outer_Trans_Execution3(8) 1 2 pre1(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Outer_Trans_Execution3(10,12) pre1(5) 1 3 by auto
      have 5 : "\<not>actlist_exec env A' e name' (Status v4' I3') (Status v5' I4') True"
        using Outer_Trans_Execution3(14) pre1(6) 1 3 4 by auto
      show ?thesis
        using 5 pre1(6) by auto
    qed
    subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' trg' path'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "\<not>translist_exec env tl2' e name'
         (Status (Vals h1' (h2'' (name' := (h2'' name')
                 (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
             (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
             (output1', output2'))
           I1) (Status v3' I2') n' False A' trg' path'"
        using Outer_Trans_Execution3(8) 1 2 by(metis)
      show ?thesis
        using 3 pre2(5) by auto
    qed
    subgoal premises pre3 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre3 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> path' = path"
        using Outer_Trans_Execution3(8) 1 2 pre3(5) by auto
      show ?thesis
        using Outer_Trans_Execution3(10,12) pre3(6) 1 3 by auto
    qed
    subgoal premises pre4 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' v5' I4'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre4 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> path' = path"
        using Outer_Trans_Execution3(8) 1 2 pre4(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Outer_Trans_Execution3(10,12) pre4(6) 1 3 by auto
      have 5 : "(Status v5' I4') = (Status v5 I4)"
        using Outer_Trans_Execution3(14) pre4(7) 1 3 4 by auto
      show ?thesis
        using 5 pre4 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution3(8) 1 2 pre5(4) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution3(8) 1 2 pre5(5) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution3(8) 1 2 pre5(5) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution3(8) 1 2 pre5(5) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution3(8) 1 2 pre5(5) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' s2' n' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Outer_Trans_Execution3(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Outer_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "n' = 1"
        using Outer_Trans_Execution3(8) 1 2 pre5(4) by auto
      show ?thesis
        using 3 pre5 by auto
    qed
    done
next
  case (Inner_Trans_Execution1 ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env v3 I2 n A trg1 path1 v4 I3 v5 I4 A2 trg2 path p ex_ST v6 I5 v7 I6 p1 p2 v8 I7 b)
  have 1: "get_Info1 (I1 name)"
    using Inner_Trans_Execution1(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Inner_Trans_Execution1(1) apply simp
    using Inner_Trans_Execution1(1) 1 apply simp
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution1(8,9) 1 2 pre1(4) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution1(8,9) 1 2 pre1(5) by(metis)
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution1(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution1(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6' v8' I7'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution1(8) 1 2 pre2(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution1(11) 1 3 pre2(6) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Inner_Trans_Execution1(13,14) 1 4 pre2(7) by auto
      have 6 : "(Status v6' I5') = (Status v6 I5)"
        using Inner_Trans_Execution1(15,17) 1 5 pre2(8) by auto
      have 7 : "(Status v7' I6') = (Status v7 I6)"
        using Inner_Trans_Execution1(19) 1 5 6 pre2(9) by auto
      have 8 : "(Status v8' I7') = (Status v8 I7) \<and> con2' = b"
        using Inner_Trans_Execution1(20,21,23) 1 5 7 pre2(10) by auto
      show ?thesis
        using 8 pre2 by auto
    qed
    subgoal premises pre3 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre3 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2)"
        using Inner_Trans_Execution1(8) 1 2 pre3(5) by auto
      show ?thesis
        using Inner_Trans_Execution1(11) 1 3 pre3(7) by auto
    qed
    subgoal premises pre4 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' 
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre4 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution1(8) 1 2 pre4(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution1(11) 1 3 pre4(7) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Inner_Trans_Execution1(13,14) 1 4 pre4(8) by auto
      show ?thesis
        using Inner_Trans_Execution1(15,17) 1 5 pre4(9) by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution1(8) 1 2 pre5(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution1(11) 1 3 pre5(7) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Inner_Trans_Execution1(13,14) 1 4 pre5(8) by auto
      have 6 : "(Status v6' I5') = (Status v6 I5)"
        using Inner_Trans_Execution1(15,17) 1 5 pre5(9) by auto
      show ?thesis
        using Inner_Trans_Execution1(19) 1 5 6 pre5(10) by auto
    qed
    subgoal premises pre6 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' 
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre6 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution1(8) 1 2 pre6(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution1(11) 1 3 pre6(7) by auto
      show ?thesis
        using Inner_Trans_Execution1(13,14) 1 3 4 pre6(8) by(metis)
    qed
    subgoal premises pre7 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' s2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution1(1,2,3,4,5,6) pre7 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution1(3,4,5,6) 1 by auto
      have 3 : "s2' = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution1(8) 1 2 pre7(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution1(11) 1 3 pre7(6) by auto
      have 5 : "n2' = 1"
        using Inner_Trans_Execution1(13,14) 1 4 pre7(7) by auto
      show ?thesis
        using 5 pre7(8) by auto
    qed
    done
next
  case (Inner_Trans_Execution2 ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env v3 I2 n A trg1 path1 v4 I3)
   have 1: "get_Info1 (I1 name)"
    using Inner_Trans_Execution2(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Inner_Trans_Execution2(1) apply simp
    using Inner_Trans_Execution2(1) 1 apply simp
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution2(8,9) 1 2 pre1(4) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution2(8,9) 1 2 pre1(5) by(metis)
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution2(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution2(8,9) 1 2 pre1(5) by auto
    qed
     subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6' v8' I7'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution2(8) 1 2 pre2(4) by auto
      show ?thesis
        using Inner_Trans_Execution2(11) 1 3 pre2(6) by auto
    qed
    subgoal premises pre3 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre3 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2)"
        using Inner_Trans_Execution2(8) 1 2 pre3(5) by auto
      show ?thesis
        using Inner_Trans_Execution2(11) 1 3 pre3(2,3,7) by auto
    qed
    subgoal premises pre4 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' 
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre4 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution2(8) 1 2 pre4(5) by auto
      show ?thesis
        using Inner_Trans_Execution2(11) 1 3 pre4(2,3,7) by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution2(8) 1 2 pre5(5) by auto
      show ?thesis
        using Inner_Trans_Execution2(11) 1 3 pre5(2,3,7) by auto
    qed
    subgoal premises pre6 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre6 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution2(8) 1 2 pre6(5) by auto
      show ?thesis
        using Inner_Trans_Execution2(11) 1 3 pre6(2,3,7) by auto
    qed
    subgoal premises pre7 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' s2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution2(1,2,3,4,5,6) pre7 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution2(3,4,5,6) 1 by auto
      have 3 : "s2' = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution2(8) 1 2 pre7(4) by auto
      show ?thesis
        using Inner_Trans_Execution2(11) 1 3 pre7(6) by auto
    qed
    done
next
  case (Inner_Trans_Execution3 ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env v3 I2 n A trg1 path1 v4 I3 v5 I4 A2 trg2 path p ex_ST v6 I5)
  have 1: "get_Info1 (I1 name)"
    using Inner_Trans_Execution3(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Inner_Trans_Execution3(1) apply simp
    using Inner_Trans_Execution3(1) 1 apply simp
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution3(8,9) 1 2 pre1(4) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution3(8,9) 1 2 pre1(5) by(metis)
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution3(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution3(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6' v8' I7'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution3(8) 1 2 pre2(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution3(11) 1 3 pre2(6) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Inner_Trans_Execution3(13,14) 1 4 pre2(7) by auto
      show ?thesis
        using Inner_Trans_Execution3(15,17) 1 3 5 pre2(8) by(metis)
    qed
    subgoal premises pre3 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre3 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2)"
        using Inner_Trans_Execution3(8) 1 2 pre3(5) by auto
      show ?thesis
        using Inner_Trans_Execution3(11) 1 3 pre3(2,3,7) by auto
    qed
    subgoal premises pre4 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' 
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre4 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution3(8) 1 2 pre4(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution3(11) 1 3 pre4(7) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Inner_Trans_Execution3(13,14) 1 4 pre4(8) by auto
      have 6 : "(Status v6' I5') = (Status v6 I5)"
        using Inner_Trans_Execution3(15,17) 1 3 5 pre4(9) by auto
      show ?thesis
        using 6 pre4 by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution3(8) 1 2 pre5(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution3(11) 1 3 pre5(7) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Inner_Trans_Execution3(13,14) 1 4 pre5(8) by auto
      show ?thesis
        using Inner_Trans_Execution3(15,17) 1 3 5 pre5(9) by(metis)
    qed
    subgoal premises pre6 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre6 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution3(8) 1 2 pre6(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution3(11) 1 3 pre6(7) by auto
      show ?thesis
        using Inner_Trans_Execution3(13,14) 1 4 pre6(8) by(metis)
    qed
    subgoal premises pre7 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' s2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution3(1,2,3,4,5,6) pre7 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution3(3,4,5,6) 1 by auto
      have 3 : "s2' = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution3(8) 1 2 pre7(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution3(11) 1 3 pre7(6) by auto
      have 5 : "n2' = 1"
        using Inner_Trans_Execution3(13) 1 3 4 pre7(7) by auto
      show ?thesis
        using 5 pre7(8) by auto
    qed
    done
next
  case (Inner_Trans_Execution4 ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env v3 I2 n A trg1 path1 v4 I3 v5 I4 A2 trg2 path p ex_ST v6 I5 v7 I6)
  have 1: "get_Info1 (I1 name)"
    using Inner_Trans_Execution4(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Inner_Trans_Execution4(1) apply simp
    using Inner_Trans_Execution4(1) 1 apply simp
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution4(8,9) 1 2 pre1(4) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution4(8,9) 1 2 pre1(5) by(metis)
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution4(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Execution4(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6' v8' I7'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution4(8) 1 2 pre2(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution4(11) 1 3 pre2(6) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Inner_Trans_Execution4(13,14) 1 4 pre2(7) by auto
      have 6 : "(Status v6' I5') = (Status v6 I5)"
        using Inner_Trans_Execution4(15,17) 1 3 5 pre2(8) by auto
      show ?thesis
        using Inner_Trans_Execution4(19) 1 5 6 pre2(9) by(metis)
    qed
    subgoal premises pre3 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre3 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2)"
        using Inner_Trans_Execution4(8) 1 2 pre3(5) by auto
      show ?thesis
        using Inner_Trans_Execution4(11) 1 3 pre3(2,3,7) by auto
    qed
    subgoal premises pre4 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' 
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre4 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution4(8) 1 2 pre4(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution4(11) 1 3 pre4(7) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Inner_Trans_Execution4(13,14) 1 4 pre4(8) by auto
      show ?thesis
        using Inner_Trans_Execution4(15,17) 1 3 5 pre4(9) by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution4(8) 1 2 pre5(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution4(11) 1 3 pre5(7) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Inner_Trans_Execution4(13,14) 1 4 pre5(8) by auto
      have 6 : "(Status v6' I5') = (Status v6 I5)"
        using Inner_Trans_Execution4(15,17) 1 3 5 pre5(9) by auto
      have 7 : "(Status v7' I6') = (Status v7 I6)"
        using Inner_Trans_Execution4(19) 1 3 5 6 pre5(10) by auto
      show ?thesis
        using 7 pre5 by auto
    qed
    subgoal premises pre6 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre6 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution4(8) 1 2 pre6(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution4(11) 1 3 pre6(7) by auto
      show ?thesis
        using Inner_Trans_Execution4(13,14) 1 4 pre6(8) by(metis)
    qed
    subgoal premises pre7 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' s2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Execution4(1,2,3,4,5,6) pre7 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Execution4(3,4,5,6) 1 by auto
      have 3 : "s2' = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Execution4(8) 1 2 pre7(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Execution4(11) 1 3 pre7(6) by auto
      have 5 : "n2' = 1"
        using Inner_Trans_Execution4(13) 1 3 4 pre7(7) by auto
      show ?thesis
        using 5 pre7(8) by auto
    qed
    done
next
  case (Inner_Trans_Termination ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env v3 I2 n A trg1 path1 v4 I3 v5 I4 n2 A2 trg2 path)
  have 1: "get_Info1 (I1 name)"
    using Inner_Trans_Termination(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Inner_Trans_Termination(1) apply simp
    using Inner_Trans_Termination(1) 1 apply simp
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Termination(8,9) 1 2 pre1(4) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Termination(8,9) 1 2 pre1(5) by(metis)
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Termination(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      show ?thesis
        using Inner_Trans_Termination(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6' v8' I7'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Termination(8) 1 2 pre2(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Termination(11) 1 3 pre2(6) by auto
      show ?thesis
        using Inner_Trans_Termination(13) 1 3 4 pre2(7) by(metis)
    qed
    subgoal premises pre3 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre3 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2)"
        using Inner_Trans_Termination(8) 1 2 pre3(5) by auto
      show ?thesis
        using Inner_Trans_Termination(11) 1 3 pre3(2,3,7) by auto
    qed
    subgoal premises pre4 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre4 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Termination(8) 1 2 pre4(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Termination(11) 1 3 pre4(7) by auto
      show ?thesis
        using Inner_Trans_Termination(13) 1 3 4 pre4(8) by(metis)
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Termination(8) 1 2 pre5(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Termination(11) 1 3 pre5(7) by auto
      show ?thesis
        using Inner_Trans_Termination(13) 1 4 pre5(8) by(metis)
    qed
    subgoal premises pre6 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre6 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Termination(8) 1 2 pre6(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Termination(11) 1 3 pre6(7) by auto
      show ?thesis
        using Inner_Trans_Termination(13) 1 3 4 pre6 by auto
    qed
    subgoal premises pre7 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' s2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Inner_Trans_Termination(1,2,3,4,5,6) pre7 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Inner_Trans_Termination(3,4,5,6) 1 by auto
      have 3 : "s2' = (Status v3 I2) \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Inner_Trans_Termination(8) 1 2 pre7(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Inner_Trans_Termination(11) 1 3 pre7(6) by auto
      show ?thesis
        using Inner_Trans_Termination(13) 1 3 4 pre7(7) by(metis)
    qed
    done
next
  case (Fail_Trans_Execution ST1 name a1 a2 a3 tl1 tl2 C I1 v1 h1 h2 h3 h4 output1 output2 h2' e h3' is_send v2 env s2 n1 A trg1 path1 v4 I3 v5 I4 n2 A2 trg2 path v6 I5 b)
  have 1: "get_Info1 (I1 name)"
    using Fail_Trans_Execution(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim state_exec2)
    using Fail_Trans_Execution(1) apply simp
    using Fail_Trans_Execution(1) 1 apply simp
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      show ?thesis
        using Fail_Trans_Execution(8,9) 1 2 pre1(4) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' n' A' path' p' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      show ?thesis
        using Fail_Trans_Execution(8,9) 1 2 pre1(5) by(metis)
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      show ?thesis
        using Fail_Trans_Execution(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre1 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' output1' output2' v3' I2' A' path' p' v4' I3' 
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre1 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      show ?thesis
        using Fail_Trans_Execution(8,9) 1 2 pre1(5) by auto
    qed
    subgoal premises pre2 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6' v8' I7'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre2 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = s2 \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Fail_Trans_Execution(8) 1 2 pre2(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Fail_Trans_Execution(11) 1 3 pre2(6) by auto
      show ?thesis
        using Fail_Trans_Execution(13,14) 1 4 pre2(7) by auto
    qed
    subgoal premises pre3 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre3 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = s2"
        using Fail_Trans_Execution(8) 1 2 pre3(5) by auto
      show ?thesis
        using Fail_Trans_Execution(11) 1 3 pre3(2,3,7) by auto
    qed
    subgoal premises pre4 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4' 
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre4 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = s2 \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Fail_Trans_Execution(8) 1 2 pre4(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Fail_Trans_Execution(11) 1 3 pre4(7) by auto
      show ?thesis
        using Fail_Trans_Execution(13,14) 1 4 pre4(8) by auto
    qed
    subgoal premises pre5 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' A2' path' p' v6' I5' v7' I6'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre5 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = s2 \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Fail_Trans_Execution(8) 1 2 pre5(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Fail_Trans_Execution(11) 1 3 pre5(7) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4) \<and> A2' = A2 \<and> P p' = P p \<and> path' = path"
        using Fail_Trans_Execution(13,14) 1 4 pre5(8) by auto
      show ?thesis
        using Fail_Trans_Execution(13,14) 1 4 pre5(8) by auto
    qed
    subgoal premises pre6 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' v3' I2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre6 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      have 3 : "(Status v3' I2') = s2 \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Fail_Trans_Execution(8) 1 2 pre6(5) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Fail_Trans_Execution(11) 1 3 pre6(7) by auto
      show ?thesis
        using Fail_Trans_Execution(13,14) 1 4 pre6(8) by(metis)
    qed
    subgoal premises pre7 for st2' con2' name' a1' a2' a3' tl1' tl2' C' h1' h2'' h3'' h4'
output1' output2' s2' n' A' trg1' path1' v4' I3' v5' I4' n2' A2' path' p' v6' I5'
    proof -
      have 1 : "name' = name \<and> a1' = a1 \<and> a2' = a2 \<and> a3' = a3 \<and> tl1' = tl1
              \<and> tl2' = tl2 \<and> C' = C \<and> h1' = h1 \<and> h2'' = h2 \<and> h3'' = h3 \<and> h4' = h4
              \<and> output1' = output1 \<and> output2' = output2"
        using Fail_Trans_Execution(1,2,3,4,5,6) pre7 by auto
      have 2 : " Vals h1' (h2'' (name' := (h2'' name')
             (e := h2'' name' e + 1, ''tick'' := h2'' name' ''tick'' + 1)))
         (if is_send then h3'' else h3''(name' := h3'' name' + 1)) h4'
         (output1', output2') = v2"
        using Fail_Trans_Execution(3,4,5,6) 1 by auto
      have 3 : "s2' = s2 \<and> A' = A \<and> trg1' = trg1 \<and> path1' = path1"
        using Fail_Trans_Execution(8) 1 2 pre7(4) by auto
      have 4 : "(Status v4' I3') = (Status v4 I3)"
        using Fail_Trans_Execution(11) 1 3 pre7(6) by auto
      have 5 : "(Status v5' I4') = (Status v5 I4)"
        using Fail_Trans_Execution(13) 1 3 4 pre7(7) by auto
      show ?thesis
        using Fail_Trans_Execution(16) 1 5 pre7 by auto
    qed
    done
next
  case (Or_Execution C TL b f I1 str1 name env e is_send v1 s2 b1)
  show ?case
    apply(intro allI impI)
    apply(elim comp_exec2)
    using Or_Execution(1) apply simp
      prefer 2 using Or_Execution(2) apply simp
     prefer 2 using Or_Execution(1) apply simp
    using Or_Execution by auto
next
  case (Start_Execution I1 SC C env e v1 s2 b1 name is_send)
  show ?case
    apply(intro allI impI)
    apply(elim comp_exec2)
    using Start_Execution(1) apply simp
    using Start_Execution(2) apply simp
     prefer 2 using Start_Execution(2) apply simp
    using Start_Execution by auto 
next
  case (Empty_Pathlist_Execution env f e is_send s)
  then show ?case
    apply(intro allI impI)
    apply(elim emptylist_exec)
    by auto
next
  case (Pathlist_Execution1 env f str e is_send s1 s2 strl s3 b)
  have 1: "\<forall>st2. \<not>state_exec env (f str) e is_send s1 st2 False"
    using Pathlist_Execution1(2) by auto
  show ?case
    apply(intro allI impI)
    apply(elim pathlist_exec)
    prefer 2 using 1 apply simp
    using Pathlist_Execution1 by auto
next
  case (Pathlist_Execution2 env f str e is_send s1 s2 strl)
  show ?case
    apply(intro allI impI)
    apply(elim pathlist_exec)
    using Pathlist_Execution2 by auto
next
  case (And_Execution C strl f env e is_send s1 s2 b name)
  show ?case
    apply(intro allI impI)
    apply(elim comp_exec2)
    using And_Execution(1) apply simp
    using And_Execution(1) apply simp
    using And_Execution(2) apply simp
    using And_Execution by auto
qed 
  


end