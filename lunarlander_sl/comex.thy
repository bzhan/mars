theory comex
  imports newParallel 

begin



locale comex =
  fixes t1 :: real  
  fixes t2 :: real  
  fixes t3 :: real 
  fixes p :: "real \<Rightarrow> real"
  assumes t1: "t1 > 1"
  assumes t2: "t2 > 1"
  assumes t3: "t3 > 1"
begin
definition T :: char where "T = CHR ''t''"
definition A :: char where "A = CHR ''a''"
definition B :: char where "B = CHR ''b''"
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"

lemma vars_distinct [simp]: "T \<noteq> X" "T \<noteq> Y" "T \<noteq> A" "T \<noteq> B" 
                            "X \<noteq> T" "X \<noteq> Y" "X \<noteq> A" "X \<noteq> B" 
                            "Y \<noteq> T" "Y \<noteq> X" "Y \<noteq> A" "Y \<noteq> B" 
                            "A \<noteq> T" "A \<noteq> X" "A \<noteq> Y" "A \<noteq> B" 
                            "B \<noteq> T" "B \<noteq> X" "B \<noteq> Y" "B \<noteq> A" 
                            
  unfolding T_def X_def Y_def A_def B_def by auto


definition Control :: proc where
  "Control =   
Rep(
  IChoice (Wait (\<lambda> t. t1)) (Wait (\<lambda> t. t2));
  Cm (''P2C''[?]X);
  Cm (''C2P''[!](\<lambda> s. p (s X) ));
  Cm (''C2P''[!](\<lambda> s. p (s X) ))
) "

inductive C_inv_ind :: " real list \<Rightarrow> tassn" where
  "C_inv_ind [] []"
| "(Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})
@\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = x)) ''P2C''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P'') tr1
\<Longrightarrow> C_inv_ind list tr2 \<Longrightarrow> C_inv_ind (x#list) (tr1@tr2)"

lemma C_inv_snoc:
"C_inv_ind fcs tr1 \<Longrightarrow> 
(Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})
@\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = x)) ''P2C''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P'') tr2
\<Longrightarrow> C_inv_ind (fcs@[x]) (tr1@tr2)"
proof (induct rule: C_inv_ind.induct)
  case 1
    then show ?case 
      using C_inv_ind.intros(2)[of x tr2 "[]" "[]"]
      using C_inv_ind.intros(1) by auto
  next
  case (2 x' tr1 list tr)
    then show ?case 
      using C_inv_ind.intros(2)[of x' tr1 "list@[x]" "tr@tr2"]
      by auto
qed

lemma C_inv_prop0:
"C_inv_ind [] = emp\<^sub>t"
using C_inv_ind.cases 
apply(auto simp add: emp_assn_def)
using C_inv_ind.intros(1) by blast




lemma C_inv_prop1:
"C_inv_ind (x#list) = Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})
@\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = x)) ''P2C''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P'' @\<^sub>t C_inv_ind (list)"
  apply(rule ext)
  subgoal for tr
  proof-
    have 1:"C_inv_ind (x # list) tr \<Longrightarrow> \<exists> tr1 tr2.(Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})
@\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = x)) ''P2C''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P'') tr1 \<and> C_inv_ind (list) tr2 \<and> tr = tr1@tr2"
    apply(rule local.C_inv_ind.cases[of "(x # list)" "tr"])
      by auto
    have 2:"C_inv_ind (x # list) tr \<Longrightarrow> ((Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})
@\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = x)) ''P2C''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P'') @\<^sub>t C_inv_ind (list)) tr "
  using 1
  by(auto simp add:join_assn_def)
  have 3:"((Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})
@\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = x)) ''P2C''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P'') @\<^sub>t C_inv_ind (list)) tr 
\<Longrightarrow> \<exists> tr1 tr2. ((Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})
@\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = x)) ''P2C''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P'') tr1 \<and> C_inv_ind (list) tr2 \<and> tr = tr1 @ tr2)"
    by(auto simp add:join_assn_def)
  have 4:"((Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})
@\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = x)) ''P2C''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P'') @\<^sub>t C_inv_ind (list)) tr 
\<Longrightarrow> C_inv_ind (x#list) tr"
  subgoal premises pre
proof-
  obtain tr1 and tr2 where g:"(Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})
@\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = x)) ''P2C''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P''
@\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p x)) ''C2P'') tr1" "C_inv_ind (list) tr2" "tr = tr1@tr2"
    using 3 pre by auto
  then have "C_inv_ind (x#list) tr"
    using C_inv_ind.intros(2)[of x tr1 list tr2] by auto
  then show ?thesis by auto
qed
  done
   then show ?thesis using 2 4 by(auto simp add: join_assoc)
  qed
  done
  
    

lemma C_rep:
  "\<Turnstile> {\<lambda>s tr. s X = x \<and> emp\<^sub>t tr}
    Control
   {\<lambda>s tr. \<exists>Fc . s X = last (x#Fc) \<and> C_inv_ind Fc tr}"
  unfolding Control_def
  apply(rule Valid_weaken_pre)
   prefer 2
   apply(rule Valid_rep)
   prefer 2
  subgoal
    apply(simp add:entails_def)
    apply clarify
    apply(rule exI[where x="[]"])
    apply (auto simp add: C_inv_ind.intros emp_assn_def)
    done
  apply(rule Valid_ex_pre)
  subgoal for Fc
    apply(rule Valid_seq)
     apply(rule Valid_ichoice_sp)
      apply(rule Valid_wait_sp)
     apply(rule Valid_wait_sp)
    apply(rule Valid_weaken_pre[where P'="\<lambda>s tr. s X = last (x # Fc) \<and> (C_inv_ind Fc @\<^sub>t Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> t. t > 1) ({}, {})) tr"])
    subgoal 
      using t1 t2
      apply(auto simp add:entails_def pure_assn_def conj_assn_def join_assn_def wait_assn.simps wait_inv_assn.simps)
      by fastforce+
    apply(rule Valid_seq)
     apply(rule Valid_receive_sp)
    apply(rule Valid_ex_pre)
    subgoal for px
      apply(rule Valid_ex_pre)
      subgoal for nx
    apply(rule Valid_seq)
     apply(rule Valid_send_sp)
    apply(rule Valid_strengthen_post)
     prefer 2
     apply(rule Valid_send_sp)
    apply(simp add: entails_def pure_assn_def conj_assn_def)
        apply(rule conjI)
        subgoal apply clarify
          subgoal for S tr
            apply(rule exI[where x="Fc@[S X]"])
            apply (auto simp add: join_assn_def)
            subgoal premises pre for tr5 tr4 tr1 tr3 tr2
            proof-
              have 1:"Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = S X)) ''P2C'' tr3"
                using pre(8)
                by(auto simp add: in_assn.simps in_inv_assn.simps srb2gsrb.simps)
              have 2:"Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p(S X))) ''C2P'' tr4"
                using pre(6)
                by(auto simp add: out_assn.simps out_inv_assn.simps srb2gsrb.simps)
              have 3:"Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p(S X))) ''C2P'' tr5"
                using pre(4)
                by(auto simp add: out_assn.simps out_inv_assn.simps srb2gsrb.simps)
              show ?thesis 
                using C_inv_snoc[of "[]" "tr1" "S X" "tr2 @ tr3 @ tr4 @ tr5"]
                using pre 1 2 3 
                apply(auto simp add: join_assn_def) by blast
            qed
            done
          done
        subgoal apply clarify
          subgoal for S tr
            apply(rule exI[where x="Fc@[S X]"])
            apply (auto simp add: join_assn_def)
            subgoal premises pre for tr5 tr4 tr1 tr3 tr2
            proof-
              have 1:"Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = S X)) ''P2C'' tr3"
                using pre(8)
                by(auto simp add: in_assn.simps in_inv_assn.simps srb2gsrb.simps)
              have 2:"Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p(S X))) ''C2P'' tr4"
                using pre(6)
                by(auto simp add: out_assn.simps out_inv_assn.simps srb2gsrb.simps)
              have 3:"Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = p(S X))) ''C2P'' tr5"
                using pre(4)
                by(auto simp add: out_assn.simps out_inv_assn.simps srb2gsrb.simps)
              show ?thesis 
                using C_inv_snoc[of "Fc" "tr1" "S X" "tr2 @ tr3 @ tr4 @ tr5"]
                using pre 1 2 3 
                apply(auto simp add: join_assn_def) by blast
            qed
            done
          done
        done
      done
    done
  done

            
        
        






definition Plant :: proc where
  "Plant =   
Rep(
 Cont (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * s X ^ 2 , Y := \<lambda> s. s B * s Y * s X , T := \<lambda> s. 1))) (\<lambda>s. s T < 1);
Interrupt (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * s X ^ 2 , Y := \<lambda> s. s B * s Y * s X , T := \<lambda> s. 1))) ((\<lambda>_. True))
      [(''P2C''[!](\<lambda>s. s X), Cm (''C2P''[?]A); Cm (''C2P''[?]B); T ::= (\<lambda>_.0))]
)"

definition inv :: "state \<Rightarrow> bool" where 
"inv s = (s X + s Y = 0)"


inductive P_inv_ind :: "real \<Rightarrow> real \<Rightarrow> (real \<times> real) list \<Rightarrow> tassn" where
  "P_inv_ind a b [] []"
| " a = b \<longrightarrow> (
  (Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {}) 
  @\<^sub>t WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C''
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'') tr1 
     \<and> P_inv_ind a' b' Fcs tr2) \<Longrightarrow> P_inv_ind a b ((a',b')#Fcs) (tr1@tr2)"

inductive same_pair :: "(real \<times> real) list \<Rightarrow> bool" where
  "same_pair []"
| " a = b \<Longrightarrow> same_pair Fcs \<Longrightarrow>same_pair ((a,b)#Fcs)"

inductive_cases same_pair_elim: "same_pair l"

lemma same_pair_prop0:
  "same_pair [(a,b)] \<Longrightarrow> a = b" 
  "a = b \<Longrightarrow> same_pair [(a,b)]"
  using same_pair.cases same_pair.intros by auto

lemma same_pair_prop1:
  "same_pair ((a,b)#xs) \<Longrightarrow> same_pair xs"
  using same_pair.intros(2)[of a b xs] 
  using same_pair.cases by auto

lemma same_pair_prop2:
  "same_pair xs \<Longrightarrow> same_pair (butlast xs)"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons p xs)
  show ?case
    apply (auto intro: same_pair.intros)
    apply (cases p)
    subgoal for a b
      apply auto
      apply (rule same_pair.intros(2))
      using Cons same_pair.cases by auto
    done
qed

lemma same_pair_prop3:
"xs \<noteq> [] \<Longrightarrow> same_pair xs \<Longrightarrow> fst (last xs) = snd (last xs)"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons p xs)
  then show ?case 
    apply (cases p)
    subgoal premises pre for a b
    proof (cases "xs = []")
      case True
      then show ?thesis 
        using pre same_pair.cases by auto
    next
      case False
      then show ?thesis using pre same_pair_prop1[of a b xs]
        by auto
    qed
    done
qed

lemma same_pair_prop4:
"same_pair (a@b) \<Longrightarrow> same_pair a"
  apply(induct a arbitrary: b)
   apply (auto simp add:same_pair.intros)
  subgoal premises pre for a b l1 l2
  proof-
    have 1:"a=b"
      using pre(2)
      using same_pair.cases by auto
    have 2:"same_pair (l1 @ l2)"
      using pre(2)
      using same_pair.cases by auto
    have 3:"same_pair l1"
      using pre(1)[OF 2] by auto
    show ?thesis using same_pair.intros(2)[OF 1 3] by auto
  qed
  done


lemma P_inv_snoc:
"P_inv_ind a b fcs tr1 \<Longrightarrow> 
  same_pair ((a,b)#fcs) \<longrightarrow> 
    (Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1)({}, {}) 
  @\<^sub>t WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C'' 
  @\<^sub>t in_inv_assn  (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t in_inv_assn  (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'') tr2
                   \<Longrightarrow> P_inv_ind a b (fcs@[(a',b')]) (tr1@tr2)"
proof (induct rule: P_inv_ind.induct)
  case (1 a b)
  then show ?case 
    apply auto
    using same_pair.intros(1)
    using same_pair.intros(2)[of a b "[]"]
    using P_inv_ind.intros(2)[of a b a' b' tr2 "[]" "[]"]
    unfolding pure_assn_def apply auto
    using P_inv_ind.intros(1)
    by auto
next
  case (2 a b a'' b'' tr1 fcs tr)
  then show ?case 
    using P_inv_ind.intros(2)[of a b a'' b'' tr1 "fcs @ [(a', b')]" "tr@tr2"]
    apply auto
    using same_pair.intros(2)[of a b "(a'', b'') # fcs"]
    apply auto
    done
qed     

lemma P_inv_prop0:
"P_inv_ind a b [] = emp\<^sub>t"
using P_inv_ind.cases 
apply(auto simp add: emp_assn_def)
  using P_inv_ind.intros(1) by blast

lemma P_inv_prop1:
  assumes "a=b"
  shows "P_inv_ind a b ((a',b')#list) = Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {}) 
  @\<^sub>t WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'' @\<^sub>t P_inv_ind a' b' list"
  apply(rule ext)
  subgoal for tr
proof-
  have 1:"P_inv_ind a b ((a',b')#list) tr \<Longrightarrow> \<exists> tr1 tr2. (Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {}) 
  @\<^sub>t WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C''
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'') tr1 \<and> P_inv_ind a' b' list tr2 \<and> tr= tr1@tr2"
    apply(rule P_inv_ind.cases[of a b "(a', b') # list" tr])
    using assms by auto
  then have 2:"P_inv_ind a b ((a',b')#list) tr \<Longrightarrow> ((Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {}) 
  @\<^sub>t WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C''
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'') @\<^sub>t P_inv_ind a' b' list) tr"
    by(auto simp add:join_assn_def)
  have 3:"((Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {}) 
  @\<^sub>t WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C''
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'') @\<^sub>t P_inv_ind a' b' list) tr 
   \<Longrightarrow> \<exists> tr1 tr2. (Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {}) 
  @\<^sub>t WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C''
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'') tr1 \<and> P_inv_ind a' b' list tr2 \<and> tr= tr1@tr2"
    by(auto simp add: join_assn_def)
  have 4:"((Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {}) 
  @\<^sub>t WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C''
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'') @\<^sub>t P_inv_ind a' b' list) tr 
   \<Longrightarrow> P_inv_ind a b ((a',b')#list) tr"
    subgoal premises pre
  proof-
    obtain tr1 tr2 where g:"(Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {}) 
  @\<^sub>t WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C''
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'') tr1 \<and> P_inv_ind a' b' list tr2 \<and> tr= tr1@tr2"
      using pre 3 by auto
    then show ?thesis
      using P_inv_ind.intros(2)[of a b a' b' tr1 list tr2] assms by auto
  qed
  done
  then show ?thesis using 2 4 by(auto simp add: join_assoc)
qed
  done

theorem Valid_post_imp:
  assumes "\<Turnstile> {P} c {Q1}"
    and "\<Turnstile> {P} c {\<lambda>s tr. Q1 s tr \<longrightarrow> Q2 s tr}"
  shows "\<Turnstile> {P} c {\<lambda>s tr. Q1 s tr \<and> Q2 s tr}"
  using assms unfolding Valid_def entails_def by blast

lemma P_rep:
  "\<Turnstile> {\<lambda>s tr. (inv s \<and> s A = a \<and> s B = b \<and> s T = 0) \<and> (emp\<^sub>t tr)}
    Plant
   {\<lambda>s tr. \<exists>Fc . s A = fst(last((a,b)#Fc)) \<and> s B = snd(last((a,b)#Fc)) \<and> s T = 0 
         \<and> P_inv_ind a b Fc tr \<and> (same_pair (butlast((a,b)#Fc)) \<longrightarrow> inv s)}"
  unfolding Plant_def
apply (rule Valid_weaken_pre)
  prefer 2
   apply(rule Valid_rep)
   prefer 2
  subgoal
    unfolding entails_def emp_assn_def apply clarify
    apply(rule exI[where x= "[]"])
    using P_inv_ind.intros(1) by auto
  subgoal
    apply (rule Valid_ex_pre)
    subgoal for Fc
      apply(rule Valid_seq[where Q="\<lambda>s t. 
                  (s T = 1)
                \<and> (s A = fst (last ((a, b) # Fc))) 
                \<and> (s B = snd (last ((a, b) # Fc))) 
                \<and> (P_inv_ind a b Fc @\<^sub>t (\<up> (same_pair ((a, b) # Fc)) \<longrightarrow>\<^sub>t  Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {}))) t 
                \<and> (same_pair (((a, b) # Fc)) \<longrightarrow> inv s) "])
      subgoal
        apply(rule Valid_post_imp)
       apply(rule Valid_weaken_pre)
        prefer 2
        apply(rule Valid_inv_b_s_le)
        apply clarify
        unfolding vec2state_def
          apply (fast intro!: derivative_intros)
        subgoal
          apply(auto simp add:state2vec_def entails_def)
          done
        apply(rule Valid_strengthen_post[where Q = "\<lambda> s t. 
               s A = fst (last ((a, b) # Fc)) 
             \<and> s B = snd (last ((a, b) # Fc)) 
             \<and> (s T = 1 \<longrightarrow>
                (P_inv_ind a b Fc @\<^sub>t (\<up> (same_pair ((a, b) # Fc)) \<longrightarrow>\<^sub>t Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {}))) t) 
             \<and> (same_pair ((a, b) # Fc) \<longrightarrow> local.inv s)"])
        subgoal 
          apply(auto simp add: entails_def)
          done
        apply(rule Valid_weaken_pre)
         prefer 2
        apply(rule DC'''g[where init = "\<lambda> s. s A = fst (last ((a, b) # Fc)) \<and>
            s B = snd (last ((a, b) # Fc)) \<and>
            s T = 0 \<and> (same_pair (butlast ((a, b) # Fc)) \<longrightarrow> local.inv s)"
          and P= "\<lambda> t. P_inv_ind a b Fc t"])
          apply(rule Valid_weaken_pre)
           prefer 2
        apply(rule Valid_inv_tr_eq)
            apply clarify
        unfolding vec2state_def
            apply (fast intro!: derivative_intros)
        apply(simp add:state2vec_def entails_def)
          apply(simp add:state2vec_def entails_def)
         prefer 2
         apply(simp add:state2vec_def entails_def)
        apply(rule Valid_strengthen_post[where Q = "\<lambda>s t. s B = snd (last ((a, b) # Fc)) \<and> 
          (s A = fst (last ((a, b) # Fc)) \<and>
              (P_inv_ind a b Fc @\<^sub>t ode_inv_assn (\<lambda>s. s A = fst (last ((a, b) # Fc)))) t \<longrightarrow> (s T = 1 \<longrightarrow>
              (P_inv_ind a b Fc @\<^sub>t (\<up> (same_pair ((a, b) # Fc)) \<longrightarrow>\<^sub>t
                Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {})))
                t) \<and>
              (same_pair ((a, b) # Fc) \<longrightarrow> local.inv s))"])
         apply(simp add: entails_def)
        apply(rule Valid_weaken_pre)
         prefer 2
        apply(rule DC'''g[where init = "\<lambda> s. s A = fst (last ((a, b) # Fc)) \<and>
            s B = snd (last ((a, b) # Fc)) \<and>
            s T = 0 \<and> (same_pair (butlast ((a, b) # Fc)) \<longrightarrow> local.inv s)"
          and P= "\<lambda> t. P_inv_ind a b Fc t"])
          apply(rule Valid_weaken_pre)
           prefer 2
        apply(rule Valid_inv_tr_eq)
            apply clarify
        unfolding vec2state_def
            apply (fast intro!: derivative_intros)
        apply(simp add:state2vec_def entails_def)
          apply(simp add:state2vec_def entails_def)
         prefer 2
        subgoal
          apply(auto simp add:state2vec_def entails_def)
          done
          unfolding Valid_def
          apply (auto simp add: same_pair.intros )
          subgoal for s1 tr1 s2 tr2
            apply (elim contE)
             apply (simp add: join_assn_def pure_assn_def imp_assn_def join_assn_def)
            subgoal premises pre for d p
      proof-
        obtain ep where ep:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep..d + ep}" "ep > 0"
          using pre unfolding ODEsol_def by auto
        have 1:"((\<lambda> x. (p x) T) has_vector_derivative 1) (at x within {- ep..d + ep})" if "x \<in> {- ep..d + ep}" for x
          using has_vderiv_on_proj[OF ep(1),of T] unfolding state2vec_def  has_vderiv_on_def
          using that apply (auto simp add:state2vec_def) done
        then have 2:"(\<And>x. 0 \<le> x \<Longrightarrow> x \<le> d \<Longrightarrow> ((\<lambda> x. (p x) T) has_derivative (\<lambda> x. x) ) (at x within {0..d}))"
          unfolding has_vector_derivative_def using ep(2) pre(6) has_derivative_subset[of "(\<lambda> x. (p x) T)" "(\<lambda>x. x *\<^sub>R 1)" _ "{- ep..d + ep}" "{0..d}"]
          by auto
        have 3:"d = 1" 
          using mvt_simple[OF _ 2] using pre by auto
        have 4:"\<forall>x. ((\<lambda>v. (\<lambda> s. s X + s Y) (vec2state v)) has_derivative (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) x) (at x within UNIV)"
          apply clarify
          apply(auto simp add:vec2state_def)
          done
        have 5:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using chainrule'[OF 4 ep(1)] using ep(2) by auto 
        have 6:" (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))
                = s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))" if "t\<in>{-ep .. d+ep}" for t s
          using 5 unfolding has_derivative_def bounded_linear_def 
          using that 
          by (metis (no_types, lifting) scaleR_add_right vector_scaleR_component)
        have 7:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using 5 6 by auto
        have 8:"\<forall>t\<in>{0 .. d}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {0 .. d})"
          apply clarify apply(rule has_derivative_subset[where s= "{-ep .. d+ep}"]) using 7 ep(2) by auto
        have 9:"ode_inv_assn (\<lambda>s. s B = s1 B) tr2"
          using pre by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 10:"\<forall>t\<in>{0 .. d}. p t B = b"
          using 9 pre(13) apply(elim ode_inv_assn_elim)  
          subgoal premises prems for d' p'
          proof -
            have a: "d = d'"
              using prems pre
              using WaitBlk_cong by blast
            have b: "State (p \<tau>) = State (p' \<tau>)" if "0 \<le> \<tau>" "ereal \<tau> \<le> ereal d" for \<tau>
              using prems pre(12)  WaitBlk_cong2 a that by fastforce
            have c: "p \<tau> = p' \<tau>" if "0 \<le> \<tau>" "\<tau> \<le> d" for \<tau>
              using b that by auto
            show ?thesis
              using c prems(3) a pre by auto
          qed
          done
        have 11:"ode_inv_assn (\<lambda>s. s A = s1 A) tr2"
          using pre by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 12:"\<forall>t\<in>{0 .. d}. p t A = a"
          using 11 pre(13) apply(elim ode_inv_assn_elim)  
          subgoal premises prems for d' p'
          proof -
            have a: "d = d'"
              using prems pre
              using WaitBlk_cong by blast
            have b: "State (p \<tau>) = State (p' \<tau>)" if "0 \<le> \<tau>" "ereal \<tau> \<le> ereal d" for \<tau>
              using prems(1,2) pre(12) WaitBlk_cong2 a that by fastforce
            have c: "p \<tau> = p' \<tau>" if "0 \<le> \<tau>" "\<tau> \<le> d" for \<tau>
              using b that by auto
            show ?thesis
              using c prems(3) a pre by auto
          qed
          done
        have 13:"a=b" if "same_pair [(s1 A, s1 B)]"
          using pre that same_pair_prop0 by auto
        have 14:"((\<lambda>t. p t X + p t Y) has_derivative
             (\<lambda>s. s * (p t A * (p t X)\<^sup>2 + p t B * p t Y * p t X)))
             (at t within {0..d})" if "t\<in>{0..d}" for t
          using 8 that by (auto simp add: state2vec_def)
        have 15:"((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_vderiv_on (\<lambda> t . (\<lambda> t. a * p t X) t * ((\<lambda>t. (\<lambda> s. s X + s Y) (p t))) t)) {0..d}" if "same_pair [(s1 A, s1 B)]"
          unfolding has_vderiv_on_def has_vector_derivative_def
          using 10 12 13 14 that by (auto simp add: power2_eq_square algebra_simps)
        have 16:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep<..<d + ep}"
          apply(rule has_vderiv_on_subset [OF ep(1)]) by auto
        have 17:"continuous_on {-ep<..<d+ep} (\<lambda>t. state2vec (p t))"
          apply(auto simp add: continuous_on_eq_continuous_within)
          using 16 unfolding has_vderiv_on_def has_vector_derivative_def
          using has_derivative_continuous 
          using greaterThanLessThan_iff by blast
        have 18:"continuous_on UNIV (\<lambda> v. a * vec2state v  X)"
          apply(auto simp add: continuous_on_eq_continuous_within vec2state_def) 
          done
        have 19:"continuous_on {-ep<..<d+ep} (\<lambda>t. a * p t X)"
          using continuous_on_compose2[OF 18 17] by auto
        have 20:" p t X + p t Y = 0" if "t\<in>{0..d}" "same_pair [(s1 A, s1 B)]"for t
          using dbxeq_weak[OF 15 _ 19] that using pre ep(2) unfolding inv_def by auto
        have 21:"Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {}) 
                  [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]" if "same_pair [(s1 A, s1 B)]"
          apply(auto simp add:wait_inv_assn.simps)
          apply(rule exI[where x= "(\<lambda>\<tau>. State (p \<tau>))"])
          apply(auto simp add:gsb2gsrb.simps sb2gsb.simps inv_def)
          using 20 3 that by auto
        show ?thesis using 21 pre apply(auto simp add: join_assn_def pure_assn_def imp_assn_def) done 
      qed
      done
    subgoal for s1 tr1 s2 tr2
      apply (elim contE)
             apply (simp add: join_assn_def)
            subgoal premises pre for d p
    proof-
        obtain ep where ep:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep..d + ep}" "ep > 0"
          using pre unfolding ODEsol_def by auto
        have 4:"\<forall>x. ((\<lambda>v. (\<lambda> s. s X + s Y) (vec2state v)) has_derivative (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) x) (at x within UNIV)"
          apply clarify
          apply(auto simp add:vec2state_def)
          done
        have 5:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using chainrule'[OF 4 ep(1)] using ep(2) by auto 
        have 6:" (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))
                = s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))" if "t\<in>{-ep .. d+ep}" for t s
          using 5 unfolding has_derivative_def bounded_linear_def 
          using that 
          by (metis (no_types, lifting) scaleR_add_right vector_scaleR_component)
        have 7:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using 5 6 by auto
        have 8:"\<forall>t\<in>{0 .. d}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {0 .. d})"
          apply clarify apply(rule has_derivative_subset[where s= "{-ep .. d+ep}"]) using 7 ep(2) by auto
        have 9:"ode_inv_assn (\<lambda>s. s B = s1 B) tr2"
          using pre by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 10:"\<forall>t\<in>{0 .. d}. p t B = b"
          using 9 pre(12) apply(elim ode_inv_assn_elim)  
          subgoal premises prems for d' p'
          proof -
            have a: "d = d'"
              using prems
              using WaitBlk_cong by blast
            have b: "State (p \<tau>) = State (p' \<tau>)" if "0 \<le> \<tau>" "ereal \<tau> \<le> ereal d" for \<tau>
              using prems(1,2) WaitBlk_cong2 a that by blast
            have c: "p \<tau> = p' \<tau>" if "0 \<le> \<tau>" "\<tau> \<le> d" for \<tau>
              using b that by auto
            show ?thesis
              using c prems(3) a pre by auto
          qed
          done
        have 11:"ode_inv_assn (\<lambda>s. s A = s1 A) tr2"
          using pre by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 12:"\<forall>t\<in>{0 .. d}. p t A = a"
          using 11 pre(12) apply(elim ode_inv_assn_elim)  
          subgoal premises prems for d' p'
          proof -
            have a: "d = d'"
              using prems(1,2)
              using WaitBlk_cong by blast
            have b: "State (p \<tau>) = State (p' \<tau>)" if "0 \<le> \<tau>" "ereal \<tau> \<le> ereal d" for \<tau>
              using prems(1,2) WaitBlk_cong2 a that by blast
            have c: "p \<tau> = p' \<tau>" if "0 \<le> \<tau>" "\<tau> \<le> d" for \<tau>
              using b that by auto
            show ?thesis
              using c prems(3) a pre by auto
          qed
          done
        have 13:"a=b"
          using pre(2,3,11) using same_pair.cases 
          by (metis list.distinct(1) list.inject prod.inject)
        have 14:"((\<lambda>t. p t X + p t Y) has_derivative
             (\<lambda>s. s * (p t A * (p t X)\<^sup>2 + p t B * p t Y * p t X)))
             (at t within {0..d})" if "t\<in>{0..d}" for t
          using 8 that by (auto simp add: state2vec_def)
        have 15:"((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_vderiv_on (\<lambda> t . (\<lambda> t. a * p t X) t * ((\<lambda>t. (\<lambda> s. s X + s Y) (p t))) t)) {0..d}"
          unfolding has_vderiv_on_def has_vector_derivative_def
          using 10 12 13 14 by (auto simp add: power2_eq_square algebra_simps)
        have 16:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep<..<d + ep}"
          apply(rule has_vderiv_on_subset [OF ep(1)]) by auto
        have 17:"continuous_on {-ep<..<d+ep} (\<lambda>t. state2vec (p t))"
          apply(auto simp add: continuous_on_eq_continuous_within)
          using 16 unfolding has_vderiv_on_def has_vector_derivative_def
          using has_derivative_continuous 
          using greaterThanLessThan_iff by blast
        have 18:"continuous_on UNIV (\<lambda> v. a * vec2state v  X)"
          apply(auto simp add: continuous_on_eq_continuous_within vec2state_def) 
          done
        have 19:"continuous_on {-ep<..<d+ep} (\<lambda>t. a * p t X)"
          using continuous_on_compose2[OF 18 17] by auto
        have 20:" p t X + p t Y = 0" if "t\<in>{0..d}" for t
          using dbxeq_weak[OF 15 _ 19] that using pre ep(2) unfolding inv_def by auto
        show ?thesis
          using 20 pre unfolding inv_def by auto
      qed
      done
    subgoal for s1 tr1 s2 tr2
      using same_pair_prop2[of "(a, b) # Fc"]
      by (auto simp add: pure_assn_def imp_assn_def join_assn_def) 
    subgoal for s1 tr1 s2 tr2
      using same_pair_prop2[of "(a, b) # Fc"]
      by auto
    subgoal for s1 tr1 s2 tr2
            apply (elim contE)
             apply (simp add: join_assn_def)
            subgoal premises pre for d p
      proof-
        obtain ep where ep:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep..d + ep}" "ep > 0"
          using pre unfolding ODEsol_def by auto
        have 1:"((\<lambda> x. (p x) T) has_vector_derivative 1) (at x within {- ep..d + ep})" if "x \<in> {- ep..d + ep}" for x
          using has_vderiv_on_proj[OF ep(1),of T] unfolding state2vec_def  has_vderiv_on_def
          using that apply (auto simp add:state2vec_def) done
        then have 2:"(\<And>x. 0 \<le> x \<Longrightarrow> x \<le> d \<Longrightarrow> ((\<lambda> x. (p x) T) has_derivative (\<lambda> x. x) ) (at x within {0..d}))"
          unfolding has_vector_derivative_def using ep(2) pre(6) has_derivative_subset[of "(\<lambda> x. (p x) T)" "(\<lambda>x. x *\<^sub>R 1)" _ "{- ep..d + ep}" "{0..d}"]
          by auto
        have 3:"d = 1" 
          using mvt_simple[OF _ 2] using pre by auto
        have 4:"\<forall>x. ((\<lambda>v. (\<lambda> s. s X + s Y) (vec2state v)) has_derivative (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) x) (at x within UNIV)"
          apply clarify
          apply(auto simp add:vec2state_def)
          done
        have 5:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using chainrule'[OF 4 ep(1)] using ep(2) by auto 
        have 6:" (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))
                = s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))" if "t\<in>{-ep .. d+ep}" for t s
          using 5 unfolding has_derivative_def bounded_linear_def 
          using that 
          by (metis (no_types, lifting) scaleR_add_right vector_scaleR_component)
        have 7:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using 5 6 by auto
        have 8:"\<forall>t\<in>{0 .. d}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {0 .. d})"
          apply clarify apply(rule has_derivative_subset[where s= "{-ep .. d+ep}"]) using 7 ep(2) by auto
        have 9:"ode_inv_assn (\<lambda>s. s B = s1 B) tr2"
          using pre by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 10:"\<forall>t\<in>{0 .. d}. p t B = snd (last Fc)"
          using 9 pre(13) apply(elim ode_inv_assn_elim)  
          subgoal premises prems for d' p'
          proof -
            have a: "d = d'"
              using prems(1,2) pre
              using WaitBlk_cong by blast
            have b: "State (p \<tau>) = State (p' \<tau>)" if "0 \<le> \<tau>" "ereal \<tau> \<le> ereal d" for \<tau>
              using prems(1,2) pre(12) WaitBlk_cong2 a that by fastforce
            have c: "p \<tau> = p' \<tau>" if "0 \<le> \<tau>" "\<tau> \<le> d" for \<tau>
              using b that by auto
            show ?thesis
              using c prems(3) a pre by auto
          qed
          done
        have 11:"ode_inv_assn (\<lambda>s. s A = s1 A) tr2"
          using pre by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 12:"\<forall>t\<in>{0 .. d}. p t A = fst (last Fc)"
          using 11 pre(13) apply(elim ode_inv_assn_elim)  
          subgoal premises prems for d' p'
          proof -
            have a: "d = d'"
              using prems(1,2) pre
              using WaitBlk_cong by blast
            have b: "State (p \<tau>) = State (p' \<tau>)" if "0 \<le> \<tau>" "ereal \<tau> \<le> ereal d" for \<tau>
              using prems(1,2) pre(12) WaitBlk_cong2 a that by fastforce
            have c: "p \<tau> = p' \<tau>" if "0 \<le> \<tau>" "\<tau> \<le> d" for \<tau>
              using b that by auto
            show ?thesis
              using c prems(3) a pre by auto
          qed
          done
        have 13:"fst (last Fc)=snd (last Fc)" if "same_pair ((a, b) # Fc)"
          using pre same_pair_prop1 same_pair_prop3 that
          by auto
        have 14:"((\<lambda>t. p t X + p t Y) has_derivative
             (\<lambda>s. s * (p t A * (p t X)\<^sup>2 + p t B * p t Y * p t X)))
             (at t within {0..d})" if "t\<in>{0..d}" for t
          using 8 that by (auto simp add: state2vec_def)
        have 15:"((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_vderiv_on (\<lambda> t . (\<lambda> t. (fst (last Fc)) * p t X) t * ((\<lambda>t. (\<lambda> s. s X + s Y) (p t))) t)) {0..d}" if "same_pair ((a, b) # Fc)"
          unfolding has_vderiv_on_def has_vector_derivative_def
          using 10 12 13 14 that by (auto simp add: power2_eq_square algebra_simps)
        have 16:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep<..<d + ep}"
          apply(rule has_vderiv_on_subset [OF ep(1)]) by auto
        have 17:"continuous_on {-ep<..<d+ep} (\<lambda>t. state2vec (p t))"
          apply(auto simp add: continuous_on_eq_continuous_within)
          using 16 unfolding has_vderiv_on_def has_vector_derivative_def
          using has_derivative_continuous 
          using greaterThanLessThan_iff by blast
        have 18:"continuous_on UNIV (\<lambda> v. fst (last Fc) * vec2state v  X)"
          apply(auto simp add: continuous_on_eq_continuous_within vec2state_def) 
          done
        have 19:"continuous_on {-ep<..<d+ep} (\<lambda>t. fst (last Fc) * p t X)"
          using continuous_on_compose2[OF 18 17] by auto
        have 20:" p t X + p t Y = 0" if "t\<in>{0..d}" "same_pair ((a, b) # Fc)"for t
          using dbxeq_weak[OF 15 _ 19] that using pre ep(2) unfolding inv_def by auto
        have 21:"Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {}) 
                  [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]" if "same_pair ((a, b) # Fc)"
          apply(auto simp add:wait_inv_assn.simps)
          apply(rule exI[where x= "(\<lambda>\<tau>. State (p \<tau>))"])
          apply(auto simp add:gsb2gsrb.simps sb2gsb.simps inv_def)
          using 20 3 that by auto
        show ?thesis using 21 pre by(auto simp add: join_assn_def pure_assn_def imp_assn_def) 
      qed
      done
    subgoal for s1 tr1 s2 tr2
      apply (elim contE)
             apply (simp add: join_assn_def)
            subgoal premises pre for d p
    proof-
        obtain ep where ep:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep..d + ep}" "ep > 0"
          using pre unfolding ODEsol_def by auto
        have 4:"\<forall>x. ((\<lambda>v. (\<lambda> s. s X + s Y) (vec2state v)) has_derivative (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) x) (at x within UNIV)"
          apply clarify
          apply(auto simp add:vec2state_def)
          done
        have 5:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using chainrule'[OF 4 ep(1)] using ep(2) by auto 
        have 6:" (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))
                = s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))" if "t\<in>{-ep .. d+ep}" for t s
          using 5 unfolding has_derivative_def bounded_linear_def 
          using that 
          by (metis (no_types, lifting) scaleR_add_right vector_scaleR_component)
        have 7:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using 5 6 by auto
        have 8:"\<forall>t\<in>{0 .. d}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {0 .. d})"
          apply clarify apply(rule has_derivative_subset[where s= "{-ep .. d+ep}"]) using 7 ep(2) by auto
        have 9:"ode_inv_assn (\<lambda>s. s B = s1 B) tr2"
          using pre by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 10:"\<forall>t\<in>{0 .. d}. p t B = snd (last Fc)"
          using 9 pre(12) apply(elim ode_inv_assn_elim)  
          subgoal premises prems for d' p'
          proof -
            have a: "d = d'"
              using prems
              using WaitBlk_cong by blast
            have b: "State (p \<tau>) = State (p' \<tau>)" if "0 \<le> \<tau>" "ereal \<tau> \<le> ereal d" for \<tau>
              using prems(1,2) WaitBlk_cong2 a that by blast
            have c: "p \<tau> = p' \<tau>" if "0 \<le> \<tau>" "\<tau> \<le> d" for \<tau>
              using b that by auto
            show ?thesis
              using c prems(3) a pre by auto
          qed
          done
        have 11:"ode_inv_assn (\<lambda>s. s A = s1 A) tr2"
          using pre by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 12:"\<forall>t\<in>{0 .. d}. p t A = fst (last Fc)"
          using 11 pre(12) apply(elim ode_inv_assn_elim)  
          subgoal premises prems for d' p'
          proof -
            have a: "d = d'"
              using prems(1,2)
              using WaitBlk_cong by blast
            have b: "State (p \<tau>) = State (p' \<tau>)" if "0 \<le> \<tau>" "ereal \<tau> \<le> ereal d" for \<tau>
              using prems(1,2) WaitBlk_cong2 a that by blast
            have c: "p \<tau> = p' \<tau>" if "0 \<le> \<tau>" "\<tau> \<le> d" for \<tau>
              using b that by auto
            show ?thesis
              using c prems(3) a pre by auto
          qed
          done
        have 13:"fst (last Fc)=snd (last Fc)"
          using pre using same_pair_prop1 same_pair_prop3
          by auto
        have 14:"((\<lambda>t. p t X + p t Y) has_derivative
             (\<lambda>s. s * (p t A * (p t X)\<^sup>2 + p t B * p t Y * p t X)))
             (at t within {0..d})" if "t\<in>{0..d}" for t
          using 8 that by (auto simp add: state2vec_def)
        have 15:"((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_vderiv_on (\<lambda> t . (\<lambda> t. fst (last Fc) * p t X) t * ((\<lambda>t. (\<lambda> s. s X + s Y) (p t))) t)) {0..d}"
          unfolding has_vderiv_on_def has_vector_derivative_def
          using 10 12 13 14 by (auto simp add: power2_eq_square algebra_simps)
        have 16:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep<..<d + ep}"
          apply(rule has_vderiv_on_subset [OF ep(1)]) by auto
        have 17:"continuous_on {-ep<..<d+ep} (\<lambda>t. state2vec (p t))"
          apply(auto simp add: continuous_on_eq_continuous_within)
          using 16 unfolding has_vderiv_on_def has_vector_derivative_def
          using has_derivative_continuous 
          using greaterThanLessThan_iff by blast
        have 18:"continuous_on UNIV (\<lambda> v. fst (last Fc) * vec2state v  X)"
          apply(auto simp add: continuous_on_eq_continuous_within vec2state_def) 
          done
        have 19:"continuous_on {-ep<..<d+ep} (\<lambda>t. fst (last Fc) * p t X)"
          using continuous_on_compose2[OF 18 17] by auto
        have 20:" p t X + p t Y = 0" if "t\<in>{0..d}" for t
          using dbxeq_weak[OF 15 _ 19] that using pre ep(2) unfolding inv_def by auto
        show ?thesis
          using 20 pre unfolding inv_def by auto
      qed
      done
    done
  apply(rule Valid_weaken_pre)
   prefer 2
  apply(rule Valid_interrupt_Out[where Q="\<lambda>s t. 
           s A = fst (last ((a, b) # Fc)) \<and>
           s B = snd (last ((a, b) # Fc)) \<and>
           ((P_inv_ind a b Fc @\<^sub>t (\<up> (same_pair ((a, b) # Fc)) \<longrightarrow>\<^sub>t
             (Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {}) @\<^sub>t
             WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C'')))
             t) \<and>
           (same_pair ((a, b) # Fc) \<longrightarrow> local.inv s)"])
   prefer 2
  subgoal
    apply(simp add: entails_def)
    apply(rule conjI)
    subgoal 
      apply clarify
      subgoal for s tr
        apply(rule conjI)
        subgoal premises pre 
        proof-
          have 1:"WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C'' [OutBlock ''P2C'' (s X)]"
                    if "same_pair [(s A, s B)]"
            apply(auto simp add: wait_out_inv_assn.simps srb2gsrb.simps gsb2gsrb.simps sb2gsb.simps) 
            apply(rule exI[where x="State s"])
            apply auto 
            using pre that by auto
          show ?thesis 
            using 1  pre(5)
            apply(auto simp add: join_assn_def pure_assn_def imp_assn_def) 
            by blast
        qed
        apply clarify
        subgoal premises pre for d p
        proof-
          obtain ep where ep:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep..d + ep}" "ep > 0"
            using pre unfolding ODEsol_def by auto
        have a1:"((\<lambda> x. (p x) A) has_vector_derivative 0) (at x within {- ep..d + ep})" if "x \<in> {- ep..d + ep}" for x
          using has_vderiv_on_proj[OF ep(1),of A] unfolding state2vec_def  has_vderiv_on_def
          using that apply (auto simp add:state2vec_def) done
        then have a2:"(\<And>x. 0 \<le> x \<Longrightarrow> x \<le> d \<Longrightarrow> ((\<lambda> x. (p x) A) has_derivative (\<lambda> x. 0) ) (at x within {0..d}))"
          unfolding has_vector_derivative_def using ep(2) pre(6) has_derivative_subset[of "(\<lambda> x. (p x) A)" "(\<lambda>x. x *\<^sub>R 0)" _ "{- ep..d + ep}" "{0..d}"]
          by auto
        have a3: "p t A = p 0 A" if "t \<in> {0 .. d}" for t
          using that a2 mvt_simple[of 0 t "\<lambda> x. (p x) A" "\<lambda> _ _ . 0" ] pre has_derivative_subset 
          by (smt atLeastAtMost_iff atLeastatMost_subset_iff)
        have b1:"((\<lambda> x. (p x) B) has_vector_derivative 0) (at x within {- ep..d + ep})" if "x \<in> {- ep..d + ep}" for x
          using has_vderiv_on_proj[OF ep(1),of B] unfolding state2vec_def  has_vderiv_on_def
          using that apply (auto simp add:state2vec_def) done
        then have b2:"(\<And>x. 0 \<le> x \<Longrightarrow> x \<le> d \<Longrightarrow> ((\<lambda> x. (p x) B) has_derivative (\<lambda> x. 0) ) (at x within {0..d}))"
          unfolding has_vector_derivative_def using ep(2) pre(6) has_derivative_subset[of "(\<lambda> x. (p x) B)" "(\<lambda>x. x *\<^sub>R 0)" _ "{- ep..d + ep}" "{0..d}"]
          by auto
        have b3: "p t B = p 0 B" if "t \<in> {0 .. d}" for t
          using that b2 mvt_simple[of 0 t "\<lambda> x. (p x) B" "\<lambda> _ _ . 0" ] pre has_derivative_subset 
          by (smt atLeastAtMost_iff atLeastatMost_subset_iff)
        have 4:"\<forall>x. ((\<lambda>v. (\<lambda> s. s X + s Y) (vec2state v)) has_derivative (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) x) (at x within UNIV)"
          apply clarify
          apply(auto simp add:vec2state_def)
          done
        have 5:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using chainrule'[OF 4 ep(1)] using ep(2) by auto 
        have 6:" (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))
                = s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))" if "t\<in>{-ep .. d+ep}" for t s
          using 5 unfolding has_derivative_def bounded_linear_def 
          using that 
          by (metis (no_types, lifting) scaleR_add_right vector_scaleR_component)
        have 7:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using 5 6 by auto
        have 8:"\<forall>t\<in>{0 .. d}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {0 .. d})"
          apply clarify apply(rule has_derivative_subset[where s= "{-ep .. d+ep}"]) using 7 ep(2) by auto
        have 9:"((\<lambda>t. p t X + p t Y) has_derivative
             (\<lambda>s. s * (p t A * (p t X)\<^sup>2 + p t B * p t Y * p t X)))
             (at t within {0..d})" if "t\<in>{0..d}" for t
          using 8 that by (auto simp add: state2vec_def)
        have 10:"p 0 A = p 0 B" if "same_pair [(p 0 A, p 0 B)]"
          using that same_pair.cases 
          by (metis Pair_inject list.inject not_Cons_self2)
        have 11:"((\<lambda>t. p t X + p t Y) has_derivative
                (\<lambda>s. s * (p 0 A * (p t X * p t X) + p 0 B * p t Y * p t X)))
                (at t within {0..d})" if "t\<in>{0..d} " for t
          using 9 apply(simp add: power2_eq_square)
          using a3 b3 that 
          proof -
            assume a1: "\<And>t. 0 \<le> t \<and> t \<le> d \<Longrightarrow> ((\<lambda>t. p t X + p t Y) has_derivative (\<lambda>s. s * (p t A * (p t X * p t X) + p t B * p t Y * p t X))) (at t within {0..d})"
              have f2: "p t B = p 0 B"
                  by (metis b3 that)
              have "p t A = p 0 A"
                  by (metis a3 that)
              then show ?thesis
                  using f2 a1 that by fastforce
              qed
        have 12:"((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_vderiv_on (\<lambda> t . (\<lambda> t. p 0 A * p t X) t * ((\<lambda>t. (\<lambda> s. s X + s Y) (p t))) t)) {0..d}" if "same_pair [(p 0 A, p 0 B)]"
          unfolding has_vderiv_on_def has_vector_derivative_def
          using 11 10 that
          by(auto simp add: algebra_simps)
        have 13:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep<..<d + ep}"
          apply(rule has_vderiv_on_subset [OF ep(1)]) by auto
        have 14:"continuous_on {-ep<..<d+ep} (\<lambda>t. state2vec (p t))"
          apply(auto simp add: continuous_on_eq_continuous_within)
          using 13 unfolding has_vderiv_on_def has_vector_derivative_def
          using has_derivative_continuous 
          using greaterThanLessThan_iff by blast
        have 15:"continuous_on UNIV (\<lambda> v. p 0 A * vec2state v  X)"
          apply(auto simp add: continuous_on_eq_continuous_within vec2state_def) 
          done
        have 16:"continuous_on {-ep<..<d+ep} (\<lambda>t. p 0 A * p t X)"
          using continuous_on_compose2[OF 15 14] by auto
        have 17:" p t X + p t Y = 0" if "t\<in>{0..d}" "same_pair [(p 0 A, p 0 B)]"for t
          using dbxeq_weak[OF 12 _ 16] that using pre ep(2) unfolding inv_def by auto
        have 18:"Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) ({''P2C''}, {})
                    [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({''P2C''}, {})]" if "same_pair [(p 0 A, p 0 B)]"
          apply(auto simp add:wait_inv_assn.simps gsb2gsrb.simps sb2gsb.simps inv_def)
          apply(rule exI[where x= "d"])
          apply(rule exI[where x= "(\<lambda>\<tau>. State (p \<tau>))"])
          apply auto using pre 17 that by auto
        have 19:"Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ''P2C''
                   [OutBlock ''P2C'' (p d X)]"
          by(auto simp add:out_inv_assn.simps srb2gsrb.simps)
        have 20:"WaitOutinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ({''P2C''}, {}) ''P2C''
                    [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({''P2C''}, {}),OutBlock ''P2C'' (p d X)]" if "same_pair [(p 0 A, p 0 B)]"
          apply(auto simp add: wait_out_inv_assn.simps gsb2gsrb.simps sb2gsb.simps srb2gsrb.simps inv_def)
          apply(rule exI[where x= "d"])
          apply(rule exI[where x= "(\<lambda>\<tau>. State (p \<tau>))"])
          apply auto using pre 17 that by auto
        show ?thesis
          apply(auto simp add: join_assn_def inv_def)
          subgoal using a3
            by (smt atLeastAtMost_iff pre(7))
          subgoal using b3
            by (smt atLeastAtMost_iff pre(7))
          subgoal 
            using 20 pre(5) apply(auto simp add: join_assn_def pure_assn_def imp_assn_def)
            by blast
          subgoal using 17 by (smt atLeastAtMost_iff pre(7))
          done
      qed
      done
    done
  subgoal 
      apply clarify
      subgoal for s tr
        apply(rule conjI)
        subgoal premises pre 
        proof-
          have 1:"WaitOutinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ({''P2C''}, {}) ''P2C'' [OutBlock ''P2C'' (s X)]"
                    if "same_pair ((a, b) # Fc)"
            apply(auto simp add: wait_out_inv_assn.simps srb2gsrb.simps gsb2gsrb.simps sb2gsb.simps) 
            apply(rule exI[where x="State s"])
            apply auto 
            using pre that  by auto
          show ?thesis 
            using 1  pre(5)
            apply(auto simp add: join_assn_def pure_assn_def imp_assn_def) 
            by blast
        qed
        apply clarify
        subgoal premises pre for d p
        proof-
          obtain ep where ep:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep..d + ep}" "ep > 0"
            using pre unfolding ODEsol_def by auto
        have a1:"((\<lambda> x. (p x) A) has_vector_derivative 0) (at x within {- ep..d + ep})" if "x \<in> {- ep..d + ep}" for x
          using has_vderiv_on_proj[OF ep(1),of A] unfolding state2vec_def  has_vderiv_on_def
          using that apply (auto simp add:state2vec_def) done
        then have a2:"(\<And>x. 0 \<le> x \<Longrightarrow> x \<le> d \<Longrightarrow> ((\<lambda> x. (p x) A) has_derivative (\<lambda> x. 0) ) (at x within {0..d}))"
          unfolding has_vector_derivative_def using ep(2) pre(6) has_derivative_subset[of "(\<lambda> x. (p x) A)" "(\<lambda>x. x *\<^sub>R 0)" _ "{- ep..d + ep}" "{0..d}"]
          by auto
        have a3: "p t A = p 0 A" if "t \<in> {0 .. d}" for t
          using that a2 mvt_simple[of 0 t "\<lambda> x. (p x) A" "\<lambda> _ _ . 0" ] pre has_derivative_subset 
          by (smt atLeastAtMost_iff atLeastatMost_subset_iff)
        have b1:"((\<lambda> x. (p x) B) has_vector_derivative 0) (at x within {- ep..d + ep})" if "x \<in> {- ep..d + ep}" for x
          using has_vderiv_on_proj[OF ep(1),of B] unfolding state2vec_def  has_vderiv_on_def
          using that apply (auto simp add:state2vec_def) done
        then have b2:"(\<And>x. 0 \<le> x \<Longrightarrow> x \<le> d \<Longrightarrow> ((\<lambda> x. (p x) B) has_derivative (\<lambda> x. 0) ) (at x within {0..d}))"
          unfolding has_vector_derivative_def using ep(2) pre(6) has_derivative_subset[of "(\<lambda> x. (p x) B)" "(\<lambda>x. x *\<^sub>R 0)" _ "{- ep..d + ep}" "{0..d}"]
          by auto
        have b3: "p t B = p 0 B" if "t \<in> {0 .. d}" for t
          using that b2 mvt_simple[of 0 t "\<lambda> x. (p x) B" "\<lambda> _ _ . 0" ] pre has_derivative_subset 
          by (smt atLeastAtMost_iff atLeastatMost_subset_iff)
        have 4:"\<forall>x. ((\<lambda>v. (\<lambda> s. s X + s Y) (vec2state v)) has_derivative (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) x) (at x within UNIV)"
          apply clarify
          apply(auto simp add:vec2state_def)
          done
        have 5:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using chainrule'[OF 4 ep(1)] using ep(2) by auto 
        have 6:" (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))
                = s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) (ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t))" if "t\<in>{-ep .. d+ep}" for t s
          using 5 unfolding has_derivative_def bounded_linear_def 
          using that 
          by (metis (no_types, lifting) scaleR_add_right vector_scaleR_component)
        have 7:"\<forall>t\<in>{-ep .. d+ep}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {-ep .. d+ep})"
          using 5 6 by auto
        have 8:"\<forall>t\<in>{0 .. d}. ((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_derivative  (\<lambda>s. s *\<^sub>R (\<lambda>_. (\<lambda>x. x $ X + x $ Y)) (state2vec(p t)) ( ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1))) (p t)))) (at t within {0 .. d})"
          apply clarify apply(rule has_derivative_subset[where s= "{-ep .. d+ep}"]) using 7 ep(2) by auto
        have 9:"((\<lambda>t. p t X + p t Y) has_derivative
             (\<lambda>s. s * (p t A * (p t X)\<^sup>2 + p t B * p t Y * p t X)))
             (at t within {0..d})" if "t\<in>{0..d}" for t
          using 8 that by (auto simp add: state2vec_def)
        have 10:"p 0 A = p 0 B" if "same_pair ((a, b) # Fc)"
          using same_pair_prop1[OF that]
          using same_pair_prop3 pre by auto
        have 11:"((\<lambda>t. p t X + p t Y) has_derivative
                (\<lambda>s. s * (p 0 A * (p t X * p t X) + p 0 B * p t Y * p t X)))
                (at t within {0..d})" if "t\<in>{0..d} " for t
          using 9 apply(simp add: power2_eq_square)
          using a3 b3 that 
          proof -
            assume a1: "\<And>t. 0 \<le> t \<and> t \<le> d \<Longrightarrow> ((\<lambda>t. p t X + p t Y) has_derivative (\<lambda>s. s * (p t A * (p t X * p t X) + p t B * p t Y * p t X))) (at t within {0..d})"
              have f2: "p t B = p 0 B"
                  by (metis b3 that)
              have "p t A = p 0 A"
                  by (metis a3 that)
              then show ?thesis
                  using f2 a1 that by fastforce
              qed
        have 12:"((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_vderiv_on (\<lambda> t . (\<lambda> t. p 0 A * p t X) t * ((\<lambda>t. (\<lambda> s. s X + s Y) (p t))) t)) {0..d}" if "same_pair ((a, b) # Fc)"
          unfolding has_vderiv_on_def has_vector_derivative_def
          using 11 10 that
          by(auto simp add: algebra_simps)
        have 13:"((\<lambda>t. state2vec (p t)) has_vderiv_on
          (\<lambda>t. ODE2Vec
                (ODE ((\<lambda>_ _. 0)
                      (X := \<lambda>s. s A * (s X)\<^sup>2, Y := \<lambda>s. s B * s Y * s X, T := \<lambda>s. 1)))
                (p t)))
            {- ep<..<d + ep}"
          apply(rule has_vderiv_on_subset [OF ep(1)]) by auto
        have 14:"continuous_on {-ep<..<d+ep} (\<lambda>t. state2vec (p t))"
          apply(auto simp add: continuous_on_eq_continuous_within)
          using 13 unfolding has_vderiv_on_def has_vector_derivative_def
          using has_derivative_continuous 
          using greaterThanLessThan_iff by blast
        have 15:"continuous_on UNIV (\<lambda> v. p 0 A * vec2state v  X)"
          apply(auto simp add: continuous_on_eq_continuous_within vec2state_def) 
          done
        have 16:"continuous_on {-ep<..<d+ep} (\<lambda>t. p 0 A * p t X)"
          using continuous_on_compose2[OF 15 14] by auto
        have 17:" p t X + p t Y = 0" if "t\<in>{0..d}" "same_pair ((a, b) # Fc)"for t
          using dbxeq_weak[OF 12 _ 16] that using pre ep(2) unfolding inv_def by auto
        have 18:"Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) ({''P2C''}, {})
                    [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({''P2C''}, {})]" if "same_pair ((a, b) # Fc)"
          apply(auto simp add:wait_inv_assn.simps gsb2gsrb.simps sb2gsb.simps inv_def)
          apply(rule exI[where x= "d"])
          apply(rule exI[where x= "(\<lambda>\<tau>. State (p \<tau>))"])
          apply auto using pre 17 that by auto
        have 19:"Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ''P2C''
                   [OutBlock ''P2C'' (p d X)]"
          by(auto simp add:out_inv_assn.simps srb2gsrb.simps)
        have 20:"WaitOutinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ({''P2C''}, {}) ''P2C''
                    [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({''P2C''}, {}),OutBlock ''P2C'' (p d X)]" if "same_pair ((a, b) # Fc)"
          apply(auto simp add: wait_out_inv_assn.simps gsb2gsrb.simps sb2gsb.simps srb2gsrb.simps inv_def)
          apply(rule exI[where x= "d"])
          apply(rule exI[where x= "(\<lambda>\<tau>. State (p \<tau>))"])
          apply auto using pre 17 that by auto
        show ?thesis
          apply(auto simp add: join_assn_def inv_def)
          subgoal using a3
            using pre(3) pre(7) by auto
          subgoal using b3
            using pre(4) pre(7) by auto
          subgoal 
            using 20 pre(5) apply(auto simp add: join_assn_def pure_assn_def imp_assn_def)
            by blast
          subgoal using 17 by (smt atLeastAtMost_iff pre(7))
          done
      qed
      done
    done
  done
  apply(rule Valid_seq)
  apply(rule Valid_receive_sp)
  apply(rule Valid_seq)
  apply(rule Valid_receive_sp)
  apply(rule Valid_strengthen_post)
  prefer 2
  apply(rule Valid_assign_sp)
  apply(simp add: entails_def)
  apply(rule conjI)
  subgoal
    apply clarify
    subgoal for s tr pt pb nb
      apply(rule exI[where x="[(s A, s B)]"])
      apply (auto simp add: pure_assn_def conj_assn_def join_assn_def inv_def imp_assn_def)
      subgoal for tr4 tr1 tr3 tr2
        using P_inv_snoc[of a b "[]" "[]" "s A" "s B" "tr1 @ tr2 @ tr3 @ tr4"]
        using P_inv_ind.intros(1)
        by auto
      subgoal for tr5 tr1 tr4 tr2 tr3 
      using P_inv_snoc[of a b "[]" "[]" "s A" "s B" "tr1 @ tr2 @ tr3 @ tr4 @ tr5"]
        using P_inv_ind.intros(1)
      by auto
      subgoal for tr4 tr1 tr3 tr2 
       using P_inv_snoc[of a b "[]" tr1 "s A" "s B" "tr2 @ tr3 @ tr4"]
      by auto
    subgoal for tr5 tr1 tr4 tr2 tr3 
      apply(subgoal_tac"Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>sa v. v = s A)) ''C2P'' tr4")
       prefer 2
      subgoal
        apply(auto simp add: in_assn.simps in_inv_assn.simps srb2gsrb.simps)
        done
      apply(subgoal_tac"Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>sa v. v = s B)) ''C2P'' tr5")
       prefer 2
      subgoal
        apply(auto simp add: in_assn.simps in_inv_assn.simps srb2gsrb.simps)
        done
      using P_inv_snoc[of a b "[]" tr1 "s A" "s B" "tr2 @ tr3 @ tr4 @ tr5 "]
      apply(auto simp add: join_assn_def) by blast
    done
  done
  apply clarify
  subgoal for s tr pt pb nb
    apply(rule exI[where x="Fc@[(s A, s B)]"])
    apply (auto simp add: pure_assn_def conj_assn_def join_assn_def inv_def imp_assn_def)
    subgoal for tr4 tr1 tr3 tr2
      using P_inv_snoc[of a b Fc tr1 "s A" "s B" "tr2 @ tr3 @ tr4"]
      by auto
    subgoal for tr5 tr1 tr4 tr2 tr3 
      using P_inv_snoc[of a b Fc tr1 "s A" "s B" "tr2 @ tr3 @ tr4 @ tr5 "]
      by auto
    subgoal for tr4 tr1 tr3 tr2
      using P_inv_snoc[of a b Fc tr1 "s A" "s B" "tr2 @ tr3 @ tr4"]
      by auto
    subgoal for tr5 tr1 tr4 tr2 tr3 
      apply(subgoal_tac"Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>sa v. v = s A)) ''C2P'' tr4")
       prefer 2
      subgoal
        apply(auto simp add: in_assn.simps in_inv_assn.simps srb2gsrb.simps)
        done
      apply(subgoal_tac"Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>sa v. v = s B)) ''C2P'' tr5")
       prefer 2
      subgoal
        apply(auto simp add: in_assn.simps in_inv_assn.simps srb2gsrb.simps)
        done
      using P_inv_snoc[of a b Fc tr1 "s A" "s B" "tr2 @ tr3 @ tr4 @ tr5 "]
      apply(auto simp add:join_assn_def) by blast
    done
  done
  done
  done

lemma P_rep':
  "\<Turnstile> {\<lambda>s tr. (inv s \<and> s A = a \<and> s B = b \<and> s T = 0) \<and> (emp\<^sub>t tr)}
    Plant
   {\<lambda>s tr. \<exists>Fc . (s A = fst(last((a,b)#Fc)) \<and> s B = snd(last((a,b)#Fc)) \<and> s T = 0) 
         \<and> P_inv_ind a b Fc tr }"
  apply(rule Valid_strengthen_post)
   prefer 2
   apply(rule P_rep)
  by(auto simp add: entails_def)


inductive tot_block :: "real list  \<Rightarrow> tassn" where
  "tot_block  [] []"
| "(Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {})  @\<^sub>t
   Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. True) ({''P2C''}, {})  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = x)''P2C''  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' ) tr1\<Longrightarrow> 
   tot_block fc tr2 \<Longrightarrow>
   tot_block (x#fc) (tr1@tr2)"

lemma tot_block_snoc:
"tot_block fc tr1 \<Longrightarrow> 
  (Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {})  @\<^sub>t
   Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. True) ({''P2C''}, {})  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = x)''P2C''  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' ) tr2 \<Longrightarrow>
  tot_block (fc@[x]) (tr1@tr2)"
proof(induct rule : tot_block.induct)
case 1
  then show ?case 
    using tot_block.intros(2)[of x tr2 "[]" "[]"]
    using tot_block.intros(1) by auto
next
  case (2 x' tr1 fc tr)
  then show ?case 
    using tot_block.intros(2)[of x' tr1 "fc @ [x]" "tr@tr2"]
    by auto
qed

lemma tot_block_prop1:
"tot_block (x#list) = Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {})  @\<^sub>t
   Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. True) ({''P2C''}, {})  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = x)''P2C''  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t tot_block list"
apply(rule ext)
  subgoal for tr
proof-
  have 1:"tot_block (x#list) tr \<Longrightarrow> \<exists> tr1 tr2. (Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {})  @\<^sub>t
   Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. True) ({''P2C''}, {})  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = x)''P2C''  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'') tr1 \<and> tot_block list tr2 \<and> tr=tr1@tr2"
    apply(rule tot_block.cases[of "(x # list)" tr]) 
    by auto
  have 2:"tot_block (x#list) tr \<Longrightarrow> ((Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {})  @\<^sub>t
   Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. True) ({''P2C''}, {})  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = x)''P2C''  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'') @\<^sub>t tot_block list ) tr"
    using 1 join_assn_def by auto
  have 3:"((Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {})  @\<^sub>t
   Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. True) ({''P2C''}, {})  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = x)''P2C''  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'') @\<^sub>t tot_block list ) tr \<Longrightarrow>
    \<exists> tr1 tr2. (Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {})  @\<^sub>t
   Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. True) ({''P2C''}, {})  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = x)''P2C''  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'') tr1 \<and> tot_block list tr2 \<and> tr=tr1@tr2"
    by(auto simp add: join_assn_def)
  have 4:"((Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {})  @\<^sub>t
   Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. True) ({''P2C''}, {})  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = x)''P2C''  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'') @\<^sub>t tot_block list ) tr \<Longrightarrow> tot_block (x#list) tr"
    subgoal premises pre
    proof-
      obtain tr1 tr2 where g:"(Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {})  @\<^sub>t
   Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb(sb2gsb inv)) (\<lambda>_ _ . True))(\<lambda> d. True) ({''P2C''}, {})  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = x)''P2C''  @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'' @\<^sub>t
   IOinv\<^sub>t (\<lambda> _. True)(\<lambda> s v. v = p x)''C2P'') tr1" "tot_block list tr2" "tr=tr1@tr2"
        using pre 3 by auto
      then show ?thesis
        using tot_block.intros(2)[of x tr1 list tr2] by auto
    qed
  done
    then show ?thesis using 2 4 by(auto simp add: join_assoc)
  qed
  done
lemma g1:
 "combine_assn chs
     (Waitinv\<^sub>t r (\<lambda>d. d = 1) ({}, {}) @\<^sub>t P)
     (Waitinv\<^sub>t (\<lambda>_ _. True) ((<) 1) ({}, {}) @\<^sub>t Q) 
      \<Longrightarrow>\<^sub>t 
   (Waitinv\<^sub>t (pgsrb2gsrb r (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {}) 
      @\<^sub>t combine_assn chs P (Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> d. d > 0) ({}, {}) @\<^sub>t Q))"
proof-
  have *:"(Waitinv\<^sub>t (pgsrb2gsrb r (\<lambda>_ _ . True))(\<lambda> d. d = 1) ({}, {}) 
      @\<^sub>t combine_assn chs P (Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> d. d > 0) ({}, {}) @\<^sub>t Q)) tr"
    if "(Waitinv\<^sub>t r (\<lambda>d. d = 1) ({}, {}) @\<^sub>t P) tr1" 
       "(Waitinv\<^sub>t (\<lambda>_ _. True) ((<) 1) ({}, {}) @\<^sub>t Q)  tr2"
       "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof-
    from that(1) [unfolded join_assn_def]
    obtain tr11 tr12 where a:"Waitinv\<^sub>t r (\<lambda>d. d = 1) ({}, {}) tr11" 
                             "P tr12" "tr1 = tr11@tr12"
      by auto
    from that(2) [unfolded join_assn_def]
    obtain tr21 tr22 where b:"Waitinv\<^sub>t (\<lambda>_ _. True) ((<) 1) ({}, {}) tr21"
                                "Q tr22" "tr2 = tr21@tr22"
      by auto
    have 1:"(Waitinv\<^sub>t (pgsrb2gsrb r (\<lambda>_ _. True)) (\<lambda>d. d = 1) ({}, {}) @\<^sub>t
     combine_assn chs P (Waitinv\<^sub>t (\<lambda>_ _. True) ((<) 0) ({}, {}) @\<^sub>t Q))
     tr" if "combine_blocks chs (WaitBlk (ereal 1) d ({}, {}) # tr12)
     (WaitBlk (ereal p1) p2 ({}, {}) # tr22) tr" "p1>1" "\<forall>t\<in>{0..1}. r (d t) t" for r d p1 p2
      using that(1)
      apply (elim combine_blocks_waitE3)
      using that apply auto
      subgoal for blks
        apply (subst join_assn_def)
        apply(rule exI[where x= "[WaitBlk (ereal 1) (\<lambda>t. ParState (d t) (p2 t)) ({}, {})]"])
        apply(rule exI[where x= blks])
        apply(auto simp add:wait_inv_assn.simps pgsrb2gsrb.simps combine_assn_def)
        apply(rule exI[where x="tr12"]) using a apply auto
        apply(rule exI[where x="(WaitBlk (ereal (p1 - 1)) (\<lambda>t. p2 (t + 1)) ({}, {}) # tr22)"]) 
        apply(auto simp add:wait_inv_assn.simps join_assn_def)
        apply(rule exI[where x= "[WaitBlk (ereal (p1 - 1)) (\<lambda>t. p2 (t + 1)) ({}, {})]"])
        using b by auto
      done
    show ?thesis
      using a(1) apply (cases rule: wait_inv_assn.cases)
      using b(1) apply (cases rule: wait_inv_assn.cases)
      apply auto
      using b(1) apply (cases rule: wait_inv_assn.cases)
       apply auto
      subgoal for d p1 p2
        using 1[of d p1 p2 r]
        using that a b by auto
      done
  qed
  then show ?thesis
         apply (subst combine_assn_def)
    by (auto simp add: entails_tassn_def)
qed 

lemma g2:
  assumes "ch \<in> chs"
  shows "combine_assn chs
     (WaitOutinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ({ch}, {}) ch  @\<^sub>t P)
     (Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> d. d > 0) ({}, {}) @\<^sub>t Q) 
      \<Longrightarrow>\<^sub>t 
   (Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_ _ . True))(\<lambda>_. True) ({ch}, {}) 
     @\<^sub>t combine_assn chs (WaitOutinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ({ch}, {}) ch  @\<^sub>t P)  Q )"
proof-
  have * :"(Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_ _ . True))(\<lambda>_. True) ({ch}, {}) 
     @\<^sub>t combine_assn chs (WaitOutinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ({ch}, {}) ch  @\<^sub>t P)  Q ) tr"
    if "(WaitOutinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ({ch}, {}) ch  @\<^sub>t P) tr1"
       "(Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> d. d > 0) ({}, {})  @\<^sub>t Q) tr2"
       "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "WaitOutinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ({ch}, {}) ch  tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "Waitinv\<^sub>t (\<lambda>_ _. True) (\<lambda> d. d > 0) ({}, {}) tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    have g:"(Waitinv\<^sub>t (pgsrb2gsrb (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_ _. True)) (\<lambda>_. True) ({ch}, {}) @\<^sub>t
     combine_assn chs (WaitOutinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ({ch}, {}) ch @\<^sub>t P) Q)
     tr" if "combine_blocks chs (WaitBlk (ereal d) p ({ch}, {}) # OutBlock ch v # tr12) (WaitBlk (ereal d') p' ({}, {}) # tr22) tr" 
      "d>0" "d'>0" "\<forall>t\<in>{0..d}. gsb2gsrb (sb2gsb local.inv) (p t) t" "srb2gsrb (\<lambda>s v. v = s X) (p d) v"for v d p d' p'
    proof -
      have "d < d' \<or> d = d' \<or> d > d'" by auto
      then show ?thesis
      proof (elim disjE)
        assume d1: "d < d'"
        have d1': "ereal d < ereal d'"
          using d1 by auto
        show ?thesis
          using that
          apply (elim combine_blocks_waitE3) apply (rule that(2))
            apply (rule d1') apply auto
          using assms(1) combine_blocks_pairE2 by blast
      next
        assume d2: "d = d'"
        show ?thesis
          using that(1)
          unfolding d2[symmetric]
          apply (elim combine_blocks_waitE2)
          apply auto
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk (ereal d) (\<lambda>t. ParState (p t) (p' t)) ({ch}, {})]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal using d2 that using wait_inv_assn.intros(2)[of d "(\<lambda>_. True)" "(pgsrb2gsrb (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_ _. True))" "(\<lambda>t. ParState (p t) (p' t))" "({ch}, {})"]
              by(auto simp add:pgsrb2gsrb.simps)
            apply (rule conjI)
             prefer 2 subgoal by auto
            unfolding combine_assn_def
            apply (rule exI[where x="(OutBlock ch v # tr12)"])
            apply (rule exI[where x=tr22])
            apply (rule conjI)
             prefer 2 subgoal using b(2) by auto
            unfolding join_assn_def
            apply (rule exI[where x="[OutBlock ch v]"])
            apply (rule exI[where x=tr12])
            using that(2,4,5)
            by (auto simp add: a(2) wait_out_inv_assn.simps gsb2gsrb.simps)
          done
      next
        assume d3: "d > d'"
        have d3': "ereal d > ereal d'"
          using d3 by auto
        show ?thesis
          using that(1)
          apply (elim combine_blocks_waitE4) apply (rule that(3))
            apply (rule d3') apply auto
          subgoal for blks'
            unfolding pure_assn_def conj_assn_def
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk (ereal d') (\<lambda>t. ParState (p t) (p' t)) ({ch}, {})]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal using wait_inv_assn.intros(2)[of d' "(\<lambda>_. True)" "(pgsrb2gsrb (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_ _. True))" " (\<lambda>t. ParState (p t) (p' t))" "({ch}, {})"]
              using that(3,4,5) d3 by(auto simp add:pgsrb2gsrb.simps)
            apply (rule conjI)
             prefer 2 subgoal by auto
            unfolding combine_assn_def
            apply (rule exI[where x="WaitBlk (ereal (d - d')) (\<lambda>t. p (t + d')) ({ch}, {}) # OutBlock ch v # tr12"])
            apply (rule exI[where x=tr22])
            apply (rule conjI)
             prefer 2 subgoal apply (rule conjI)
               apply (rule b(2)) by auto
            unfolding join_assn_def
            apply (rule exI[where x="[WaitBlk (ereal (d - d')) (\<lambda>t. p (t + d')) ({ch}, {}), OutBlock ch v]"])
            apply (rule exI[where x=tr12])
            apply (rule conjI)
            subgoal
              using that d3
              using wait_out_inv_assn.intros(2)[of "d-d'" "(\<lambda>_. True)" "(gsb2gsrb (sb2gsb local.inv))" "(\<lambda>t. p (t + d'))" "(srb2gsrb (\<lambda>s v. v = s X))" "v" "({ch}, {})" ch]
               by(auto simp add:gsb2gsrb.simps)
            using a(2) by auto
          done
      qed
    qed
    show ?thesis
      using a(1) apply (cases rule: wait_out_inv_assn.cases)
      using b(1) apply (cases rule: wait_inv_assn.cases)
        apply auto
      subgoal for v d p s
        using that a b apply auto
        using assms combine_blocks_pairE2 by blast
      using b(1) apply (cases rule: wait_inv_assn.cases)
       apply auto
      subgoal for d p v d' p'
        using g[of d p v d' p'] that a b by auto
      done
  qed
  then show ?thesis
    apply (subst combine_assn_def)
    by (auto simp add: entails_tassn_def)
qed
        











lemma entails_tassn_cancel_both_m:
  assumes "P \<Longrightarrow>\<^sub>t Q"
    and "\<forall>tr. P tr \<longrightarrow> f"
    and "f \<Longrightarrow> R \<Longrightarrow>\<^sub>t S"
  shows "P @\<^sub>t R \<Longrightarrow>\<^sub>t Q @\<^sub>t S"
  using assms
  by (auto simp add: entails_tassn_def join_assn_def)
 

lemma combine:
 "combine_assn {''P2C'', ''C2P''} (P_inv_ind a a ps) (C_inv_ind cs) \<Longrightarrow>\<^sub>t  tot_block cs"
proof(induction ps arbitrary: cs a)
case Nil
  then show ?case 
  proof(cases cs)
    case Nil
    then show ?thesis 
      apply (auto simp add:entails_tassn_def pure_assn_def conj_assn_def same_pair.intros)
      subgoal premises pre for tr
    proof-
      have 1:"P_inv_ind a a [] = emp\<^sub>t"
        using P_inv_ind.cases 
        apply(auto simp add: emp_assn_def)
        using P_inv_ind.intros(1) by blast
      have 2:"C_inv_ind [] = emp\<^sub>t"
        using C_inv_ind.cases 
        apply(auto simp add: emp_assn_def)
        using C_inv_ind.intros(1) by blast
      have 3:"tot_block [] = emp\<^sub>t"
        using tot_block.cases 
        apply(auto simp add: emp_assn_def)
        using tot_block.intros(1) by blast
      show ?thesis
        using 1 2 3 pre by simp
    qed
    done
  next
    case (Cons c list)
    then show ?thesis 
      apply(auto simp add:same_pair.intros C_inv_prop1[of c list] P_inv_prop0)
      apply (rule entails_tassn_trans)
       apply (subst combine_assn_emp_waitinv)
       apply auto
      apply (rule entails_tassn_trans)
       apply (subst combine_assn_emp_ininv)
      apply auto
      by (rule false_assn_entails)
  qed

next
  case (Cons pp ps)
  note Cons1 = Cons
  then show ?case 
  proof (cases cs)
      case Nil
      then show ?thesis
        apply(cases pp)
        apply(auto simp add:C_inv_prop0 P_inv_prop1 same_pair.intros)
        subgoal for a' b'
          apply (rule entails_tassn_trans)
           apply (subst combine_assn_waitinv_emp)
           apply auto
      apply (rule entails_tassn_trans)
           apply (subst combine_assn_waitoutinv_emp)
           apply auto
          done
        done
    next
      case (Cons c list)
      then show ?thesis
        apply (cases pp)
        subgoal for a' b'
         apply(auto simp add:P_inv_prop1 C_inv_prop1 tot_block_prop1 )
          apply (rule entails_tassn_trans)
           apply(subst g1)
           apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply(subst g2)
            apply auto
          apply (rule entails_tassn_cancel_left)
          apply (rule entails_tassn_trans)
           apply(subst combine_assn_waitoutinv_ininv)
             apply auto
          apply (rule entails_tassn_cancel_both)
          subgoal by(auto simp add:entails_tassn_def io_inv_assn.simps pgsb2gsb.simps pgsrb2gsrb.simps srb2gsrb.simps)
          apply (rule entails_tassn_trans)
           apply(subst combine_assn_ininv_outinv)
            apply auto
          apply (rule entails_tassn_cancel_both_m[where f="a' = p c"])
          subgoal by(auto simp add:entails_tassn_def io_inv_assn.simps pgsb2gsb.simps pgsrb2gsrb.simps srb2gsrb.simps)
          subgoal by(auto simp add:entails_tassn_def io_inv_assn.simps pgsb2gsb.simps pgsrb2gsrb.simps srb2gsrb.simps)
          apply (rule entails_tassn_trans)
           apply(subst combine_assn_ininv_outinv)
            apply auto
          apply (rule entails_tassn_cancel_both_m[where f="b' = p c"])
          subgoal by(auto simp add:entails_tassn_def io_inv_assn.simps pgsb2gsb.simps pgsrb2gsrb.simps srb2gsrb.simps)
          subgoal by(auto simp add:entails_tassn_def io_inv_assn.simps pgsb2gsb.simps pgsrb2gsrb.simps srb2gsrb.simps)
          apply auto
          using Cons1
          by auto
        done
    qed
  qed


lemma sing_gassn_split_m3:
  "sing_gassn (\<lambda>s tr. P1 s \<and> P2 s \<and> P3 s \<and> Q tr) = (state_gassn (sing_assn (\<lambda> s. P1 s \<and> P2 s \<and> P3 s)) \<and>\<^sub>g trace_gassn Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: state_gassn_def trace_gassn_def and_gassn_def)
  done


lemma system_Prop:
 "\<Turnstile>\<^sub>p {pair_assn (\<lambda>s. inv s \<and> s A = a \<and> s B = a \<and> s T = 0 )
               (\<lambda>s. s X = x)}
      Parallel (Single Plant)
                     {''P2C'', ''C2P''}
                     (Single Control)
    {\<exists>\<^sub>g cs. trace_gassn (tot_block cs)}"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
     apply(rule P_rep')
    apply(rule C_rep)
   apply (auto simp add: sing_gassn_split sing_gassn_ex sing_gassn_split_m3)
    apply (rule sync_gassn_ex_pre_left)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for ps cs
unfolding sync_gassn_state_left sync_gassn_state_right
  apply (rule entails_ex_gassn)
  apply(rule exI[where x="cs"])
  apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
     apply (rule entails_tassn_trans)
      prefer 2 apply(rule combine)
  apply (rule combine_assn_mono)
  apply (auto simp add: entails_tassn_def entails_gassn_def and_gassn_def)
  done
  done
end
end