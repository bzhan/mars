theory comex
  imports newParallel 

begin



locale comex =
  fixes t1 :: real  
  fixes t2 :: real  
  fixes t3 :: real 
  assumes t1: "t1 > 0"
  assumes t2: "t2 > 0"
  assumes t3: "t3 > 0"
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
  Wait (\<lambda> t. t1);
  Cm (''P2C''[?]X);
  Cm (''C2P''[!](\<lambda> s. s X + 1));
  Cm (''C2P''[!](\<lambda> s. s X + 1));
  Wait (\<lambda> t. t2);
  Cm (''P2C''[?]X);
  Cm (''C2P''[!](\<lambda> s. s X + 1));
  Cm (''C2P''[!](\<lambda> s. s X + 1));
  Wait (\<lambda> t. t3);
  Cm (''P2C''[?]X);
  Cm (''C2P''[!](\<lambda> s. s X + 1));
  Cm (''C2P''[!](\<lambda> s. s X + 1))
) "

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
  @\<^sub>t Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) ({''P2C''}, {})
  @\<^sub>t Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ''P2C'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = a')) ''C2P'' 
  @\<^sub>t Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = b')) ''C2P'') tr1 
     \<and> P_inv_ind a' b' Fcs tr2) \<Longrightarrow> P_inv_ind a b ((a',b')#Fcs) (tr1@tr2)"

inductive_cases P_inv_elim: "P_inv_ind a b l tr"

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
  @\<^sub>t Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> _. True) ({''P2C''}, {}) 
  @\<^sub>t out_inv_assn (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ''P2C'' 
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


lemma same_pair_prop5:
"\<not> same_pair ((a, b) # list1) \<Longrightarrow>  list2 \<noteq> [] \<Longrightarrow>P_inv_ind a b (list1 @ list2) tr"
  apply(induct list2 arbitrary: a b list1 tr)
  apply auto
  subgoal premises pre for a' b' list2 a b list1 tr
  proof-
    have "\<not> same_pair ((a, b) # (list1@[(a',b')]))"
    proof(rule ccontr)
      assume "\<not> \<not> same_pair ((a, b) # list1 @ [(a', b')])"
      then have "same_pair ((a, b) # list1 @ [(a', b')])" by auto
      then have "same_pair ((a, b) # list1)"
        using same_pair_prop4[of "(a, b) # list1" "[(a', b')]"]
        by auto
      then show False using pre by auto
    qed
    then show ?thesis 
      using pre(1)[of a b "list1 @ [(a', b')]" tr] 
  qed
  done


theorem Valid_post_imp:
  assumes "\<Turnstile> {P} c {Q1}"
    and "\<Turnstile> {P} c {\<lambda>s tr. Q1 s tr \<longrightarrow> Q2 s tr}"
  shows "\<Turnstile> {P} c {\<lambda>s tr. Q1 s tr \<and> Q2 s tr}"
  using assms unfolding Valid_def entails_def by blast

lemma P_rep:
  "\<Turnstile> {\<lambda>s tr. inv s \<and> s A = a \<and> s B = b \<and> s T = 0 \<and> (emp\<^sub>t tr)}
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
                \<and> (same_pair (((a, b) # Fc)) 
    \<longrightarrow> (P_inv_ind a b Fc @\<^sub>t Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda> d. d = 1) ({}, {})) t )
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
        apply(rule Valid_strengthen_post[where Q = "\<lambda> s t. s A = fst (last ((a, b) # Fc)) \<and>
               s B = snd (last ((a, b) # Fc)) \<and> ((s T = 1 \<longrightarrow>((same_pair ((a, b) # Fc) \<longrightarrow>
                (P_inv_ind a b Fc @\<^sub>t Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {}))
                 t))) \<and> (
               (same_pair ((a, b) # Fc) \<longrightarrow> local.inv s)))"])
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
               same_pair ((a, b) # Fc) \<longrightarrow>
               (P_inv_ind a b Fc @\<^sub>t
                Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {}))
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
          using pre(6,8,10,13) by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 10:"\<forall>t\<in>{0 .. d}. p t B = b"
          using 9 pre(13) apply(elim ode_inv_assn_elim)  
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
        have 11:"ode_inv_assn (\<lambda>s. s A = s1 A) tr2"
          using pre(6,8,10,13) by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 12:"\<forall>t\<in>{0 .. d}. p t A = a"
          using 11 pre(13) apply(elim ode_inv_assn_elim)  
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
          using pre(2,3,12) using same_pair.cases 
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
        have 21:"Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {}) 
                  [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
          apply(auto simp add:wait_inv_assn.simps)
          apply(rule exI[where x= "(\<lambda>\<tau>. State (p \<tau>))"])
          apply(auto simp add:gsb2gsrb.simps sb2gsb.simps inv_def)
          using 20 3 by auto
        show ?thesis using 21 pre apply(auto simp add: join_assn_def) done
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
      by auto
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
        have 11:"ode_inv_assn (\<lambda>s. s A = s1 A) tr2"
          using pre by(auto simp add:join_assn_def ode_inv_assn.simps)
        have 12:"\<forall>t\<in>{0 .. d}. p t A = fst (last Fc)"
          using 11 pre(13) apply(elim ode_inv_assn_elim)  
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
          using pre same_pair_prop1 same_pair_prop3
          by auto
        have 14:"((\<lambda>t. p t X + p t Y) has_derivative
             (\<lambda>s. s * (p t A * (p t X)\<^sup>2 + p t B * p t Y * p t X)))
             (at t within {0..d})" if "t\<in>{0..d}" for t
          using 8 that by (auto simp add: state2vec_def)
        have 15:"((\<lambda>t. (\<lambda> s. s X + s Y) (p t)) has_vderiv_on (\<lambda> t . (\<lambda> t. (fst (last Fc)) * p t X) t * ((\<lambda>t. (\<lambda> s. s X + s Y) (p t))) t)) {0..d}"
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
        have 21:"Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {}) 
                  [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
          apply(auto simp add:wait_inv_assn.simps)
          apply(rule exI[where x= "(\<lambda>\<tau>. State (p \<tau>))"])
          apply(auto simp add:gsb2gsrb.simps sb2gsb.simps inv_def)
          using 20 3 by auto
        show ?thesis using 21 pre apply(auto simp add: join_assn_def) done
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
           (same_pair ((a, b) # Fc) \<longrightarrow>
            (P_inv_ind a b Fc @\<^sub>t
             Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>d. d = 1) ({}, {}) @\<^sub>t
             Waitinv\<^sub>t (gsb2gsrb(sb2gsb inv)) (\<lambda>_. True) ({''P2C''}, {}) @\<^sub>t
             out_inv_assn (\<lambda>_. True) (srb2gsrb (\<lambda> s v. v = s X)) ''P2C'')
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
          have 1:"Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ''P2C'' [OutBlock ''P2C'' (s X)]"
            by(auto simp add: out_inv_assn.simps srb2gsrb.simps)
          have 2:"Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) ({''P2C''}, {}) []"
            by(auto simp add: wait_inv_assn.simps)
          show ?thesis 
            using 1 2 pre(5)
            apply(auto simp add: join_assn_def) 
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
        show ?thesis
          apply(auto simp add: join_assn_def inv_def)
          subgoal using a3
            by (smt atLeastAtMost_iff pre(7))
          subgoal using b3
            by (smt atLeastAtMost_iff pre(7))
          subgoal 
            using 18 19 pre(5) apply(auto simp add: join_assn_def)
            by force
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
          have 1:"Outinv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>s v. v = s X)) ''P2C'' [OutBlock ''P2C'' (s X)]"
            by(auto simp add: out_inv_assn.simps srb2gsrb.simps)
          have 2:"Waitinv\<^sub>t (gsb2gsrb (sb2gsb local.inv)) (\<lambda>_. True) ({''P2C''}, {}) []"
            by(auto simp add: wait_inv_assn.simps)
          show ?thesis 
            using 1 2 pre(5)
            apply(auto simp add: join_assn_def) 
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
        show ?thesis
          apply(auto simp add: join_assn_def inv_def)
          subgoal using a3
            using pre(3) pre(7) by auto
          subgoal using b3
            using pre(4) pre(7) by auto
          subgoal 
            using 18 19 pre(5) apply(auto simp add: join_assn_def)
            by force
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
      apply (auto simp add: pure_assn_def conj_assn_def join_assn_def inv_def)
      subgoal for tr1 tr3 tr2
        using P_inv_snoc[of a b "[]" "[]" "s A" "s B" "tr1 @ tr2 @ tr3"]
        using P_inv_ind.intros(1)
      by auto
      subgoal for tr1 tr3 tr2
      using P_inv_snoc[of a b "[]" "[]" "s A" "s B" "tr1 @ tr2 @ tr3"]
        using P_inv_ind.intros(1)
      by auto
      subgoal for tr2b tr2a tr1a tr1b tr1c tr1d
       using P_inv_snoc[of a b "[]" tr1a "s A" "s B" "tr1b @ tr1c @ tr1d @ tr2a @ tr2b"]
      by auto
    subgoal for tr2b tr2a tr1a tr1b tr1c tr1d
      apply(subgoal_tac"Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>sa v. v = s A)) ''C2P'' tr2a")
       prefer 2
      subgoal
        apply(auto simp add: in_assn.simps in_inv_assn.simps srb2gsrb.simps)
        done
      apply(subgoal_tac"Ininv\<^sub>t (\<lambda>_. True) (srb2gsrb (\<lambda>sa v. v = s B)) ''C2P'' tr2b")
       prefer 2
      subgoal
        apply(auto simp add: in_assn.simps in_inv_assn.simps srb2gsrb.simps)
        done
      using P_inv_snoc[of a b "[]" tr1a "s A" "s B" "tr1b @ tr1c @ tr1d @ tr2a @ tr2b"]
      apply(auto simp add: join_assn_def) by blast
    done
  done
  apply clarify
  subgoal for s tr pt pb nb
    apply(rule exI[where x="Fc@[(s A, s B)]"])
    apply (auto simp add: pure_assn_def conj_assn_def join_assn_def inv_def)



          
end
end