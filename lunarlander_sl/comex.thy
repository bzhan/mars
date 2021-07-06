theory comex
  imports HHLProver.newParallel 

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

inductive same_pair :: "(real \<times> real) list \<Rightarrow> bool" where
  "same_pair []"
| " a = b \<Longrightarrow> same_pair Fcs \<Longrightarrow>same_pair ((a,b)#Fcs)"

inductive_cases same_pair_elim: "same_pair l"


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

          
end
end