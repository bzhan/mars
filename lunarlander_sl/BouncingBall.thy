section \<open>Bouncing ball example\<close>

theory BouncingBall
  imports BigStep
begin


text \<open>From Derivs in AFP/Green.\<close>
lemma has_vector_derivative_divide[derivative_intros]:
  fixes a :: "'a::real_normed_field"
  shows "(f has_vector_derivative x) F \<Longrightarrow> ((\<lambda>x. f x / a) has_vector_derivative (x / a)) F"
  unfolding divide_inverse by (fact has_vector_derivative_mult_left)

locale bouncing_ball =
  fixes g :: real and
    c :: real and
    H :: real
  assumes pos_g: "g > 0" and
    pos_c: "c > 0" and
    le1_c: "c \<le> 1"
begin

definition V :: char where "V = CHR ''v''"

lemma vars_distinct: "X \<noteq> V"
  unfolding X_def V_def by auto

subsection \<open>Single run\<close>


lemma bouncingBallOne:
  assumes "v0 > 0"
  shows "Valid
    (\<lambda>t. t = Trace ((\<lambda>_. 0)(V := v0)) [])
    (Cont (ODE {X, V} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (\<lambda>s. s X > 0 \<or> s V > 0))
    (\<lambda>t. t = Trace ((\<lambda>_. 0)(V := v0))
        [ODEBlock (2 * v0/g) (restrict (\<lambda>t. (\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t)) {0..2 * v0/g})])"
proof -
  have main: "restrict p2 {0..d2} = restrict (\<lambda>t. (\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t)) {0..2 * v0/g} \<and> d2 = 2 * v0/g"
    if cond: "0 \<le> d2"
       "ODEsol (ODE {X, V} ((\<lambda>_ _. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) p2 d2"
       "\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> p2 t X > 0 \<or> p2 t V > 0"
       "\<not> (p2 d2 X > 0 \<or> p2 d2 V > 0)"
       "p2 0 = ((\<lambda>_. 0)(V := v0))"
     for p2 d2
  proof -
    interpret loc:ll_on_open_it "{-1<..}" "(\<lambda>t v. ODE2Vec (ODE {X, V} ((\<lambda>_ _. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (vec2state v))" "UNIV" "0"
      apply standard
      apply auto
      subgoal proof -
        show ?thesis
          unfolding state2vec_def vec2state_def fun_upd_def
          sorry
      qed
      done
    have step2: "((\<lambda>t. state2vec ((\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t)))
                    solves_ode
                 ((\<lambda>t. \<lambda>v. ODE2Vec (ODE {X, V} ((\<lambda>_ _. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (vec2state v)))) {0..2 * v0/g} UNIV"
     unfolding solves_ode_def has_vderiv_on_def
     apply auto
     apply (rule has_vector_derivative_projI)
     apply (auto simp add: vars_distinct state2vec_def)
      apply (rule has_vector_derivative_eq_rhs)
     unfolding power2_eq_square apply (fast intro!: derivative_intros) apply simp
     apply (rule has_vector_derivative_eq_rhs)
      apply (fast intro!: derivative_intros) apply simp
     done
   have step4: "(loc.flow 0 (state2vec ((\<lambda>_. 0)(V := v0)))) t = (\<lambda>t. state2vec ((\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t))) t" if "t \<in> {0..2 * v0/g}" for t
     apply (rule loc.maximal_existence_flow(2)[OF step2])
     using that by (auto simp add: state2vec_def)
   have step5: "((\<lambda>t. state2vec(p2 t)) solves_ode ((\<lambda>t. \<lambda>v. ODE2Vec (ODE {X, V} ((\<lambda>_ _. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g))))(vec2state v)))) {0..d2} UNIV"
     using cond(2) unfolding ODEsol_def solves_ode_def by auto
   have step7: "loc.flow 0 (state2vec ((\<lambda>_. 0)(V := v0))) t = state2vec (p2 t)" if "t\<in>{0..d2}" for t
     apply (rule loc.maximal_existence_flow(2)[OF step5])
     using cond(1,5) that by auto
   have step8: "2 * v0 / g \<le> d2"
   proof (rule ccontr)
     assume 0:" \<not> (2 * v0 / g \<le> d2)"
     from 0 have 1:"(\<lambda>t. state2vec((\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t))) d2 = (\<lambda>t. state2vec(p2 t)) d2"
       using step4[of d2] step7[of d2] cond(1) by auto
     from 1 have 2:"((\<lambda>_. 0)(X := v0 * d2 - g * d2\<^sup>2 / 2, V := v0 - g * d2)) = p2 d2"
       unfolding state2vec_def by auto
     have arith: "g * d2\<^sup>2 < v0 * d2 * 2" if "\<not> 2 * v0 / g \<le> d2" "d2 > 0"
     proof -
       have "2 * v0 / g > d2" using that by arith
       then have "2 * v0 > d2 * g" using pos_g
         using pos_less_divide_eq by auto
       moreover have "d2 * g \<ge> 0" using pos_g cond(1) by auto
       ultimately have "2 * v0 * d2 > d2 * g * d2" using \<open>d2 > 0\<close> by simp  
       then show ?thesis
         unfolding power2_eq_square by (auto simp add: algebra_simps)
     qed
     have 3: "p2 d2 X > 0 \<or> p2 d2 V > 0"
     proof (cases "d2 > 0")
       case True
       then show ?thesis
         unfolding 2[symmetric] apply (auto simp add: vars_distinct)
         using True arith 0 by auto
     next
       case False
       have "d2 = 0" using False cond(1) by auto 
       then show ?thesis
         unfolding 2[symmetric] using assms by auto
     qed
     then show "False" using 3 cond(4) by auto
   qed
   have step9: "2 * v0 / g \<ge> d2"
   proof (rule ccontr)
     assume 0:"\<not> d2 \<le> 2 * v0 / g" 
     from 0 have 1:"(\<lambda>t. state2vec((\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t))) (2 * v0 / g) = (\<lambda>t. state2vec(p2 t)) (2 * v0 / g)"
       using step4[of "2 * v0 / g"] step7[of "2 * v0 / g"] assms pos_g by auto
     from 1 have 2:"((\<lambda>_. 0)(X := 0, V := - v0)) = p2 (2 * v0 / g)"
       unfolding state2vec_def using pos_g by (auto simp add: power2_eq_square algebra_simps)
     have 3:"p2 (2 * v0 / g) X > 0 \<or> p2 (2 * v0 / g) V > 0" using cond(1,3) 0
       using assms pos_g by auto
     show False using 3
       using assms by (auto simp add: 2[symmetric] vars_distinct)
   qed
   have step10: "d2 = 2 * v0 / g" using step8 step9 by auto
   have step11: "t\<in>{0..2 * v0 / g} \<Longrightarrow> (p2 t) = ((\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t))" for t
     using step4 step7 step10 by (metis vec_state_map1)
   have step12: "restrict p2 {0..d2} = restrict (\<lambda>t. ((\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t))) {0..2 * v0 / g}"
     using step10 step11 unfolding restrict_def by auto
    show ?thesis using step10 step12 by auto
  qed
  show ?thesis
    apply(rule Valid_ode_solution2[where d="2 * v0 / g" and p="\<lambda>t. (\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t)"])
    using main by auto
qed

definition Inv :: "state \<Rightarrow> real" where
  "Inv = (\<lambda>s. (s V) ^ 2 + 2 * g * s X)"

lemma bouncingBallInv:
  assumes "v0 > 0"
  shows "Valid
    (\<lambda>t. t = Trace ((\<lambda>_. 0)(V := v0)) [])
    (Cont (ODE {X, V} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (\<lambda>s. s X > 0 \<or> s V > 0))
    (\<lambda>t. \<exists>d p. t = extend_trace (Trace ((\<lambda>_. 0)(V := v0)) []) (ODEBlock d (restrict p {0..d})) \<and>
               d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) []) \<and>
               (\<forall>t. 0\<le>t \<and> t\<le>d \<longrightarrow> Inv (p t) = Inv (p 0)))"
proof -
  show ?thesis
    apply (rule Valid_ode_invariant)
    unfolding Inv_def 
     apply (auto simp add: vec2state_def)[1]
     apply (auto intro!: derivative_intros)[1]
    apply (auto simp add: vec2state_def state2vec_def)
    using vars_distinct by auto
qed


inductive valid_blocks :: "real \<Rightarrow> trace_block list \<Rightarrow> bool" where
  "v0 > 0 \<Longrightarrow> valid_blocks v0 []"
| "valid_blocks v0 blks \<Longrightarrow>
   d \<ge> 0 \<Longrightarrow>
   p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<Longrightarrow>
   (\<forall>t. 0\<le>t \<and> t\<le>d \<longrightarrow> Inv (p t) = Inv (p 0)) \<Longrightarrow>
   valid_blocks v0 (blks @ [ODEBlock d (restrict p {0..d}), TauBlock ((p d)(V := - c * p d V))])"


lemma bouncingBall:
  assumes "v0 > 0"
  shows "Valid
    (\<lambda>t. t = Trace ((\<lambda>_. 0)(V := v0)) [])
    (Rep (Cont (ODE {X, V} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (\<lambda>s. s X > 0 \<or> s V > 0);
          Assign V (\<lambda>s. - c * s V)))
    (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks v0 blks)"
proof -
  have 1: "Valid
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks v0 blks)
     (Cont (ODE {X, V} ((\<lambda>_ _. 0)(X := \<lambda>s. s V, V := \<lambda>_. - g))) (\<lambda>s. 0 < s X \<or> 0 < s V))
     (\<lambda>t. \<exists>blks d p.
             t = Trace ((\<lambda>_. 0)(V := v0)) (blks @ [ODEBlock d (restrict p {0..d})]) \<and>
             valid_blocks v0 blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
             (\<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv (p t) = Inv (p 0)))"
    apply (simp only: Valid_ex_pre Valid_and_pre, clarify)
    subgoal premises pre for blks
      apply (rule Valid_post)
      prefer 2
       apply (rule Valid_ode_invariant[where inv=Inv])
        prefer 3 apply clarify
      subgoal for blks2 d p
        apply (rule exI[where x=blks]) apply (rule exI[where x=d]) apply (rule exI[where x=p])
        using pre by fastforce
      sorry
    done
  have 2: "Valid
     (\<lambda>t. \<exists>blks d p.
             t = Trace ((\<lambda>_. 0)(V := v0)) (blks @ [ODEBlock d (restrict p {0..d})]) \<and>
             valid_blocks v0 blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
             (\<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv (p t) = Inv (p 0)))
     (V ::= (\<lambda>s. - (c * s V)))
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks v0 blks)"
    apply (simp only: Valid_ex_pre Valid_and_pre, clarify)
    subgoal premises pre for blks d p
      apply (rule Valid_assign2)
      using valid_blocks.intros(2)[of v0 blks d p, OF pre]
      by (auto simp add: pre(2) end_of_blocks_append)
    done
  have 3: "Valid
      (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks v0 blks)
      (Rep (Cont (ODE {X, V} ((\<lambda>_ _. 0)(X := \<lambda>s. s V, V := \<lambda>_. - g))) (\<lambda>s. 0 < s X \<or> 0 < s V); V ::= (\<lambda>s. - c * s V)))
      (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks v0 blks)"
    apply (auto intro!: Valid_rep Valid_seq)
    using 1 2 by auto
  show ?thesis
    apply (rule Valid_pre)
    using 3 valid_blocks.intros(1) assms by auto
qed


lemma valid_blocks_prop:
  "valid_blocks v0 blks \<Longrightarrow>
   s = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<Longrightarrow>
   Inv s \<le> v0 ^ 2"
proof (induction arbitrary: s rule: valid_blocks.induct)
  case (1 v0)
  then show ?case
    by (auto simp add: Inv_def vars_distinct)
next
  case (2 v0 blks d p)
  have s1: "s = (\<lambda>a. if a = V then - (c * p d V) else p d a)"
    using 2(6) by (auto simp add: end_of_blocks_append)
  have s2: "Inv (p 0) \<le> v0 ^ 2"
    using 2(3) 2(5) unfolding end_of_trace.simps by blast
  have s3: "Inv (p 0) = Inv (p d)"
    using 2(4) 2(2) by (metis order_refl)
  have s4: "Inv s \<le> Inv (p d)"
  proof -
    have "p d V * p d V \<ge> 0" by auto
    then have s2: "c * (p d V * p d V) \<le> p d V * p d V"
      using pos_c le1_c by (metis mult.commute mult_left_le)
    then have s3: "c * (c * (p d V * p d V)) \<le> c * (p d V * p d V)"
      using pos_c le1_c by simp
    have s4: "(c * p d V)^2 \<le> (p d V)^2"
      using s2 s3 unfolding power2_eq_square by (auto simp add: algebra_simps)
    then show ?thesis
      by (auto simp add: Inv_def s1 vars_distinct)
  qed
  show ?case
    using s2 s3 s4 by auto
qed


lemma bouncingBallFinal:
  assumes "v0 > 0"
  shows "Valid
    (\<lambda>t. t = Trace ((\<lambda>_. 0)(V := v0)) [])
    (Rep (Cont (ODE {X, V} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (\<lambda>s. s X > 0 \<or> s V > 0);
          Assign V (\<lambda>s. - c * s V)))
    (\<lambda>t. Inv (end_of_trace t) \<le> v0 ^ 2)"
  apply (rule Valid_post[OF _ bouncingBall])
  using valid_blocks_prop assms by auto


end  (* locale bouncing_ball *)

end
