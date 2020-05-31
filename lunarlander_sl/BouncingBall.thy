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

lemma vars_distinct: "X \<noteq> V" "V \<noteq> X"
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
  have 1: "ODEsol (ODE {X, V} ((\<lambda>_ _. 0)(X := \<lambda>s. s V, V := \<lambda>_. - g))) (\<lambda>t. (\<lambda>_. 0)(X := v0 * t - g * t\<^sup>2 / 2, V := v0 - g * t)) (2 * v0 / g)"
    unfolding ODEsol_def solves_ode_def has_vderiv_on_def
    apply auto using assms pos_g apply simp
    apply (rule has_vector_derivative_projI)
    apply (auto simp add: vars_distinct state2vec_def)
     apply (rule has_vector_derivative_eq_rhs)
    unfolding power2_eq_square apply (fast intro!: derivative_intros) apply simp
    apply (rule has_vector_derivative_eq_rhs)
     apply (fast intro!: derivative_intros) apply simp
    done
  have 2: "local_lipschitz {- (1::real)<..} UNIV
     (\<lambda>t v. state2vec (\<lambda>a. if a = X \<or> a = V then ((\<lambda>_ _. 0)(X := \<lambda>s. s V, V := \<lambda>_. - g)) a (vec2state v) else 0))"
  proof -
    have bounded: "bounded_linear (\<lambda>(y::vec). \<chi> a. if a = X then y $ V else 0)"
      apply (rule bounded_linearI')
      using vec_lambda_unique by fastforce+
    show ?thesis
      unfolding state2vec_def vec2state_def fun_upd_def
      apply (rule c1_implies_local_lipschitz[where f'="(\<lambda>(t,y). Blinfun(\<lambda>y. \<chi> a. if a = X then y $ V else 0))"])
      apply (auto simp add: bounded_linear_Blinfun_apply[OF bounded])
      subgoal premises pre for t x
        unfolding has_derivative_def apply (auto simp add: bounded)
        apply (rule vec_tendstoI)
        by (auto simp add: vars_distinct)
      done
  qed
  have 3: "g * t\<^sup>2 < v0 * t * 2" if "t < 2 * v0 / g" "\<not> g * t < v0" "0 \<le> t" for t
  proof -
    have "t \<noteq> 0"
      using that(2) assms by auto
    then have "t > 0"
      using that(3) by auto
    have "2 * v0 / g > t" using that by arith
    then have "2 * v0 > t * g" using pos_g
      using pos_less_divide_eq by auto
    moreover have "t * g \<ge> 0" using pos_g that(3) by auto
    ultimately have "2 * v0 * t > t * g * t" using \<open>t > 0\<close> by simp  
    then show ?thesis
      unfolding power2_eq_square by (auto simp add: algebra_simps)
  qed
  have 4: "g * (2 * v0 / g)\<^sup>2 < 4 * (v0 * v0) / g \<Longrightarrow> False"
    apply (auto simp add: power2_eq_square)
    using pos_g by auto
  show ?thesis
    apply (rule Valid_ode_unique_solution[of "2 * v0/g" _ "\<lambda>t. (\<lambda>_. 0)(X := v0*t-g*t^2/2, V := v0-g*t)"])
    using assms vars_distinct pos_g 1 2 3 4 by auto
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
      apply (auto simp add: vec2state_def Inv_def)[1]
      apply (auto intro!: derivative_intros)[1]
      by (auto simp add: state2vec_def vars_distinct)
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
