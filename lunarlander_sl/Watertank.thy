theory Watertank
  imports BigStep
begin


locale watertank =
  fixes Qmax :: real and
    r :: real and
    g :: real and
    period :: real
  assumes
    Qmax_def: "Qmax = 0.007" and
    r_def: "r = 0.0254" and
    g_def: "g = 9.8" and
    period_def: "period = 0.01"
begin

definition H :: char where "H = CHR ''h''"
definition V :: char where "V = CHR ''v''"
definition T :: char where "T = CHR ''t''"

lemma vars_distinct: "H \<noteq> V" "V \<noteq> H" "H \<noteq> T" "T \<noteq> H" "V \<noteq> T" "T \<noteq> V"
  unfolding H_def V_def T_def by auto

definition plant :: proc where
  "plant = Rep (
    T ::= (\<lambda>_. 0);
    Cont (ODE ((\<lambda>_ _. 0)(H := (\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)), T := (\<lambda>_. 1)))) (\<lambda>s. s T < period);
    Cm (''wl''[!](\<lambda>s. s H));
    Cm (''cc''[?]V))"

definition controller :: proc where
  "controller = Rep (
    Wait period;
    Cm (''wl''[?]H);
    (IF (\<lambda>s. s H \<le> 0.31) (V ::= (\<lambda>_. 1)) Skip);
    (IF (\<lambda>s. s H \<ge> 0.59) (V ::= (\<lambda>_. 0)) Skip);
    Cm (''cc''[!](\<lambda>s. s V)))"

definition model :: pproc where
  "model = PProc [plant, controller]"

text \<open>Invariant for plant at start of loop\<close>
definition Inv1 :: "state \<Rightarrow> bool" where
  "Inv1 s \<longleftrightarrow> (s H \<ge> 0.3 \<and> s H \<le> 0.6 \<and> (s H \<le> 0.31 \<longrightarrow> s V = 1) \<and> (s H \<ge> 0.59 \<longrightarrow> s V = 0)\<and>(s V\<in>{0,1}))"

text \<open>Invariant for plant after running the ODE\<close>
definition Inv2 :: "state \<Rightarrow> bool" where
  "Inv2 s \<longleftrightarrow> (s H \<ge> 0.3 \<and> s H \<le> 0.6)"


thm contE


lemma INV:
  assumes "\<forall>t\<in>{0..d}. ((f :: real \<Rightarrow> real) has_derivative (\<lambda>s. s * f' t)) (at t within {0..d})"
    and "\<forall>t\<in>{0..d}. f t = c \<longrightarrow> f' t < 0"
    and "d>0"
    and "f 0 \<le> c"
  shows "\<forall>t\<in>{0..d}. f t \<le> c"
proof-
  assume "\<not> (\<forall>t\<in>{0..d}. f t \<le> c)"
  then obtain s where s:"f s > c" "s\<in>{0..d}"
    unfolding not_def assms(3) by force
  then have 1:"s>0 \<and> s\<le>d"
    using assms(4) 
    using atLeastAtMost_iff by fastforce
  have 2:"continuous_on {0..d} f"
    using assms(1)
    using has_derivative_continuous_on by fastforce
  then have 3:"continuous_on {0..s} f"
    using 1
    using continuous_on_subset by fastforce
  then obtain D where D:"D = vimage f {..c} \<inter> {0..s}"
    by auto
  then have 4:"D \<noteq> {}" using assms(4) 
    using "1" by auto
  have 5:"closed D"
    using closed_vimage_Int[of "{..c}" "{0..s}" f] D 3 by auto
  then have 6:"compact D"
    using compact_Int_closed[of "{0..s}" D] D 
    by (metis compact_Icc inf.idem inf_left_commute)
  obtain i where i:"i\<in>D" "\<forall>x\<in>D. x\<le>i" "{0..i}\<subseteq>{0..s}"
         using compact_attains_sup[of "D"] D 4 6 
         by (metis Int_iff atLeastAtMost_iff atLeastatMost_subset_iff less_eq_real_def)
  then have 7:"i<s" using D s 
    using less_eq_real_def by auto

  then show "False"
    
  
lemma Valid_of_ODE:
  assumes "Inv1 (end_of_trace (tr)) \<and> end_of_trace (tr) T = 0"
    shows "Valid
    (\<lambda>t. t = tr)
    (Cont (ODE ((\<lambda>_ _. 0)(H := (\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)), T := (\<lambda>_. 1)))) (\<lambda>s. s T < period))
    (\<lambda>t. \<exists>p. t = extend_trace tr (ODEBlock period (restrict p {0..period})) \<and> (\<forall> l\<in>{0..period}. Inv2 (p l)) \<and> p 0 = end_of_trace tr)"
proof-
  have 1:"d = period" 
    if cond:
    "ODEsol (ODE ((\<lambda>_ _. 0)(H := (\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)), T := (\<lambda>_. 1)))) p d "
    "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> (\<lambda>s. s T < period) (p t) "
    " \<not> (\<lambda>s. s T < period) (p d) "
    "p 0 = end_of_trace tr" 
    "d\<ge>0" for d and p
  proof-
    have 101:"((\<lambda>t. state2vec (p t)) has_vderiv_on
   (\<lambda>t. ODE2Vec (ODE ((\<lambda>_ _. 0)(H := \<lambda>s. s V * Qmax - pi * r\<^sup>2 * sqrt (2 * g * s H), T := \<lambda>_. 1)))
         (p t)))
   {0..d}" using cond(1) unfolding ODEsol_def by auto
    have 102:"((\<lambda>t. (p t) T) has_vderiv_on (\<lambda>t. 1)) {0..d}"
      using 101 has_vderiv_on_proj[of "(\<lambda>t. state2vec (p t))" "(\<lambda>t. ODE2Vec (ODE ((\<lambda>_ _. 0)(H := \<lambda>s. s V * Qmax - pi * r\<^sup>2 * sqrt (2 * g * s H), T := \<lambda>_. 1)))
         (p t))" "{0..d}" "T"] 
      unfolding state2vec_def apply auto
      unfolding state2vec_def by auto
    have 103:"p 0 T = 0" using cond assms by auto
    interpret loc:ll_on_open_it "{-1<..}" "(\<lambda>t v. 1)" "UNIV" "0"
        apply standard
          apply auto 
      by(rule local_lipschitz_constI)
    have 104: "((\<lambda>t. t) solves_ode (\<lambda>t. \<lambda>v. 1)) {0..} UNIV"
      unfolding solves_ode_def has_vderiv_on_def
      by auto
    have 105: "(loc.flow 0 0) t = (\<lambda>t. t) t" if "t \<in> {0..}" for t
        apply (rule loc.maximal_existence_flow(2)[OF 104])
      using that by (auto simp add: state2vec_def)
    have 106: "((\<lambda>t. (p t) T) solves_ode (\<lambda>t. \<lambda>v. 1)) {0..d} UNIV"
        using 102 unfolding solves_ode_def by auto
    have 107: "loc.flow 0 0 t =  ((\<lambda>t. (p t) T) t)" if "t\<in>{0..d}" for t
        apply (rule loc.maximal_existence_flow(2)[OF 106])
        using assms that 103 by auto
    have 108:"t =  (p t) T" if "t\<in>{0..d}" for t
      using 105 107 that by auto
    have 109:"\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> t<period" 
      using 108 cond(2) by auto
    have 110:"d\<ge>period"
      using 108 cond by auto
    show ?thesis using 109 110 period_def cond(5) 
      by (metis divide_le_0_iff divide_self_if less_divide_eq_1_pos less_eq_real_def less_numeral_extra(4) zero_less_power2 zero_neq_numeral)
  qed
  have 2:"\<forall> l\<in>{0..period}. Inv2 (p l)"
      if cond:
        "ODEsol (ODE ((\<lambda>_ _. 0)(H := (\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)), T := (\<lambda>_. 1)))) p d "
        "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> (\<lambda>s. s T < period) (p t) "
        " \<not> (\<lambda>s. s T < period) (p d) "
        "p 0 = end_of_trace tr" 
        "d\<ge>0" for d and p
    proof-
      have 201:"d = period"
        using 1 cond by auto
      have 202:"\<forall>x. ((\<lambda>v. (vec2state v) H) has_derivative (\<lambda>x. \<lambda>v. (vec2state v) H)(x)) (at x within UNIV)"
        unfolding vec2state_def by auto
      have 203: "\<forall>t\<in>{0 .. d}. ((\<lambda>t. (p t) H) has_derivative  (\<lambda>s. (\<lambda>x. \<lambda>v. (vec2state v) H) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(H := (\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)), T := (\<lambda>_. 1)))) (p t)))) (at t within {0 .. d})"
        using chainrule[of "(\<lambda>v. v H)" "\<lambda>x. (\<lambda>x. \<lambda>v. (vec2state v) H)(state2vec x)" "(ODE ((\<lambda>_ _. 0)(H := (\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)), T := (\<lambda>_. 1))))" p d] 
        using 202 cond(1) by auto
      have 204: "\<forall>s. (\<lambda>x. \<lambda>v. (vec2state v) H) (state2vec(p t)) (s *\<^sub>R ODE2Vec (ODE ((\<lambda>_ _. 0)(H := (\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)), T := (\<lambda>_. 1)))) (p t)) = s * ((\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)) (p t))" if "t\<in>{0 .. d}" for t
        unfolding vec2state_def apply simp unfolding state2vec_def apply auto
        using vars_distinct by auto
      have 205:"\<forall>t\<in>{0 .. d}. (((\<lambda>t. (p t) H) has_derivative (\<lambda>s. s * ((\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)) (p t)))) (at t within {0 .. d}))"
        using 203 204 by auto
      have 206:"\<forall>t\<in>{0 .. d}. (p 0) V  = (p t) V"
        using cond(1) unfolding ODEsol_def apply simp unfolding has_vderiv_on_def
        using mvt_vector[of d p "\<lambda>x. (\<lambda>a. (if a = T then \<lambda>_. 1
                else ((\<lambda>_ _. 0)(H := \<lambda>s. s V * Qmax - pi * r\<^sup>2 * sqrt (2 * g * s H))) a)
                (p x))" "V"]
        using vars_distinct by auto
      have 207:"\<forall>t\<in>{0 .. d}. (p t) H - 0.6 * (p t) T \<le> 0"
         
         
         
         show ?thesis
        sorry
    qed
show ?thesis unfolding Valid_def apply auto
  subgoal for tr2
    using contE
end

thm continuous_image_closed_interval
thm open_vimage
thm closed_vimage
end
