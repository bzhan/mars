theory example_sl
  imports syntax_sl
begin


typedef vars = "{''x'', ''y'', ''z''}"
  by auto

print_theorems

lemma vars_mem: "v \<in> {Abs_vars ''x'', Abs_vars ''y'', Abs_vars ''z''}"
proof -
  have "Rep_vars v \<in> {''x'', ''y'', ''z''}"
    using Rep_vars by auto
  then have "Abs_vars (Rep_vars v) \<in> {Abs_vars ''x'', Abs_vars ''y'', Abs_vars ''z''}"
    by auto
  then show ?thesis
    by (auto simp add: Rep_vars_inverse)
qed

lemma vars_UNIV: "(UNIV::vars set) = {Abs_vars ''x'', Abs_vars ''y'', Abs_vars ''z''}"
  using vars_mem by auto

instance vars :: finite
  apply standard
  by (simp add: vars_UNIV)

abbreviation "VAR \<equiv> Abs_vars"

definition test :: "vars state" where
  "test = (\<chi> x. if x = VAR ''x'' then 1 else
                if x = VAR ''y'' then 2 else 0)"

lemma vars_neq[simp]:
  "VAR ''x'' \<noteq> VAR ''y''"
  "VAR ''y'' \<noteq> VAR ''z''"
  "VAR ''x'' \<noteq> VAR ''z''"
  by (auto simp add: Abs_vars_inject)

lemma test1:"test $ VAR ''x'' = 1"
  unfolding test_def by auto



definition sumsq :: "vars state \<Rightarrow> real" where
"sumsq s = (s $ VAR ''x'')^2 + (s $ VAR ''y'')^2"

definition sumsq' :: "vars state \<Rightarrow> vars state \<Rightarrow>real" where
"sumsq' x s = 2 * s $ VAR ''x'' * x $ VAR ''x'' + 2 * s $ VAR ''y'' * x $ VAR ''y'' "

lemma sumsqderiv:"(sumsq has_derivative sumsq' x) (at x) "
  unfolding sumsq_def sumsq'_def
  apply(rule has_derivative_add [of "\<lambda>s. (s $ VAR ''x'')\<^sup>2" "\<lambda>s. 2 * s $ VAR ''x'' * x $ VAR ''x''" "at x"
                               "\<lambda>s. (s $ VAR ''y'')\<^sup>2" "\<lambda>s. 2 * s $ VAR ''y'' * x $ VAR ''y''"])
  subgoal
    using derivcoord has_derivative_power[of "\<lambda>s. (s $ VAR ''x'')" "\<lambda>s. (s $ VAR ''x'')" x UNIV 2] by auto
   subgoal
     using derivcoord has_derivative_power[of "\<lambda>s. (s $ VAR ''y'')" "\<lambda>s. (s $ VAR ''y'')" x UNIV 2] by auto
   done

lemma sumsqvalid:
  assumes "p=(\<lambda>s. (s $ VAR ''x'') = 2 \<and> (s $ VAR ''y'') = 3)"
      and "ode=ODE {VAR ''x'', VAR ''y''} (\<lambda>x. if x=VAR ''x'' then (\<lambda>s. s $ VAR ''y'') else if x=VAR ''y'' then (\<lambda>s. -s $ VAR ''x'') else undefined)"
      and "Inv=(\<lambda>s. sumsq s = 13)"
      and "b=(\<lambda>s. (s $ VAR ''x'')<3)"
    shows "\<Turnstile> {p} <ode && Inv&b> {(Inv [&][\<not>]b); (almost (Inv [&]  b) [[|]] elE 0)}"
  apply(rule continTR)
    apply auto
  unfolding INV_def
  subgoal premises pre for tr d
  proof-
    have step1:"d\<ge>0" 
      using pre assms(2) unfolding ODEsol_def by auto
    have step2:" ((\<lambda>t. sumsq (tr t)) has_derivative (\<lambda>t. (\<lambda>s. sumsq'(tr t) (s*\<^sub>R(ODE2Vec ode(tr t))))) x) (at x within {0..d})" if cond1:"0\<le>x\<and>x\<le>d" for x
      using chainrule[of sumsq sumsq' ode tr d x]
      using pre cond1 sumsqderiv by auto
    have step3:"\<forall>t\<in>{0 .. d}. \<forall>s. (\<lambda>t. (\<lambda>s. sumsq'(tr t) (s*\<^sub>R(ODE2Vec ode(tr t))))) t s = 0"
      unfolding sumsq'_def assms(2) ODE2Vec.simps apply simp
      using vars_neq(1) by force
    have step4:"\<forall>t\<in>{0 .. d}. (\<lambda>t. sumsq (tr t)) 0 = (\<lambda>t. sumsq (tr t)) t"
      using mvt_real_eq[of d "(\<lambda>t. sumsq (tr t))" "(\<lambda>t. (\<lambda>s. sumsq'(tr t) (s*\<^sub>R(ODE2Vec ode(tr t)))))"]
      using step1 step2 step3 by auto
    have step5:"Inv (tr 0)" using assms pre unfolding sumsq_def by auto
    have step6:"\<forall>t\<in>{0 .. d}. Inv (tr t)" using step4 step5 assms by auto
    then show ?thesis using step1 by auto
  qed
done
      
    



end