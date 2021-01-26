theory Analysis_More
  imports Ordinary_Differential_Equations.Flow
begin


subsection \<open>Some results about derivatives\<close>

text \<open>Projection of has_vector_derivative onto components.\<close>
lemma has_vector_derivative_proj:
  assumes "(p has_vector_derivative q t) (at t within D)"
  shows "((\<lambda>t. p t $ i) has_vector_derivative q t $ i) (at t within D)"
  using assms unfolding has_vector_derivative_def has_derivative_def 
  apply (simp add: bounded_linear_scaleR_left)
  using tendsto_vec_nth by fastforce

lemma has_vderiv_on_proj:
  assumes "(p has_vderiv_on q) D"
  shows "((\<lambda>t. p t $ i) has_vderiv_on (\<lambda>t. q t $ i)) D"
  using assms unfolding has_vderiv_on_def 
  by (simp add: has_vector_derivative_proj)

lemma has_vector_derivative_projI:
  assumes "\<forall>i. ((\<lambda>t. p t $ i) has_vector_derivative q t $ i) (at t within D)"
  shows "(p has_vector_derivative q t) (at t within D)"
  using assms unfolding has_vector_derivative_def has_derivative_def
  apply (auto simp add: bounded_linear_scaleR_left)
  by (auto intro: vec_tendstoI)

lemma has_derivative_coords [simp,derivative_intros]:
  "((\<lambda>t. t$i) has_derivative (\<lambda>t. t$i)) (at x)"
  unfolding has_derivative_def by auto


text \<open>If the derivative is always 0, then the function is always 0.\<close>
lemma mvt_real_eq:
  fixes p :: "real \<Rightarrow> real"
  assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 ..<d}. \<forall>s. q t s = 0"
    and "x \<in> {0 .. d}"
  shows "p 0 = p x" 
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by force
qed

text \<open>If the derivative is always non-negative, then the function is increasing.\<close>
lemma mvt_real_ge:
  fixes p :: "real \<Rightarrow>real"
 assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
  and "d \<ge> 0"
  and "\<forall>t\<in>{0 ..<d}. \<forall>s\<ge>0. q t s \<ge> 0"
  and "x \<in> {0 .. d}"
  shows "p 0 \<le> p x"
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by (smt atLeastAtMost_iff atLeastLessThan_iff greaterThanLessThan_iff)
qed

text \<open>If the derivative is always non-positive, then the function is decreasing.\<close>
lemma mvt_real_le:
  fixes p :: "real \<Rightarrow>real"
  assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 ..<d}. \<forall>s\<ge>0 . q t s \<le> 0"
    and "x \<in> {0 .. d}"
  shows "p 0 \<ge> p x"
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by (smt atLeastAtMost_iff atLeastLessThan_iff greaterThanLessThan_iff)
qed


lemma real_inv_le:
  fixes p :: "real \<Rightarrow>real"
 assumes "\<forall>t\<in>{-1<..}. (p has_derivative q t) (at t within {-1<..}) "
  and "d \<ge> 0"
  and "\<forall>t\<in>{0 ..<d}. (p t = 0 \<longrightarrow> (\<forall>s\<ge>0. q t s < 0))"
  and "p 0 \<le> 0 "
  and "x \<in> {0 .. d}"
  shows "p x \<le> 0"
proof(rule ccontr)
  assume a:" \<not> p x \<le> 0"
  have 1:"p x > 0"
    using a by auto
  have 2:"\<forall>t\<in>{0 .. d}. continuous (at t within {-1<..}) p"
    using assms
    using has_derivative_continuous by fastforce
  have 3:"\<forall>t\<in>{0 .. d}. isCont p t"
    apply auto subgoal for t
      using continuous_within_open[of t "{-1<..}" p]
      using 2 assms(5) by auto
    done
  have 4:"{y. p y = 0 \<and> y \<in> {0 .. x}} \<noteq> {}"
    using IVT[of p 0 0 x] using 3 1 assms 
    by auto
  have 5: "{y. p y = 0 \<and> y \<in> {0 .. x}} = ({0 .. x} \<inter> p -` {0})"
    by auto
  have 6: "closed ({0 .. x} \<inter> p -` {0})"
    using 3 assms(5) apply simp
    apply (rule continuous_closed_preimage)
      apply auto
    by (simp add: continuous_at_imp_continuous_on)
  have 7: "compact {0 .. x}"
    using assms
    by blast
  have 8: "compact {y. p y = 0 \<and> y \<in> {0 .. x}}"
    apply auto
    using 4 5 6 7 
    by (smt Collect_cong Int_left_absorb atLeastAtMost_iff compact_Int_closed)
  obtain t where t1:"t \<in> {y. p y = 0 \<and> y \<in> {0 .. x}}" and t2:"\<forall> tt\<in> {y. p y = 0 \<and> y \<in> {0 .. x}}. tt \<le>t"
    using compact_attains_sup[of "{y. p y = 0 \<and> y \<in> {0 .. x}}"] 4 8 
    by blast
  have 9:"t<x"
    using t1 1 
    using leI by fastforce
  have 10:"p tt > 0" if "tt\<in>{t<..x}" for tt
  proof(rule ccontr)
    assume "\<not> 0 < p tt"
    then have not:"p tt \<le>0" by auto
    have "\<exists> t' \<in> {t<..x}. p t' = 0"
    proof(cases "p tt = 0")
      case True
      then show ?thesis using that by auto
    next
      case False
      then have "p tt < 0"
        using not by auto
      then have "{y. p y = 0 \<and> y \<in> {tt .. x}} \<noteq> {}"
        using IVT[of p tt 0 x] using 3 1 assms that t1 
        by auto
      then show ?thesis using that by auto
    qed
    then show False using t1 t2 9 
      using atLeastAtMost_iff greaterThanAtMost_iff by auto
  qed     
  have 11:"(p has_derivative q t) (at t within {-1<..})"
    using assms t1 by auto
  then have 12:"\<forall>s . q t s = q t 1 * s"
    using has_derivative_bounded_linear[of p "q t" "(at t within {- 1<..})"]
    using real_bounded_linear by auto
  have 13:"(p has_real_derivative q t 1) (at t within {-1<..})"
    using 11 12 
    by (metis has_derivative_imp_has_field_derivative mult.commute)
  have 14:"q t 1 < 0" using t1 assms 9 by auto
  have 15:"\<exists>d>0. \<forall>h>0. t + h \<in> {- 1<..} \<longrightarrow> h < d \<longrightarrow> p (t + h) < p t"
    using has_real_derivative_neg_dec_right[of p "q t 1" t "{- 1<..}"] 13 14 by auto
  show False using 15 10 t1 
    by (smt "12" "9" assms(3) assms(5) atLeastAtMost_iff atLeastLessThan_iff mem_Collect_eq mult_cancel_right1)
qed

subsection \<open>Definition of states\<close>

text \<open>Variable names\<close>
type_synonym var = char

text \<open>Some common variables\<close>
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"

lemma vars_distinct [simp]: "X \<noteq> Y" "X \<noteq> Z" "Y \<noteq> Z" "Y \<noteq> X" "Z \<noteq> X" "Z \<noteq> Y"
  unfolding X_def Y_def Z_def by auto

text \<open>State\<close>
type_synonym state = "var \<Rightarrow> real"

text \<open>Expressions\<close>
type_synonym exp = "state \<Rightarrow> real"

text \<open>Predicates\<close>
type_synonym fform = "state \<Rightarrow> bool"

text \<open>States as a vector\<close>
type_synonym vec = "real^(var)"

text \<open>Conversion between state and vector\<close>
definition state2vec :: "state \<Rightarrow> vec" where
  "state2vec s = (\<chi> x. s x)"

definition vec2state :: "vec \<Rightarrow> state" where
  "(vec2state v) x = v $ x"

lemma vec_state_map1[simp]: "vec2state (state2vec s) = s"
  unfolding vec2state_def state2vec_def by auto

lemma vec_state_map2[simp]: "state2vec (vec2state s) = s"
  unfolding vec2state_def state2vec_def by auto

subsection \<open>Definition of ODEs\<close>

datatype ODE =
  ODE "var \<Rightarrow> exp"

text \<open>Given ODE and a state, find the derivative vector.\<close>
fun ODE2Vec :: "ODE \<Rightarrow> state \<Rightarrow> vec" where
  "ODE2Vec (ODE f) s = state2vec (\<lambda>a. f a s)"

text \<open>History p on time {0 .. d} is a solution to ode.\<close>
definition ODEsol :: "ODE \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> real \<Rightarrow> bool" where
  "ODEsol ode p d = (d \<ge> 0 \<and> (((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {0 .. d}))"

text \<open>History p on time {0 ..} is a solution to ode.\<close>
definition ODEsolInf :: "ODE \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> bool" where
  "ODEsolInf ode p = (((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {0 ..})"


subsection \<open>Further results in analysis\<close>

lemma ODEsol_merge:
  assumes "ODEsol ode p d"
    and "ODEsol ode p2 d2"
    and "p2 0 = p d"
  shows "ODEsol ode (\<lambda>\<tau>. if \<tau> < d then p \<tau> else p2 (\<tau> - d)) (d + d2)"
  unfolding ODEsol_def
  apply auto
  subgoal 
    using assms(1,2) unfolding ODEsol_def by auto
  subgoal
  proof-
    have step1:"d\<ge>0 \<and> d2\<ge>0"
      using assms unfolding ODEsol_def by auto
    then have step2:"{0 .. d+d2} = {0 .. d}\<union>{d .. d+d2}"
      by auto
    have step3:"({0..d} \<union> closure {d..d + d2} \<inter> closure {0..d}) = {0..d}"
      using step1 by auto
    have step4:"({d..d + d2} \<union> closure {d..d + d2} \<inter> closure {0..d}) = {d..d+d2}"
      using step1 by auto
    have step5:"(((\<lambda>t. (t-d)) has_vderiv_on (\<lambda>t.1)) {d .. d+d2})"
      by (auto intro!: derivative_intros)
    then have step6:"(((\<lambda>t. state2vec (p2 (t-d))) has_vderiv_on (\<lambda>t. ODE2Vec ode (p2 (t-d)))) {d .. d+d2})"
      using has_vderiv_on_compose2[of "(\<lambda>t. state2vec (p2 (t)))" "(\<lambda>t. ODE2Vec ode (p2 (t)))" "{0 .. d2}" "(\<lambda>t. (t-d))" "(\<lambda>t.1)" "{d .. d+d2}"]
      using assms(2) unfolding ODEsol_def
      by auto
    have step7:" ((\<lambda>t. if t \<in> {0..d} then state2vec (p t) else state2vec (p2 (t - d))) has_vderiv_on
     (\<lambda>t. if t \<in> {0..d} then ODE2Vec ode (p t) else ODE2Vec ode (p2 (t - d)))){0..d + d2}"
      using has_vderiv_on_If[of "{0 .. d+d2}" "{0 .. d}" "{d .. d+d2}" "(\<lambda>t. state2vec (p t))" "(\<lambda>t. ODE2Vec ode (p t))" "(\<lambda>t. state2vec (p2 (t-d)))" "(\<lambda>t. ODE2Vec ode (p2 (t-d)))"]
      using step1 step2 step3 step4 step6
      using assms(1) assms(3) unfolding ODEsol_def 
      by auto
    then show ?thesis 
      using has_vderiv_eq[of "(\<lambda>t. if t \<in> {0..d} then state2vec (p t) else state2vec (p2 (t - d)))" "(\<lambda>t. if t \<in> {0..d} then ODE2Vec ode (p t) else ODE2Vec ode (p2 (t - d)))" "{0..d + d2}" "(\<lambda>t. state2vec (if t < d then p t else p2 (t - d)))" "(\<lambda>t. ODE2Vec ode (if t < d then p t else p2 (t - d)))" "{0..d + d2}"]
      using assms(3) step1 
      by auto
  qed
  done

lemma ODEsol_split:
  assumes "ODEsol ode p d"
    and "0 < t1" and "t1 < d"
  shows "ODEsol ode p t1"
        "ODEsol ode (\<lambda>t. p (t + t1)) (d - t1)"
  subgoal
    using has_vderiv_on_subset[of "(\<lambda>t. state2vec (p t))" " (\<lambda>t. ODE2Vec ode (p t))" "{0..d}" "{0..t1}"]
    using assms unfolding ODEsol_def by auto
  subgoal
    unfolding ODEsol_def apply auto
    subgoal using assms by auto
    subgoal 
    proof-
      have step1:"((\<lambda>t. state2vec (p (t))) has_vderiv_on (\<lambda>t. ODE2Vec ode (p (t)))) {t1..d}"
        using has_vderiv_on_subset[of "(\<lambda>t. state2vec (p t))" " (\<lambda>t. ODE2Vec ode (p t))" "{0..d}" "{t1..d}"]
        using assms unfolding ODEsol_def by auto
      have step2:"((\<lambda>t.(t+t1)) has_vderiv_on (\<lambda>t. 1)) {0..d-t1}"
        by (auto intro!: derivative_intros)
      show ?thesis
        using has_vderiv_on_compose2[of "(\<lambda>t. state2vec (p (t)))" "(\<lambda>t. ODE2Vec ode (p (t)))" "{t1..d}" "(\<lambda>t.(t+t1))" "(\<lambda>t. 1)" " {0..d-t1}"]
        using step1 step2 assms by auto
    qed
    done
  done

end
