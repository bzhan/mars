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
    and "\<forall>t\<in>{0 .. d}. \<forall>s. q t s = 0"
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
  and "\<forall>t\<in>{0 .. d}. \<forall>s\<ge>0. q t s \<ge> 0"
  and "x \<in> {0 .. d}"
  shows "p 0 \<le> p x"
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by (smt atLeastAtMost_iff greaterThanLessThan_iff)
qed

text \<open>If the derivative is always non-positive, then the function is decreasing.\<close>
lemma mvt_real_le:
  fixes p :: "real \<Rightarrow>real"
  assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 .. d}. \<forall>s\<ge>0 . q t s \<le> 0"
    and "x \<in> {0 .. d}"
  shows "p 0 \<ge> p x"
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_within_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by (smt atLeastAtMost_iff greaterThanLessThan_iff)
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
  sorry

lemma ODEsol_split:
  assumes "ODEsol ode p d"
    and "0 < t1" and "t1 < d"
  shows "ODEsol ode p t1"
        "ODEsol ode (\<lambda>t. p (t + t1)) (d - t1)"
  sorry


end
