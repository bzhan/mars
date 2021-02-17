
theory Lander1
  imports HHLProver.ContinuousInv
begin


lemma frontier_closed_open:
  "frontier {s. f s \<ge> a \<and> f s < b} = {s. f s = b}"
  sorry

text \<open>Variables\<close>

definition Fc :: char where "Fc = CHR ''a''"
definition M :: char where "M = CHR ''b''"
definition T :: char where "T = CHR ''c''"
definition V :: char where "V = CHR ''d''"
definition W :: char where "W = CHR ''e''"

text \<open>Constants\<close>
definition Period :: real where "Period = 0.128"

lemma train_vars_distinct [simp]: "T \<noteq> V" "T \<noteq> W"  
                                  "V \<noteq> T" "V \<noteq> W" 
                                  "W \<noteq> T" "W \<noteq> V" 
  unfolding T_def V_def W_def by auto


definition W_upd :: "real \<Rightarrow> real \<Rightarrow> real" where
  "W_upd v w = (-(w - 3.732) * 0.01 + 3.732 - (v - (-1.5)) * 0.6)"

definition landerinv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"landerinv t v w = (15025282795421706426953 - 38191371615549881350000*t + 
  9482947285373987200000*t^2 - 90382078252408000000*t^3 - 
  12597135205472000000*t^4 + 5070724623344300111384 * v + 
  29051341984741759604000 * t * v + 12905500940447680000000*t^2 * v - 
  3452247087952000000*t^3 * v + 3754952256975690758168 * v^2 - 
  4369639740028640264000*t * v^2 + 4290324517728000000000*t^2 * v^2 + 
  10509874347360 * v^3 - 8711967253392000*t * v^3 + 1751645724560 * v^4 - 
  6016579819909859424000*w + 32152462695621728000000*t*w + 
  63926169690400000000*t^2*w + 1659591880613072768000 * v *w - 
  11298598523808000000000*t * v *w + 2216823024256000 * v^2*w + 
  1139598426176000000000*w^2 - 6579819920896000000000*t*w^2)/(160000000000000000000)"


lemma landerinv_prop2:
  "landerinv Period v w \<le> 0 \<Longrightarrow> landerinv 0 v (W_upd v w) \<le> 0"
  sorry

definition landerInv :: "state \<Rightarrow> real" where
  "landerInv s = landerinv (s T) (s V) (s W)"

text \<open>Processes\<close>

(*
  V ::= (\<lambda>_. -1.5);
  W ::= (\<lambda>_. 2835/759.5);
*)
definition P0 :: proc where
  "P0 =
    Rep (
      T ::= (\<lambda>_. 0);
      Cont (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))) ((\<lambda>s. s T \<ge> 0 \<and> s T < Period));
      W ::= (\<lambda>s. W_upd (s V) (s W))
    )"

fun P0_inv :: "nat \<Rightarrow> tassn" where
  "P0_inv 0 = emp\<^sub>t"
| "P0_inv (Suc n) = (ode_inv_assn (\<lambda>s. landerInv s \<le> 0) @\<^sub>t P0_inv n)"

lemma P0_inv_Suc:
  "P0_inv n @\<^sub>t ode_inv_assn (\<lambda>s. landerInv s \<le> 0) = 
   ode_inv_assn (\<lambda>s. landerInv s \<le> 0) @\<^sub>t P0_inv n"
  apply (induct n) by (auto simp add: join_assoc)

lemma ContODE:
 "\<Turnstile> {\<lambda>s tr. landerInv s \<le> 0 \<and>
             (\<lambda>s. s T \<ge> 0 \<and> s T < Period) s \<and>
             supp s \<subseteq> {V, W, T} \<and> P tr}
     Cont (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732), W := (\<lambda>s. (s W)^2 / 2500 ), T := (\<lambda>_. 1)))) ((\<lambda>s. s T \<ge> 0 \<and> s T < Period))
    {\<lambda>s tr. s \<in> frontier {s. s T \<ge> 0 \<and> s T < Period} \<and>
            supp s \<subseteq> {V, W, T} \<and>
            landerInv s \<le> 0 \<and>
            (P @\<^sub>t ode_inv_assn (\<lambda>s. landerInv s \<le> 0)) tr}"
  apply(rule Valid_inv_new')
   apply auto
  unfolding landerInv_def landerinv_def vec2state_def power2_eq_square power3_eq_cube power4_eq_xxxx
   apply(rule has_derivative_divide)
     apply (fast intro!: derivative_intros)[1]
    apply (fast intro!: derivative_intros)[1]
  apply auto
  apply(simp add:state2vec_def Period_def)
  subgoal for S
    sorry
  done


lemma P0_prop:
  "\<Turnstile> {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0, W := w0, T := Period) \<and>
                  landerinv 0 v0 w0 \<le> 0 \<and> emp\<^sub>t tr}
     P0
   {\<lambda>s tr. \<exists>n v w. s = (\<lambda>_. 0)(V := v, W := w, T := Period) \<and>
                   landerinv 0 v w \<le> 0 \<and> P0_inv n tr}"
  unfolding P0_def
  apply (rule Valid_weaken_pre)
   prefer 2
  apply (rule Valid_rep)
  apply (rule Valid_ex_pre) apply (rule Valid_ex_pre)
  apply (rule Valid_ex_pre)
  subgoal for n v w
    apply (rule Valid_seq)
     apply (rule Valid_assign_sp)
    apply (rule Valid_seq)
     apply (rule Valid_weaken_pre)
      prefer 2 
    apply (rule ContODE[where P="P0_inv n"])
     apply auto
     apply (auto simp add: entails_def landerInv_def supp_def Period_def)[1]
    apply (rule Valid_weaken_pre[where P'=
          "\<lambda>s tr. \<exists>v w. s = ((\<lambda>_. 0)(V := v, W := w, T := Period)) \<and>
                        landerInv s \<le> 0 \<and>
                        (P0_inv n @\<^sub>t ode_inv_assn (\<lambda>s. landerInv s \<le> 0)) tr"])
    subgoal
      apply (auto simp add: entails_def frontier_closed_open supp_def)
      subgoal for s tr
        apply (rule exI[where x="s V"]) apply (rule exI[where x="s W"])
        apply (rule ext) by auto
      done
    apply (rule Valid_ex_pre)
    apply (rule Valid_ex_pre)
    subgoal for v w
    apply (rule Valid_strengthen_post)
       prefer 2 apply (rule Valid_assign_sp)
      apply (auto simp add: entails_def)
      apply (rule exI[where x="Suc n"])
      apply (rule exI[where x=v]) apply (rule exI[where x="W_upd v w"])
      apply (auto simp add: P0_inv_Suc)
      by (auto simp add: landerInv_def landerinv_prop2)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x=0]) apply (rule exI[where x=v0])
  apply (rule exI[where x=w0]) by auto
  
end
