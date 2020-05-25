section \<open>Bouncing ball example, parallel version\<close>

theory BouncingBallPar
  imports BigStep
begin


locale bouncing_ball_par =
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


definition Inv :: "state \<Rightarrow> real" where
  "Inv = (\<lambda>s. (s V) ^ 2 + 2 * g * s X)"


inductive valid_blocks_plant :: "real \<Rightarrow> trace_block list \<Rightarrow> bool" where
  "v0 > 0 \<Longrightarrow> valid_blocks_plant v0 []"
| "valid_blocks_plant v0 blks \<Longrightarrow>
   d \<ge> 0 \<Longrightarrow>
   p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<Longrightarrow>
   (\<forall>t. 0\<le>t \<and> t\<le>d \<longrightarrow> Inv (p t) = Inv (p 0)) \<Longrightarrow>
   valid_blocks_plant v0 (blks @ [ODEBlock d (restrict p {0..d}),
                                  OutBlock dly1 ''ch1'' (p d V) ({''ch1''}, {}), 
                                  InBlock dly2 ''ch2'' V v1 ({}, {''ch2''})])"


lemma bouncingBallPlant:
  assumes "v0 > 0"
  shows "Valid
    (\<lambda>t. t = Trace ((\<lambda>_. 0)(V := v0)) [])
    (Rep (Cont (ODE {X, V} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (\<lambda>s. s X > 0 \<or> s V > 0);
          Cm (Send ''ch1'' (\<lambda>s. s V)); Cm (Receive ''ch2'' V)))
    (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant v0 blks)"
proof -
  have 1: "Valid
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant v0 blks)
     (Cont (ODE {X, V} ((\<lambda>_ _. 0)(X := \<lambda>s. s V, V := \<lambda>_. - g))) (\<lambda>s. 0 < s X \<or> 0 < s V))
     (\<lambda>t. \<exists>blks d p.
             t = Trace ((\<lambda>_. 0)(V := v0)) (blks @ [ODEBlock d (restrict p {0..d})]) \<and>
             valid_blocks_plant v0 blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
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
             valid_blocks_plant v0 blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
             (\<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv (p t) = Inv (p 0)))
     (Cm (''ch1''[!](\<lambda>s. s V)))
     (\<lambda>t. \<exists>blks d p dly1.
             t = Trace ((\<lambda>_. 0)(V := v0)) (blks @ [ODEBlock d (restrict p {0..d}),
                                                   OutBlock dly1 ''ch1'' (p d V) ({''ch1''}, {})]) \<and>
             valid_blocks_plant v0 blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
             (\<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv (p t) = Inv (p 0)))"
    apply (simp only: Valid_ex_pre Valid_and_pre, clarify)
    subgoal premises pre for blks d p
      apply (rule Valid_send2)
      apply clarify
      subgoal for dly1
        apply (rule exI[where x=blks]) apply (rule exI[where x=d])
        apply (rule exI[where x=p]) apply (rule exI[where x=dly1])
        using pre by (auto simp add: extend_send_def end_of_blocks_append)
      done
    done
  have 3: "Valid
     (\<lambda>t. \<exists>blks d p dly1.
             t = Trace ((\<lambda>_. 0)(V := v0)) (blks @ [ODEBlock d (restrict p {0..d}),
                                                   OutBlock dly1 ''ch1'' (p d V) ({''ch1''}, {})]) \<and>
             valid_blocks_plant v0 blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
             (\<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv (p t) = Inv (p 0)))
     (Cm (''ch2''[?]V))
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant v0 blks)"
    apply (simp only: Valid_ex_pre Valid_and_pre, clarify)
    subgoal premises pre for blks d p dly1
      apply (rule Valid_receive2)
      apply (auto simp add: extend_receive_def)
      using pre by (rule valid_blocks_plant.intros(2))
    done
  have 4: "Valid
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant v0 blks)
     (Rep (Cont (ODE {X, V} ((\<lambda>_ _. 0)(X := \<lambda>s. s V, V := \<lambda>_. - g)))
            (\<lambda>s. 0 < s X \<or> 0 < s V); Cm (''ch1''[!](\<lambda>s. s V)); Cm (''ch2''[?]V)))
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant v0 blks)"
    by (auto intro!: Valid_rep Valid_seq 1 2 3)
  show ?thesis
    apply (rule Valid_pre)
    using 4 using assms by (auto intro: valid_blocks_plant.intros(1))
qed


inductive valid_blocks_ctrl :: "trace_block list \<Rightarrow> bool" where
  "valid_blocks_ctrl []"
| "valid_blocks_ctrl blks \<Longrightarrow>
   valid_blocks_ctrl (blks @ [InBlock dly1 ''ch1'' V v ({}, {''ch1''}), 
                              OutBlock dly2 ''ch2'' (- (c * v)) ({''ch2''}, {})])"

lemma bouncingBallCtrl:
  "Valid
    (\<lambda>t. t = Trace (\<lambda>_. 0) [])
    (Rep (Cm (Receive ''ch1'' V); Cm (Send ''ch2'' (\<lambda>s. - (c * s V)))))
    (\<lambda>t. \<exists>blks. t = Trace (\<lambda>_. 0) blks \<and> valid_blocks_ctrl blks)"
proof -
  have 1: "Valid
      (\<lambda>t. \<exists>blks. t = Trace (\<lambda>_. 0) blks \<and> valid_blocks_ctrl blks)
      (Cm (''ch1''[?]V))
      (\<lambda>t. \<exists>blks dly1 v. t = Trace (\<lambda>_. 0) (blks @ [InBlock dly1 ''ch1'' V v ({}, {''ch1''})]) \<and>
                         valid_blocks_ctrl blks)"
    apply (simp only: Valid_ex_pre Valid_and_pre, clarify)
    apply (rule Valid_receive2)
    by (auto simp add: extend_receive_def)
  have 2: "Valid
      (\<lambda>t. \<exists>blks dly1 v. t = Trace (\<lambda>_. 0) (blks @ [InBlock dly1 ''ch1'' V v ({}, {''ch1''})]) \<and>
                         valid_blocks_ctrl blks)
      (Cm (''ch2''[!](\<lambda>s. - c * s V)))
      (\<lambda>t. \<exists>blks. t = Trace (\<lambda>_. 0) blks \<and> valid_blocks_ctrl blks)"
    apply (simp only: Valid_ex_pre Valid_and_pre, clarify)
    subgoal premises pre for blks dly1 v
      apply (rule Valid_send2)
      apply (auto simp add: extend_send_def end_of_blocks_append)
      using pre by (rule valid_blocks_ctrl.intros(2))
    done
  have 3: "Valid
      (\<lambda>t. \<exists>blks. t = Trace (\<lambda>_. 0) blks \<and> valid_blocks_ctrl blks)
      (Rep (Cm (''ch1''[?]V); Cm (''ch2''[!](\<lambda>s. - c * s V))))
      (\<lambda>t. \<exists>blks. t = Trace (\<lambda>_. 0) blks \<and> valid_blocks_ctrl blks)"
    apply (auto intro!: Valid_rep Valid_seq)
    using 1 2 by auto
  show ?thesis
    apply (rule Valid_pre)
    using 3 by (auto intro: valid_blocks_ctrl.intros(1))
qed


end  (* locale bouncing_ball_par *)

end
