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

inductive valid_blocks_plant :: "state \<Rightarrow> trace_block list \<Rightarrow> bool" where
  "valid_blocks_plant st []"
| "valid_blocks_plant ((p d)(V := v1)) blks \<Longrightarrow>
   d \<ge> 0 \<Longrightarrow> p 0 = st \<Longrightarrow>
   (\<forall>t. 0\<le>t \<and> t\<le>d \<longrightarrow> Inv (p t) = Inv (p 0)) \<Longrightarrow>
   valid_blocks_plant st (ODEBlock d (restrict p {0..d}) #
                          OutBlock dly1 ''ch1'' (p d V) ({''ch1''}, {}) #
                          InBlock dly2 ''ch2'' V v1 ({}, {''ch2''}) # blks)"

lemma valid_blocks_plant_snoc:
  "valid_blocks_plant st blks \<Longrightarrow>
   d \<ge> 0 \<Longrightarrow> p 0 = end_of_trace (Trace st blks) \<Longrightarrow>
   (\<forall>t. 0\<le>t \<and> t\<le>d \<longrightarrow> Inv (p t) = Inv (p 0)) \<Longrightarrow>
   valid_blocks_plant st
                      (blks @ [ODEBlock d (restrict p {0..d}),
                               OutBlock dly1 ''ch1'' (p d V) ({''ch1''}, {}), 
                               InBlock dly2 ''ch2'' V v1 ({}, {''ch2''})])"  
proof (induct rule: valid_blocks_plant.induct)
  case (1 st)
  then show ?case
    apply (subst append.left_neutral)
    by (auto intro: valid_blocks_plant.intros) 
next
  case (2 p2 d2 v1 blks st dly1 dly2)
  show ?case
    apply (simp only: append_Cons)
    apply (rule valid_blocks_plant.intros(2)[where p=p2, OF _ 2(3-5)])
    apply (rule 2(2)[OF 2(6) _ 2(8)])
    using 2(7) by (simp add: 2(3) fun_upd_def)
qed
 

lemma bouncingBallPlant:
  assumes "v0 > 0"
  shows "Valid
    (\<lambda>t. t = Trace ((\<lambda>_. 0)(V := v0)) [])
    (Rep (Cont (ODE {X, V} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (\<lambda>s. s X > 0 \<or> s V > 0);
          Cm (Send ''ch1'' (\<lambda>s. s V)); Cm (Receive ''ch2'' V)))
    (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks)"
proof -
  have 1: "Valid
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks)
     (Cont (ODE {X, V} ((\<lambda>_ _. 0)(X := \<lambda>s. s V, V := \<lambda>_. - g))) (\<lambda>s. 0 < s X \<or> 0 < s V))
     (\<lambda>t. \<exists>blks d p.
             t = Trace ((\<lambda>_. 0)(V := v0)) (blks @ [ODEBlock d (restrict p {0..d})]) \<and>
             valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
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
             valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
             (\<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv (p t) = Inv (p 0)))
     (Cm (''ch1''[!](\<lambda>s. s V)))
     (\<lambda>t. \<exists>blks d p dly1.
             t = Trace ((\<lambda>_. 0)(V := v0)) (blks @ [ODEBlock d (restrict p {0..d}),
                                                   OutBlock dly1 ''ch1'' (p d V) ({''ch1''}, {})]) \<and>
             valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
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
             valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks \<and> d \<ge> 0 \<and> p 0 = end_of_trace (Trace ((\<lambda>_. 0)(V := v0)) blks) \<and>
             (\<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv (p t) = Inv (p 0)))
     (Cm (''ch2''[?]V))
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks)"
    apply (simp only: Valid_ex_pre Valid_and_pre, clarify)
    subgoal premises pre for blks d p dly1
      apply (rule Valid_receive2)
      apply (auto simp add: extend_receive_def)
      using pre by (rule valid_blocks_plant_snoc)
    done
  have 4: "Valid
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks)
     (Rep (Cont (ODE {X, V} ((\<lambda>_ _. 0)(X := \<lambda>s. s V, V := \<lambda>_. - g)))
            (\<lambda>s. 0 < s X \<or> 0 < s V); Cm (''ch1''[!](\<lambda>s. s V)); Cm (''ch2''[?]V)))
     (\<lambda>t. \<exists>blks. t = Trace ((\<lambda>_. 0)(V := v0)) blks \<and> valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks)"
    by (auto intro!: Valid_rep Valid_seq 1 2 3)
  show ?thesis
    apply (rule Valid_pre)
    using 4 using assms by (auto intro: valid_blocks_plant.intros(1))
qed


inductive valid_blocks_ctrl :: "trace_block list \<Rightarrow> bool" where
  "valid_blocks_ctrl []"
| "valid_blocks_ctrl blks \<Longrightarrow>
   valid_blocks_ctrl (InBlock dly1 ''ch1'' V v ({}, {''ch1''}) #
                      OutBlock dly2 ''ch2'' (- (c * v)) ({''ch2''}, {}) # blks)"


lemma valid_blocks_ctrl_snoc:
  "valid_blocks_ctrl blks \<Longrightarrow>
   valid_blocks_ctrl (blks @ [InBlock dly1 ''ch1'' V v ({}, {''ch1''}), 
                              OutBlock dly2 ''ch2'' (- (c * v)) ({''ch2''}, {})])"
proof (induct rule: valid_blocks_ctrl.induct)
  case 1
  then show ?case
    by (auto intro: valid_blocks_ctrl.intros)
next
  case (2 blks dly1 v dly2)
  show ?case
    by (auto intro: valid_blocks_ctrl.intros(2) 2(2))
qed


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
      using pre by (rule valid_blocks_ctrl_snoc)
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


inductive valid_blocks_par :: "par_block list \<Rightarrow> bool" where
  "valid_blocks_par []"
| "valid_blocks_par pblks \<Longrightarrow> d \<ge> 0 \<Longrightarrow>  (\<forall>t. 0\<le>t \<and> t\<le>d \<longrightarrow> Inv ((p t)!0) = Inv ((p 0)!0)) \<Longrightarrow>
   valid_blocks_par (ParWaitBlock d (restrict p {0..d}) # IOBlock 1 0 ''ch1''V v # IOBlock 0 1 ''ch2'' V (- (c * v)) # pblks)"

lemma bouncingBallBlocks:
  "valid_blocks_plant st blks1 \<Longrightarrow>
   valid_blocks_ctrl blks2 \<Longrightarrow>
   combine_blocks [st, sr] [blks1, blks2] par_blks \<Longrightarrow>
   valid_blocks_par par_blks"
proof (induct arbitrary: blks2 par_blks sr rule: valid_blocks_plant.induct)
  case (1 st)
  note plant1 = 1
  from plant1(1) show ?case
  proof (induct rule: valid_blocks_ctrl.cases)
    case 1
    note ctrl1 = 1
    have s1: "par_blks = []"
      using plant1(2) unfolding ctrl1
      by (rule combine_blocks_triv2)
    show ?case
      unfolding s1 by (rule valid_blocks_par.intros(1))
  next
    case (2 blks dly1 v dly2)
    note ctrl2 = 2
    show ?case
      using plant1(2) ctrl2(1)
      using combine_blocks_NilIn by blast
  qed
next
  case (2 p d v1 blks st dly11 dly12)
  note plant2 = 2
  from plant2(6) show ?case
  proof (induct rule: valid_blocks_ctrl.cases)
    case 1
    note ctrl1 = 1
    show ?case
      using plant2(7) unfolding ctrl1
      using combine_blocks_ODENil2 combine_blocks_OutNil by blast
  next
    case (2 blks2' dly21 v dly22)
    note ctrl2 = 2
    have 21: "restrict p {0..d} d = p d" using plant2(3) by auto
    have 22: "(\<lambda>t\<in>{0..d}. [restrict p {0..d} t, sr]) = (\<lambda>t\<in>{0..d}. [p t, sr])"
      using plant2(3) by auto
    obtain rest where s1: "d \<le> dly21"
      "combine_blocks [p d, sr]
       [OutBlock dly11 ''ch1'' (p d V) ({''ch1''}, {}) # InBlock dly12 ''ch2'' V v1 ({}, {''ch2''}) # blks,
        InBlock (dly21 - d) ''ch1'' V v ({}, {''ch1''}) # OutBlock dly22 ''ch2'' (- (c * v)) ({''ch2''}, {}) # blks2']
       rest"
      "par_blks = ParWaitBlock d (restrict (\<lambda>t. [p t, sr]) {0..d}) # rest"
      using plant2(3, 7) unfolding ctrl2(1)
      using combine_blocks_ODEIn2[of st sr d "(restrict p {0..d})"
        "OutBlock dly11 ''ch1'' (p d V) ({''ch1''}, {}) # InBlock dly12 ''ch2'' V v1 ({}, {''ch2''}) # blks"
       dly21 "''ch1''" V v "({}, {''ch1''})" "OutBlock dly22 ''ch2'' (- (c * v)) ({''ch2''}, {}) # blks2'" par_blks
       ] 21 22 by auto   
    have 23: "[p d, sr][1 := end_of_blocks ([p d, sr] ! 1) [InBlock (dly21 - d) ''ch1'' V v ({}, {''ch1''})]]
            = [p d, sr (V:=v)]"
      by auto
     obtain rest2 where s2:
      "dly11 = 0" "dly21 - d = 0" "p d V = v"
      "combine_blocks [p d, sr(V:=v)] [InBlock dly12 ''ch2'' V v1 ({}, {''ch2''}) # blks,
                       OutBlock dly22 ''ch2'' (- (c * v)) ({''ch2''}, {}) # blks2'] rest2"
      "rest = IOBlock 1 0 ''ch1'' V (p d V) # rest2"
       using combine_blocks_IO2[OF s1(2)] 23  by auto
     have 24: "([p d, sr(V := v)][0 := end_of_blocks ([p d, sr(V := v)] ! 0) [InBlock dly12 ''ch2'' V v1 ({}, {''ch2''})]])
              =  [(p d)(V := v1), sr(V := v)]" by auto
    obtain rest3 where s3:
      "dly22 = 0" "dly12 = 0" "- (c * v) = v1"
      "combine_blocks [(p d)(V:=v1), sr(V:=v)] [blks, blks2'] rest3" "rest2 = IOBlock 0 1 ''ch2'' V (- (c * v)) # rest3"
      using combine_blocks_IO2'[OF s2(4)] 24 by auto
    have s4: "valid_blocks_par rest3"
      using plant2(2)[of blks2'] ctrl2(2) s3(4) by blast
    have "d \<ge> 0" using plant2(3) by auto 
    have 26: "\<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv (p t) = Inv (p 0)" 
      by (rule plant2(5))
    have 27: " \<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv([p t, sr] ! 0) = Inv(p t)" by auto
    have 28: " \<forall>t. 0 \<le> t \<and> t \<le> d \<longrightarrow> Inv([p 0, sr] ! 0) = Inv(p 0)" by auto
    show ?case
      unfolding s1(3) s2(5) s3(5) s2(3)
      apply (rule valid_blocks_par.intros(2)[OF s4 \<open>0 \<le> d\<close>])
      using 26 27 28 by arith
  qed
qed

lemma bouncingBall:
  assumes "v0 > 0"
  shows "ParValid
    (\<lambda>t. t = ParTrace [((\<lambda>_. 0)(V := v0)), (\<lambda>_. 0)] [])
    (PProc [Rep (Cont (ODE {X, V} ((\<lambda>_. \<lambda>_. 0)(X := (\<lambda>s. s V), V := (\<lambda>_. -g)))) (\<lambda>s. s X > 0 \<or> s V > 0);
            Cm (Send ''ch1'' (\<lambda>s. s V)); Cm (Receive ''ch2'' V)),
            Rep (Cm (Receive ''ch1'' V); Cm (Send ''ch2'' (\<lambda>s. - (c * s V))))])
    (\<lambda>t. \<exists>pblks. t = ParTrace [((\<lambda>_. 0)(V := v0)), (\<lambda>_. 0)] pblks \<and> valid_blocks_par pblks)"
proof -
  have 1: "\<exists>pblks. par_t = ParTrace [(\<lambda>_. 0)(V := v0), \<lambda>_. 0] pblks \<and> valid_blocks_par pblks"
    if tr1: "tr1 = Trace ((\<lambda>_. 0)(V := v0)) blks1" "valid_blocks_plant ((\<lambda>_. 0)(V := v0)) blks1" and
       tr2: "tr2 = Trace (\<lambda>_. 0) blks2" "valid_blocks_ctrl blks2" and
       rdy: "compat_trace_pair tr1 tr2" and
       par_trace: "combine_par_trace [tr1, tr2] par_t"
     for par_t tr1 tr2 blks1 blks2
  proof -
    from par_trace[unfolded tr1 tr2] obtain par_blks where
      1: "par_t = ParTrace [(\<lambda>_. 0)(V := v0), \<lambda>_. 0] par_blks" and
      2: "combine_blocks  [((\<lambda>_. 0)(V := v0)), (\<lambda>_. 0)]  [blks1, blks2] par_blks"
      using combine_par_traceE2 by blast
    then have 3: "valid_blocks_par par_blks"
      using bouncingBallBlocks[OF tr1(2) tr2(2) 2] by auto
    show ?thesis
      apply (rule exI[where x=par_blks])
      using 1 3 by auto
  qed
  show ?thesis
    apply (rule Valid_parallel2'[OF _ _ bouncingBallPlant[OF assms] bouncingBallCtrl])
    using 1 by blast+
qed


end  (* locale bouncing_ball_par *)

end
