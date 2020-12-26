theory ExampleSimple
  imports BigStepParallel
begin

subsection \<open>Test of big-step semantics\<close>

text \<open>Send 1 immediately\<close>
lemma test1a: "big_step (Cm (''ch''[!](\<lambda>_. 1)))
  (\<lambda>_. 0) [OutBlock ''ch'' 1] (\<lambda>_. 0)"
  by (rule sendB1)

text \<open>Send x + 1 immediately\<close>
lemma test1b: "big_step (Cm (''ch''[!](\<lambda>s. s X + 1)))
  ((\<lambda>_. 0)(X := 1)) [OutBlock ''ch'' 2] ((\<lambda>_. 0)(X := 1))"
  by (rule sendB1', auto)

text \<open>Send 1 after delay 2\<close>
lemma test1c: "big_step (Cm (''ch''[!](\<lambda>_. 1)))
  (\<lambda>_. 0) [WaitBlock 2 (\<lambda>_\<in>{0..2}. State (\<lambda>_. 0)) ({''ch''}, {}),
           OutBlock ''ch'' 1] (\<lambda>_. 0)"
  by (rule sendB2, auto)

text \<open>Receive 1 immediately\<close>
lemma test2a: "big_step (Cm (''ch''[?]X))
  (\<lambda>_. 0) [InBlock ''ch'' 1] ((\<lambda>_. 0)(X := 1))"
  by (rule receiveB1)

text \<open>Receive 1 after delay 2\<close>
lemma test2b: "big_step (Cm (''ch''[?]X))
  (\<lambda>_. 0) [WaitBlock 2 (\<lambda>_\<in>{0..2}. State (\<lambda>_. 0)) ({}, {''ch''}),
           InBlock ''ch'' 1] ((\<lambda>_. 0)(X := 1))"
  by (rule receiveB2, auto)

text \<open>Communication\<close>
lemma test3: "par_big_step (
  Parallel (Single (Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
           (Single (Cm (''ch''[?]X))))
  (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [IOBlock ''ch'' 1]
  (ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test1a])
   apply (rule SingleB[OF test2a])
  by (auto intro: combine_blocks.intros)

text \<open>Wait\<close>
lemma test4: "big_step (Wait 2)
  (\<lambda>_. 0) [WaitBlock 2 (\<lambda>_\<in>{0..2}. State (\<lambda>_. 0)) ({}, {})] (\<lambda>_. 0)"
  apply (rule waitB1) by auto

text \<open>Seq\<close>
lemma test5: "big_step (Wait 2; Cm (''ch''[!](\<lambda>_. 1)))
  (\<lambda>_. 0) [WaitBlock 2 (\<lambda>_\<in>{0..2}. State (\<lambda>_. 0)) ({}, {}), OutBlock ''ch'' 1] (\<lambda>_. 0)"
  by (rule seqB'[OF test4 test1a], auto)

text \<open>Communication after delay 2\<close>
lemma test6: "par_big_step (
  Parallel (Single (Wait 2; Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
           (Single (Cm (''ch''[?]X))))
  (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [WaitBlock 2 (\<lambda>_\<in>{0..2}. ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0))) ({}, {''ch''}), IOBlock ''ch'' 1]
  (ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test5])
   apply (rule SingleB[OF test2b])
  by (auto intro!: combine_blocks.intros)

text \<open>Loop one time\<close>
lemma test7: "big_step (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X))))
  (\<lambda>_. 0) [OutBlock ''ch'' 1] ((\<lambda>_. 0)(X := 1))"
  apply (rule RepetitionB2)
    apply (rule seqB) apply (rule assignB) apply (rule sendB1)
  apply auto[1] apply (rule RepetitionB1)
  by auto

text \<open>Loop two times\<close>
lemma test8: "big_step (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X))))
  (\<lambda>_. 0) [OutBlock ''ch'' 1, OutBlock ''ch'' 2] ((\<lambda>_. 0)(X := 2))"
  apply (rule RepetitionB2)
    apply (rule seqB) apply (rule assignB) apply (rule sendB1)
   apply auto[1] apply (rule RepetitionB2)
     apply (rule seqB) apply (rule assignB) apply (rule sendB1)
    apply auto[1] apply (rule RepetitionB1)
  by auto

text \<open>External choice 1\<close>
lemma test9a: "big_step (EChoice [(''ch1''[!](\<lambda>_. 1), Wait 1),
                                  (''ch2''[!](\<lambda>_. 2), Wait 2)])
  (\<lambda>_. 0) [OutBlock ''ch1'' 1, WaitBlock 1 (\<lambda>_\<in>{0..1}. State (\<lambda>_. 0)) ({}, {})] (\<lambda>_. 0)"
  apply (rule EChoiceSendB1[where i=0])
  apply auto apply (rule waitB1) by auto

text \<open>External choice 2\<close>
lemma test9b: "big_step (EChoice [(''ch1''[!](\<lambda>_. 1), Wait 1),
                                  (''ch2''[!](\<lambda>_. 2), Wait 2)])
  (\<lambda>_. 0) [OutBlock ''ch2'' 2, WaitBlock 2 (\<lambda>_\<in>{0..2}. State (\<lambda>_. 0)) ({}, {})] (\<lambda>_. 0)"
  apply (rule EChoiceSendB1[where i=1])
  apply auto apply (rule waitB1) by auto

text \<open>Communication with external choice\<close>
lemma test10: "par_big_step (
  Parallel (Single (EChoice [(''ch1''[!](\<lambda>_. 1), Wait 1),
                             (''ch2''[!](\<lambda>_. 2), Wait 2)])) {''ch1'', ''ch2''}
           (Single (Cm (''ch1''[?]X); Wait 1)))
  (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [IOBlock ''ch1'' 1, WaitBlock 1 (\<lambda>_\<in>{0..1}. ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1)))) ({}, {})]
  (ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test9a])
   apply (rule SingleB)
   apply (rule seqB) apply (rule receiveB1) apply (rule waitB1)
  apply auto
  by (intro combine_blocks.intros, auto)

text \<open>ODE Example 1\<close>
lemma test11: "big_step (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
  (\<lambda>_. 0) [WaitBlock 1 (\<lambda>t\<in>{0..1}. State ((\<lambda>_. 0)(X := t))) ({}, {})] ((\<lambda>_. 0)(X := 1))"
  apply (rule ContB2)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
  by (auto intro!: derivative_intros)

text \<open>Interrupt examples\<close>

text \<open>Exit through boundary\<close>
lemma test_interrupt1:
  "big_step (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 2) [(''ch''[!](\<lambda>_. 1), Assign X (\<lambda>_. 0))])
    (\<lambda>_. 0) [WaitBlock 2 (\<lambda>t\<in>{0..2}. State ((\<lambda>_. 0)(X := t))) ({''ch''}, {})] ((\<lambda>_. 0)(X := 2))"
  apply (rule InterruptB2)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
  by (auto intro!: derivative_intros)

text \<open>Immediate communication\<close>
lemma test_interrupt2:
  "big_step (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 2) [(''ch''[!](\<lambda>_. 1), Assign X (\<lambda>_. 3))])
    (\<lambda>_. 0) [OutBlock ''ch'' 1] ((\<lambda>_. 0)(X := 3))"
  apply (rule InterruptSendB1)
    apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule assignB') by auto

text \<open>Communication in the middle\<close>
lemma test_interrupt3:
  "big_step (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 2) [(''ch''[!](\<lambda>_. 1), Assign X (\<lambda>_. 3))])
    (\<lambda>_. 0) [WaitBlock 1 (\<lambda>t\<in>{0..1}. State ((\<lambda>_. 0)(X := t))) ({''ch''}, {}),
             OutBlock ''ch'' 1] ((\<lambda>_. 0)(X := 3))"
  apply (rule InterruptSendB2)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
  apply (auto intro!: derivative_intros)
  apply (rule assignB') by auto

text \<open>Note with current definition, communication at the end is also possible\<close>
lemma test_interrupt4:
  "big_step (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 2) [(''ch''[!](\<lambda>_. 1), Assign X (\<lambda>_. 3))])
    (\<lambda>_. 0) [WaitBlock 2 (\<lambda>t\<in>{0..2}. State ((\<lambda>_. 0)(X := t))) ({''ch''}, {}),
             OutBlock ''ch'' 1] ((\<lambda>_. 0)(X := 3))"
  apply (rule InterruptSendB2)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
  apply (auto intro!: derivative_intros)
  apply (rule assignB') by auto

text \<open>Some tests with internal and external choice\<close>
lemma test_internal:
  "big_step (Rep (IChoice (Cm (''ch1''[!](\<lambda>_. 1))) (Cm (''ch2''[!](\<lambda>_. 2)))))
    (\<lambda>_. 0) [WaitBlock 2 (\<lambda>\<tau>\<in>{0..2}. State (\<lambda>_. 0)) ({''ch2''}, {}),
             OutBlock ''ch2'' 2,
             OutBlock ''ch1'' 1] (\<lambda>_. 0)"
  apply (rule RepetitionB2)
    apply (rule IChoiceB2)
    apply (rule sendB2[where d=2]) apply auto[1]
  apply (rule RepetitionB2)
  apply (rule IChoiceB1)
     apply (rule sendB1) apply (rule RepetitionB1)
  by auto

lemma test_internal_other:
  "par_big_step (Parallel (Single (Wait 1; Cm (''ch1''[?]X))) {}
                          (Single (Wait 2; Cm (''ch2''[?]X))))
    (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [WaitBlock 1 (\<lambda>_\<in>{0..1}. ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0))) ({}, {}),
     WaitBlock 1 (\<lambda>_\<in>{0..1}. ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0))) ({}, {''ch1''}),
     InBlock ''ch2'' 2,
     InBlock ''ch1'' 1]
    (ParState (State ((\<lambda>_. 0)(X := 1))) (State ((\<lambda>_. 0)(X := 2))))"
proof -
  have left: "big_step (Wait 1; Cm (''ch1''[?]X)) (\<lambda>_. 0)
    [WaitBlock 1 (\<lambda>_\<in>{0..1}. State (\<lambda>_. 0)) ({}, {}),
     WaitBlock 1 (\<lambda>_\<in>{0..1}. State (\<lambda>_. 0)) ({}, {''ch1''}),
     InBlock ''ch1'' 1] ((\<lambda>_. 0)(X := 1))"
    apply (rule seqB') apply (rule waitB1) apply simp
     apply (rule receiveB2'[where d=1]) by auto
  have right: "big_step (Wait 2; Cm (''ch2''[?]X)) (\<lambda>_. 0)
    [WaitBlock 2 (\<lambda>_\<in>{0..2}. State (\<lambda>_. 0)) ({}, {}),
     InBlock ''ch2'' 2] ((\<lambda>_. 0)(X := 2))"
    apply (rule seqB') apply (rule waitB1) apply simp
     apply (rule receiveB1) by auto
  show ?thesis
    apply (rule ParallelB)
      apply (rule SingleB[OF left])
     apply (rule SingleB[OF right])
    apply (rule combine_blocks_wait2) apply auto
    apply (rule combine_blocks_wait1) apply auto
     apply (rule combine_blocks_unpair3) apply auto
     apply (rule combine_blocks_unpair1) apply auto
    by (rule combine_blocks_empty)
qed

lemma test_internal_parallel:
  "par_big_step (Parallel
    (Single (Rep (IChoice (Cm (''ch1''[!](\<lambda>_. 1))) (Cm (''ch2''[!](\<lambda>_. 2)))))) {''ch1'', ''ch2''}
    (Parallel (Single (Wait 1; Cm (''ch1''[?]X))) {}
                          (Single (Wait 2; Cm (''ch2''[?]X)))))
    (ParState (State (\<lambda>_. 0)) (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0))))
    [WaitBlock 1 (\<lambda>_\<in>{0..1}. ParState (State (\<lambda>_. 0)) (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))) ({''ch2''}, {}),
     WaitBlock 1 (\<lambda>_\<in>{0..1}. ParState (State (\<lambda>_. 0)) (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))) ({''ch2''}, {''ch1''}),
     IOBlock ''ch2'' 2,
     IOBlock ''ch1'' 1]
    (ParState (State (\<lambda>_. 0))
              (ParState (State ((\<lambda>_. 0)(X := 1))) (State ((\<lambda>_. 0)(X := 2)))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test_internal])
  apply (rule test_internal_other)
  apply (rule combine_blocks_wait3) apply auto
  apply (rule combine_blocks_wait1) apply auto
  apply (rule combine_blocks_pair2) apply auto
  apply (rule combine_blocks_pair2) apply auto
  by (rule combine_blocks_empty)

subsection \<open>Simple examples\<close>

text \<open>Send 1\<close>
lemma testHL1:
  "Valid
    (\<lambda>s tr. Q s (tr @ [OutBlock ''ch'' 1]) \<and>
            (\<forall>d>0. Q s (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({''ch''}, {}), OutBlock ''ch'' 1])))
    (Cm (''ch''[!](\<lambda>_. 1)))
    Q"
  by (rule Valid_send)

text \<open>This implies the strongest postcondition form\<close>
lemma testHL1':
  "Valid
    (\<lambda>s t. s = st \<and> t = tr)
    (Cm (''ch''[!](\<lambda>_. 1)))
    (\<lambda>s t. s = st \<and>
           (t = tr @ [OutBlock ''ch'' 1] \<or>
             (\<exists>d>0. t = tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State st) ({''ch''}, {}), OutBlock ''ch'' 1])))"
  apply (rule Valid_weaken_pre)
   prefer 2
   apply (rule Valid_send)
  unfolding entails_def by auto

text \<open>Send 1, then send 2\<close>
lemma testHL2:
  "Valid
    (\<lambda>s tr. (Q s ((tr @ [OutBlock ''ch'' 1]) @ [OutBlock ''ch'' 2]) \<and>
             (\<forall>d>0. Q s ((tr @ [OutBlock ''ch'' 1]) @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({''ch''}, {}), OutBlock ''ch'' 2]))) \<and>
            (\<forall>d>0. Q s ((tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({''ch''}, {}), OutBlock ''ch'' 1]) @ [OutBlock ''ch'' 2]) \<and>
             (\<forall>da>0. Q s ((tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({''ch''}, {}), OutBlock ''ch'' 1]) @
                           [WaitBlock da (\<lambda>\<tau>\<in>{0..da}. State s) ({''ch''}, {}), OutBlock ''ch'' 2]))))
    (Cm (''ch''[!](\<lambda>_. 1)); Cm (''ch''[!](\<lambda>_. 2)))
    Q"
  apply (rule Valid_seq)
    prefer 2 apply (rule Valid_send)
  by (rule Valid_send)

text \<open>Receive from ch\<close>
lemma testHL3:
  "Valid
    (\<lambda>s tr.
        (\<forall>v. Q (s(X := v)) (tr @ [InBlock ''ch'' v])) \<and>
        (\<forall>d>0. \<forall>v. Q (s(X := v)) (tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State s) ({}, {''ch''}), InBlock ''ch'' v])))
    (Cm (''ch''[?]X))
    Q"
  by (rule Valid_receive)

text \<open>Strongest postcondition form\<close>
lemma testHL3':
  "Valid
    (\<lambda>s t. s = st \<and> t = tr)
    (Cm (''ch''[?]X))
    (\<lambda>s t. (\<exists>v. s = st(X := v) \<and>
             (t = tr @ [InBlock ''ch'' v]) \<or>
               (\<exists>d>0. t = tr @ [WaitBlock d (\<lambda>\<tau>\<in>{0..d}. State st) ({}, {''ch''}), InBlock ''ch'' v])))"
  apply (rule Valid_weaken_pre)
   prefer 2
   apply (rule testHL3)
  unfolding entails_def by auto

text \<open>Communication\<close>
lemma testHL4:
  "ParValid
    (pair_assn (\<lambda>s. s = st1) (\<lambda>s. s = st2))
    (Parallel (Single (Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
              (Single (Cm (''ch''[?]X))))
    (\<lambda>s tr. pair_assn (\<lambda>s. s = st1) (\<lambda>s. s = st2(X := 1)) s \<and> tr = [IOBlock ''ch'' 1])"
  apply (rule ParValid_conseq)
    apply (rule ParValid_Parallel)
  apply (rule ParValid_Single[OF testHL1'])
  apply (rule ParValid_Single[OF testHL3'])
   apply (simp add: pair_assn_def)
  subgoal for s tr
    apply (cases s)
    subgoal by auto
    subgoal for s1 s2
      apply (cases s1) apply auto apply (cases s2) apply (auto simp add: pair_assn_def)
      using combine_blocks_elim2a apply blast
      using combine_blocks_elim2b apply blast
        apply (cases s2) apply auto
         apply (metis combine_blocks_elim1 combine_blocks_elim2a singletonI)
      using combine_blocks_elim2b apply blast
       apply (cases s2) apply auto
      using combine_blocks_elim2e apply blast
       apply (auto elim!: combine_blocks_elim4a)
      apply (cases s2) apply auto
      using combine_blocks_elim2e apply blast
      by (auto elim!: combine_blocks_elim4a)
    done
  done


subsection \<open>Simple examples redone\<close>

text \<open>Send 1\<close>
lemma testHL1s:
  "Valid
    (\<lambda>s. Out\<^sub>A s ''ch'' (s X) @- P s)
    (Cm (''ch''[!](\<lambda>s. s X)))
    P"
  by (rule Valid_send')

text \<open>Strongest postcondition form\<close>
lemma testHL1s':
  "Valid
    (\<lambda>s tr. s = st \<and> P tr)
    (Cm (''ch''[!](\<lambda>s. s X)))
    (\<lambda>s tr. s = st \<and> (P @\<^sub>t Out\<^sub>A st ''ch'' (st X)) tr)"
  by (rule Valid_send_sp)

text \<open>Send 1, then send 2\<close>
lemma testHL2s:
  "Valid
    (\<lambda>s. Out\<^sub>A s ''ch'' (s X) @- Out\<^sub>A s ''ch'' (s Y) @- P s)
    (Cm (''ch''[!](\<lambda>s. s X)); Cm (''ch''[!](\<lambda>s. s Y)))
    P"
  apply (rule Valid_seq)
    prefer 2 apply (rule Valid_send')
  by (rule Valid_send')

text \<open>Strongest postcondition form\<close>
lemma testHL2s':
  "Valid
    (\<lambda>s tr. s = st \<and> P tr)
    (Cm (''ch''[!](\<lambda>s. s X)); Cm (''ch''[!](\<lambda>s. s Y)))
    (\<lambda>s tr. s = st \<and> (P @\<^sub>t (Out\<^sub>A s ''ch'' (s X)) @\<^sub>t (Out\<^sub>A s ''ch'' (s Y))) tr)"
  apply (rule Valid_seq)
   apply (rule Valid_send_sp)
  apply (rule Valid_strengthen_post)
   prefer 2 apply (rule Valid_send_sp)
  by (auto simp add: entails_def join_assoc)

text \<open>Receive from ch\<close>
lemma testHL3s:
  "Valid
    (\<lambda>s. \<forall>\<^sub>Av. In\<^sub>A s ''ch'' v @- P (s(X := v)))
    (Cm (''ch''[?]X))
    P"
  by (rule Valid_receive')

text \<open>Strongest postcondition form\<close>
lemma testHL3s':
  "Valid
    (\<lambda>s tr. s = st \<and> P tr)
    (Cm (''ch''[?]X))
    (\<lambda>s tr. \<exists>v. s = st(X := v) \<and> (P @\<^sub>t In\<^sub>A st ''ch'' v) tr)"
  by (rule Valid_receive_sp)

text \<open>Receive two values in a row\<close>
lemma testHL3a:
  "Valid
    ((\<lambda>s. \<forall>\<^sub>Av. In\<^sub>A s ''ch'' v @- (\<forall>\<^sub>Aw. In\<^sub>A (s(X := v)) ''ch'' w @- P (s(X := w)))))
    (Cm (''ch''[?]X); Cm (''ch''[?]X))
    P"
  apply (rule Valid_weaken_pre) prefer 2
  apply (rule Valid_seq)
    prefer 2 apply (rule Valid_receive')
  apply (rule Valid_receive')
  by (auto simp add: entails_def)

text \<open>Strongest postcondition form\<close>
lemma testHL3a':
  "Valid
    (\<lambda>s tr. s = st \<and> P tr)
    (Cm (''ch''[?]X); Cm (''ch''[?]X))
    (\<lambda>s tr. \<exists>v w. s = st(X := w) \<and> (P @\<^sub>t In\<^sub>A st ''ch'' v @\<^sub>t In\<^sub>A (st(X := v)) ''ch'' w) tr)"
  apply (rule Valid_seq)
   apply (rule Valid_receive_sp)
  apply (rule Valid_ex_pre)
  subgoal for v apply (rule Valid_ex_post)
    apply (rule exI[where x=v])
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_receive_sp)
    by (auto simp add: entails_def join_assoc)
  done

lemma ParValid_Parallel':
  assumes "Valid (\<lambda>s tr. P1 s \<and> emp\<^sub>A tr) p1 Q1"
    and "Valid (\<lambda>s tr. P2 s \<and> emp\<^sub>A tr) p2 Q2"
  shows "ParValid
    (pair_assn P1 P2)
    (Parallel (Single p1) chs (Single p2))
    (sync_gassn chs (sing_gassn Q1) (sing_gassn Q2))"
  unfolding pair_assn_def
  apply (rule ParValid_Parallel)
  using ParValid_Single assms unfolding emp_assn_def by auto

definition entails_gassn :: "gassn \<Rightarrow> gassn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>g" 25) where
  "(P \<Longrightarrow>\<^sub>g Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

definition state_gassn :: "gs_assn \<Rightarrow> gassn" where
  "state_gassn P = (\<lambda>s tr. P s)"

fun left_gassn :: "gs_assn \<Rightarrow> gassn" where
  "left_gassn P (State s) tr = False"
| "left_gassn P (ParState s1 s2) tr = P s1"

fun right_gassn :: "gs_assn \<Rightarrow> gassn" where
  "right_gassn P (State s) tr = False"
| "right_gassn P (ParState s1 s2) tr = P s2"

definition trace_gassn :: "tassn \<Rightarrow> gassn" where
  "trace_gassn P = (\<lambda>s tr. P tr)"

definition and_gassn :: "gassn \<Rightarrow> gassn \<Rightarrow> gassn" (infixr "\<and>\<^sub>g" 35) where
  "(P \<and>\<^sub>g Q) = (\<lambda>s tr. P s tr \<and> Q s tr)"

definition ex_gassn :: "('a \<Rightarrow> gassn) \<Rightarrow> gassn" (binder "\<exists>\<^sub>g" 10) where
  "(\<exists>\<^sub>g x. P x) = (\<lambda>s tr. \<exists>x. P x s tr)"

lemma ParValid_conseq':
  assumes "ParValid P c Q"
    and "\<And>s. P' s \<Longrightarrow> P s"
    and "Q \<Longrightarrow>\<^sub>g Q'"
  shows "ParValid P' c Q'"
  using assms ParValid_conseq unfolding entails_gassn_def by auto

lemma sync_gassn_ex_pre_left:
  assumes "\<And>x. sync_gassn chs (P x) Q \<Longrightarrow>\<^sub>g R"
  shows "sync_gassn chs (\<exists>\<^sub>g x. P x) Q \<Longrightarrow>\<^sub>g R"
  apply (auto simp add: entails_gassn_def)
  subgoal for s tr
    apply (cases s) apply auto
    unfolding ex_gassn_def apply auto
    using assms entails_gassn_def by fastforce
  done

lemma sync_gassn_ex_pre_right:
  assumes "\<And>x. sync_gassn chs P (Q x) \<Longrightarrow>\<^sub>g R"
  shows "sync_gassn chs P (\<exists>\<^sub>g x. Q x) \<Longrightarrow>\<^sub>g R"
  apply (auto simp add: entails_gassn_def)
  subgoal for s tr
    apply (cases s) apply auto
    unfolding ex_gassn_def apply auto
    using assms entails_gassn_def by fastforce
  done

lemma entails_ex_gassn:
  assumes "\<exists>x. P \<Longrightarrow>\<^sub>g Q x"
  shows "P \<Longrightarrow>\<^sub>g (\<exists>\<^sub>g x. Q x)"
  using assms unfolding entails_gassn_def ex_gassn_def by auto

lemma sing_gassn_split [simp]:
  "sing_gassn (\<lambda>s tr. P s \<and> Q tr) = (state_gassn (sing_assn P) \<and>\<^sub>g trace_gassn Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: state_gassn_def trace_gassn_def and_gassn_def)
  done

lemma sing_gassn_ex [simp]:
  "sing_gassn (\<lambda>s tr. \<exists>x. P x s tr) = (\<exists>\<^sub>gx. sing_gassn (\<lambda>s tr. P x s tr))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: ex_gassn_def)
  done

lemma sync_gassn_state_left:
  "sync_gassn chs (state_gassn P1 \<and>\<^sub>g P2) Q = (left_gassn P1 \<and>\<^sub>g sync_gassn chs P2 Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: and_gassn_def state_gassn_def)
  done

lemma sync_gassn_state_right:
  "sync_gassn chs P (state_gassn Q1 \<and>\<^sub>g Q2) = (right_gassn Q1 \<and>\<^sub>g sync_gassn chs P Q2)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: and_gassn_def state_gassn_def)
  done

lemma sync_gassn_traces:
  "sync_gassn chs (trace_gassn P) (trace_gassn Q) \<Longrightarrow>\<^sub>g trace_gassn (combine_assn chs P Q)"
  unfolding entails_gassn_def apply auto
  subgoal for s tr
    apply (cases s) by (auto simp add: trace_gassn_def combine_assn_def)
  done

lemma entails_trace_gassn:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> trace_gassn P \<Longrightarrow>\<^sub>g trace_gassn Q"
  unfolding entails_tassn_def entails_gassn_def trace_gassn_def by auto 

lemma and_entails_gassn:
  "P2 \<Longrightarrow>\<^sub>g P2' \<Longrightarrow> P1 \<and>\<^sub>g P2' \<Longrightarrow>\<^sub>g Q \<Longrightarrow> P1 \<and>\<^sub>g P2 \<Longrightarrow>\<^sub>g Q"
  unfolding entails_gassn_def and_gassn_def by auto

lemma and_entails_gassn2:
  "P3 \<Longrightarrow>\<^sub>g P3' \<Longrightarrow> P1 \<and>\<^sub>g P2 \<and>\<^sub>g P3' \<Longrightarrow>\<^sub>g Q \<Longrightarrow> P1 \<and>\<^sub>g P2 \<and>\<^sub>g P3 \<Longrightarrow>\<^sub>g Q"
  unfolding entails_gassn_def and_gassn_def by auto


text \<open>Communication\<close>
lemma testHL4s:
  "ParValid
    (pair_assn (\<lambda>s. s = st1) (\<lambda>s. s = st2))
    (Parallel (Single (Cm (''ch''[!](\<lambda>s. s X)))) {''ch''}
              (Single (Cm (''ch''[?]X))))
    (left_gassn (sing_assn (\<lambda>s. s = st1)) \<and>\<^sub>g right_gassn (sing_assn (\<lambda>s. s = st2(X := st1 X))) \<and>\<^sub>g
     trace_gassn (IO\<^sub>A ''ch'' (st1 X)))"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
     apply (rule testHL1s')
    apply (rule testHL3s')
   apply auto[1]
  apply auto apply (rule sync_gassn_ex_pre_right)
  subgoal for v
    unfolding sync_gassn_state_left sync_gassn_state_right
    apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
     apply (rule combine_assn_out_in') apply auto
    by (auto simp add: entails_gassn_def and_gassn_def conj_assn_def pure_assn_def trace_gassn_def)
  done

text \<open>Receive then send\<close>
lemma testHL5:
  "Valid
    (\<lambda>s. \<forall>\<^sub>Av. In\<^sub>A s ''ch1'' v @- Out\<^sub>A (s(X := v)) ''ch2'' (v + 1) @- Q (s(X := v)))
    (Cm (''ch1''[?]X); Cm (''ch2''[!](\<lambda>s. s X + 1)))
    Q"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_seq)
    prefer 2 apply (rule Valid_send')
   apply (rule Valid_receive')
  by auto

text \<open>Receive then send, strongest postcondition version\<close>
lemma testHL5sp:
  "Valid
    (\<lambda>s tr. s = st \<and> P s tr)
    (Cm (''ch1''[?]X); Cm (''ch2''[!](\<lambda>s. s X + 1)))
    (\<lambda>s tr. \<exists>v. s = st(X := v) \<and> ((P st @\<^sub>t In\<^sub>A st ''ch1'' v) @\<^sub>t Out\<^sub>A (st(X := v)) ''ch2'' (v + 1)) tr)"
  apply (rule Valid_seq)
   apply (rule Valid_receive_sp)
  apply (rule Valid_ex_pre)
  subgoal for v
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_send_sp)
    by (auto simp add: entails_def)
  done


subsection \<open>Examples for loops\<close>

text \<open>First example simply counts up variable X.\<close>

fun count_up_inv :: "real \<Rightarrow> nat \<Rightarrow> tassn" where
  "count_up_inv a 0 = emp\<^sub>A"
| "count_up_inv a (Suc n) = Out\<^sub>A ((\<lambda>_. 0)(X := a + 1)) ''ch'' (a + 1) @\<^sub>t count_up_inv (a + 1) n"

lemma count_up_inv_Suc:
  "count_up_inv a (Suc n) = count_up_inv a n @\<^sub>t Out\<^sub>A ((\<lambda>_. 0)(X := a + real n + 1)) ''ch'' (a + real n + 1)"
  apply (induct n arbitrary: a)
   apply (auto simp add: join_assoc)
  by (smt join_assoc)

lemma testLoop1:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> emp\<^sub>A tr)
    (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X))))
    (\<lambda>s tr. \<exists>n. s = ((\<lambda>_. 0)(X := a + n)) \<and> count_up_inv a n tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for n
    apply (rule Valid_seq)
    apply (rule Valid_assign_sp)
  apply (rule Valid_strengthen_post) prefer 2
     apply (rule Valid_send_sp)
    apply (auto simp add: entails_def)
    apply (rule exI[where x="Suc n"])
    by (auto simp add: count_up_inv_Suc simp del: count_up_inv.simps)    
  apply (auto simp add: entails_def)
  apply (rule exI[where x=0])
  by (auto simp add: emp_assn_def)

text \<open>In each iteration, increment by 1, output, then increment by 2.\<close>
fun count_up3_inv :: "nat \<Rightarrow> tassn" where
  "count_up3_inv 0 = emp\<^sub>A"
| "count_up3_inv (Suc n) = count_up3_inv n @\<^sub>t Out\<^sub>A ((\<lambda>_. 0)(X := 3 * real n + 1)) ''ch'' (3 * real n + 1)"

lemma testLoop2:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := 0)) \<and> emp\<^sub>A tr)
    (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X)); Assign X (\<lambda>s. s X + 2)))
    (\<lambda>s tr. \<exists>n. s = ((\<lambda>_. 0)(X := 3 * real n)) \<and> count_up3_inv n tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for n
    apply (rule Valid_seq)
     apply (rule Valid_assign_sp)
    apply (rule Valid_seq)
     apply (rule Valid_send_sp)
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_assign_sp)
    apply (auto simp add: entails_def)
    apply (rule exI[where x="Suc n"])
    by auto
    apply (auto simp add: entails_def)
  apply (rule exI[where x=0])
  by (auto simp add: emp_assn_def)

text \<open>Example that repeatedly receives on X\<close>

text \<open>Here a is the starting value of X\<close>
fun receive_inv :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "receive_inv a [] = emp\<^sub>A"
| "receive_inv a (x # xs) = In\<^sub>A ((\<lambda>_. 0)(Y := a)) ''ch'' x @\<^sub>t receive_inv x xs"

fun last_val :: "real \<Rightarrow> real list \<Rightarrow> real" where
  "last_val a [] = a"
| "last_val a (x # xs) = last_val x xs"

lemma receive_inv_snoc:
  "receive_inv a (xs @ [v]) = receive_inv a xs @\<^sub>t In\<^sub>A ((\<lambda>_. 0)(Y := last_val a xs)) ''ch'' v"
  apply (induct xs arbitrary: a)
  by (auto simp add: join_assoc)

lemma last_val_snoc [simp]:
  "last_val a (xs @ [v]) = v"
  by (induct xs arbitrary: a, auto)

lemma testLoop3:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(Y := a)) \<and> emp\<^sub>A tr)
    (Rep (Cm (''ch''[?]Y)))
    (\<lambda>s tr. \<exists>xs. s = ((\<lambda>_. 0)(Y := last_val a xs)) \<and> receive_inv a xs tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for xs
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_receive_sp)
    apply (auto simp add: entails_def)
    subgoal for tr v
      apply (rule exI[where x="xs@[v]"])
      by (auto simp add: receive_inv_snoc)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

text \<open>Example that repeated receives, and add the input values\<close>

text \<open>Here a is the starting value of X, b is the starting value of Y\<close>
fun receive_add_inv :: "real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> tassn" where
  "receive_add_inv a b [] = emp\<^sub>A"
| "receive_add_inv a b (x # xs) = In\<^sub>A ((\<lambda>_. 0)(X := a, Y := b)) ''ch'' x @\<^sub>t receive_add_inv (a + x) x xs"

fun last_add_val :: "real \<Rightarrow> real list \<Rightarrow> real" where
  "last_add_val a [] = a"
| "last_add_val a (x # xs) = last_add_val (a + x) xs"

lemma receive_add_inv_snoc:
  "receive_add_inv a b (xs @ [v]) = receive_add_inv a b xs @\<^sub>t In\<^sub>A ((\<lambda>_. 0)(X := last_add_val a xs, Y := last_val b xs)) ''ch'' v"
  apply (induct xs arbitrary: a b)
  by (auto simp add: join_assoc)

lemma last_add_val_snoc [simp]:
  "last_add_val a (xs @ [v]) = last_add_val a xs + v"
  by (induct xs arbitrary: a, auto)

lemma testLoop4:
  "Valid
    (\<lambda>s tr. s = ((\<lambda>_. 0)(X := a, Y := b)) \<and> emp\<^sub>A tr)
    (Rep (Cm (''ch''[?]Y); X ::= (\<lambda>s. s X + s Y)))
    (\<lambda>s tr. \<exists>xs. s = ((\<lambda>_. 0)(X := last_add_val a xs, Y := last_val b xs)) \<and> receive_add_inv a b xs tr)"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for xs
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_seq)
      apply (rule Valid_receive_sp)
    apply (rule Valid_assign_sp')
    apply (auto simp add: entails_def)
    subgoal for tr v
      apply (rule exI[where x="xs@[v]"])
      by (auto simp add: receive_add_inv_snoc)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

subsection \<open>Example of parallel\<close>

fun count_up_io_inv :: "real \<Rightarrow> nat \<Rightarrow> tassn" where
  "count_up_io_inv a 0 = emp\<^sub>A"
| "count_up_io_inv a (Suc n) = IO\<^sub>A ''ch'' (a + 1) @\<^sub>t count_up_io_inv (a + 1) n"

lemma combine_count_up:
  "combine_assn {''ch''} (count_up_inv a n) (receive_inv b xs) \<Longrightarrow>\<^sub>t
   count_up_io_inv a n"
proof (induction n arbitrary: a b xs)
  case 0
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by auto
  next
    case (Cons x xs')
    then show ?thesis
      by (auto simp add: combine_assn_emp_in)
  qed
next
  case (Suc n)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      by (auto simp add: combine_assn_out_emp)
  next
    case (Cons x xs')
    then show ?thesis
      apply auto
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_out_in)
       apply auto apply (rule entails_tassn_cancel_left)
      by (rule Suc)
  qed
qed

lemma testLoopPar:
  "ParValid
    (pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(X := a))) (\<lambda>s. s = ((\<lambda>_. 0)(Y := b))))
    (Parallel (Single (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X))))) {''ch''}
              (Single (Rep (Cm (''ch''[?]Y)))))
    (\<exists>\<^sub>gn. trace_gassn (count_up_io_inv a n))"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
     apply (rule testLoop1)
    apply (rule testLoop3)
   apply auto
  apply (rule sync_gassn_ex_pre_left)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for n xs
    unfolding sync_gassn_state_left sync_gassn_state_right
    apply (rule entails_ex_gassn)
    apply (rule exI[where x=n])
    apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
    apply (rule entails_tassn_trans)
     prefer 2 apply (rule combine_count_up)
    apply (rule combine_assn_mono)
    by (auto simp add: entails_tassn_def entails_gassn_def and_gassn_def)
  done


end
